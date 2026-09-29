// SPDX-License-Identifier: ISC
// Explain an SPV counterexample: the path along which run A and run B start to differ.
//
// Both runs of the spv miter share inputs and initial state; only the injected source
// may differ. So every net that differs has a differing input (a register: one step
// earlier), and walking back from the failing comparison always ends at the source.
// The idea of reading taint from the difference of two runs follows Pathfinder
// (Ceesay-Seitz et al., ICCAD 2025).

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/fstdata.h"
#include "kernel/yw.h"
#include <tuple>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// sim writes witness step k at time k * cycle_width.
static const int cycle_width = 10;

// The cell output bit that drives a net bit. Example: $ff Q[3] of a counter register.
struct Driver
{
	Cell *cell;
	IdString port;
	int offset;
};

// One net bit whose value differs between the runs at one step.
struct DiffNode
{
	SigBit bit_a, bit_b; // the same net in run A and in run B
	int step;
	int parent;          // first node this one explains, towards the destination; -1 at the destination
};

// Every difference found by walking back from the destination.
// Example: out_valid@3 has cause buff.busy@3, which has cause mul_valid@2, ...
struct DiffGraph
{
	std::vector<DiffNode> nodes;
	std::vector<std::vector<int>> causes; // node -> the differing input nodes that explain it
	std::vector<int> sources;             // nodes driven by the injected source, in search order
};

// One reported line: one bit of a named signal over steps step..last_step, with both runs' values.
struct PathEntry
{
	Wire *wire;          // run-A wire, or nullptr for an unnamed injected bit
	int step, last_step;
	std::string label, value_a, value_b, note;
	std::vector<std::string> controls; // mux selects equal in both runs that let the difference pass
};

struct SpvPathWorker
{
	Module *module;
	SigMap sigmap;
	dict<SigBit, Driver> drivers;
	dict<SigBit, std::pair<Wire *, int>> run_a_names; // net bit -> user-visible run-A wire bit
	dict<std::string, Wire *> run_b_wires;            // user name -> run-B copy of that wire
	dict<SigBit, int> value_columns;                  // net bit -> column in values
	std::vector<std::vector<State>> values;           // [step][column], replayed by sim

	// Index drivers and user-visible names of the flattened miter.
	// Example: hdlname "run_a_run_b run_a mul cnt" -> run-A wire named "mul.cnt".
	SpvPathWorker(Module *module) : module(module), sigmap(module)
	{
		for (auto cell : module->cells())
			for (auto &connection : cell->connections())
				if (cell->output(connection.first))
					for (int i = 0; i < GetSize(connection.second); i++)
						drivers[sigmap(connection.second[i])] = {cell, connection.first, i};

		for (auto wire : module->wires()) {
			// spv gives both copies the scope of their run, below the fmcombine instance.
			auto hdlname = wire->get_hdlname_attribute();
			if (GetSize(hdlname) < 3) continue;
			if (hdlname[1] == "run_b") run_b_wires[user_name(wire)] = wire;
			if (hdlname[1] != "run_a") continue;
			for (int i = 0; i < wire->width; i++) {
				// Prefer the name closest to the top when a net has several.
				auto bit = sigmap(SigBit(wire, i));
				auto known = run_a_names.find(bit);
				if (known == run_a_names.end() ||
				    GetSize(known->second.first->get_hdlname_attribute()) > GetSize(hdlname))
					run_a_names[bit] = {wire, i};
			}
		}
	}

	// Name of a run wire as the user wrote it. Example: hdlname "run_a_run_b run_a mul cnt" -> "mul.cnt".
	static std::string user_name(Wire *wire)
	{
		auto hdlname = wire->get_hdlname_attribute();
		std::string name;
		for (int i = 2; i < GetSize(hdlname); i++)
			name += (name.empty() ? "" : ".") + hdlname[i];
		return name;
	}

	// Name of one bit of a run wire. Example: (mul.cnt, offset 1) -> "mul.cnt[1]".
	static std::string bit_name(Wire *wire, int offset)
	{
		std::string name = user_name(wire);
		if (wire->width > 1) name += stringf("[%d]", wire->to_hdl_index(offset));
		return name;
	}

	// Replay the witness with every wire recorded, including internal ones, and read it back.
	// Example: trace.yw with 4 steps -> values[0..3] for every net bit.
	void replay(const std::string &witness_file)
	{
		const int steps = GetSize(ReadWitness(witness_file).steps);
		std::string fst_file = make_temp_file(get_base_tmpdir() + "/yosys_spv_path_XXXXXX.fst");
		Pass::call(module->design, std::vector<std::string>{"sim", "-q", "-a", "-width", std::to_string(cycle_width),
			"-r", witness_file, "-fst", fst_file});
		{
			FstData fst(fst_file);
			// One column per net bit: which FST variable holds it, and where.
			struct Column { fstHandle handle; int width, offset; };
			std::vector<Column> columns;
			for (auto wire : module->wires()) {
				fstHandle handle = fst.getHandle(module->name.unescape() + "." + wire->name.unescape());
				if (handle == 0) continue;
				for (int i = 0; i < wire->width; i++) {
					auto bit = sigmap(SigBit(wire, i));
					if (!bit.wire || value_columns.count(bit)) continue;
					value_columns[bit] = GetSize(columns);
					columns.push_back({handle, wire->width, i});
				}
			}

			// Samples arrive in time order and each stays valid until the next one.
			// Example: samples at times 0 and 20 -> steps 0 and 1 both use the first.
			values.resize(steps);
			std::vector<State> sample;
			int next_step = 0;
			auto use_sample_before = [&](uint64_t end_time) {
				for (; next_step < steps && uint64_t(next_step) * cycle_width < end_time; next_step++)
					values[next_step] = sample;
			};
			std::vector<fstHandle> no_clocks; // an empty clock list samples every value change
			fst.reconstructAllAtTimes(no_clocks, fst.getStartTime(), fst.getEndTime(), INT_MAX, [&](uint64_t time) {
				if (!sample.empty()) use_sample_before(time);
				sample.resize(GetSize(columns));
				fstHandle last_handle = 0;
				std::string text;
				for (int c = 0; c < GetSize(columns); c++) {
					// FST values are MSB first. Example: "0110", offset 1 -> '1'.
					if (columns[c].handle != last_handle) {
						text = fst.valueOf(columns[c].handle);
						last_handle = columns[c].handle;
						if (GetSize(text) != columns[c].width)
							log_error("FST value of width %d for a wire of width %d.\n", GetSize(text), columns[c].width);
					}
					char digit = text[columns[c].width - 1 - columns[c].offset];
					sample[c] = digit == '0' ? State::S0 : digit == '1' ? State::S1 : digit == 'z' ? State::Sz : State::Sx;
				}
			});
			use_sample_before(UINT64_MAX);
		}
		remove(fst_file.c_str());
	}

	// Replayed value of one net bit. Example: (mul.cnt[0] of run A, step 2) -> State::S1.
	State value(SigBit bit, int step)
	{
		if (!bit.wire) return bit.data;
		auto column = value_columns.find(bit);
		if (column == value_columns.end())
			log_error("No replayed value for %s.\n", log_signal(bit));
		return values.at(step)[column->second];
	}

	Const value(const SigSpec &signal, int step)
	{
		std::vector<State> bits;
		for (auto bit : sigmap(signal)) bits.push_back(value(bit, step));
		return Const(bits);
	}

	const Driver &driver(SigBit bit, int step)
	{
		auto found = drivers.find(bit);
		if (found == drivers.end())
			log_error("%s differs between the runs at step %d but has no driver.\n", log_signal(bit), step);
		return found->second;
	}

	// Whether output bit i of a cell reads only bit i of its data inputs (a $pmux also
	// reads bit i of every case, and every select bit). Example: 8-bit $and -> true; $add -> false.
	static bool is_bitwise(Cell *cell)
	{
		if (!cell->type.in(ID($not), ID($pos), ID($and), ID($or), ID($xor), ID($xnor), ID($mux), ID($pmux), ID($bwmux)))
			return cell->type.begins_with("$_"); // gate cells are one bit wide
		int width = GetSize(cell->getPort(ID::Y));
		return GetSize(cell->getPort(ID::A)) == width &&
			(!cell->hasPort(ID::B) || cell->type == ID($pmux) || GetSize(cell->getPort(ID::B)) == width);
	}

	// Input bits that one output bit reads, as (port, index), in CellTypes::eval port order.
	// Example: $mux Y[5] -> A[5], B[5], S[0]; $add Y[5] -> all of A, then all of B.
	static std::vector<std::pair<IdString, int>> input_bits(Cell *cell, int offset)
	{
		std::vector<IdString> ports = {ID::A, ID::B, ID::C, ID::D, ID::S};
		if (cell->type.in(ID($bmux), ID($demux))) ports = {ID::A, ID::S};
		std::vector<std::pair<IdString, int>> bits;
		int width = GetSize(cell->getPort(ID::Y));
		for (auto port : ports) {
			if (!cell->hasPort(port)) continue;
			int size = GetSize(cell->getPort(port));
			if (!is_bitwise(cell) || (port == ID::S && cell->type != ID($bwmux)))
				for (int i = 0; i < size; i++) bits.push_back({port, i});
			else if (port == ID::B && cell->type == ID($pmux))
				for (int i = offset; i < size; i += width) bits.push_back({port, i});
			else
				bits.push_back({port, offset});
		}
		return bits;
	}

	// Output bit of one run-A cell at a step when one of its input bits takes another value.
	// Bitwise cells are evaluated on one bit slice only. Example: $and with A=1, B=0 -> Y=0;
	// with B set to 1 instead -> Y=1.
	State output_with(Cell *cell, const Driver &output, const std::vector<std::pair<IdString, int>> &bits,
		SigBit input, State input_value, int step)
	{
		if (output.port != ID::Y)
			log_error("spv_path cannot evaluate output %s of cell %s (%s).\n", output.port, cell, cell->type);
		// One value vector per port, in the order of input_bits.
		std::vector<Const> inputs;
		std::vector<State> current;
		for (int i = 0; i < GetSize(bits); i++) {
			SigBit net = sigmap(cell->getPort(bits[i].first)[bits[i].second]);
			current.push_back(net == input ? input_value : value(net, step));
			if (i + 1 == GetSize(bits) || bits[i + 1].first != bits[i].first) {
				inputs.push_back(Const(current));
				current.clear();
			}
		}
		inputs.resize(4);
		bool error = false, bitwise = is_bitwise(cell);
		Const result;
		if (bitwise && cell->type.in(ID($not), ID($pos), ID($and), ID($or), ID($xor), ID($xnor)))
			result = CellTypes::eval(cell->type, inputs[0], inputs[1], false, false, 1, &error);
		else
			result = CellTypes::eval(cell, inputs[0], inputs[1], inputs[2], inputs[3], &error);
		if (error)
			log_error("spv_path cannot evaluate cell %s (%s).\n", cell, cell->type);
		return result[bitwise ? 0 : output.offset];
	}

	// Walk back from the differing destination bits until every difference is explained,
	// breadth first so the first source found is the one with the fewest cells in between.
	// Example: out_valid@3 <- $ff busy@2 <- ... <- $anyseq source bit in_a[2]@1.
	DiffGraph find_differences(Cell *comparison, int fail_step)
	{
		DiffGraph graph;
		dict<std::tuple<SigBit, SigBit, int>, int> index;
		// Record that (a, b, step) explains node parent; returns false if a and b are equal.
		auto add_if_different = [&](SigBit a, SigBit b, int step, int parent) {
			if (value(a, step) == value(b, step)) return false;
			auto found = index.find({a, b, step});
			int node = found != index.end() ? found->second : GetSize(graph.nodes);
			if (found == index.end()) {
				index[{a, b, step}] = node;
				graph.nodes.push_back({a, b, step, parent});
				graph.causes.emplace_back();
			}
			if (parent >= 0) graph.causes[parent].push_back(node);
			return true;
		};

		SigSpec destination_a = sigmap(comparison->getPort(ID::A));
		SigSpec destination_b = sigmap(comparison->getPort(ID::B));
		for (int i = 0; i < GetSize(destination_a); i++)
			add_if_different(destination_a[i], destination_b[i], fail_step, -1);

		for (int n = 0; n < GetSize(graph.nodes); n++) {
			DiffNode node = graph.nodes[n]; // copy: adding nodes may reallocate
			const Driver &driver_a = driver(node.bit_a, node.step);
			if (driver_a.cell->type == ID($anyseq)) {
				// Shared free values are equal in both runs, so this is the injected source.
				graph.sources.push_back(n);
				continue;
			}
			const Driver &driver_b = driver(node.bit_b, node.step);
			if (driver_a.cell->type != driver_b.cell->type || driver_a.port != driver_b.port ||
			    driver_a.offset != driver_b.offset || driver_a.cell->parameters != driver_b.cell->parameters)
				log_error("Run A and run B are not copies of each other at %s / %s (%s / %s).\n",
					log_signal(node.bit_a), log_signal(node.bit_b), driver_a.cell, driver_b.cell);

			Cell *cell_a = driver_a.cell, *cell_b = driver_b.cell;
			if (cell_a->type.in(ID($ff), ID($anyinit))) {
				// A register difference was loaded from a data difference one step earlier.
				if (node.step == 0)
					log_error("Register %s starts with different values in the two runs.\n", cell_a);
				SigBit data_a = sigmap(cell_a->getPort(ID::D)[driver_a.offset]);
				SigBit data_b = sigmap(cell_b->getPort(ID::D)[driver_b.offset]);
				if (!add_if_different(data_a, data_b, node.step - 1, n))
					log_error("Register %s differs at step %d without a data difference before.\n", cell_a, node.step);
				continue;
			}
			if (!yosys_celltypes.cell_evaluable(cell_a->type))
				log_error("spv_path does not support cell %s (%s); use SBY's model/design_prep.il.\n",
					cell_a, cell_a->type);
			// Collect the input net bits that differ. Example: $mux with A and B differing, S equal.
			auto bits = input_bits(cell_a, driver_a.offset);
			std::vector<std::pair<SigBit, SigBit>> differing;
			pool<SigBit> listed;
			for (auto &bit : bits) {
				SigBit input_a = sigmap(cell_a->getPort(bit.first)[bit.second]);
				SigBit input_b = sigmap(cell_b->getPort(bit.first)[bit.second]);
				if (value(input_a, node.step) != value(input_b, node.step) && listed.insert(input_a).second)
					differing.push_back({input_a, input_b});
			}
			if (differing.empty())
				log_error("Cell %s differs at step %d with equal inputs.\n", cell_a, node.step);
			// Follow only differences that change this output bit on their own: give run A
			// one input bit of run B and re-evaluate. Example: an unselected mux branch is
			// skipped. If no single bit does it (an AND whose two inputs both flip), all do.
			// A single differing input is the cause without evaluating anything.
			std::vector<std::pair<SigBit, SigBit>> causes;
			if (GetSize(differing) > 1)
				for (auto &candidate : differing)
					if (output_with(cell_a, driver_a, bits, candidate.first, value(candidate.second, node.step), node.step) !=
					    value(node.bit_a, node.step))
						causes.push_back(candidate);
			if (causes.empty()) causes = differing;
			for (auto &cause : causes)
				add_if_different(cause.first, cause.second, node.step, n);
		}
		if (graph.sources.empty())
			log_error("No injected source explains the difference; the two-run model is broken.\n");
		log("Visited %d differing bit-steps.\n", GetSize(graph.nodes));
		return graph;
	}

	// The path through the first source found, source first. Example: in_a[0]@2 ... out_valid@3.
	static std::vector<DiffNode> shortest_path(const DiffGraph &graph)
	{
		std::vector<DiffNode> path;
		for (int n = graph.sources.front(); n >= 0; n = graph.nodes[n].parent)
			path.push_back(graph.nodes[n]);
		return path;
	}

	// Mux selects that are equal in both runs decide which way the difference goes.
	// Example: $mux with S = mul.busy, 1 in both runs -> "mul.busy = 1'1 (rtl/mul.sv:12)".
	std::string control_of(const DiffNode &node)
	{
		Cell *cell_a = drivers.at(node.bit_a).cell, *cell_b = drivers.at(node.bit_b).cell;
		if (!cell_a->type.in(ID($mux), ID($pmux))) return "";
		SigSpec select_a = sigmap(cell_a->getPort(ID::S));
		Const select_value = value(select_a, node.step);
		if (select_value != value(cell_b->getPort(ID::S), node.step)) return "";
		auto named = GetSize(select_a) == 1 ? run_a_names.find(select_a[0]) : run_a_names.end();
		std::string name = named != run_a_names.end() ? bit_name(named->second.first, named->second.second) : "select";
		return stringf("%s = %s (%s %s)", name, log_const(select_value), log_id(cell_a->type), cell_a->get_src_attribute());
	}

	// Turn the bit path into lines of named signals; unnamed internal nets are skipped.
	// Example: in_a[2]@1 (injected) -> mul.cnt[0]@2 -> out_valid@3 (destination).
	std::vector<PathEntry> describe(const std::vector<DiffNode> &path, const std::vector<std::string> &source_bit_names)
	{
		std::vector<PathEntry> entries;
		std::vector<std::string> controls;
		for (int i = 0; i < GetSize(path); i++) {
			const DiffNode &node = path[i];
			if (i > 0) {
				auto control = control_of(node);
				if (!control.empty()) controls.push_back(control);
			}
			auto named = run_a_names.find(node.bit_a);
			if (i == 0) {
				// The source line names the -from bit and, if any, the wire that reads it.
				int offset = drivers.at(node.bit_a).offset;
				if (offset >= GetSize(source_bit_names))
					log_error("Source bit %d has no name; rerun spv to rebuild the model.\n", offset);
				PathEntry entry{nullptr, node.step, node.step, source_bit_names[offset],
					log_const(Const(value(node.bit_a, node.step))), log_const(Const(value(node.bit_b, node.step))),
					"injected source", {}};
				if (named != run_a_names.end())
					entry.note += ", read as " + bit_name(named->second.first, named->second.second);
				entries.push_back(entry);
				continue;
			}
			if (named == run_a_names.end()) {
				if (i == GetSize(path) - 1)
					log_error("Destination bit %s has no user-visible name.\n", log_signal(node.bit_a));
				continue;
			}
			Wire *wire_a = named->second.first;
			std::string label = bit_name(wire_a, named->second.second);
			auto &last = entries.back();
			if (last.wire == wire_a && last.label == label && last.controls == controls &&
			    (last.step == node.step || last.last_step + 1 == node.step)) {
				// The same bit held under the same conditions, e.g. a register keeping its value.
				last.last_step = node.step;
				controls.clear();
				continue;
			}
			Cell *assigner = drivers.at(node.bit_a).cell;
			entries.push_back({wire_a, node.step, node.step, label,
				log_const(Const(value(node.bit_a, node.step))), log_const(Const(value(node.bit_b, node.step))),
				stringf("%s %s", log_id(assigner->type), assigner->get_src_attribute()), controls});
			controls.clear();
		}
		entries.back().note = "destination, " + entries.back().note;
		return entries;
	}

	// Draw every source-to-destination path at signal level, like Pathfinder's reduced
	// graph: one node per signal, unnamed internal nets skipped, and each edge labeled
	// with the steps at which the difference crossed it.
	// Example: in_a -> mul_valid [2], mul_valid -> buff.busy [3], buff.busy -> out_valid [3].
	void write_dot(const std::string &filename, const DiffGraph &graph, const std::vector<std::string> &source_bit_names)
	{
		// Signal name of a node, or "" for an unnamed net. Source bits use the -from name.
		// Example: mul.cnt[1] -> "mul.cnt"; injected bit "key[7]" -> "key".
		pool<int> source_nodes(graph.sources.begin(), graph.sources.end());
		auto signal_of = [&](int n) -> std::string {
			if (source_nodes.count(n)) {
				std::string name = source_bit_names.at(drivers.at(graph.nodes[n].bit_a).offset);
				return name.back() == ']' ? name.substr(0, name.rfind('[')) : name;
			}
			auto named = run_a_names.find(graph.nodes[n].bit_a);
			return named == run_a_names.end() ? "" : user_name(named->second.first);
		};

		// Nearest named causes of each node, looking through unnamed nets.
		std::vector<std::vector<int>> named_causes(GetSize(graph.nodes));
		std::vector<bool> done(GetSize(graph.nodes));
		std::function<const std::vector<int> &(int)> nearest_named = [&](int n) -> const std::vector<int> & {
			if (done[n]) return named_causes[n];
			done[n] = true;
			pool<int> found;
			for (int cause : graph.causes[n]) {
				if (!signal_of(cause).empty()) found.insert(cause);
				else for (int c : nearest_named(cause)) found.insert(c);
			}
			named_causes[n] = std::vector<int>(found.begin(), found.end());
			return named_causes[n];
		};

		// Edge between two signals -> first and last step at which it carried the difference.
		dict<std::pair<std::string, std::string>, std::pair<int, int>> edges;
		pool<std::string> signals, sources, destinations;
		for (int n = 0; n < GetSize(graph.nodes); n++) {
			std::string signal = signal_of(n);
			if (signal.empty()) continue;
			signals.insert(signal);
			if (source_nodes.count(n)) sources.insert(signal);
			if (graph.nodes[n].parent < 0) destinations.insert(signal);
			for (int cause : nearest_named(n)) {
				int step = graph.nodes[n].step;
				auto edge = edges.find({signal_of(cause), signal});
				if (edge == edges.end())
					edges[{signal_of(cause), signal}] = {step, step};
				else
					edge->second = {std::min(edge->second.first, step), std::max(edge->second.second, step)};
			}
		}

		std::ofstream dot(filename);
		if (!dot) log_error("Cannot write %s.\n", filename);
		dot << "digraph spv_path {\n  rankdir=LR;\n  node [shape=ellipse];\n";
		for (auto &signal : signals) {
			std::string style = sources.count(signal) ? ", style=filled, fillcolor=lightcoral" :
				destinations.count(signal) ? ", style=filled, fillcolor=lightblue" : "";
			dot << stringf("  \"%s\" [label=\"%s\"%s];\n", signal, signal, style);
		}
		for (auto &edge : edges) {
			auto steps = edge.second;
			std::string label = steps.first == steps.second ? std::to_string(steps.first) :
				stringf("%d-%d", steps.first, steps.second);
			dot << stringf("  \"%s\" -> \"%s\" [label=\"%s\"];\n", edge.first.first, edge.first.second, label);
		}
		dot << "}\n";
		log("Wrote %s: %d signals, %d edges.\n", filename, GetSize(signals), GetSize(edges));
	}

	// Steps of one entry. Example: 4..9 -> "4-9"; 3..3 -> "3".
	static std::string step_range(const PathEntry &entry)
	{
		if (entry.step == entry.last_step) return std::to_string(entry.step);
		return stringf("%d-%d", entry.step, entry.last_step);
	}

	void run(const std::string &witness_file, const std::string &dot_file)
	{
		Cell *assertion = nullptr;
		for (auto cell : module->cells())
			if (cell->type == ID($assert) && cell->has_attribute(ID(spv_property))) {
				if (assertion) log_error("Module %s has more than one SPV assertion.\n", module);
				assertion = cell;
			}
		if (!assertion)
			log_error("Module %s has no SPV assertion; read SBY's model/design_prep.il.\n", module);
		SigBit equal = sigmap(assertion->getPort(ID::A)), enable = sigmap(assertion->getPort(ID::EN));
		auto comparison = drivers.find(equal);
		if (comparison == drivers.end() || comparison->second.cell->type != ID($eq))
			log_error("SPV assertion %s is not driven by the run A/B comparison.\n", assertion);

		replay(witness_file);
		int fail_step = -1;
		for (int step = 0; step < GetSize(values) && fail_step < 0; step++)
			if (value(enable, step) == State::S1 && value(equal, step) == State::S0)
				fail_step = step;
		if (fail_step < 0)
			log_error("The witness does not violate SPV assertion %s.\n", assertion);

		auto graph = find_differences(comparison->second.cell, fail_step);
		auto source_bit_names = split_tokens(assertion->get_string_attribute(ID(spv_source_bits)));
		auto entries = describe(shortest_path(graph), source_bit_names);

		log("SPV property %s fails at step %d. Shortest path from source to destination:\n",
			assertion->get_string_attribute(ID(spv_property)), fail_step);
		for (auto &entry : entries) {
			log("  step %-9s %-32s run_a=%-5s run_b=%-5s %s\n", step_range(entry), entry.label,
				entry.value_a, entry.value_b, entry.note);
			for (auto &control : entry.controls)
				log("           when %s\n", control);
		}
		if (!dot_file.empty())
			write_dot(dot_file, graph, source_bit_names);
	}
};

struct SpvPathPass : Pass
{
	SpvPathPass() : Pass("spv_path", "show how the source difference reaches the destination in an SPV counterexample") { }

	void help() override
	{
		log("\n    spv_path -witness <trace.yw> [-dot <file>]\n\n");
		log("Replay an SPV counterexample and explain it. The text output is the shortest\n");
		log("path along which run A and run B differ: from an injected -from bit, through\n");
		log("named signals and registers, to the compared -to bit at the first failing step.\n");
		log("Each line shows the step, both runs' values and the cell and RTL location that\n");
		log("assign the signal. Mux selects that are equal in both runs are listed as the\n");
		log("conditions that let the difference pass.\n\n");
		log("Run it on SBY's prepared model, from the engine directory of a failing task:\n");
		log("    read_rtlil ../model/design_prep.il\n");
		log("    spv_path -witness trace.yw -dot path.dot\n\n");
		log("    -dot <file>    also draw every path from the sources to the destination, one\n");
		log("                   node per signal; edge labels are the steps at which the\n");
		log("                   difference crossed that edge (source red, destination blue)\n\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		std::string witness_file, dot_file;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-witness" && argidx + 1 < args.size()) {
				witness_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-dot" && argidx + 1 < args.size()) {
				dot_file = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if (witness_file.empty()) log_cmd_error("spv_path requires -witness.\n");
		Module *module = design->top_module();
		if (!module) log_cmd_error("spv_path requires a top module.\n");
		log_header(design, "Executing SPV_PATH pass for %s.\n", module);
		SpvPathWorker(module).run(witness_file, dot_file);
	}
} SpvPathPass;

PRIVATE_NAMESPACE_END
