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
#include <filesystem>
#include <numeric>
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

// One signal of the taint waveform: its bits in both runs and its name below the top scope.
// Example: run-A wire mul.in_a -> scope {"mul"}, name "in_a", range "[3:0]".
struct WaveSignal
{
	std::vector<std::string> scope;
	std::string name, range; // range is "" for a one-bit wire
	SigSpec bits_a, bits_b;  // LSB first

	// Example: scope {"mul"}, name "in_a" -> "mul.in_a".
	std::string dotted_name() const
	{
		std::string text;
		for (auto &part : scope) text += part + ".";
		return text + name;
	}
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

	// Split a -from bit name into signal and HDL index. Example: "key[7]" -> ("key", "7");
	// a one-bit wire "rst" -> ("rst", "").
	static std::pair<std::string, std::string> split_bit_name(const std::string &name)
	{
		if (name.back() != ']') return {name, ""};
		auto bracket = name.rfind('[');
		return {name.substr(0, bracket), name.substr(bracket + 1, name.size() - bracket - 2)};
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
			if (source_nodes.count(n))
				return split_bit_name(source_bit_names.at(drivers.at(graph.nodes[n].bit_a).offset)).first;
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

	// Signals of the taint waveform, like the fanin Jasper exports for a counterexample:
	// first the -from signals with the values the two runs actually read, then every named
	// run-A signal in the structural fanin of the destination, sorted by name.
	// Example: buffered_mul -> in_a, in_b (injected), buff.busy, ..., mul.in_a, ..., out_valid.
	std::vector<WaveSignal> wave_signals(Cell *comparison, const DiffGraph &graph,
		const std::vector<std::string> &source_bit_names)
	{
		// Run A reads the $anyseq that drives a found source bit. Run B reads the output of the
		// cell that drives the same bit in run B: the source-choice $mux, whose A input is run A's
		// value, or its own $anyseq. prep may narrow the $mux to the bits run B reads, so pair
		// bits through A -> Y. Example: se_cache's 704 source bits, $mux narrowed to 384.
		const DiffNode &source = graph.nodes.at(graph.sources.front());
		SigSpec injected_a = sigmap(drivers.at(source.bit_a).cell->getPort(ID::Y));
		Cell *choice = driver(source.bit_b, source.step).cell;
		SigSpec choice_y = sigmap(choice->getPort(ID::Y));
		SigSpec choice_a = choice->type == ID($mux) ? sigmap(choice->getPort(ID::A)) : injected_a;
		if (GetSize(injected_a) != GetSize(source_bit_names) || GetSize(choice_a) != GetSize(choice_y))
			log_error("The injected source does not match the %d -from bits; rerun spv to rebuild the model.\n",
				GetSize(source_bit_names));
		dict<SigBit, SigBit> run_b_of;
		for (int i = 0; i < GetSize(choice_y); i++)
			run_b_of[choice_a[i]] = choice_y[i];
		// A source bit that run B never reads cannot make a visible difference: draw it untainted.
		SigSpec injected_b;
		int unread = 0;
		for (auto bit : injected_a) {
			auto found = run_b_of.find(bit);
			injected_b.append(found != run_b_of.end() ? found->second : bit);
			unread += found == run_b_of.end();
		}
		if (unread > 0)
			log("%d of %d source bits are not read by run B; they are drawn without taint.\n",
				unread, GetSize(injected_a));

		// Group the -from bits into signals. Example: "in_a[0] in_a[1]" -> in_a with (0, 0), (1, 1).
		std::vector<std::string> source_names;
		dict<std::string, std::vector<std::pair<int, int>>> source_bits; // name -> (HDL index, injected offset)
		pool<std::string> sliced; // sources given as bits of a wider wire
		for (int i = 0; i < GetSize(source_bit_names); i++) {
			auto [name, index] = split_bit_name(source_bit_names[i]);
			if (!source_bits.count(name)) source_names.push_back(name);
			if (!index.empty()) sliced.insert(name);
			source_bits[name].push_back({index.empty() ? 0 : std::stoi(index), i});
		}
		std::vector<WaveSignal> signals;
		for (auto &name : source_names) {
			auto &bits = source_bits[name];
			std::sort(bits.begin(), bits.end());
			WaveSignal signal;
			signal.scope = split_tokens(name, ".");
			signal.name = signal.scope.back();
			signal.scope.pop_back();
			for (int k = 0; k < GetSize(bits); k++) {
				if (bits[k].first != bits[0].first + k)
					log_error("Source %s is not one contiguous slice; spv_path cannot draw it as one signal.\n", name);
				signal.bits_a.append(injected_a[bits[k].second]);
				signal.bits_b.append(injected_b[bits[k].second]);
			}
			// Example: key[15:8] -> "[15:8]"; a single bit key[7] -> "[7]".
			if (sliced.count(name))
				signal.range = GetSize(bits) == 1 ? stringf("[%d]", bits[0].first) :
					stringf("[%d:%d]", bits.back().first, bits.front().first);
			signals.push_back(signal);
		}

		// Structural fanin of the run-A destination, one cell at a time.
		pool<SigBit> fanin;
		pool<Cell *> visited;
		std::vector<SigBit> pending;
		for (auto bit : sigmap(comparison->getPort(ID::A))) pending.push_back(bit);
		while (!pending.empty()) {
			SigBit bit = pending.back();
			pending.pop_back();
			if (!bit.wire || !fanin.insert(bit).second) continue;
			auto found = drivers.find(bit);
			if (found == drivers.end() || !visited.insert(found->second.cell).second) continue; // top input, or seen
			for (auto &connection : found->second.cell->connections())
				if (found->second.cell->input(connection.first))
					for (auto input : sigmap(connection.second)) pending.push_back(input);
		}

		pool<std::string> source_set(source_names.begin(), source_names.end());
		std::vector<WaveSignal> fanin_signals;
		for (auto wire : module->wires()) {
			auto hdlname = wire->get_hdlname_attribute();
			if (GetSize(hdlname) < 3 || hdlname[1] != "run_a") continue;
			SigSpec bits_a = sigmap(wire);
			bool in_fanin = false;
			for (auto bit : bits_a) in_fanin |= fanin.count(bit) > 0;
			if (!in_fanin) continue;
			// Under a -from name the design reads the injected value, which is already listed.
			std::string name = user_name(wire);
			if (source_set.count(name)) continue;
			auto twin = run_b_wires.find(name);
			if (twin == run_b_wires.end())
				log_error("Run-A wire %s has no run-B copy.\n", name);
			WaveSignal signal{{hdlname.begin() + 2, hdlname.end() - 1}, hdlname.back(), "", bits_a, sigmap(twin->second)};
			if (wire->width > 1)
				signal.range = stringf("[%d:%d]", wire->to_hdl_index(wire->width - 1), wire->to_hdl_index(0));
			fanin_signals.push_back(signal);
		}
		std::sort(fanin_signals.begin(), fanin_signals.end(),
			[](const WaveSignal &x, const WaveSignal &y) { return x.dotted_name() < y.dotted_name(); });
		signals.insert(signals.end(), fanin_signals.begin(), fanin_signals.end());
		return signals;
	}

	// Short VCD identifier of signal number n. Example: 0 -> "!", 94 -> "!\"".
	static std::string vcd_id(int n)
	{
		std::string id;
		do {
			id += char('!' + n % 94);
			n /= 94;
		} while (n > 0);
		return id;
	}

	// Write run A's value of every signal plus a one-bit <name>__taint that is 1 while the two
	// runs differ on any of its bits. Step k is at time k * cycle_width, as in SBY's trace.vcd.
	// Example: in_a = 4'b0000 with in_a__taint = 1 at steps 1-2 of buffered_mul.
	void write_vcd(const std::string &filename, const std::vector<WaveSignal> &signals)
	{
		std::ofstream vcd(filename);
		if (!vcd) log_error("Cannot write %s.\n", filename);
		vcd << "$version Yosys spv_path $end\n$timescale 1ns $end\n";
		vcd << "$scope module " << module->name.unescape() << " $end\n";
		// Sorted by scope, every scope is opened once. Signal s uses ids 2s (value) and 2s+1 (taint).
		std::vector<int> order(GetSize(signals));
		std::iota(order.begin(), order.end(), 0);
		std::sort(order.begin(), order.end(), [&](int x, int y) {
			return std::tie(signals[x].scope, signals[x].name) < std::tie(signals[y].scope, signals[y].name);
		});
		std::vector<std::string> open;
		for (int s : order) {
			auto &scope = signals[s].scope;
			size_t common = 0;
			while (common < open.size() && common < scope.size() && open[common] == scope[common]) common++;
			for (; open.size() > common; open.pop_back()) vcd << "$upscope $end\n";
			for (; open.size() < scope.size(); open.push_back(scope[open.size()]))
				vcd << "$scope module " << scope[open.size()] << " $end\n";
			std::string range = signals[s].range.empty() ? "" : " " + signals[s].range;
			vcd << stringf("$var wire %d %s %s%s $end\n", GetSize(signals[s].bits_a), vcd_id(2 * s), signals[s].name, range);
			vcd << stringf("$var wire 1 %s %s__taint $end\n", vcd_id(2 * s + 1), signals[s].name);
		}
		for (; !open.empty(); open.pop_back()) vcd << "$upscope $end\n";
		vcd << "$upscope $end\n$enddefinitions $end\n";

		// Write only changes; the first step writes every value.
		std::vector<std::string> last(2 * GetSize(signals));
		auto write_change = [&](int id, const std::string &text) {
			if (text == last[id]) return;
			vcd << text << "\n";
			last[id] = text;
		};
		for (int step = 0; step < GetSize(values); step++) {
			vcd << "#" << step * cycle_width << "\n";
			for (int s = 0; s < GetSize(signals); s++) {
				Const value_a = value(signals[s].bits_a, step);
				std::string bits = value_a.as_string(); // MSB first
				write_change(2 * s, GetSize(bits) == 1 ? bits + vcd_id(2 * s) : "b" + bits + " " + vcd_id(2 * s));
				bool differs = value_a != value(signals[s].bits_b, step);
				write_change(2 * s + 1, (differs ? "1" : "0") + vcd_id(2 * s + 1));
			}
		}
		// Close the last step so viewers draw it with a full step width.
		vcd << "#" << GetSize(values) * cycle_width << "\n";
		log("Wrote %s: %d signals with taint.\n", filename, GetSize(signals));
	}

	// GTKWave view of the taint waveform: the text path's signals in path order, then the
	// rest of the fanin, each followed by its taint in red. Open with: gtkwave path.gtkw
	void write_gtkw(const std::string &filename, const std::string &vcd_file,
		const std::vector<WaveSignal> &signals, const std::vector<PathEntry> &entries)
	{
		dict<std::string, int> by_name;
		for (int s = 0; s < GetSize(signals); s++) by_name[signals[s].dotted_name()] = s;
		// The source entry has no wire; its label is the -from bit. Example: "in_a[0]" -> in_a.
		std::vector<int> path;
		pool<int> on_path;
		for (auto &entry : entries) {
			std::string name = entry.wire ? user_name(entry.wire) : split_bit_name(entry.label).first;
			auto found = by_name.find(name);
			if (found == by_name.end())
				log_error("Path signal %s is missing from the waveform.\n", name);
			if (on_path.insert(found->second).second) path.push_back(found->second);
		}

		std::ofstream gtkw(filename);
		if (!gtkw) log_error("Cannot write %s.\n", filename);
		gtkw << "[dumpfile] \"" << std::filesystem::absolute(vcd_file).string() << "\"\n";
		// Flags: @28 binary, @22 hex, @200 a comment line. Color 1 is red.
		auto add_trace = [&](int s) {
			std::string name = module->name.unescape() + "." + signals[s].dotted_name();
			gtkw << (GetSize(signals[s].bits_a) == 1 ? "@28\n" : "@22\n") << name << signals[s].range << "\n";
			gtkw << "@28\n[color] 1\n" << name << "__taint\n";
		};
		gtkw << "@200\n-Path from source to destination\n";
		for (int s : path) add_trace(s);
		gtkw << "@200\n-\n@200\n-Rest of the destination fanin\n";
		for (int s = 0; s < GetSize(signals); s++)
			if (!on_path.count(s)) add_trace(s);
		log("Wrote %s: %d path signals, %d others.\n", filename, GetSize(path), GetSize(signals) - GetSize(path));
	}

	void run(const std::string &witness_file, const std::string &dot_file, const std::string &vcd_file,
		const std::string &gtkw_file)
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
		if (!vcd_file.empty()) {
			auto signals = wave_signals(comparison->second.cell, graph, source_bit_names);
			write_vcd(vcd_file, signals);
			if (!gtkw_file.empty())
				write_gtkw(gtkw_file, vcd_file, signals, entries);
		}
	}
};

struct SpvPathPass : Pass
{
	SpvPathPass() : Pass("spv_path", "show how the source difference reaches the destination in an SPV counterexample") { }

	void help() override
	{
		log("\n    spv_path -witness <trace.yw> [-dot <file>] [-vcd <file> [-gtkw <file>]]\n\n");
		log("Replay an SPV counterexample and explain it. The text output is the shortest\n");
		log("path along which run A and run B differ: from an injected -from bit, through\n");
		log("named signals and registers, to the compared -to bit at the first failing step.\n");
		log("Each line shows the step, both runs' values and the cell and RTL location that\n");
		log("assign the signal. Mux selects that are equal in both runs are listed as the\n");
		log("conditions that let the difference pass.\n\n");
		log("Run it on SBY's prepared model, from the engine directory of a failing task:\n");
		log("    read_rtlil ../model/design_prep.il\n");
		log("    spv_path -witness trace.yw -dot path.dot -vcd path.vcd -gtkw path.gtkw\n\n");
		log("    -dot <file>    also draw every path from the sources to the destination, one\n");
		log("                   node per signal; edge labels are the steps at which the\n");
		log("                   difference crossed that edge (source red, destination blue)\n\n");
		log("    -vcd <file>    write a taint waveform: the -from signals and every named\n");
		log("                   signal in the destination's fanin, with run A's value and\n");
		log("                   <name>__taint = 1 while the runs differ. Step k is at time 10k.\n\n");
		log("    -gtkw <file>   write a GTKWave view of that waveform: the text path's signals\n");
		log("                   first, in path order, each followed by its taint in red\n\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		std::string witness_file, dot_file, vcd_file, gtkw_file;
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
			if (args[argidx] == "-vcd" && argidx + 1 < args.size()) {
				vcd_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-gtkw" && argidx + 1 < args.size()) {
				gtkw_file = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if (witness_file.empty()) log_cmd_error("spv_path requires -witness.\n");
		if (!gtkw_file.empty() && vcd_file.empty()) log_cmd_error("spv_path -gtkw requires -vcd.\n");
		Module *module = design->top_module();
		if (!module) log_cmd_error("spv_path requires a top module.\n");
		log_header(design, "Executing SPV_PATH pass for %s.\n", module);
		SpvPathWorker(module).run(witness_file, dot_file, vcd_file, gtkw_file);
	}
} SpvPathPass;

PRIVATE_NAMESPACE_END
