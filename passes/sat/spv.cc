// SPDX-License-Identifier: ISC
// Security path verification by two executions of the same circuit.

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "frontends/ast/ast.h"
#include <charconv>
#include <sstream>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Resolve one named wire or HDL slice without merging its aliases.
// Example: "key[15:8]" -> the eight corresponding RTLIL bits, LSB first.
SigSpec resolve_spv_signal(Module *module, const std::string &text)
{
	Wire *wire = module->wire(RTLIL::escape_id(text));
	if (wire)
		return wire;

	std::string name = text;
	std::string slice;
	if (!text.empty() && text.back() == ']') {
		auto bracket = text.rfind('[');
		if (bracket != std::string::npos) {
			name = text.substr(0, bracket);
			slice = text.substr(bracket + 1, text.size() - bracket - 2);
		}
	}
	wire = module->wire(RTLIL::escape_id(name));
	if (!wire) {
		for (auto candidate : module->wires()) {
			std::string hdlname;
			for (const auto &part : candidate->get_hdlname_attribute()) {
				if (!hdlname.empty()) hdlname += '.';
				hdlname += part;
			}
			if (hdlname != name) continue;
			if (wire)
				log_cmd_error("Ambiguous SPV signal '%s'.\n", text);
			wire = candidate;
		}
	}
	if (!wire)
		log_cmd_error("SPV signal '%s' not found in module %s.\n", text, module);
	if (slice.empty()) {
		if (name != text)
			log_cmd_error("Empty slice in SPV signal '%s'.\n", text);
		return wire;
	}

	// Use Yosys's HDL-index conversion, including ascending and offset ranges.
	auto parse_index = [&](const std::string &value) {
		int index;
		auto parsed = std::from_chars(value.data(), value.data() + value.size(), index);
		if (parsed.ec != std::errc() || parsed.ptr != value.data() + value.size())
			log_cmd_error("Invalid slice in SPV signal '%s'.\n", text);
		int offset = wire->from_hdl_index(index);
		if (offset == INT_MIN)
			log_cmd_error("HDL index %d is outside SPV signal '%s'.\n", index, text);
		return offset;
	};
	auto colon = slice.find(':');
	int first = parse_index(slice.substr(0, colon));
	int last = colon == std::string::npos ? first : parse_index(slice.substr(colon + 1));
	return SigSpec(wire, std::min(first, last), std::abs(first - last) + 1);
}

struct SpvBuilder
{
	Design temporary;
	Module *base;
	Module *product;
	IdString source_port, destination_port, from_condition_port, to_condition_port;
	IdString property_name;
	std::string initial_state;
	SigSpec sources, destinations, from_condition, to_condition;
	int source_width;
	bool has_from_condition, has_to_condition;

	// Work on a private copy; the user's DUT and selection stay intact.
	// Example: DUT + from/to selections -> a private base ready for source cutting.
	SpvBuilder(Module *original, const std::vector<std::string> &from,
		const std::vector<std::string> &to, const std::string &from_precond,
		const std::string &to_precond, const std::vector<std::string> &clocks,
		const std::string &reset, const std::vector<std::string> &assumptions,
		IdString name, const std::string &init) : property_name(name), initial_state(init)
	{
		base = original->clone();
		base->name = ID(spv_base);
		base->attributes.erase(ID::top);
		base->attributes.erase(ID::initial_top);
		temporary.add(base);
		for (auto wire : base->wires()) {
			wire->port_output = false;
			if (!wire->port_input) wire->port_id = 0;
		}

		// Keep command order, and reject repeated bits rather than silently changing it.
		pool<SigBit> selected;
		for (const auto &text : from) {
			auto signal = resolve_spv_signal(base, text);
			for (auto bit : signal)
				if (!selected.insert(bit).second)
					log_cmd_error("Repeated SPV source bit in '%s'.\n", text);
			sources.append(signal);
		}
		selected.clear();
		for (const auto &text : to) {
			auto signal = resolve_spv_signal(base, text);
			for (auto bit : signal)
				if (!selected.insert(bit).second)
					log_cmd_error("Repeated SPV destination bit in '%s'.\n", text);
			destinations.append(signal);
		}
		if (sources.empty() || destinations.empty())
			log_cmd_error("SPV sources and destinations must not be empty.\n");
		source_width = GetSize(sources);
		has_from_condition = !from_precond.empty();
		has_to_condition = !to_precond.empty();
		std::vector<std::string> expressions = {from_precond, to_precond, reset};
		expressions.insert(expressions.end(), assumptions.begin(), assumptions.end());
		auto conditions = read_conditions(expressions);
		from_condition = conditions[0];
		to_condition = conditions[1];
		add_environment(clocks, !reset.empty(), conditions);
	}

	// Let the native Verilog frontend handle operators, widths, signedness and slices.
	// Example: "child.count[7:0] == 3" -> a one-bit condition connected to that raw net.
	std::vector<SigSpec> read_conditions(const std::vector<std::string> &expressions)
	{
		std::vector<SigSpec> results(expressions.size(), State::S1);
		if (std::all_of(expressions.begin(), expressions.end(), [](const auto &s) { return s.empty(); }))
			return results;

		// Parse only the expressions first. Declaring every DUT wire as a port is very
		// expensive on large designs; the native AST tells us exactly which names occur.
		std::ostringstream source;
		source << "module spv_conditions(\n";
		std::vector<IdString> outputs;
		for (int i = 0; i < GetSize(expressions); i++) {
			outputs.push_back(base->uniquify(stringf("\\spv_condition_%d", i)));
			source << "output " << outputs.back().str() << (i + 1 == GetSize(expressions) ? " );\n" : " ,\n");
		}
		for (int i = 0; i < GetSize(expressions); i++)
			source << "assign " << outputs[i].str() << " = !!("
				<< (expressions[i].empty() ? "1'b1" : expressions[i]) << " );\n";
		source << "endmodule\n";
		std::istringstream input(source.str());
		Frontend::frontend_call(&temporary, &input, "<spv conditions>", "verilog -sv -noautowire -defer");
		auto parsed = dynamic_cast<AST::AstModule *>(temporary.module("$abstract\\spv_conditions"));
		log_assert(parsed);
		pool<IdString> declared(outputs.begin(), outputs.end());
		std::vector<AST::AstNode *> pending = {parsed->ast.get()};
		std::vector<Wire *> inputs;
		while (!pending.empty()) {
			auto node = pending.back();
			pending.pop_back();
			if (node->type == AST::AST_IDENTIFIER && declared.insert(node->str).second) {
				auto wire = base->wire(node->str);
				if (!wire || wire->width == 0)
					log_cmd_error("SPV condition signal '%s' not found in module %s.\n", node->str, base);
				inputs.push_back(wire);
			}
			for (auto &child : node->children) pending.push_back(child.get());
		}
		// Supply each referenced wire's real HDL range and signedness, then let Yosys
		// elaborate the parsed expressions just as it elaborates a parameterized module.
		int port_id = GetSize(outputs);
		for (auto wire : inputs) {
			auto loc = parsed->ast->location;
			auto range = std::make_unique<AST::AstNode>(loc, AST::AST_RANGE,
				AST::AstNode::mkconst_int(loc, wire->to_hdl_index(wire->width - 1), true),
				AST::AstNode::mkconst_int(loc, wire->to_hdl_index(0), true));
			auto declaration = std::make_unique<AST::AstNode>(loc, AST::AST_WIRE, std::move(range));
			declaration->str = wire->name.str();
			declaration->is_input = true;
			declaration->is_signed = wire->is_signed;
			declaration->port_id = ++port_id;
			parsed->ast->children.push_back(std::move(declaration));
		}
		parsed->ast->fixup_hierarchy_flags(true);
		auto conditions = temporary.module(parsed->derive(&temporary, {}, false));
		temporary.remove(parsed);
		auto instance = base->addCell(NEW_ID, conditions->name);
		for (auto port : conditions->ports)
			if (conditions->wire(port)->port_input)
				instance->setPort(port, base->wire(port));
		for (int i = 0; i < GetSize(expressions); i++) {
			results[i] = base->addWire(NEW_ID);
			instance->setPort(outputs[i], results[i]);
		}
		// Inline before cutting sources, so assumptions and preconditions read the cut nets.
		Pass::call_on_module(&temporary, base, "flatten -noscopeinfo");
		temporary.remove(conditions);
		return results;
	}

	// Apply startup reset for one cycle, or two steps with explicit half-cycle clocks.
	// Example: -reset rst -> rst=1,0,0,...; adding -clock clk -> rst=1,1,0,...
	void add_environment(const std::vector<std::string> &clocks, bool has_reset, const std::vector<SigSpec> &conditions)
	{
		if (!clocks.empty()) {
			auto phase = base->addWire(NEW_ID_SUFFIX("clock_phase"));
			phase->attributes[ID::init] = State::S0;
			base->addFf(NEW_ID, base->Not(NEW_ID, phase), phase);
			for (const auto &name : clocks) {
				auto clock = resolve_spv_signal(base, name);
				if (GetSize(clock) != 1 || !clock[0].wire->port_input)
					log_cmd_error("SPV clock '%s' must be one input bit.\n", name);
				base->addAssume(NEW_ID, base->Eq(NEW_ID, clock, phase), State::S1);
			}
		}
		SigSpec active = State::S1;
		if (has_reset) {
			// Explicit clocks need two steps to span their first rising edge.
			const int reset_steps = clocks.empty() ? 1 : 2;
			for (int step = 0; step < reset_steps; step++) {
				auto delayed = base->addWire(NEW_ID_SUFFIX("reset_startup"));
				delayed->attributes[ID::init] = State::S0;
				base->addFf(NEW_ID, active, delayed);
				active = delayed;
			}
			base->addAssume(NEW_ID, base->Eq(NEW_ID, conditions[2], base->Not(NEW_ID, active)), State::S1);
			from_condition = base->And(NEW_ID, active, from_condition);
			to_condition = base->And(NEW_ID, active, to_condition);
		}
		for (int i = 3; i < GetSize(conditions); i++)
			base->addAssume(NEW_ID, conditions[i], active);
	}

	// Redirect only readers of the selected net, including property observation points.
	// Example: s=a; sibling=a; out=s -> out reads injection, sibling still reads a.
	void cut_sources()
	{
		source_port = base->uniquify("$spv_source");
		auto injected = base->addWire(source_port, GetSize(sources));
		injected->port_input = true;
		dict<SigBit, SigBit> replacement;
		for (int i = 0; i < GetSize(sources); i++)
			replacement[sources[i]] = SigBit(injected, i);

		CellTypes cell_types(&temporary);
		for (auto cell : base->cells()) {
			for (auto connection : cell->connections()) {
				if (!cell_types.cell_input(cell->type, connection.first)) continue;
				connection.second.replace(replacement);
				cell->setPort(connection.first, connection.second);
			}
		}
		std::vector<SigSig> connections = base->connections();
		for (auto &connection : connections)
			connection.second.replace(replacement);
		base->new_connections(connections);
		destinations.replace(replacement);
		from_condition.replace(replacement);
		to_condition.replace(replacement);

		// Export the three observation points to the two-run wrapper.
		destination_port = base->uniquify("$spv_destination");
		from_condition_port = base->uniquify("$spv_from_condition");
		to_condition_port = base->uniquify("$spv_to_condition");
		for (auto item : std::vector<std::pair<IdString, SigSpec>>{
			{destination_port, destinations}, {from_condition_port, from_condition}, {to_condition_port, to_condition}}) {
			auto port = base->addWire(item.first, GetSize(item.second));
			port->port_output = true;
			base->connect(port, item.second);
		}
		base->fixup_ports();
	}

	// Lower state before pairing it, and materialize unknown values before sharing them.
	// Example: a synchronous memory read -> explicit FF included by fmcombine -initeq.
	void prepare_base()
	{
		Pass::call_on_module(&temporary, base, "chformal -assert -cover -live -fair -remove");
		for (auto cell : base->cells().to_vector())
			if (cell->type == ID($print)) base->remove(cell);
		Pass::call_on_module(&temporary, base, "opt_clean");
		Pass::call_on_module(&temporary, base, "memory_nordff");
		Pass::call_on_module(&temporary, base, "memory_map -formal");
		Pass::call_on_module(&temporary, base, "formalff -anyinit2ff");
		Pass::call_on_module(&temporary, base, "setundef -undriven -anyseq");
		// Explicit non-resettable initialization is a model choice, not a solver shortcut.
		// Materialize combinational X values first so this only fills missing FF init bits.
		if (initial_state != "shared")
			Pass::call_on_module(&temporary, base, {"setundef", "-init", "-" + initial_state});
		Pass::call_on_module(&temporary, base, "opt_clean");
	}

	// Build public inputs, source choices, comparison, and the requested condition covers.
	// Example: C1=0 -> source A=B; C2=1 -> require all destination bits A=B.
	Module *build()
	{
		// Startup reset also keeps sources equal without an explicit from-precondition.
		const bool gate_source_changes = !from_condition.is_fully_ones();
		cut_sources();
		prepare_base();
		product = temporary.addModule(ID(spv_product));
		product->set_bool_attribute(ID::top);
		auto run_a = product->addCell(ID(run_a), base->name);
		auto run_b = product->addCell(ID(run_b), base->name);
		dict<IdString, SigSpec> outputs_a, outputs_b;
		for (auto id : base->ports) {
			auto port = base->wire(id);
			if (id == source_port) continue;
			if (port->port_input) {
				auto common = product->addWire(port->name, port);
				run_a->setPort(id, common);
				run_b->setPort(id, common);
			} else {
				outputs_a[id] = product->addWire(NEW_ID, port->width);
				outputs_b[id] = product->addWire(NEW_ID, port->width);
				run_a->setPort(id, outputs_a[id]);
				run_b->setPort(id, outputs_b[id]);
			}
		}
		auto common_source = product->Anyseq(NEW_ID_SUFFIX("source_a"), source_width);
		auto changed_source = product->Anyseq(NEW_ID_SUFFIX("source_b"), source_width);
		auto source_b = gate_source_changes
			? product->Mux(NEW_ID, common_source, changed_source, outputs_a.at(from_condition_port))
			: changed_source;
		run_a->setPort(source_port, common_source);
		run_b->setPort(source_port, source_b);

		auto equal = product->Eq(NEW_ID, outputs_a.at(destination_port), outputs_b.at(destination_port));
		auto assertion = product->addAssert(property_name.str(), equal, outputs_a.at(to_condition_port));
		assertion->set_string_attribute(ID(spv_property), property_name.unescape());
		auto add_cover = [&](const std::string &role, SigSpec condition) {
			product->addCover(property_name.str() + ":" + role, condition, State::S1);
		};
		if (has_from_condition) add_cover("from_precondition", outputs_a.at(from_condition_port));
		if (has_to_condition) add_cover("to_precondition", outputs_a.at(to_condition_port));
		if (has_from_condition && has_to_condition) {
			auto seen = product->addWire(NEW_ID);
			seen->attributes[ID::init] = State::S0;
			auto now_or_before = product->Or(NEW_ID, seen, outputs_a.at(from_condition_port));
			product->addFf(NEW_ID, now_or_before, seen);
			add_cover("combined_precondition", product->And(NEW_ID, now_or_before, outputs_a.at(to_condition_port)));
		}
		product->fixup_ports();

		// Reuse Yosys's two-run construction. Source choices are outside the copied base,
		// so -anyeq shares only the original environment, never the injected difference.
		Pass::call(&temporary, {"fmcombine", "-initeq", "-anyeq", "-nop", product->name.str(), "run_a", "run_b"});
		// fmcombine copies hdlname unchanged. Give each side a distinct HDL scope so
		// AIGER witnesses and SMT replay refer to the same, unambiguous signal names.
		auto combined = temporary.module("$fmcombine" + base->name.str());
		log_assert(combined);
		auto distinguish_run = [](auto *object) {
			std::string side = object->name.str().ends_with("_gate") ? "run_b" : "run_a";
			if (object->has_attribute(ID::hdlname)) {
				auto hdlname = object->get_hdlname_attribute();
				hdlname.insert(hdlname.begin(), side);
				object->set_hdlname_attribute(hdlname);
			}
			if (object->has_attribute(ID(scopename)))
				object->set_string_attribute(ID(scopename), side + " " + object->get_string_attribute(ID(scopename)));
		};
		for (auto wire : combined->wires()) distinguish_run(wire);
		for (auto cell : combined->cells()) distinguish_run(cell);
		Pass::call(&temporary, "flatten");
		product->attributes.erase(ID::top);
		product->set_string_attribute(ID(spv_property), property_name.unescape());
		return product;
	}
};

struct SpvPass : Pass
{
	SpvPass() : Pass("spv", "check information flow using two executions") { }

	// Show the core interface and the preparation order that preserves source nets.
	// Example: help spv -> usage and a runnable Yosys script fragment.
	void help() override
	{
		log("\n    spv [-create] -from <wire-or-slice> -to <wire-or-slice> [options] [selection]\n\n");
		log("    -from <signal> / -to <signal>    repeat for multiple source/destination signals\n");
		log("    -from-precond <expression>      condition allowing source differences\n");
		log("    -to-precond <expression>        condition enabling the comparison\n");
		log("    -clock <input-bit>             repeat for aligned half-cycle clocks\n");
		log("    -reset <expression>             active-high startup reset condition\n");
		log("    -assume <expression>            repeat for assumptions after startup reset\n");
		log("    -name <name>                    assertion name (default: information_flow)\n");
		log("    -module <name>                  output module (default: spv_miter)\n\n");
		log("    -init shared|zero|one           unspecified state initial values (default: shared)\n\n");
		log("Select one flattened module with no processes or blackboxes. Without a\n");
		log("selection, the module marked top is used (read_slang --top / hierarchy -top).\n");
		log("For read_verilog, use insbuf before proc to preserve named source branches:\n");
		log("    read_verilog -formal -sv dut.sv\n    hierarchy -top dut\n");
		log("    insbuf\n    proc\n    flatten\n    spv -from secret -to observable\n");
		log("    prep -top spv_miter\n\n");
		log("Do not run opt_clean/clean before spv: they can merge the named source nets.\n");
		log("Slang already preserves continuous assignments as buffers.\n");
		log("The pass cuts readers, maps memories, and uses fmcombine to share initial\n");
		log("state and environment values. SBY handles clock conversion, proving and traces.\n\n");
		log("Conditions use Verilog expressions over flattened wires; quote spaces.\n");
		log("Widths, signedness and HDL ranges come from the DUT. No SVA sequences,\n");
		log("design functions or package types are imported. Unknown names are errors.\n");
		log("With -reset, reset is active for one formal step without -clock, or two\n");
		log("steps with explicit half-cycle clocks, then inactive forever. During reset,\n");
		log("sources stay equal and output comparison and -assume are disabled.\n");
		log("Without -reset, checking starts immediately from the specified initial state.\n");
		log("Only explicit source/destination preconditions add cover properties.\n\n");
		log("For single-clock SBY proofs, omit -clock and use multiclock off. Explicit\n");
		log("-clock inputs start at 0 and toggle together every formal step; use\n");
		log("multiclock on for this waveform. Other clocks remain unconstrained.\n");
		log("Single-clock SBY example after proc and flatten (multiclock off):\n");
		log("    spv -reset \"!rst_n\" -assume \"enable || idle\"\\\n");
		log("        -from key -to debug -to-precond \"count == 3\"\n\n");
	}

	// Validate the command, build privately, then publish one completed product module.
	// Example: spv -from key -to debug -> a new spv_miter; the DUT stays unchanged.
	void execute(std::vector<std::string> args, Design *design) override
	{
		std::vector<std::string> from, to, clocks, assumptions;
		std::string from_precond, to_precond, name = "information_flow", module_name = "spv_miter";
		std::string reset, initial_state = "shared";
		pool<std::string> single_options;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			const auto &option = args[argidx];
			if (option == "-create") continue;
			if (option.empty() || option[0] != '-') break;
			if (option != "-from" && option != "-to" && option != "-from-precond" &&
				option != "-to-precond" && option != "-name" && option != "-module" && option != "-init" &&
				option != "-clock" && option != "-reset" && option != "-assume")
				log_cmd_error("Unknown SPV option '%s'.\n", option);
			if (argidx + 1 == args.size()) log_cmd_error("Missing value for %s.\n", option);
			if (option != "-from" && option != "-to" && option != "-clock" && option != "-assume" &&
				!single_options.insert(option).second)
				log_cmd_error("Repeated SPV option '%s'.\n", option);
			auto value = args[++argidx];
			if (value.size() >= 2 && value.front() == '"' && value.back() == '"')
				value = value.substr(1, value.size() - 2);
			if (value.empty()) log_cmd_error("Empty value for %s.\n", option);
			if (option == "-from") from.push_back(value);
			if (option == "-to") to.push_back(value);
			if (option == "-from-precond") from_precond = value;
			if (option == "-to-precond") to_precond = value;
			if (option == "-name") name = value;
			if (option == "-module") module_name = value;
			if (option == "-init") initial_state = value;
			if (option == "-clock") clocks.push_back(value);
			if (option == "-reset") reset = value;
			if (option == "-assume") assumptions.push_back(value);
		}
		extra_args(args, argidx, design);
		if (initial_state != "shared" && initial_state != "zero" && initial_state != "one")
			log_cmd_error("SPV -init must be shared, zero, or one.\n");
		if (from.empty() || to.empty()) log_cmd_error("SPV requires -from and -to.\n");
		auto modules = design->selected_modules();
		// One named module wins; otherwise use the module marked top after flatten leftovers.
		auto original = GetSize(modules) == 1 ? modules.front() : design->top_module();
		if (!original || !original->is_selected_whole())
			log_cmd_error("SPV requires one fully selected module, or a top module.\n");
		if (original->has_processes()) log_cmd_error("Run proc before spv (and insbuf before proc).\n");
		CellTypes cell_types(design);
		for (auto cell : original->cells()) {
			if (design->module(cell->type) || !cell_types.cell_known(cell->type))
				log_cmd_error("SPV requires a flattened design without blackboxes: %s (%s).\n", cell, cell->type);
			for (auto connection : cell->connections())
				if (cell_types.cell_input(cell->type, connection.first) && cell_types.cell_output(cell->type, connection.first))
					log_cmd_error("SPV does not support inout cell ports: %s.%s.\n", cell, connection.first);
		}
		for (auto wire : original->wires())
			if (wire->port_input && wire->port_output) log_cmd_error("SPV does not support inout port %s.\n", wire);
		auto result_name = RTLIL::escape_id(module_name);
		if (design->module(result_name)) log_cmd_error("SPV module '%s' already exists.\n", module_name);
		log_header(design, "Executing SPV pass for %s: %s.\n", original, name);
		SpvBuilder builder(original, from, to, from_precond, to_precond, clocks, reset, assumptions,
			RTLIL::escape_id(name), initial_state);
		auto built = builder.build();
		auto result = design->addModule(result_name);
		built->cloneInto(result);
		log("Created SPV property %s in module %s.\n", name, result);
	}
} SpvPass;

PRIVATE_NAMESPACE_END
