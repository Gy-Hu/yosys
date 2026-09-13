// A selected branch must not absorb its sibling, but must reach its own readers.
module spv_branches(input clk, input [1:0] public_value,
                    output [1:0] sibling, downstream, output reg [1:0] state);
    wire [1:0] selected = public_value;
    wire disabled = 1'b0;
    assign sibling = public_value;
    assign downstream = selected;
    always @(posedge clk) state <= selected;
endmodule

// ROM contents are defined; the synchronous read register initially is not.
// With no source path, independently chosen read-register states must not leak.
module spv_memory(input clk, input address, input secret, output reg value);
    reg memory [0:1];
    initial begin memory[0] = 0; memory[1] = 1; end
    always @(posedge clk) value <= memory[address];
endmodule

// Both arithmetic paths compute one. A literal X is shared environmental freedom,
// not an additional secret difference introduced when copying the circuit.
module spv_unknown(input choose_unknown, input [3:0] secret, output [3:0] value);
    assign value = choose_unknown ? 4'bxxxx : ((secret + 4'd1) - secret);
endmodule
