// toy.v

module toy (input            reset,
            input            clk,
            input            op,
            input [1:0]      in,
            output reg [1:0] out);

   reg [1:0]                 tmp;
   reg [1:0]                 w1;
   reg [1:0]                 w2;   

   always@* w1 = tmp|in;
   always@* w2 = tmp&{2{in[0]}};
   always@(posedge clk) tmp <= in;
   always@(posedge clk) out <= (op ? w1 : w2);
endmodule // toy

// Now we build the "top" module which includes an instance of the ALU along with
// logic for mapping inputs from "wave" inputs and "free" inputs and defining the
// "fail_out" signal we are checking:

module top (input       reset,
            input       clk,
            input       wave_op,
            input [1:0] free_in);

   wire [1:0]          out;
   reg [1:0]           in;
   reg                 op;
   reg                 fail_out;

   always@(posedge clk) in <= free_in;
   always@(posedge clk) op <= wave_op;

   toy des(.reset(reset), .clk(clk), .op(op), .in(in), .out(out));

   always@(posedge clk) fail_out <= &out;
endmodule // top
