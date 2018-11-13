// alu.v
//
// This is a simple 16-bit ALU with 8 opcodes pulled from the SV tutorial. As it is there, 
// there is a "copy/paste" bug in its COUNT operation.

`define OP_PLUS    3'd0
`define OP_MINUS   3'd1
`define OP_BITAND  3'd2
`define OP_BITOR   3'd3
`define OP_BITXOR  3'd4
`define OP_MIN     3'd5
`define OP_COUNT   3'd6  // count how many one bits in the A bus
`define OP_MULT    3'd7

  
module alu (output reg [15:0] out,
            input [2:0]  opcode,
            input [15:0] abus,
            input [15:0] bbus,
            input        reset,
            input        clk);

   reg [15:0]            abus1;
   reg [15:0]            bbus1;
     
   always@(posedge clk) abus1 <= abus;
   always@(posedge clk) bbus1 <= bbus;
   
   wire [15:0] ans_plus   = abus1 + bbus1;
   wire [15:0] ans_minus  = abus1 - bbus1;
   wire [15:0] ans_bitand = abus1 & bbus1;
   wire [15:0] ans_bitor  = abus1 | bbus1;
   wire [15:0] ans_bitxor = abus1 ^ bbus1;
   wire [15:0] ans_min    = (abus1 < bbus1) ? abus1 : bbus1;
   wire [15:0] ans_mult   = abus1 * bbus1;

   // This has a "copy/paste" bug -- I "forgot" to change abus1[3] to abus1[7]
   wire [15:0] ans_count =
                 abus1[0]  + abus1[1]  + abus1[2]  + abus1[3]
               + abus1[4]  + abus1[5]  + abus1[6]  + abus1[3]
               + abus1[8]  + abus1[9]  + abus1[10] + abus1[11]
               + abus1[12] + abus1[13] + abus1[14] + abus1[15];
   
   wire [15:0] ans;
   
   assign ans =   (opcode == `OP_PLUS)   ? ans_plus
                : (opcode == `OP_MINUS)  ? ans_minus
                : (opcode == `OP_BITAND) ? ans_bitand
                : (opcode == `OP_BITOR)  ? ans_bitor
                : (opcode == `OP_BITXOR) ? ans_bitxor
                : (opcode == `OP_MIN)    ? ans_min
                : (opcode == `OP_COUNT)  ? ans_count
                : (opcode == `OP_MULT)   ? ans_mult
                : 16'bx;
   
   always@(posedge clk) out <= ans;

endmodule // alu

// Now we build the "top" module which includes an instance of the ALU along with
// logic for mapping inputs from "wave" inputs and "free" inputs and defining the
// "fail_out" signal we are checking:

module top (input        reset,
            input        clk,
            input [15:0] free_abus,
            input [15:0] free_bbus,
            input [2:0]  free_opcode,
            input [2:0]  wave_opcode);
   
   reg  [15:0]  abus;
   reg  [15:0]  bbus;
   reg  [2:0]   opcode;
   wire [15:0]  out;
   reg          fail_out;

   // For this simple example, we will take the "opcode" input from
   // the wave input, but will use free inputs for the abus and bbus
   // inputs.. The 
   
   always@(posedge clk) abus   <= free_abus;
   always@(posedge clk) bbus   <= free_bbus;
   // We pull the opcode from the waves which just
   // cycles through the possible values:
   //
   always@(posedge clk) opcode <= wave_opcode;

   // As an interesting simple modification, you can just
   // make the opcode a free input as well and run it.
   // The above run (with opcode tracking waves), effectively
   // case splits the search with a maximum clause count
   // around 1K with many of the cases being solved with very
   // few decisions while the following will have a clause count
   // around 9K. It is also interesting to "fix" the bug
   // and rerun which exposes the SAT to the full force of
   // the multiplication instance:
   // 
   // always@(posedge clk) opcode <= free_opcode;
      
   alu des(.*);

   // For the ALU, we will include a "check" against a "spec".
   // The "spec" is just a differently computed result we compare:
   
   reg [15:0]   abus_d1;
   reg [15:0]   bbus_d1;
   reg [15:0]   spec;

   always@(posedge clk) begin
      abus_d1 <= abus;
      bbus_d1 <= bbus;
   end
   
   reg [15:0] spec_count;
   always@* begin
      spec_count = 0;
      for (int i = 0; i < 16; i++)
        spec_count = spec_count + abus_d1[i];
   end

   always@(posedge clk) begin
      if (reset) spec <= 0;
      else begin
         case (opcode)
           `OP_PLUS   : spec <= (abus_d1 + bbus_d1);
           `OP_MINUS  : spec <= (abus_d1 - bbus_d1);
           `OP_BITAND : spec <= (abus_d1 & bbus_d1);
           `OP_BITOR  : spec <= (abus_d1 | bbus_d1);
           `OP_BITXOR : spec <= (abus_d1 ^ bbus_d1);
           `OP_MIN    : spec <= (abus_d1 < bbus_d1) ? abus_d1 : bbus_d1;
           `OP_COUNT  : spec <= spec_count;
           `OP_MULT   : spec <= (abus_d1 * bbus_d1);
         endcase
      end
   end
   
   always@(posedge clk) fail_out <= (spec != out);

endmodule // top


