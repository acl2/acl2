

module flop (q, d, clk);
   parameter width = 1;

  output [width-1:0] q;
  input [width-1:0] d;
  input clk;

   always @(posedge clk) q <= d;

endmodule // flop
