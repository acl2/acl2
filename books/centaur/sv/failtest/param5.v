module top (output topout, input topin);

  wire [3:0] o, a, b;

  sub #(.size(4), .delay(2)) mysub (o, a, b);   // can't override delay because it's local

endmodule

module sub (o, a, b);

  parameter size = 1;
  localparam delay = 2;

  output [size-1:0] o;
  output [size-1:0] a;
  output [size-1:0] b;

  assign #delay o = a & b;

endmodule
