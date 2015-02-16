module top (output topout, input topin);

  wire [3:0] o;
  wire [2:0] i;

  not foo [3:0] (o, i);  // can't connect 3-bit wire to 4-bit instance array

endmodule
