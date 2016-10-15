module top (output topout, input topin);

  logic [3:0] w1;
  logic [3:0] w2;

  assign w1 = (w2 = 0);  // inner assignment shouldn't be allowed here

endmodule
