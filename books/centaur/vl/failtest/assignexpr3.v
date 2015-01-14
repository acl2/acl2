module top (output topout, input topin);

  logic [3:0] w1;
  logic [3:0] w2;

  sub mysub( (w1 = 0) );  // inner assignment shouldn't be allowed here

endmodule

module sub (logic [3:0] in);

endmodule
