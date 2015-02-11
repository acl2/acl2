module top (output topout, input topin);

  wire w;
  sub mysub (w, w); // too many arguments

endmodule


module sub (a);

  input a;

endmodule
