module top (output topout, input topin);

  wire w;
  sub mysub (.a(w), .a()); // can't multiply connect to same port

endmodule


module sub (a);

  input a;

endmodule
