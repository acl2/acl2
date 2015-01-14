module top (output topout, input topin);

  wire w;
  sub mysub (.b(w)); // wrong argument name

endmodule


module sub (a);

  input a;

endmodule
