module top ;

  wire w;
  sub mysub (.b(w)); // wrong argument name

endmodule


module sub (a);

  input a;

endmodule
