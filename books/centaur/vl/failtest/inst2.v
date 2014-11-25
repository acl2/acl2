module top ;

  wire w;
  sub mysub (w, w); // too many arguments

endmodule


module sub (a);

  input a;

endmodule
