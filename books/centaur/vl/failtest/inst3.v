module top ;

  wire w;
  sub mysub (.a(w), .a()); // can't multiply connect to same port

endmodule


module sub (a);

  input a;

endmodule
