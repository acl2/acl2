module top ;

  wire a;
  sub mysub (.a, .a(a)); // can't connect to a twice

endmodule


module sub (a);

  input a;

endmodule
