module top ;

  wire a;

  sub mysub (a);

endmodule



module sub (a);

  parameter a = 1; // Can't have a parameter overlap an input name

  input a;

endmodule
