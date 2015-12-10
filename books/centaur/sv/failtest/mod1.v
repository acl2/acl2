module sub ;

  logic [2:0] w1;
  logic [3:0] w2;

  modport producer (input w1, output w2);  // oops, modports are only OK in interfaces

endmodule

module top ;

  sub mysub ();

endmodule
