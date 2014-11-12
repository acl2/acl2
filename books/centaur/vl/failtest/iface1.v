interface simplebus ;

  logic [2:0] foo;
  logic [2:0] foo;  // oops, previously declared

endinterface


module top ;

  simplebus sb ();

endmodule
