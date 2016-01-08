interface simplebus ;

  logic [2:0] foo;

endinterface

module sub1 (simplebus thebus) ;

endmodule

module sub2 () ;

endmodule

module top (output topout, input topin);

  simplebus sb ();

  sub2 mysub2 () ;
  sub1 mysub1 (mysub2);  // oops, can't use a submodule instance here

endmodule
