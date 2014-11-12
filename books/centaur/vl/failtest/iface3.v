interface simplebus (foo);    // oops, no direction for foo

  logic [2:0] bar;

endinterface


module top ;

  wire foo;

  simplebus sb (foo);

endmodule
