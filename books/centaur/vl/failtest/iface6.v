interface simplebus (input foo);

  logic [2:0] bar;
  logic [3:0] baz;

  modport master (input bar, output bar); // oops, input and output?

endinterface


module top ;

  wire foo;

  simplebus sb (foo);

endmodule
