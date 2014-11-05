interface simplebus (input foo);

  logic [2:0] bar;
  logic [3:0] baz;

  modport bar (input bar, output baz);  // oops, can't use same name (bar) for modport and wire

endinterface


module top ;

  wire foo;

  simplebus sb (foo);

endmodule
