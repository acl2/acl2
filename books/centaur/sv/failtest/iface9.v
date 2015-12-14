interface simplebus ;

  logic [2:0] bar;
  logic [3:0] baz;

  modport bar (input bar, output baz);  // oops, can't use same name (bar) for modport and wire

endinterface


module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule
