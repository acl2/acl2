interface simplebus ;

  logic [2:0] bar;
  logic [3:0] baz;

  modport master (input bar, output bar); // oops, input and output?

endinterface

module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule
