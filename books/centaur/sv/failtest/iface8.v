// NCV tolerates this but VCS does not.

interface simplebus ;

  logic [2:0] bar;

  modport master (input bar, output baz); // oops, baz not defined YET

  logic [3:0] baz;

endinterface


module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule
