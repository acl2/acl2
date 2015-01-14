interface simplebus (input foo);

  logic [2:0] bar;
  logic [3:0] baz;

  modport master (input bar, input bar); // oops, same input??

endinterface


module top (output topout, input topin);

  wire foo;

  simplebus sb (foo);

endmodule
