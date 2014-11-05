interface simplebus (input foo);

  logic [2:0] bar;
  logic [3:0] baz;

  modport master (input bar, output whoo); // oops, whoo not declared

endinterface


module top ;

  wire foo;

  simplebus sb (foo);

endmodule
