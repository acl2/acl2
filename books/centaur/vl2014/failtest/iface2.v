interface simplebus (input foo);

  logic [2:0] bar;
  wire 	      foo; // oops, redeclaring input

endinterface


module top (output topout, input topin);

  wire foo;

  simplebus sb (foo);

endmodule
