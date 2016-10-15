interface simplebus (input foo);

  logic [2:0] bar;

endinterface : oops  // oops, wrong name


module top (output topout, input topin);

  wire foo;

  simplebus sb (foo);

endmodule
