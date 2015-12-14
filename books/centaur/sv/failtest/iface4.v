interface simplebus (foo); // oops, no direction for FOO

  logic foo;       // not good enough, need an actual port declaration
  logic [2:0] bar;

endinterface


module top (output topout, input topin);

  wire foo;

  simplebus sb (foo);

endmodule
