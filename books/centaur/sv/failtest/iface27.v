interface simplebus ;

  logic [2:0] foo;

endinterface


module top (output topout, input topin);

  simplebus sb ();

  wire [3:0] bar = sb + 1;  // oops, adding an interface to something?

endmodule
