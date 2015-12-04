module top (output topout, input topin);

  wire [1:0] o;
  wire 	     i;

  not(o, i);  // can't connect wide ports to gates

endmodule
