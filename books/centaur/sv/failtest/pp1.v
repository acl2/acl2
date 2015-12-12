
module top (output topout, input topin);

// Can't use undefined preprocessor macro
wire w = `foo;

endmodule
