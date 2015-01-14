module tricky;
  logic [2:0] foo_t;
endmodule

module top (output topout, input topin);
  tricky.foo_t a;
endmodule
