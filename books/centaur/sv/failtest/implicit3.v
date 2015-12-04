module top (output topout, input topin);

  wire o, i;
  sub mysub(o, i);

endmodule

module sub (output var o, input wire i);
  logic i;  // illegal due to wire declaration above
endmodule
