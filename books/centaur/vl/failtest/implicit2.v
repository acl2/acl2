module top (output topout, input topin);

  wire o, i;
  sub mysub(o, i);

endmodule

module sub (output var o, input i);
  wire o;  // illegal due to var declaration above
endmodule
