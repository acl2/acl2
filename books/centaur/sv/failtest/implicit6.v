module top (output topout, input topin);

  wire o, i;
  sub mysub(o, i);

endmodule

module sub (input o, input wire i);
  wire o; // illegal due to declaration above
endmodule
