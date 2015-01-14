module top (output topout, input topin);

  wire o, i;
  sub mysub(o, i);

endmodule

module sub (output integer o, input wire i);
  wire i; // illegal due to declaration above
endmodule
