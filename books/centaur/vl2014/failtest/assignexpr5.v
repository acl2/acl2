module top (output topout, input topin);

  logic [3:0] w1;
  logic [3:0] w2;

  // Heh, this causes VCS to crash with an assertion failure inside the tool
  and myand (w2[0], w1[0], (w1[1] = 0));

endmodule
