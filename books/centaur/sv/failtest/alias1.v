module top ;

  wire [3:0] a;
  wire [1:0] b;

  alias a = b; // oops, different widths

endmodule
