module top ;

  parameter version = 1;

  case(version)
    1: wire [3:0] aa = 1;
    2: wire [3:0] aa = 2;
  endcase

  wire [3:0]   bb = aa;  // oops, aa shouldn't be in scope here

endmodule
