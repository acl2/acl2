module top ;

  begin : myblock
    wire [3:0] aa;
  end

  wire [3:0]   bb = aa;  // oops, should be myblock.aa

endmodule
