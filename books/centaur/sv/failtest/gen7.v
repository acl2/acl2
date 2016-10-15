module top ;

  wire [3:0] aa;
  wire [3:0] bb;

  genvar     i;

  // This is explicitly prohibited in SystemVerilog-2012 27.4,
  //
  //    "the initialization assignment shall not reference the loop index
  //    variable on the right-hand side."

  generate
    for(i = i; i < 4; i = i+1)   // oops, initializer i=i makes no sense
    begin
      not (aa[i], bb[i]);
    end
  endgenerate

endmodule
