module top ;

  wire [3:0] aa;
  wire [3:0] bb;

  genvar     i, j;

  generate
    for(i = 0; i < 4; i = i+1) begin
      not (aa[i], bb[j]);               // oops, using bb[j] instead of bb[i]
    end
  endgenerate

endmodule
