module top ;

  wire [3:0] aa;
  wire [3:0] bb;

  generate
    for(genvar i = 0; i < 4; i = i+1)
    begin:a
      for(genvar i = 0; i < 2; i = i+1)
      begin:b
	not (aa[i], bb[i]);
      end
    end
  endgenerate

endmodule
