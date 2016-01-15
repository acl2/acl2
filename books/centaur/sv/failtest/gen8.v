module top ;

  wire [3:0] aa;
  wire [3:0] bb;

  genvar     i;

  // This is explicitly prohibited by SystemVerilolg-2012 Section 27.4,
  // "It is not possible to have two nested loop generate constructs that
  // use the same genvar."

  // Note: see also cosims/generate11 and cosims/generate10b.  NCV and VL say
  // that it's OK for loops to use the same variable when there are explicit
  // genvar declarations in the loops.  (VCS disagrees).

  generate
    for(i = 0; i < 4; i = i+1)
    begin:a
      for(i = 0; i < 2; i = i+1)  // oops, nested generate loops with the same var
      begin:b
	not (aa[i], bb[i]);
      end
    end
  endgenerate

endmodule
