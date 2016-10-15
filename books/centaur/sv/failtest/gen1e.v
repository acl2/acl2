module top ;

  // Example based on the SystemVerilog-2012 standard, Section 27.4, page 752,
  // "mod_b".

  logic a;
  genvar     i;

  wire [3:0] aa, bb;

  for(i = 0; i < 4; i = i+1)
  begin: a                    // oops, a previously declared as "logic a"
    not(aa[i], bb[i]);
  end
endmodule
