module top ;

  wire [7:0] warn_hex = 8'h FFF;
  wire [7:0] warn_oct = 8'o 7777;
  wire [7:0] warn_bin = 8'b 1111_1111_1111;
  wire [7:0] warn_dec = 8'd 1234567890;

  wire [7:0] normal_hex = 8'hFE;
  wire [7:0] normal_oct = 8'o176;
  wire [7:0] normal_bin = 8'b1111_1110;
  wire [7:0] normal_dec = 8'd254;

  wire [31:0] warn_unsized1 = 18446744073709551616;   // 2^64
  wire [31:0] warn_unsized2 = 2147483648;             // 2^31
  wire [31:0] normal_unsized1 = 2147483647;           // 2^31 - 1
  wire [31:0] normal_unsized2 = 9876;

  wire [8:0]  normal_hex2 = 9'h 1FF;
  wire [8:0]  warn_hex2   = 9'h 3FF;

endmodule

module weird ;

  // Some truncations
  wire [7:0] warn_hex  = 8'h FXF;
  wire [7:0] warn_oct = 8'o 77X7;
  wire [7:0] warn_bin = 8'b 111X_1111_1111;

  // Special exception: we allow X digits when they're all X without any warnings.
  wire [7:0] special_exception = 8'h XXX;

  // Extensions.  Shouldn't warn about these.
  wire [19:0] ext_hex = 20'h FX;
  wire [19:0] ext_oct = 20'o 7X;
  wire [19:0] ext_bin = 20'b 11X;

  // Extensions with leading X/Z bits.  Don't need to warn about these because they
  // are sized.
  wire [19:0] ext_hex2 = 20'h XF;
  wire [19:0] ext_oct2 = 20'o X7;
  wire [19:0] ext_bin2 = 20'b X11;

  // Unsized extensions with leading X/Z bits.  Want to warn about these.
  wire [19:0] bad_hex = 'h XA;
  wire [19:0] bad_oct = 'o X6;
  wire [19:0] bad_bin = 'b X10;

endmodule
