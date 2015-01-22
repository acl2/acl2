// VL Verilog Toolkit
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

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
