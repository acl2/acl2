// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2014-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire a0;
  wire a1;
  wire a2;
  wire a3;

  reg out_a1;
  always @(a0 or a1 or a2 or a3)
  begin
    out_a1 = a3;
    out_a1 = a0 ? a1 : a2;
  end

  reg out_a2;
  always @(a0 or a1 or a2 or a3)
  begin
    out_a2 = a3;
    if (a0) out_a2 = a1;
    else out_a2 = a2;
  end

  reg out_a3;
  always @(a0 or a1 or a2 or a3)
  begin
    out_a3 = a0 ? a1 : a2;
    out_a3 = a3;
  end

  reg out_a4;
  always @(a0 or a1 or a2 or a3)
  begin
    if (a0) out_a4 = a1;
    else out_a4 = a2;
    out_a4 = a3;
  end



  wire [2:0] b0;
  wire [2:0] b1;
  wire [2:0] b2;
  wire [2:0] b3;

  reg [2:0] out_b1;
  always @(b0 or b1 or b2 or b3)
  begin
    out_b1[0] = b3;
    out_b1 = b0 ? b1 : b2;
  end

  reg [2:0] out_b2;
  always @(b0 or b1 or b2 or b3)
  begin
    out_b2[0] = b3;
    if (b0) out_b2 = b1;
    else out_b2 = b2;
  end

  reg [2:0] out_b3;
  always @(b0 or b1 or b2 or b3)
  begin
    out_b3 = b0 ? b1 : b2;
    out_b3[0] = b3;
  end

  reg [2:0] out_b4;
  always @(b0 or b1 or b2 or b3)
  begin
    if (b0) out_b4 = b1;
    else out_b4 = b2;
    out_b4[0] = b3;
  end

  reg [1:0] out_b5;  // truncation
  always @(*)
  begin
    if (b0) out_b5[0] = b1;
    else out_b5[0] = b2;
    out_b5[1] = b3;
  end

  reg [3:0] out_b6;  // extension
  always @* begin
    if (b0) out_b6 = b1;
    else out_b6 = b2;
    out_b6[0] = b3;
  end

  assign { b3, b2, b1, b0, a3, a2, a1, a0 } = in;

  assign out = {
	       out_b6, out_b5, out_b4, out_b3, out_b2, out_b1,
               out_a4, out_a3, out_a2, out_a1
       };

endmodule // spec
