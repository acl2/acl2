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

  reg out_a1;
  always @(a0 or a1 or a2)
  begin
    out_a1 = a0 ? a1 : a2;
  end

  reg out_a2;
  always @(a0 or a1 or a2)
  begin
    if (a0) out_a2 = a1;
    else out_a2 = a2;
  end

  wire [2:0] b0;
  wire [2:0] b1;
  wire [2:0] b2;

  reg [2:0] out_b1;
  always @(b0 or b1 or b2)
    out_b1 = b0 ? b1 : b2;

  reg [2:0] out_b2;
  always @(b0 or b1 or b2)
    if (b0) out_b2 = b1;
    else out_b2 = b2;

  reg [1:0] out_b3;  // truncation
  always @(*)
  if (b0) out_b3 = b1;
  else out_b3 = b2;

  reg [3:0] out_b4;  // extension
  always @* begin
    if (b0) out_b4 = b1;
    else out_b4 = b2;
  end

  logic signed [3:0] c0;
  logic signed [3:0] c1;
  logic signed [3:0] c2;

  logic signed [3:0] out_c1;
  always_comb begin
    if (c0) out_c1 = c1;
    else out_c1 = c2;
  end

  logic signed [3:0] out_c2;
  always_comb
    if (c0) out_c2 = c1 + c2;
    else out_c2 = c1 - c2;

  logic signed [4:0] out_c3;  // extension
  always_comb
    if (c0) out_c3 = c1 + c2;
    else out_c3 = c1 - c2;

  logic signed [1:0] out_c4;  // truncation
  always_comb
    if (c0) out_c4 = c1 + c2;
    else out_c4 = c1 - c2;

  assign { c2, c1, c0, b2, b1, b0, a2, a1, a0 } = in;

  assign out = {
	       out_c4, out_c3, out_c2, out_c1,
	       out_b4, out_b3, out_b2, out_b1,
               out_a2, out_a1
       };

endmodule // spec
