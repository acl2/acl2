// Centaur Hardware Verification Tutorial for ESIM/VL2014
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

// nextstate.v -- supporting file for nextstate.lsp

module myreg #(width = 1)
  (output [width-1:0] q, input [width-1:0] d, input clk);

  always @(posedge clk)
    q <= d;

endmodule

module top (output [3:0] o, input [3:0] a, input [3:0] b, input clk);

  // Stage 1 -- register gets A & B.

  wire [3:0] stage1;
  myreg #(4) r1 (stage1, a & b, clk);

  // Stage 2 -- register gets ~stage1

  wire [3:0] stage2;
  myreg #(4) r2 (stage2, ~stage1, clk);

  // Stage 3 -- Integer division of stage2 by 3

  wire [3:0] stage3;
  myreg #(4) r3 (stage3, stage2 / 4'd3, clk);

  // Output result of stage 3.

  assign o = stage3;

endmodule
