// Centaur SV Hardware Verification Tutorial
// Copyright (C) 2012-2015 Centaur Technology
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
// Original authors: Jared Davis <jared@centtech.com>
//                   Sol Swords <sswords@centtech.com>

// alu16.v
//
// This is a simple 16-bit ALU with 8 opcodes.  There is a "copy/paste" bug
// in its COUNT operation.

`define OP_PLUS    3'd0
`define OP_MINUS   3'd1
`define OP_BITAND  3'd2
`define OP_BITOR   3'd3
`define OP_BITXOR  3'd4
`define OP_MIN     3'd5
`define OP_COUNT   3'd6  // count how many one bits in the A bus
`define OP_MULT    3'd7

module alu16 (
  output [15:0] out,
  input [2:0] opcode,
  input [15:0] abus,
  input [15:0] bbus,
  input clk
);

  wire [15:0] abus1;
  wire [15:0] bbus1;

  flop #(16) aflop (.q(abus1), .d(abus), .clk(clk));
  flop #(16) bflop (.q(bbus1), .d(bbus), .clk(clk));

  wire [15:0] ans_plus   = abus1 + bbus1;
  wire [15:0] ans_minus  = abus1 - bbus1;
  wire [15:0] ans_bitand = abus1 & bbus1;
  wire [15:0] ans_bitor  = abus1 | bbus1;
  wire [15:0] ans_bitxor = abus1 ^ bbus1;
  wire [15:0] ans_min    = (abus1 < bbus1) ? abus1 : bbus1;
  wire [15:0] ans_mult   = abus1 * bbus1;

  // This has a "copy/paste" bug -- I "forgot" to change abus1[3] to abus1[7]

  wire [15:0] ans_count =
     abus1[0]  + abus1[1]  + abus1[2]  + abus1[3]
   + abus1[4]  + abus1[5]  + abus1[6]  + abus1[3]
   + abus1[8]  + abus1[9]  + abus1[10] + abus1[11]
   + abus1[12] + abus1[13] + abus1[14] + abus1[15];

  wire [15:0] ans;

  assign ans =
      (opcode == `OP_PLUS)   ? ans_plus
    : (opcode == `OP_MINUS)  ? ans_minus
    : (opcode == `OP_BITAND) ? ans_bitand
    : (opcode == `OP_BITOR)  ? ans_bitor
    : (opcode == `OP_BITXOR) ? ans_bitxor
    : (opcode == `OP_MIN)    ? ans_min
    : (opcode == `OP_COUNT)  ? ans_count
    : (opcode == `OP_MULT)   ? ans_mult
    : 16'bx;

  flop #(16) outflop (.q(out), .d(ans), .clk(clk));

endmodule

