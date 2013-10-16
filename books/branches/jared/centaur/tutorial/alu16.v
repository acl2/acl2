/*

Centaur Hardware Verification Tutorial
Copyright (C) 2012 Centaur Technology

Contact:
  Centaur Technology Formal Verification Group
  7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
  http://www.centtech.com/

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.  This program is distributed in the hope that it will be useful but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.  You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

Original author: Jared Davis <jared@centtech.com>

*/



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
  input [15:0] bbus
);

wire [15:0] ans_plus   = abus + bbus;
wire [15:0] ans_minus  = abus - bbus;
wire [15:0] ans_bitand = abus & bbus;
wire [15:0] ans_bitor  = abus | bbus;
wire [15:0] ans_bitxor = abus ^ bbus;
wire [15:0] ans_min    = (abus < bbus) ? abus : bbus;
wire [15:0] ans_mult   = abus * bbus;

// This has a "copy/paste" bug -- I "forgot" to change abus[3] to abus[7]

wire [15:0] ans_count =
   abus[0]  + abus[1]  + abus[2]  + abus[3]
 + abus[4]  + abus[5]  + abus[6]  + abus[3]
 + abus[8]  + abus[9]  + abus[10] + abus[11]
 + abus[12] + abus[13] + abus[14] + abus[15];

assign out =
    (opcode == `OP_PLUS)   ? ans_plus
  : (opcode == `OP_MINUS)  ? ans_minus
  : (opcode == `OP_BITAND) ? ans_bitand
  : (opcode == `OP_BITOR)  ? ans_bitor
  : (opcode == `OP_BITXOR) ? ans_bitxor
  : (opcode == `OP_MIN)    ? ans_min
  : (opcode == `OP_COUNT)  ? ans_count
  : (opcode == `OP_MULT)   ? ans_mult
  : 16'bx;

endmodule

