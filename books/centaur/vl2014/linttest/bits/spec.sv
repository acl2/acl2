// VL 2014 -- Verilog Toolkit, 2014 Edition
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

typedef logic [3:0] opcode_t;

typedef struct packed
{
  opcode_t opcode;     // 4 bits
  logic ready;         // 1 bit
  logic [1:0] flags;   // 2 bits
} inst_t;              // == 7 bits

module myand #(width = 4) (output [width-1:0] o,
                           input [width-1:0] a, b);
  assign o = a & b;
endmodule

module top ;

  wire [3:0] foo;
  wire [4:0] bar;
  wire [100:0] w;

  // Basic tests of $bits on built-in types

  wire [$bits(foo)-1:0] normal1 = bar[3:0];
  wire [$bits(foo)-1:0] ext1 = bar[2:0];
  wire [$bits(foo)-1:0] trunc1 = bar[4:0];

  wire [$bits(foo[2:0]):0] normal2 = bar[3:0];
  wire [$bits(foo[1]):0] normal3 = bar[1:0];
  wire [$bits(foo)+$bits(bar)-1:0] normal4 = {foo,bar};


  // Basic tests of $bits on data structure instances

  opcode_t op; // 4 bits
  wire [$bits(op)-1:0] normal_op1 = w[3:0];  // 4 bits = 4 bits
  wire [$bits(op):0]   ext_op1 = w[3:0];     // 5 bits = 4 bits
  wire [$bits(op)+1:0] trunc_op1 = w[6:0];   // 6 bits = 7 bits

  inst_t inst; // 7 bits
  wire [$bits(inst)-1:0] normal_inst1 = w[6:0];  // 7 bits = 7 bits
  wire [$bits(inst):0]   ext_inst1 = w[6:0];     // 8 bits = 7 bits
  wire [$bits(inst)+1:0] trunc_inst1 = w[9:0];   // 9 bits = 10 bits


  // Basic tests of $bits on data structure names

  wire [$bits(opcode_t)-1:0] normal_op2 = w[3:0];  // 4 bits = 4 bits
  wire [$bits(opcode_t):0]   ext_op2 = w[3:0];     // 5 bits = 4 bits
  wire [$bits(opcode_t)+1:0] trunc_op2 = w[6:0];   // 6 bits = 7 bits

  wire [$bits(inst_t)-1:0] normal_inst2 = w[6:0];  // 7 bits = 7 bits
  wire [$bits(inst_t):0]   ext_inst2 = w[6:0];     // 8 bits = 7 bits
  wire [$bits(inst_t)+1:0] trunc_inst2 = w[9:0];   // 9 bits = 10 bits


  // Fancier expressions
  wire [$bits(op[2:0])-1:0] normal_op3 = w[2:0];  // 3 bits = 3 bits
  wire [$bits(op[2:0]):0]   ext_op3 = w[2:0];     // 4 bits = 3 bits
  wire [$bits(op[2:0])+1:0] trunc_op3 = w[5:0];   // 5 bits = 6 bits

  wire [$bits(inst.opcode)-1:0] normal_inst3 = w[3:0]; // 4 bits = 4 bits
  wire [$bits(inst[2:0]):0]     ext_inst3 = w[2:0];    // 4 bits = 3 bits
  wire [$bits({inst.opcode,inst.ready})+1:0] trunc_inst3 = w[7:0];   // 7 bits = 8 bits


  // Basic array
  logic [3:0][4:0] arr1;  // 4 * 5 == 20 bits, entries are 5 bits each
  wire [$bits(arr1):0]       normal_arr1 = w[20:0]; // 21 bits = 21 bits
  wire [$bits(arr1[0])-1:0]  ext_arr1    = w[3:0];  // 5 bits = 4 bits
  wire [$bits(arr1[0][2]):0] trunc_arr1  = w[2:0];  // 2 bits = 3 bits

  // Basic unpacked array
  logic [6:0] arr2 [3:0]; // entries are 7 bits each
  wire [$bits(arr2[0])-1:0]    normal_arr2 = w[6:0];  // 7 bits = 7 bits
  wire [$bits(arr2[1])-1:0]    ext_arr2    = w[5:0];  // 7 bits = 6 bits
  wire [$bits(arr2[2])-1:0]    trunc_arr2  = w[7:0];  // 7 bits = 8 bits

  // Array of typedef'd thing
  opcode_t [5:0] arr3;    // 6 entries, 4 bits each == 24 bits
  wire [$bits(arr3)-1:0]     normal_arr3 = w[23:0];  // 24 bits = 24 bits
  wire [$bits(arr3[1])-1:0]  ext_arr3    = w[2:0];   // 4 bits = 3 bits
  wire [$bits(arr3[2])-1:0]  trunc_arr3  = w[4:0];   // 4 bits = 5 bits

  // Array of packed structures
  inst_t [2:0] arr4;    // 3 entries, 7 bits each == 21 bits
  wire [$bits(arr4)-1:0]     normal_arr4 = w[20:0];       // 21 bits = 21 bits
  wire [$bits(arr4[1])-1:0]  ext_arr4    = w[5:0];        // 7 bits = 6 bits
  wire [$bits(arr4[2].opcode)-1:0]  trunc_arr4  = w[4:0]; // 4 bits = 5 bits



  wire [3:0] aa0, aa1, aa2;
  myand and_a (aa0, aa1, aa2);

  wire [3:0] bb0, bb1, bb2;
  myand #($bits(bb0)) and_b (bb0, bb1, bb2);

  wire [3:0] cc0, cc1, cc2;
  myand #($bits(opcode_t)) and_c (cc0, cc1, cc2);

  wire [3:0] dd0, dd1, dd2;
  myand #($bits(inst.opcode)) and_d (dd0, dd1, dd2);

  wire [3:0] ee0, ee1, ee2;
  myand #($bits(arr4[1].opcode)) and_e (ee0, ee1, ee2);

endmodule
