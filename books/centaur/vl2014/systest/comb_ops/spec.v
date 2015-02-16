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

// tests of basic operators in combinational always blocks

module spec ( unary_plus,
	      unary_minus,
	      unary_lognot,
	      unary_bitnot,
	      unary_bitand,
	      unary_nand,
	      unary_bitor,
	      unary_nor,
	      unary_xor,
	      unary_xnor1,
	      unary_xnor2,
	      binary_plus,
	      binary_minus,
	      binary_times,
	      binary_div,
	      binary_rem,
	      binary_eq,
	      binary_neq,
	      binary_ceq,
	      binary_logand,
	      binary_logor,
	      // binary_power,
	      binary_lt,
	      binary_lte,
	      binary_gt,
	      binary_gte,
	      binary_bitand,
	      binary_bitor,
	      binary_xor,
	      binary_xnor1,
	      binary_xnor2,
	      binary_shr,
	      binary_shl,
	      //binary_ashr,
	      //binary_ashl,
	      qmark,
	      a,
	      b,
	      c);

  parameter width = 1;

  output [width-1:0] unary_plus;
  output [width-1:0] unary_minus;
  output unary_lognot;
  output [width-1:0] unary_bitnot;
  output unary_bitand;
  output unary_nand;
  output unary_bitor;
  output unary_nor;
  output unary_xor;
  output unary_xnor1;
  output unary_xnor2;
  output [width-1:0] binary_plus;
  output [width-1:0] binary_minus;
  output [width-1:0] binary_times;
  output [width-1:0] binary_div;
  output [width-1:0] binary_rem;
  output binary_eq;
  output binary_neq;
  output binary_ceq;
  output binary_logand;
  output binary_logor;
  // output [width-1:0] binary_power;
  output binary_lt;
  output binary_lte;
  output binary_gt;
  output binary_gte;
  output [width-1:0] binary_bitand;
  output [width-1:0] binary_bitor;
  output [width-1:0] binary_xor;
  output [width-1:0] binary_xnor1;
  output [width-1:0] binary_xnor2;
  output [width-1:0] binary_shr;
  output [width-1:0] binary_shl;
  //output [width-1:0] binary_ashr;
  //output [width-1:0] binary_ashl;
  output [width-1:0] qmark;

  input [width-1:0]  a, b, c;


  reg [width-1:0] unary_plus;
  reg [width-1:0] unary_minus;
  reg unary_lognot;
  reg [width-1:0] unary_bitnot;
  reg unary_bitand;
  reg unary_nand;
  reg unary_bitor;
  reg unary_nor;
  reg unary_xor;
  reg unary_xnor1;
  reg unary_xnor2;
  reg [width-1:0] binary_plus;
  reg [width-1:0] binary_minus;
  reg [width-1:0] binary_times;
  reg [width-1:0] binary_div;
  reg [width-1:0] binary_rem;
  reg binary_eq;
  reg binary_neq;
  reg binary_ceq;
  reg binary_logand;
  reg binary_logor;
  // reg [width-1:0] binary_power;
  reg binary_lt;
  reg binary_lte;
  reg binary_gt;
  reg binary_gte;
  reg [width-1:0] binary_bitand;
  reg [width-1:0] binary_bitor;
  reg [width-1:0] binary_xor;
  reg [width-1:0] binary_xnor1;
  reg [width-1:0] binary_xnor2;
  reg [width-1:0] binary_shr;
  reg [width-1:0] binary_shl;
  //reg [width-1:0] binary_ashr;
  //reg [width-1:0] binary_ashl;
  reg [width-1:0] qmark;

  always @(a)
    begin
      unary_plus = +a;
      unary_minus = -a;
      unary_lognot = !a;
      unary_bitnot = ~a;
      unary_bitand = &a;
      unary_nand = ~&a;
      unary_bitor = |a;
      unary_nor = ~|a;
      unary_xor = ^a;
      unary_xnor1 = ~^a;
      unary_xnor2 = ^~a;
    end

  always @(a or b)
    begin
      binary_plus = a + b;
      binary_minus = a - b;
      binary_times = a * b;
      binary_div = a / b;
      binary_rem = a % b;
      binary_eq = a == b;
      binary_neq = a != b;
      binary_ceq = a === b;
      binary_logand = a & b;
      binary_logor = a | b;
      binary_lt = a < b;
      binary_lte = a <= b;
      binary_gt = a > b;
      binary_gte = a >= b;
      binary_bitand = a & b;
      binary_bitor = a | b;
      binary_xor = a ^ b;
      binary_xnor1 = a ~^ b;
      binary_xnor2 = a ^~ b;
      binary_shr = a >> b;
      binary_shl = a << b;
      //binary_ashr = a >>> b;
      //binary_ashl = a <<< b;
    end

  always @(a or b or c)
    begin
      qmark = a ? b : c;
    end

endmodule

/*+VL
module make_tests () ;

 wire [100:0] w;
 wire a;

 `define ARGS \
   .unary_plus(), \
   .unary_minus(), \
   .unary_lognot(), \
   .unary_bitnot(), \
   .unary_bitand(), \
   .unary_nand(), \
   .unary_bitor(), \
   .unary_nor(), \
   .unary_xor(), \
   .unary_xnor1(), \
   .unary_xnor2(), \
   .binary_plus(), \
   .binary_minus(), \
   .binary_times(), \
   .binary_div(), \
   .binary_rem(), \
   .binary_eq(), \
   .binary_neq(), \
   .binary_ceq(), \
   .binary_logand(), \
   .binary_logor(), \
   .binary_lt(), \
   .binary_lte(), \
   .binary_gt(), \
   .binary_gte(), \
   .binary_bitand(), \
   .binary_bitor(), \
   .binary_xor(), \
   .binary_xnor1(), \
   .binary_xnor2(), \
   .binary_shr(), \
   .binary_shl(), \
   .qmark(), \
   .a(), \
   .b(), \
   .c()


 spec #(1) spec_1 (`ARGS);
 spec #(2) spec_2 (`ARGS);
 spec #(3) spec_3 (`ARGS);
 spec #(4) spec_4 (`ARGS);
 spec #(5) spec_5 (`ARGS);
 spec #(6) spec_6 (`ARGS);
 spec #(7) spec_7 (`ARGS);
 spec #(8) spec_8 (`ARGS);

endmodule

*/
