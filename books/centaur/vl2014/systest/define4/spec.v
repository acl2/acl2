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

// basic tests of defines with arguments

//`define cat(a, b) \la,la,la + /* hello */ a b
//`define cat(a, b) \la,la,la + a b
`define cat(a, b) \la  + a b

module dut (o1, o2, o3, o4, o5, a, n1, n2);

  parameter size = 1;

  output [3:0] o1, o2, o3, o4, o5;
  input [3:0]  a, n1, n2;

  wire [2:0]   \la = {a[3],n1[2],n2[1]};


  assign o1 = `cat(a, + n1);

`ifndef VL_SYSTEST_NCV
// NCVerilog apparently doesn't like this, but VCS seems to think it is ok.

  assign o2 = `cat(a ? n1, : n2);
`endif


//   assign o3 = `cat({a[1:0], n1[1:0]}, + n2);
//   assign o4 = `cat(a /* foo,
// 		      bar */,
//   + // comment
// 	      n1);

// `define foo a
// `define bar + n1 ;

//   assign o5 = `cat(`foo, `bar)

  wire 	       make_size_matter = size;

endmodule


/*+VL

module make_tests () ;

   wire [3:0] a;

   dut #(1) inst (a, a, a, a, a, a, a, a);

endmodule

*/


