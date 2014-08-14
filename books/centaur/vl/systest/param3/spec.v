// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
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

// Stupid little two-level unparameterization test, with some bad modules
// thrown in to boot.

/*+VL

module BadA (o, a);
  output o;
  output o; // Illegal redefinition
  input  a;
endmodule

module BadB (o, a);  // Transitively bad because it instantiates BadA.
  output o;
  input  a;
  BadA ainst (o, a);
endmodule

module BadC (o, a);  // Transitively bad since it instantiates BadB.
  parameter size = 1;
  output [size-1:0] o;
  input [size-1:0]  a;
   BadB arr [size-1:0] (o, a);

  // also instantiate some good module, just to cause trouble
  GoodC #(size) extra (o, a);
endmodule

module BadTop ();

 wire [2:0] o, a;
 BadC #(3) c1(o, a);

 GoodD #(3) c2(o, a);

 GoodE c3(o, a);

endmodule

module BadD (o, a);
 output o;
 input a;

 BadA ainst (o, a);

 wire [2:0] n, m;
 GoodE einst (n, m);

endmodule


*/

module GoodA(o, a);
  output o;
  input  a;
  assign o = a;
endmodule

module GoodB(o, a);
  output o;
  input  a;
  GoodA ainst (o, a);
endmodule

module GoodC(o, a);
  parameter size = 1;
  output [size-1:0] o;
  input [size-1:0]  a;
  GoodB arr [size-1:0] (o, a);
endmodule

module GoodD(o, a);
  parameter size = 1;
  output [size-1:0] o;
  input [size-1:0] a;
  GoodC #(size) c1 (o, a);
endmodule

module GoodE(o, a);
  parameter blah = 1;

  output [2:0] o;
  input [2:0] a;
  GoodD #(.size(3)) inst (o, a);

  wire [2:0]  m, n;

  GoodC #(.size(3)) extra (m, n);

  wire 	      make_blah_matter = blah;

endmodule

/*+VL

module GoodTop ();

 wire [2:0] o, a;

 GoodE #(.blah(1)) blah(o, a);

endmodule

*/