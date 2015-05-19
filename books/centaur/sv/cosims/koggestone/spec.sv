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
// Original author: Sol Swords <sswords@centtech.com>

module foo #(a=1, b=2) (input i);
endmodule

module koggestone_gen #(width=1,lev=1) (input [width-1:0] a,
			       input [width-1:0] b,
			       output [width-1:0] p,
			       output [width-1:0] g,
			       output [width-1:0] p0);

  wire [width-1:0] pprev;
  wire [width-1:0] gprev;

   if (lev==0) begin : main

     assign p = a ^ b;
     assign g = a & b;
     assign p0 = p;

   end else begin : main
     localparam shift = 1 << (lev-1);

     koggestone_gen #(width, lev-1) sub (a, b, pprev, gprev, p0);

     assign p = pprev & (pprev << shift);
     assign g = (pprev & (gprev << shift)) | gprev;
   end

endmodule

module koggestone_adder #(lev=1) (input [(1<<lev)-1:0] a,
			       input [(1<<lev)-1:0] b,
			     output [(1<<lev):0] out);

  //wire [(1<<lev)-1:0] p;
  wire [(1<<lev)-1:0] g;
  wire [(1<<lev)-1:0] p0;
  koggestone_gen #((1<<lev),lev) kog (.a(a), .b(b), .p(), .g(g), .p0(p0));
  assign out = { g, 1'b0 } ^ { 1'b0, p0 };

endmodule

module spec (input logic [127:0] in,
	     output wire [127:0] out);


  localparam lev=4;

  wire [(1<<lev)-1:0] a;
  wire [(1<<lev)-1:0] b;

  assign {a,b} = in;

  koggestone_adder #(lev) inst (a, b, out[(1<<lev):0]);

endmodule
