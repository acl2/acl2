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


typedef enum logic [3:0]
{
 va = 4'd0,
 vb = 4'd1,
 vc = 4'd2,
 vd = 4'd3,
 ve = 4'd4,
 vf = 4'd5,
 vg = 4'd6,
 vh = 4'd7,
 vi = 4'd8,
 vj = 4'd9,
 vk = 4'd10

 } st_t;

module spec (input logic [127:0] in,
	     output wire [127:0] out);
   
  logic [3:0] curr, next;
  logic cond;
   
   always_comb begin
     next = 'x;
     if (cond)
       case (curr)
	 va: next = vb;
	 vb: next = vc;
	 vc: next = vd;
	 vd: next = ve;
	 ve: next = vf;
	 vf: next = vg;
	 vg: next = vh;
	 vh: next = vi;
	 vi: next = vj;
	 vj: next = vk;
	 vk: next = va;
       endcase // case (curr)
     else
       case (curr)
	 va: next = vc;
	 vb: next = vd;
	 vc: next = ve;
	 vd: next = vf;
	 ve: next = vg;
	 vf: next = vh;
	 vg: next = vi;
	 vh: next = vj;
	 vi: next = vk;
	 vj: next = va;
	 vk: next = vb;
       endcase // case (curr)
   end // always_comb

   assign {cond, curr} = in;
   assign out = next;

endmodule // spec
