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
// Original authors: Sol Swords <sswords@centtech.com>
//                   Jared Davis <jared@centtech.com>


module sub #(parameter val=5) (output [5:0] o);

   assign o = val;
endmodule

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  logic [3:0] [2:0] out1, out2, out3, out4, out5, out6, out7, out8;

   assign {>> {out1}} = in[11:0];
   assign {<< {out2}} = in[11:0];
   assign {<< 3 {out3}} = in[11:0];
   assign {<< 5 {out4}} = in[11:0];
   assign {>> {out5}} = in[15:0];
   assign {<< {out6}} = in[15:0];
   assign {<< 3 {out7}} = in[15:0];
   assign {<< 5 {out8}} = in[15:0];
   
   assign out = {out8, out7, out6, out5, out4, out3, out2, out1 };

endmodule
