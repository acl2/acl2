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



module spec (input logic [127:0] in,
	     output wire [127:0] out);



  logic [3:0] a, b, c, d, e;
   assign {a, b, c, d, e} = in;
  logic [7:0] o1, o2, o3, o4, o5, o6;
   assign out = { o6, 4'bz, o5, 4'bz, o4, 4'bz, o3, 4'bz, o2, 4'bz, o1 };
   // assign o1 = signed'(a);
   // assign o2 = -signed'(a);
   // assign o3 = (a[3] ? -signed'(a) : a) | 8'b0;
   // assign o4 = (~a[3] ? a : -signed'(a)) | 8'b0;
   // assign o5 = signed'(a) | 8'b0;
   // assign o6 = -signed'(a) | 8'b0;
   // assign o6 = -signed'(a) | 4'b0;
  logic test;
   assign test = 1'b1;
   assign o1 = test ? signed'(a) : 8'b0;
   assign o2 = test ? signed'(a) : 4'b0;
   assign o3 = signed'(a) | 8'b0;
   assign o4 = signed'(a) | 4'b0;
   assign o5 = a[3] ? -signed'(a) : a;
   assign o6 = ~a[3] ? a : -signed'(a);

endmodule
                 

   
