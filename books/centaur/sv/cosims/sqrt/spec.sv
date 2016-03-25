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
// Original authors: Jared Davis <jared@centtech.com>
//                   Sol Swords <sswords@centtech.com>

module sub #(parameter sqsize = 5)
   (output [sqsize-1:0] o,
    input [sqsize-1:0] i);

   localparam sidelen = int'($sqrt(sqsize));

  logic [sidelen-1:0][sidelen-1:0] square;
   logic [sidelen-1:0][sidelen-1:0] square2;
   always_comb begin
     for (int i=0; i<sidelen; i++)
       square2[sidelen-1-i]=square[i];
   end
   assign square = i;
   assign o = square2;

endmodule
   

module spec (input logic [127:0] in,
	     output logic [127:0] out);

   sub #(16) sub16 (out[15:0], in[15:0]);

   sub #(20) sub20 (out[35:16], in[19:0]);

   sub #(10) sub10 (out[45:36], in[9:0]);

endmodule
