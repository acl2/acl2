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
	     output logic [127:0] out);

  logic [3:0] a, b, c, d;

   assign {a, b, c, d} = in;

  logic [18:3] e;

   always_comb begin
     e = 16'b0;
     e[a] = 1'b1;
   end

  logic [3:0] f [15:0];

     int i, j, k;

   always_comb begin
     for (i=0; i<16; i++) begin
       f[i] = 0;
     end
     f[b] = c;
   end

  logic [3:0] g [15:0], h [15:0];

   always_comb begin
     for (j=0; j<16; j++) begin
       g[j] = 0;
       h[j] = 0;
     end
     {g[d], h[d]} = {a, b};
   end

   always_comb begin
     for (k=0; k<16; k++) begin
       out[4*k +: 3] = (k & 1) ? f[k] : (k & 2) ? g[k] : h[k] ;
     end
     out[79:64] = e;
   end

   // assign out = e;
endmodule // spec

