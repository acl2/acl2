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

module genloop_adder #(width=8)
   (input logic [width-1:0] a,
    input logic [width-1:0] b,
    output wire [width:0] out);

  genvar i;
   for (i=0; i<width; i=i+1) begin : adder

     wire cout;
     if (i != 0) begin : inner
       wire lastcout = adder[i-1].cout;
       assign cout = (a[i] & b[i]) | (a[i] & lastcout) | (b[i] & lastcout);
       assign out[i] = a[i] ^ b[i] ^ lastcout;
     end else begin : inner
       assign cout = (a[i] & b[i]);
       assign out[i] = a[i] ^ b[i];
     end
   end

     assign out[width] = adder[width-1].cout;


endmodule

parameter width=8;

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire [width-1:0] a;
  wire [width-1:0] b;

   assign {a,b} = in;

   genloop_adder #(width) inst (a, b, out[width:0]);

endmodule
