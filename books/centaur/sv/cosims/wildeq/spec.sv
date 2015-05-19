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


  wire [3:0] a;
  wire signed [3:0] b;

  wire a1 = a ==? 6'b??1??0;
  wire a2 = a !=? 6'b??1??0;
  wire a3 = a ==? 6'b001??0;
  wire a4 = a !=? 6'b001??0;
  wire a5 = a ==? 6'b111??0;
  wire a6 = a !=? 6'b111??0;
  wire a7 = a ==?   4'b1??0;
  wire a8 = a !=?   4'b1??0;

  wire b1 = b ==? 6'b??1??0;
  wire b2 = b !=? 6'b??1??0;
  wire b3 = b ==? 6'b001??0;
  wire b4 = b !=? 6'b001??0;
  wire b5 = b ==? 6'b111??0;
  wire b6 = b !=? 6'b111??0;
  wire b7 = b ==?   4'b1??0  ;
  wire b8 = b !=?   4'b1??0  ;

   assign a = in;
   assign b = in;
   assign out = {a1, a2, a3, a4, a5, a6, a7, a8,
                 b1, b2, b3, b4, b5, b6, b7, b8 };

endmodule
