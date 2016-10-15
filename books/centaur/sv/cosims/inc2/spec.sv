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

module spec (input logic [127:0] in,
	     output [127:0] out);


  typedef logic [3:0] u4;
  typedef logic [7:0] u8;
  typedef logic [11:0] u12;

  // These seem to provoke NCV bugs, at least on NCV 15.10-s008.
  // Reported to Sujit 1-22-2015.

  function automatic u12 c1 (u4 in1, u4 in2);
    u4 a;
    a = in1++ ^ in2++;
    return {in1, in2, a};
  endfunction

  function automatic u12 c2 (u4 in1, u4 in2);
    u4 a;
    a = in1-- + in2--;
    return {in1, in2, a};
  endfunction

  function automatic u12 c3 (u4 in1, u4 in2);
    u4 a;
    a = ++in1 | ++in2;
    return {in1, in2, a};
  endfunction

  function automatic u12 c4 (u4 in1, u4 in2);
    u4 a;
    a = --in1 & --in2;
    return {in1, in2, a};
  endfunction

   u4 w1, w2;
   assign {w1, w2} = in;

  assign out = { c4(w1,w2), c3(w1,w2), c2(w1,w2), c1(w1,w2) };

endmodule // spec


