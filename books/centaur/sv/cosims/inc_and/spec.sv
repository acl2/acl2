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
	     output logic [127:0] out);

  typedef logic [3:0] u4;
  typedef logic [7:0] u8;
  typedef logic [11:0] u12;
  typedef logic [15:0] u16;

  typedef logic [3:0] s4;
  typedef logic [7:0] s8;
  typedef logic [11:0] s12;
  typedef logic [15:0] s16;

  function automatic u12 f1u (u4 in1, u4 in2);
    u4 a;
    a = in1;
    a &= in2;
    return {a, in1, in2};
  endfunction

  function automatic s12 f1s (s4 in1, s4 in2);
    s4 a;
    a = in1;
    a &= in2;
    return {a, in1, in2};
  endfunction


  function automatic u16 f2u (u4 in1, u4 in2);
    u4 a;
    u4 b;
    a = 0;
    b = (a &= (in1 &= in2));
    return {a, b, in1, in2};
  endfunction

  function automatic s16 f2s (s4 in1, s4 in2);
    s4 a;
    s4 b;
    a = 0;
    b = (a &= (in1 &= in2));
    return {a, b, in1, in2};
  endfunction


  function automatic u16 f3u (u4 in1, u4 in2);
    u4 a;
    u4 b;
    a = 0;
    b = (a &= (in1 &= in2) >>> 1);
    return {a, b, in1, in2};
  endfunction

  function automatic s16 f3s (s4 in1, s4 in2);
    s4 a;
    s4 b;
    a = 0;
    b = (a &= (in1 &= in2) >>> 1);
    return {a, b, in1, in2};
  endfunction


  function automatic u16 f4u (u4 in1, u4 in2);
    u8 a;
    u4 b;
    a = 0;
    b = (a &= (in1 >>> 1) + in2);
    return {a, b, in1};
  endfunction

  function automatic s16 f4s (s4 in1, s4 in2);
    s8 a;
    s4 b;
    a = 0;
    b = (a &= (in1 >>> 1) + in2);
    return {a, b, in1};
  endfunction


  u4 w1, w2;
  assign {w1,w2} = in;

  assign out = {
	       f4s(w1,w2), f4u(w1,w2), // 32
	       f3s(w1,w2), f3u(w1,w2), // 32
	       f2s(w1,w2), f2u(w1,w2), // 32
	       f1s(w1,w2), f1u(w1,w2)  // 24
  };

endmodule : spec
