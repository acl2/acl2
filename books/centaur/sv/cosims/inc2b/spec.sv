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
  typedef logic [19:0] u20;

  // NCVerilog 15.10-s008 doesn't seem to support assignments inside of
  // expressions yet.  I get a parse error for each of these:
  //
  //   a = b = in;
  //   a = (b = in);
  //   a = ((b = in));
  //   a = ((b) = in);
  //   a = b += in;
  //   a = (b += in);
  //
  // So I don't think we can test these on NCV.  So all of these tests
  // are only against VCS.

  function automatic u8 b1 (u4 in);
    // assignment expression
    u4 a;
    u4 b;
    a = (b = in);
    return {a,b};
  endfunction

  function automatic u12 b2 (u4 in);
    // basic chained assignments
    u4 a;
    u4 b;
    u4 c;
    a = (b = (c = in));
    return {a,b,c};
  endfunction

  function automatic u12 b3 (u4 in);
    // chained assignments with negations
    u4 a;
    u4 b;
    u4 c;
    a = ~((b = ~((c = ~in))));
    return {a,b,c};
  endfunction


  function automatic u20 c1 (u4 in1, u4 in2);
    // post-increments within nested assignments
    u4 a;
    u4 b;
    u4 c;
    // I originally planned to use the following instead:
    //
    //    a = (b = (in1++ + (c = in2++)) + in1);
    //
    // But I now think that is undefined because we don't know whether in1++
    // will happen before or after the final in1 is read.
    a = (b = (in1++ + (c = in2++)));
    return {a,b,c,in1,in2};
  endfunction

  function automatic u20 c2 (u4 in1, u4 in2);
    // post-decrements within nested assignments
    u4 a;
    u4 b;
    u4 c;
    a = (b = (in1-- + (c = in2--)));
    return {a,b,c,in1,in2};
  endfunction

  function automatic u20 c3 (u4 in1, u4 in2);
    // pre-increments within nested assignments
    u4 a;
    u4 b;
    u4 c;
    a = (b = (++in1 + (c = ++in2)));
    return {a,b,c,in1,in2};
  endfunction

  function automatic u20 c4 (u4 in1, u4 in2);
    // pre-decrements within nested assignments
    u4 a;
    u4 b;
    u4 c;
    a = (b = (--in1 + (c = --in2)));
    return {a,b,c,in1,in2};
  endfunction

  u4 w1, w2;
  assign {w1, w2} = in;


  assign out = { c4(w1, w2),  // 20 bits
                 c3(w1, w2),  // 40
                 c2(w1, w2),  // 60
                 c1(w1, w2),  // 80
                 b3(w1),      // 92
                 b2(w1),      // 104
                 b1(w1)       // 112
               };

endmodule : spec
