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

  typedef logic signed [3:0] s4;
  typedef logic signed [7:0] s8;
  typedef logic signed [11:0] s12;

  // This is intended to do only the most very basic testing of increment and
  // decrement expressions.
  //
  // We found that NCV didn't seem to support assignment expressions like a =
  // (b = c), so we've left those out and only focus on ++/-- here in for
  // better cross-checking.
  //
  // We also found that NCV seems to have some problems with post-increment and
  // post-decrement operators, so we only do very basic tests of those here.
  //
  // The other increment-testing cosims are more interesting.

  function automatic u8 a1 (u4 in);
    // unsigned post-increment
    u4 a;
    u4 b;
    a = in;
    b = a++;
    return {b,a};
  endfunction

  function automatic u8 a2 (u4 in);
    // unsigned post-decrement
    u4 a;
    u4 b;
    a = in;
    b = a--;
    return {b,a};
  endfunction

  function automatic u8 a3 (u4 in);
    // unsigned pre-increment
    u4 a;
    u4 b;
    a = in;
    b = ++a;
    return {b,a};
  endfunction

  function automatic u8 a4 (u4 in);
    // unsigned pre-decrement
    u4 a;
    u4 b;
    a = in;
    b = --a;
    return {b,a};
  endfunction



  function automatic u8 b1 (u4 in);
    // unsigned two post-increments, touching function input
    u4 a;
    u4 b;
    a = in++;
    b = a++;
    return {b,a};
  endfunction

  function automatic u8 b2 (u4 in);
    // unsigned two post-decrements, touching function input
    u4 a;
    u4 b;
    a = in--;
    b = a--;
    return {b,a};
  endfunction

  function automatic u8 b3 (u4 in);
    // unsigned two pre-increments, touching function input
    u4 a;
    u4 b;
    a = ++in;
    b = ++a;
    return {b,a};
  endfunction

  function automatic u8 b4 (u4 in);
    // unsigned two pre-decrements, touching function input
    u4 a;
    u4 b;
    a = --in;
    b = --a;
    return {b,a};
  endfunction



  function automatic s8 c1 (s4 in);
    // signed post-increment
    s4 a;
    s4 b;
    a = in;
    b = a++;
    return {b,a};
  endfunction

  function automatic s8 c2 (s4 in);
    // signed post-decrement
    s4 a;
    s4 b;
    a = in;
    b = a--;
    return {b,a};
  endfunction

  function automatic s8 c3 (s4 in);
    // signed pre-increment
    s4 a;
    s4 b;
    a = in;
    b = ++a;
    return {b,a};
  endfunction

  function automatic s8 c4 (s4 in);
    // signed pre-decrement
    s4 a;
    s4 b;
    a = in;
    b = --a;
    return {b,a};
  endfunction


  function automatic s8 d1 (s4 in);
    // signed two post-increments, touching function input
    s4 a;
    s4 b;
    a = in++;
    b = a++;
    return {b,a};
  endfunction

  function automatic s8 d2 (s4 in);
    // signed two post-decrements, touching function input
    s4 a;
    s4 b;
    a = in--;
    b = a--;
    return {b,a};
  endfunction

  function automatic s8 d3 (s4 in);
    // signed two pre-increments, touching function input
    s4 a;
    s4 b;
    a = ++in;
    b = ++a;
    return {b,a};
  endfunction

  function automatic s8 d4 (s4 in);
    // signed two pre-decrements, touching function input
    s4 a;
    s4 b;
    a = --in;
    b = --a;
    return {b,a};
  endfunction

  u4 w1;
  assign w1 = in;

  assign out = { d4(w1), d3(w1), d2(w1), d1(w1),
                 c4(w1), c3(w1), c2(w1), c1(w1),
                 b4(w1), b3(w1), b2(w1), b1(w1),
                 a4(w1), a3(w1), a2(w1), a1(w1) };


endmodule // spec

