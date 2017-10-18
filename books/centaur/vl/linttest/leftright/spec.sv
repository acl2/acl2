// VL Verilog Toolkit
// Copyright (C) 2008-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

module sub (input [3:0] i);

endmodule

module m0 () ;

  wire [3:0] a, b, c;

  wire plain_no1 = a;
  wire plain_no2 = 5;
  wire plain_no3 = +a;
  wire plain_no4 = -a;
  wire plain_no5 = &a;
  wire plain_no6 = |a;
  wire plain_no7 = ~a;
  wire plain_no8 = ^a;

  wire and_no1 = a & b;
  wire and_no2 = a & b & c;
  wire and_warn1 = a & a;
  wire and_warn2 = a & b & a;
  wire and_warn3 = (a & b) & c & a;

  wire or_no1 = a | b;
  wire or_no2 = a | b | c;
  wire or_warn1 = a | a;
  wire or_warn2 = a | b | a;
  wire or_warn3 = (a | b) | c | a;



  wire eq_no1 = a == b;
  wire eq_no2 = a == b & a;
  wire eq_no3 = a == (a & b);
  wire eq_warn1 = a == a;
  wire eq_warn2 = (a == a) & b;
  wire eq_warn3 = (a & b) & (a == a) & d;

  wire lt_no1 = a < b;
  wire lt_no2 = a < b & a;
  wire lt_no3 = a < (a & b);
  wire lt_warn1 = a < a;
  wire lt_warn2 = (a < a) & b;
  wire lt_warn3 = (a & b) & (a < a) & d;

  wire lte_no1 = a <= b;
  wire lte_no2 = a <= b & a;
  wire lte_no3 = a <= (a & b);
  wire lte_warn1 = a <= a;
  wire lte_warn2 = (a <= a) & b;
  wire lte_warn3 = (a & b) & (a <= a) & d;


  wire shl_no1 = a << b;
  wire shl_no2 = a << b & a;
  wire shl_no3 = a << (a & b);
  wire shl_no4 = 1 << 2;
  wire shl_no5 = 2 << 3;
  wire shl_no6 = 1 << 1;         // Special case, no warning for this one
  wire shl_warn1 = a << a;
  wire shl_warn2 = (a << a) & b;
  wire shl_warn3 = (a & b) & (a << a) & d;
  wire shl_warn4 = 2 << 2;       // Still want to warn on this, I think

  wire ashl_no1 = a <<< b;
  wire ashl_no2 = a <<< b & a;
  wire ashl_no3 = a <<< (a & b);
  wire ashl_no4 = 1 <<< 2;
  wire ashl_no5 = 2 <<< 3;
  wire ashl_no6 = 1 <<< 1;         // Special case, no warning for this one
  wire ashl_warn1 = a <<< a;
  wire ashl_warn2 = (a <<< a) & b;
  wire ashl_warn3 = (a & b) & (a <<< a) & d;
  wire ashl_warn4 = 2 <<< 2;       // Still want to warn on this, I think

  wire shr_no1 = a >> b;
  wire shr_no2 = a >> b & a;
  wire shr_no3 = a >> (a & b);
  wire shr_no4 = 1 >> 2;
  wire shr_no5 = 2 >> 3;
  wire shr_warn1 = a >> a;
  wire shr_warn2 = (a >> a) & b;
  wire shr_warn3 = (a & b) & (a >> a) & d;
  wire shr_warn4 = 2 >> 2;       // Still want to warn on this, I think
  wire shr_warn5 = 1 >> 1;       // Still want to warn on this, I think

  wire ashr_no1 = a >>> b;
  wire ashr_no2 = a >>> b & a;
  wire ashr_no3 = a >>> (a & b);
  wire ashr_no4 = 1 >>> 2;
  wire ashr_no5 = 2 >>> 3;
  wire ashr_warn1 = a >>> a;
  wire ashr_warn2 = (a >>> a) & b;
  wire ashr_warn3 = (a & b) & (a >>> a) & d;
  wire ashr_warn4 = 2 >>> 2;       // Still want to warn on this, I think
  wire ashr_warn5 = 1 >>> 1;       // Still want to warn on this, I think

  // After discussing it and doing it the other way, we don't want to warn
  // about a * a.
  wire times_no1 = a * b;
  wire times_no2 = a * b & a;
  wire times_no3 = a * (a & b);
  wire times_no4 = 1 * 2;
  wire times_no5 = 2 * 3;
  wire times_no6 = a * a;
  wire times_no7 = (a * a) & b;
  wire times_no8 = (a & b) & (a * a) & d;
  wire times_no9 = 2 * 2;
  wire times_no10 = 1 * 1;

  wire plus_no1 = a + 1 + 1;
  wire plus_no2 = b + 2 + 2;
  wire plus_no3 = 1 + a + 1;
  wire plus_no4 = (1 + 2) + a + (1 + 2);
  wire plus_no5 = a[b+b];
  wire plus_no6 = a[b+b+1];
  wire plus_no7 = a[b+b:0];
  wire plus_no8 = a[b+b+1:0];
  wire plus_no9 = {b+b{a,a}};
  wire plus_no10 = {b+b+1{a,a}};
  wire plus_warn1 = a + a;
  wire plus_warn2 = a + b + c + a;
  wire plus_warn3 = (a + 1) + (a + 1);
  wire plus_warn4 = a + b + (c - d) + a;
  wire plus_warn5 = a[3] + a[3];
  wire plus_warn6 = {a{b+b}};

  wire minus_no1 = a - (1 - 1);
  wire minus_no2 = b + 2 - 2;
  wire minus_no3 = 3 - a - 3;
  wire minus_no4 = a[b-b];
  wire minus_no5 = a[(b-b)+1];
  wire minus_no6 = a[b-b:0];
  wire minus_no7 = a[(b-b)+1:0];
  wire minus_no8 = {b-b{a,a}};
  wire minus_no9 = {(b-b)+1{a,a}};
  wire minus_warn1 = a - a;
  wire minus_warn2 = a - a + b - c;
  wire minus_warn3 = (a + 1) - (a + 1);
  wire minus_warn4 = a[3] - a[3];
  wire minus_warn5 = {a{b-b}};

  // BOZO it would be good to flag things like this too.  But this is trickier
  // because it gets parsed as, e.g., ((a+b)+c)-c.  So we'd need to go into the
  // LHS and gather up summands/subtrahends and then see if the RHS is among
  // them, or something like that.  I'll leave that for future work.
  // wire minus_warn6 = a + b + c - c;


  wire qmark_no1 = a ? b : c;
  wire qmark_no2 = a ? a : b;
  wire qmark_no3 = a ? b : a;
  wire qmark_warn1 = a ? b : b;
  wire qmark_warn2 = a ? b[3] : b[3];
  wire qmark_warn3 = a ? 1 : 1;

  wire [1:0] wire_no1;
  wire [1+1:0] wire_no2;
  wire [1-1:0] wire_no3;
  wire [1*1:0] wire_no4;

   sub subinst1 (.i(a % a));

   sub subinst2 (//@VL LINT_IGNORE_WARN_LEFTRIGHT
		 .i(a % a));

   //@VL LINT_IGNORE_WARN_LEFTRIGHT
   sub subinst3 (.i(a % a));


endmodule
