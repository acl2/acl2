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

module m0 ;

  wire a;
  wire b;
  wire c;

  wire [1:0] AA;
  wire [1:0] BB;
  wire [1:0] CC;


  wire xxplus1  = a + b + c;
  wire xxplus2  = a + b - c;
  wire xxplus3  = a + b << c;
  wire xxplus4  = a + b < c;
  wire xxplus5  = a + b == c;
  wire xxplus6  = a + b & c;
  wire xxplus7  = a + b ^ c;
  wire xxplus8  = a + b | c;
  wire xxplus9  = a + b && c;
  wire xxplusA  = a + b || c;


  wire xxminus1  = a - b + c;
  wire xxminus2  = a - b - c;
  wire xxminus3  = a - b << c;
  wire xxminus4  = a - b < c;
  wire xxminus5  = a - b == c;
  wire xxminus6  = a - b & c;
  wire xxminus7  = a - b ^ c;
  wire xxminus8  = a - b | c;
  wire xxminus9  = a - b && c;
  wire xxminusA  = a - b || c;


  wire xxshl1  = a << b + c;
  wire xxshl2  = a << b - c;
  wire xxshl3  = a << b << c;
  wire xxshl4  = a << b < c;
  wire xxshl5  = a << b == c;
  wire xxshl6  = a << b & c;
  wire xxshl7  = a << b ^ c;
  wire xxshl8  = a << b | c;
  wire xxshl9  = a << b && c;
  wire xxshlA  = a << b || c;


  wire xxshr1  = a >> b + c;
  wire xxshr2  = a >> b - c;
  wire xxshr3  = a >> b << c;
  wire xxshr4  = a >> b < c;
  wire xxshr5  = a >> b == c;
  wire xxshr6  = a >> b & c;
  wire xxshr7  = a >> b ^ c;
  wire xxshr8  = a >> b | c;
  wire xxshr9  = a >> b && c;
  wire xxshrA  = a >> b || c;


  wire xxlt1  = a < b + c;
  wire xxlt2  = a < b - c;
  wire xxlt3  = a < b << c;
  wire xxlt4  = a < b < c;
  wire xxlt5  = a < b == c;
  wire xxlt6  = a < b & c;   // should not warn because it's too common
  wire xxlt7  = a < b ^ c;   // same??
  wire xxlt8  = a < b | c;   // should not warn because it's too common
  wire xxlt9  = a < b && c;
  wire xxltA  = a < b || c;

  wire yylt1  = a < b + CC;
  wire yylt2  = a < b - CC;
  wire yylt3  = a < b << CC;
  wire yylt4  = a < b < CC;
  wire yylt5  = a < b == CC;
  wire yylt6  = a < b & CC;   // should warn because we're doing (a < b) & wide thing
  wire yylt7  = a < b ^ CC;   // same??
  wire yylt8  = a < b | CC;   // same
  wire yylt9  = a < b && CC;
  wire yyltA  = a < b || CC;



  wire xxeq1  = a == b + c;
  wire xxeq2  = a == b - c;
  wire xxeq3  = a == b << c;
  wire xxeq4  = a == b < c;
  wire xxeq5  = a == b == c;
  wire xxeq6  = a == b & c;   // should not warn because it's too common
  wire xxeq7  = a == b ^ c;   // eh??
  wire xxeq8  = a == b | c;   // should not warn because it's too common
  wire xxeq9  = a == b && c;
  wire xxeqA  = a == b || c;

  wire yyeq1  = a == b + CC;
  wire yyeq2  = a == b - CC;
  wire yyeq3  = a == b << CC;
  wire yyeq4  = a == b < CC;
  wire yyeq5  = a == b == CC;
  wire yyeq6  = a == b & CC;   // should warn because we're doing (a == b) & wide thing
  wire yyeq7  = a == b ^ CC;   // eh??
  wire yyeq8  = a == b | CC;   // same
  wire yyeq9  = a == b && CC;
  wire yyeqA  = a == b || CC;


  wire xxand1  = a & b + c;
  wire xxand2  = a & b - c;
  wire xxand3  = a & b << c;
  wire xxand4  = a & b < c;    // a & (b < c) -- permit since a is one bit
  wire xxand5  = a & b == c;   // a & (b == c) -- permit since a is one bit
  wire xxand6  = a & b & c;
  wire xxand7  = a & b ^ c;
  wire xxand8  = a & b | c;
  wire xxand9  = a & b && c;   // (a & b) && c
  wire xxandA  = a & b || c;   // (a & b) || c    bozo want finer grained cases here


  wire yyand1  = AA & b + c;
  wire yyand2  = AA & b - c;
  wire yyand3  = AA & b << c;
  wire yyand4  = AA & b < c;    // AA & (b < c) -- warn since A is wide
  wire yyand5  = AA & b == c;   // AA & (b == c) -- warn since A is wide
  wire yyand6  = AA & b & c;
  wire yyand7  = AA & b ^ c;
  wire yyand8  = AA & b | c;
  wire yyand9  = AA & b && c;   // (AA & b) && c
  wire yyandA  = AA & b || c;   // (AA & b) || c    bozo want finer grained cases here




endmodule
