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

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  parameter version = 1;

  wire [3:0] A9, A8, A7, A6, A5, A4, A3, A2, A1, A0;
  wire [3:0] B9, B8, B7, B6, B5, B4, B3, B2, B1, B0;


  assign { B9, B8, B7, B6, B5, B4, B3, B2, B1, B0,
           A9, A8, A7, A6, A5, A4, A3, A2, A1, A0 } = in;

  // This one is just a bunch of tests of direct conditional nesting; see
  // SystemVerilog 27.5.  I originally thought these should be conditionally
  // nested and wouldn't introduce scopes, but that's not quite right: a new
  // scope is only not added when the IF/CASE occurs directly within another
  // IF/CASE.

  if (version == 0)
  begin : foo
    wire [3:0] bar = A0;
  end
  else if (version == 1)
     wire [3:0] xxx = A1;
  else
     wire [3:0] foo = A2;

  wire [3:0] xxx = A3;  // This works, so the above if/else are not directly nested


  if (version == 0)
      wire [3:0] yyy = A4;
  else if (version == 1)
  begin : bar
      wire [3:0] yyy = A5;
  end
  else ;

  if (version == 0)
      wire [3:0] zzz = A6;
  else if (version == 1)
      wire [3:0] zzz = A7;
  else ;

  wire [3:0] zzz = A8;   // This works, so the zzz ifelse are not directly nested


  if (version == 0)
      wire [3:0] www = A9;
  else if (version == 1)
      wire [3:0] www = B0;

  wire [3:0] www = B1;   // This works, so the www ifelse are not directly nested


  if (version == 0)
      wire [3:0] vvv = B2;
  else if (version == 1)
      wire [3:0] vvv = B3;
  else
     wire [3:0] vvv = B4;

  wire [3:0] 	vvv = B5; // This works, so the vvv ifelse are not directly nested


  if (version == 0)
      wire [3:0] uuu = B6;
  else
      wire [3:0] uuu = B7;

  wire [3:0] 	uuu = B8; // This works, so the uuu ifelse are not directly nested


  assign out = { uuu, vvv, www, zzz, bar.yyy, xxx };


  for(genvar i = 0; i < 10; ++i) ;



endmodule
