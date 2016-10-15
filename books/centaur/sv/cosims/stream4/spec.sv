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
	     output wire [127:0] out);

  logic [8:0] out0;
  logic [6:0] out1;
   assign in1 = in;
   assign {<< 5 {{<< 3 {out0}}, out1}} = in[31:0];

  logic [8:0] out2;
  logic [6:0] out3;

   assign {<< 5 {{>> {out2}}, out3}} = in[31:0];


  logic [8:0] out4;
  logic [6:0] out5;

   assign {>> 5 {{<< 3 {out4}}, out5}} = in[31:0];

  logic [4:0] out6;
  logic [3:0] out7;
  logic [2:0] out8;
  logic [3:0] out9;

   assign {<< 5 {{>> {{<< 3 {out6}}, {<< 2 {out7}}}}, {<< 4 {{>> {out8}}, {>> {out9}}}}}} = in[31:0];


  logic [8:0] out10;
  logic [6:0] out11;
   assign in1 = in;
   assign {<< 5 {{<< 3 {out10}}, out11}} = in[15:0];

  logic [8:0] out12;
  logic [6:0] out13;

   assign {<< 5 {{>> {out12}}, out13}} = in[15:0];


  logic [8:0] out14;
  logic [6:0] out15;

   assign {>> {{<< 3 {out14}}, out15}} = in[15:0];

  logic [4:0] out16;
  logic [3:0] out17;
  logic [2:0] out18;
  logic [3:0] out19;

   assign {<< 5 {{>> {{<< 3 {out16}}, {<< 2 {out17}}}}, {<< 4 {{>> {out18}}, {>> {out19}}}}}} = in[15:0];




   assign out = {out19, out18, out17, out16, out15, out14, out13, out12, out11, out10,
		 out9, out8, out7, out6, out5, out4, out3, out2, out1, out0};


endmodule
