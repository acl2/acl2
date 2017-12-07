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


module to_be_stubbed
  #(parameter width=5)
   (input [width-1:0] in0,
    input [width-1:0] in1,
    input in2,
    input in3,
    output [width-1:0] out0,
    output [width-1:0] out1,
    output out2,
    output out3);



endmodule // to_be_stubbed


module container ();

  logic [3:0] usedset4;
  logic [3:0] unset4;
  logic usedset1;
  logic unset1;
  logic [3:0] setused4;
  logic [3:0] unused4;
  logic setused1;
  logic unused1;

   assign usedset4 = setused4;
   assign usedset1 = setused1;

   //@VL LINT_IGNORE_INST
   to_be_stubbed #(4) stubinst (.in0(usedset4),
				.in1(unset4),
				.in2(usedset1),
				.in3(unset1),
				.out0(setused4),
				.out1(unused4),
				.out2(setused1),
				.out3(unused1));


endmodule // container

				
