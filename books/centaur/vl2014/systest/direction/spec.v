// VL 2014 -- Verilog Toolkit, 2014 Edition
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


// basic tests of wire direction handling

module dir_test (

in1,
in2,

out1,
out2,
out3,
out4,
out5,
out6,
out7,
out8,
out9,
out10,
out11,
out12,
out13,
out14,
out15

);

   parameter size = 1;
   wire [size-1:0] make_size_matter;

   input [3:0] in1;
   input [3:0] in2;

   output [3:0] out1;
   output [0:3] out2;
   output [7:0] out3;

   assign out1 = in1;
   assign out2 = in1;
   assign out3 = { out1, out2 };


   output [3:0] out4;
   output [3:0] out5;
   output [0:3] out6;
   output [0:3] out7;

   two_bit_and and1 [1:0] (out4, in1, in2);
   two_bit_and and2 [0:1] (out5, in1, in2);
   two_bit_and and3 [2:1] (out6, in1, in2);
   two_bit_and and4 [1:2] (out7, in1, in2);


   output [3:0] out8;
   output [3:0] out9;
   output [0:3] out10;
   output [0:3] out11;

   assign out8  = out1[3:0];
   assign out9  = {out1[3], out1[2], out1[1:0]};
   assign out10 = out1[3:0];
   assign out11 = {out1[3], out1[2], out1[1:0]};

   output [3:0] out12;
   output [3:0] out13;
   output [0:3] out14;
   output [0:3] out15;

   assign out12 = out2[0:3];
   assign out13 = {out2[3], out2[1:2], out2[0]};
   assign out14 = out2[0:3];
   assign out15 = {out2[3], out2[1:2], out2[0]};

endmodule


/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

   dir_test #(1) dir_test_1 (4'b0, 4'b0,
    w[3:0],
    w[3:0],
    w[7:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0],
    w[3:0]);

endmodule

*/
