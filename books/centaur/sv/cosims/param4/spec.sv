// Parameter declaration test
// Copyright (C) 2019 Apple, Inc.
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
// Original author: Jared Davis

typedef logic [10:0] foo_t;

module m1 #(SIZE = 4)

  (input [SIZE-1:0] a,
   input [SIZE-1:0] b,
   output [SIZE-1:0] o);

   assign o = a & b;

endmodule

module m2 #(foo_t SIZE = 4)
  (input [SIZE-1:0] a,
   input [SIZE-1:0] b,
   output [SIZE-1:0] o);

   assign o = a | b;

endmodule

module m3 #(SIZE_A = 4,
            foo_t SIZE_B = 3    // foo_t is just the type of the parameter, has no relation to the actual size
            )

  (input [SIZE_A-1:0] a,
   input [SIZE_B-1:0] b,

   output [(SIZE_A + SIZE_B - 1):0] o);

   assign o = {a, b};

endmodule

module m4 #(SIZE_A,
            foo_t SIZE_B = 3)

  (input [SIZE_A-1:0] a,
   input [SIZE_B-1:0] b,

   output [(SIZE_A + SIZE_B - 1):0] o);

   assign o = {a, b};

endmodule


module spec (input logic [127:0] in,
	     output wire [127:0] out);

   localparam SIZE_M1 = 5;
   localparam SIZE_M2 = 2;

   localparam SIZE_M3_A = 4;
   localparam SIZE_M3_B = 7;

   localparam SIZE_M4_A = 2;
   localparam SIZE_M4_B = 3;

   wire [SIZE_M1-1:0] a1, b1, o1;
   wire [SIZE_M2-1:0] a2, b2, o2;

   wire [SIZE_M3_A-1:0] a3;
   wire [SIZE_M3_B-1:0] b3;
   wire [(SIZE_M3_A + SIZE_M3_B - 1):0] o3;

   wire [SIZE_M4_A-1:0] a4;
   wire [SIZE_M4_B-1:0] b4;
   wire [(SIZE_M4_A + SIZE_M4_B - 1):0] o4;

   assign {a4,a3,a2,a1,b4,b3,b2,b1} = in;

   m1 #(.SIZE(SIZE_M1)) m1_inst (.a(a1), .b(b1), .o(o1));
   m2 #(.SIZE(SIZE_M2)) m2_inst (.a(a2), .b(b2), .o(o2));
   m3 #(.SIZE_A(SIZE_M3_A), .SIZE_B(SIZE_M3_B)) m3_inst (.a(a3), .b(b3), .o(o3));
   m4 #(.SIZE_A(SIZE_M4_A), .SIZE_B(SIZE_M4_B)) m4_inst (.a(a4), .b(b4), .o(o4));

   assign out = {o4,o3,o2,o1};

endmodule

