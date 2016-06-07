// Cosim Test for `define default parameters
// Copyright (C) 2016 Apple, Inc.
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

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   logic [3:0] i3, i2, i1, i0;
   assign {i3, i2, i1, i0} = in;

   logic [7:0] o3, o2, o1, o0;

   // Other tools are smart enough to parse string literals
   `define foo0(a, b=")") b
   assign o0 = `foo0(i0);
   assign o1 = `foo0(i0, i1);

   // Other tools seem to be able to handle this
   `define foo2(a=) a
   assign o2 = `foo2(i2);
   assign o3 = `foo2()i3;

   // Other tools seem to be able to handle this
   `define foo(a, b=wire [2:0] w) b
   `foo(ignored);
   wire [3:0]  o4 = w;
   assign w = i0;

   assign out = { o4, o3, o2, o1, o0 };

   initial begin
      #10;
      $display("o0 is %d", o0);
      $display("o1 is %d", o1);
      $display("o2 is %d", o2);
      $display("o3 is %d", o3);
   end

endmodule : spec
