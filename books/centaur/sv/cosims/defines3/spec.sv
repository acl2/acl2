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

   // Some other tools handle this, and some don't.  In some cases it what is
   // supported doesn't seem to make sense, e.g., there seems to be more
   // consistent support for this when put a [2:0] range on the wire, but some
   // tools complain there's a parse error with an unexpected semicolon here.
   `define foo(a, b=wire w) b
   `foo(ignored);
   assign o0 = w;
   assign w = i0;

   // Some tools tolerate the following, but we have seen at least one other
   // tool go insane and print a crazy 'unexpected character' message about
   // 'the character code '\012' is illegal' and that the file may be
   // corrupted.
   `define foo1(a, b=\foo,bar ) a + b
   wire [3:0]  \foo,bar = i1;
   assign o1 = `foo1(i0);
   assign o2 = `foo1(i2,i3);
   assign o3 = `foo1(i2);

   assign out = { o3, o2, o1, o0 };

   initial begin
      #10;
      $display("o0 is %d", o0);
      $display("o1 is %d", o1);
      $display("o2 is %d", o2);
      $display("o3 is %d", o3);
   end

endmodule : spec
