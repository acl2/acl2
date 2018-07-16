// Cosim Test for `define redefinition
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

   logic [3:0] o5, o4, o3, o2, o1, o0;

   // Note that this test should be run with +define+test_define=3

   // Other tools treat command-line defines as somehow "sticky."  I don't
   // think this behavior is described anywhere in the standard but they both
   // seem to follow it.

   // By "sticky", I mean that the if you give +define+test_define=3 at the
   // command line, then test_define won't be redefined to be 4 when you
   // encounter `define test_define 4.  That is, this will (of course) be 3:

   assign o0 = `test_define;

   // But surprisingly o1 will also be 3 even though it looks like we are
   // defining test_define to be 4.
   `define test_define 4
   assign o1 = `test_define;

   // It seems that an undefine is sufficient to get rid of this sticky
   // behavior.  That is, o2 will become 5 here.
   `undef test_define
   `define test_define 5
   assign o2 = `test_define;

   // Once the stickiness has gone away, it stays away.  That is, this
   // will become 6.
   `define test_define 6
   assign o3 = `test_define;


   // Normal defines don't work this way.  A subsequent definition is
   // always treated as a redefinition without needing an undef.
   `define other_define 3
   assign o4 = `other_define;

   `define other_define 4
   assign o5 = `other_define;


   assign out = { o5, o4, o3, o2, o1, o0 };

endmodule : spec
