// paramarray3 cosim test
// Copyright (C) 2017 Apple, Inc.
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
// Same idea as paramarray2, but extended to cover some additional cases

module spec (input logic [127:0] in,
	     output logic [127:0] out);

   // Packed dimensions instead of unpacked
   localparam logic [7:0][7:0] foo = '{ 'h80, 'h40, 'h20, 'h10, 'h08, 'h04, 'h02, 'h01 };

   // Implicit type instead of explicit type
   localparam [7:0][7:0] foo2 = '{ 'h08, 'h04, 'h02, 'h01, 'h80, 'h40, 'h20, 'h10 };

   function automatic logic [7:0] floo (logic [2:0] in);
     floo = foo[in] ^ (1 << in);
   endfunction

   function automatic logic [7:0] floo2 (logic [2:0] in);
     return foo2[in] ^ (1 << in);
   endfunction

   wire [7:0] o1 = floo(in[2:0]);
   wire [7:0] o2 = floo2(in[2:0]);

   assign out = {o2, o1};

endmodule // spec
