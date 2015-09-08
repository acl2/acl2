// SV - Regression Test
// Copyright (C) 2015, Oracle and/or its affiliates. All rights reserved.
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
// Original authors: David L. Rager <david.rager@oracle.com>

module spec (input logic [127:0] in,
			 output logic [127:0] out);

   logic [7:0] 				  local_in;
   logic [7:0] 				  local_out;

   assign local_in[7:0] = in[7:0];
   always @ *
   begin
	  convert (local_in, local_out);
   end

   assign out[127:8] = 120'b0;
   assign out[7:0] = local_out;

   task convert;
	  input [7:0] the_in;
	  output [7:0] the_out;
	  begin
		 the_out = 5 * (the_in - 32);
	  end
   endtask

endmodule // spec
