// Plusarg Cosim Test
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

   logic [3:0] o3, o2, o1, o0;

   // We expect to run this with +test_is_plusarg but not other stuff.
   always_comb
     begin
	o0 = $test$plusargs("unlikely_plusarg") ? i0 : ~i0;
     end

   assign o1 = i1 + $test$plusargs("test_is_plusarg");

   assign o2 = i2 + $test$plusargs("unlikely_plusarg");

   // Should be 1 since $test$plusargs does substring matching.
   assign o3 = $test$plusargs("test_is");

   // What about signedness and size?  It seems to be 32 bits on other tools.
   // It's probably a signed integer.
   wire [7:0] o4 = $bits($test$plusargs("test_is_plusarg"));
   wire [7:0] o5 = $bits($test$plusargs("unlikely_plusarg"));

   // If it is signed, then this should get sign extended
   wire [5:0] o6 = ($test$plusargs("test_is_plusarg") << 31) >> 30;
   wire [5:0] o7 = ($signed($test$plusargs("test_is_plusarg")) << 31) >> 30;

   assign out = {o7, o6, o5, o4, o3, o2, o1, o0};

endmodule : spec

module temp ;

   logic [127:0] in, out;
   spec myspec (.*);

   initial begin
      $display("Hello world");
      #10;
      in = 0;
      #10;
      $display("Out is %b", out);
      $display("blah: %d", $bits($test$plusargs("test_is_plusarg")));
      
   end 
      
endmodule
