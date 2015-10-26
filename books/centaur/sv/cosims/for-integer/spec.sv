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

  // [Jared] originally this test had the following:
  //
  // integer [7:0] i;
  //
  // However AFAICT this is not legal SystemVerilog anyway -- integer is an
  // integer_atom_type, and note that the rule for data_type is:
  //    data_type ::= integer_atom_type [ signing ]
  //
  // so I don't believe that dimensions should be allowed here.  It's really
  // surprising that NCVerilog and VCS both tolerate it.  According to this,
  // both simulators seem to think that i is 32 bits anyway, despite the [7:0]
  // range on it.
  //
  // initial begin
  //    $display("Size of i is %d", $bits(i));
  // end
  //
  // At any rate, I think VL is perfectly correct to reject this as a parse
  // error, and NCVerilog and VCS should not be tolerating this syntax.  I'll
  // keep this test but just change i to be an ordinary integer.

  integer i;

  always @* begin
    for (i=0; i<128; i=i+1) begin
      out[i] = in[i];
    end
  end

endmodule
