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

module m0 (output o, input a, b);
  assign o = a & b;
endmodule

module m1 ;
  initial $display("Hello, world!");
endmodule

interface i0 ;
  logic [3:0] foo, bar;
endinterface

interface i1 (output o, input a);
  logic       b, c;
endinterface



module top ;

  logic w1, w2, w3, w4, w5, w6;

  // Ports don't agree with anything else.
  m0 m0_normal (w1, w2, w4);

  // Same ports all the way across.
  m0 m0_sp_a (w1, w2, w3);
  m0 m0_sp_b (.o(w1), .a(w2), .b(w3));

  // Same inputs but not outputs.
  m0 m0_si_a (w4, w2, w6);
  m0 m0_si_b (.o(w5), .a(w2), .b(w6));

  // I think we shouldn't warn about duplicates when they have no ports, since
  // those are likely to be checker code or something we're not really going to
  // be understanding.
  m1 m1_normal_a ();
  m1 m1_normal_b ();

  // I think we should never warn about interfaces.  Unlike module instances,
  // the interface instance doesn't tell us much of anything.  It is perfectly
  // sensible to have multiple instances of the same interface, and the ports
  // of the interface, if any, aren't the only way info flows into/out of the
  // interface.
  i0 i0_normal_a ();
  i0 i0_normal_b ();

  // Same ports, but don't warn because they're interfaces.
  i1 i1_normal_a (w4, w5);
  i1 i1_normal_b (w4, w5);

  // Same inputs, but don't warn because they're interfaces.
  i1 i1_normal_c (w4, w5);
  i1 i1_normal_d (w5, w5);





  wire 	xx0, xx1, xx2;
  genvar i;
  generate
    for(i = 0; i < 3; ++i) begin : foo
      m0 m0arr(xx0, xx1, xx2);
      i0 i0arr();
    end
  endgenerate


  wire w7;
  if (size == 0)
  begin
    m0 m0_gen1 (w7, a, a);
  end
  else
  begin
    m0 m0_gen2 (w7, a, a);
  end

endmodule
