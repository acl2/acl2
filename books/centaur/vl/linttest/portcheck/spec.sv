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

module m0 (port1, port2, port3);
  output port1;
  input  port2;
  inout  port3;
endmodule

module m1 (output [1:0] port1, input [3:0] port2, inout [2:0] port3) ;

endmodule

module m2 (port1, port2, , port3);
  output port1;
  input  port2;
  inout  port3;
endmodule

module m4 (port1, port2[3:0], port3);
  output port1;
  input [3:0] port2;
  inout       port3;
endmodule

module m5 (port1, {port2[3:0], port3}, port4);
  output port1;
  input [3:0] port2;
  inout       port3;
  input       port4;
endmodule

module m6 (port1, .port2(), port3) ;
  output port1;
  input port3;
endmodule

module m7 (port1, port1);
  output port1;
endmodule

module m8 (port1, port2);
  output port1;
endmodule

module m9 (port1, port2);
  output port1;
  input  port2;
  output port3;
endmodule
