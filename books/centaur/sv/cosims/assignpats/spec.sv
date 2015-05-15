// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2014-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Sol Swords <sswords@centtech.com>

typedef logic [3:0][3:0] fourbyfour;

typedef struct { logic [3:0] foo; logic [2:0] bar [1:3]; } fb;

typedef struct { logic [3:0] foo; logic [3:0] bar; logic[3:0] baz; } bz;

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire [3:0] a;
  wire [3:0] b;
  wire [3:0] c;
  wire [3:0] d;
  wire [3:0] e;
   assign {a,b,c,d,e} = in;

  wire logic [3:0] a1 [1:4];
   // BOZO this doesn't work in ncverilog yet
   // assign a1 = '{4{a}};

  wire logic [3:0] a2 [1:4];
   assign a2 = '{ a,b,c,d };

  wire logic [3:0] a3 [1:4];
   assign a3 = '{ 1:a, 3:b, default:d };

  wire logic [12:0] a4;
  assign a4 = fourbyfour'{ 1:a, 3:b, default:d };

   fb f1;
   assign f1 = '{ a, '{b[2:0], c[3:1], d[2:0]} };

   fb f2;
    // BOZO this doesn't work in ncverilog yet
   // assign f2 = '{ a, '{3{e[2:0]}} };

   fb f3;
    // BOZO this doesn't work in ncverilog yet
   // assign f3 = '{ foo:a, bar:'{3{e[3:1]}} };

   fb f4;
    // BOZO this doesn't work in ncverilog yet
   // assign f4 = '{ bar:'{3{e[3:1]}}, default:d };

   // ncverilog doesn't allow replication for structs
   // bz b1;
   // assign b1 = '{3{d}};

   assign out = { // a1[1],a1[2],a1[3],a1[4],
                  a2[1],a2[2],a2[3],a2[4],
                  a3[1],a3[2],a3[3],a3[4],
                  a4,
		  f1.foo, f1.bar[1], f1.bar[2], f1.bar[3]
		  // f2.foo, f2.bar[1], f2.bar[2], f2.bar[3],
		  // f3.foo, f3.bar[1], f3.bar[2], f3.bar[3],
		  // f4.foo, f4.bar[1], f4.bar[2], f4.bar[3]
		  };

   // initial begin
   //  #10;
   //  // a1 = '{4{a}};
   //  $display("a1[1]: %h", a1[1]);
   //  $display("a: %h", a);
   //  end

endmodule
