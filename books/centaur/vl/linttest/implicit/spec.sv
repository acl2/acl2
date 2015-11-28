// VL 2014 -- Verilog Toolkit, 2014 Edition
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

module sub (output out, input in);
  assign out = in;
endmodule

logic top_g1;
logic top_m1;
logic top_a1;

typedef struct packed {
  logic a;
  logic b;
  logic c;
} triple_t;

module subtriple (output triple_t out, input triple_t in) ;
  assign out = in;
endmodule

module m0 () ;

  wire w1_declared = 0;

  // Some implicit gate stuff
  buf(g1_implicit, w1_declared);
  and(w1_declared, g2_implicit, g3_implicit);
  and(w1_declared, g4_implicit + g5_implicit);
  buf mybuf [1:0] ({g6_implicit,g7_implicit}, 2'b0);
  buf(top_g1, g8_implicit);

  // NCV and VCS allow this, even though s1 isn't declared until later.
  wire subref1 = s1.in;

  // NCV and VCS allow this, even though t1 isn't declared until later.
  wire subref2 = t1.a;

  triple_t t1 = 0;


  // Implicit wires in module instances
  sub s1 (w1_declared, m1_implicit);
  sub s2 (m2_implicit, w1_declared);
  sub s3 (m3_implicit, m4_implicit + m5_implicit);
  sub s4 (top_m1, {m6_implicit,{m7_implicit,m8_implicit}});

`ifndef VCS
  // NCV infers these are implicit wires
  // VCS says structure patterns aren't implemented here yet
  sub s5 (.out(triple_t'{a:m9_implicit,b:m10_implicit,c:m11_implicit}), .in(0));
`endif

  // BOZO maybe add array pattern

  // Implicit wires in assignments
  assign a1_implicit = w1_declared;
  assign {a2_implicit,a3_implicit} = 0;
  //+VL  assign top_a1 = a4_undeclared;
  assign a5_implicit = a5_implicit;
  assign {a6_implicit,a7_implicit} = {a7_implicit,a6_implicit};

  // Implicit wires in aliases
  alias al_implicit1 = w1_declared;
  alias al_implicit2 = al_implicit3;
  alias al_implicit4 = al_implicit5;
  assign al_implicit4 = 0;
  alias al_implicit6 = al_implicit7;
  assign w1_declared = al_implicit7;


endmodule


module m1 () ;

  wire [3:0] vec;

  // VCS and NCV reject this, saying that w1_undeclared is undeclared.
  //+VL assign vec[w1_undeclared] = 0;

  // VCS and NCV reject this, saying that w2_undeclared is undeclared.
  //+VL assign {xxx,vec[w2_undeclared]} = 0;

  // NCV and VCS reject this, saying that w3_undeclared is undeclared.
  //+VL assign w3_undeclared[0] = 0;


  function logic myfun (input logic [2:0] bar) ;
    myfun = bar;
  endfunction

//  buf(o, myfun(y));

//  buf(o, {foo{bar}});

//  buf(o, a inside {b, c, d});

//  buf(o, {<< w {a,b,c}});






// More things to test --
  // .name style connections to submodule are not allowed to introduce implicit wires
  // .* style connections should not add implicit wires

// all the stuff below
  
  // NCV and VCS reject this:
  //  assign vec[d] = 0;

  // NCV and VCS reject this:
  // assign {d,vec[d]} = 0;

  // NCV says d is implicitly declared and then redeclared
  // VCS says it's not implicitly declared
  //  assign vec[d] = 0;
  //  parameter d = 0;

  // NCV and VCS reject this, saying vec2 isn't declared yet
  // parameter d = 0;
  // assign vec2[d] = 0;

  // VCS says these aren't declared yet, NCV says this isn't a legal net_lvalue anyway
  // assign {>>{e, f, g}} = 0;

  // NCV and VCS both allow this but warn that w1/w2 aren't driven
  //and myand(o, w1 + w2);

  // NCV rejects this but VCS accepts it (with warnings)
  //and myand(o, w1[0] + w2[0]);

  // NCV rejects this but VCS accepts it (with warnings)
//  and myand(o, w1[w2]);


// undeclared variables in blocks
  // corner cases:
  //   reg [r:0-1] r;
  // etc.


// all kinds of port-implicitness stuff

endmodule

