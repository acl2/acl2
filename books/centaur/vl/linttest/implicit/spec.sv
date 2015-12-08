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

// This started out as a test of implicit wire handling.  Since then it's grown
// to do a lot of testing of scoping and knowing when things are declared or
// undeclared.

//+VL `define VL 1

module sub (output out, input in);
  assign out = in;
endmodule

function logic myfun (input logic [2:0] bar) ;
  myfun = bar;
endfunction

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

// VCS and NCV both complain that this is not declared yet.
// BOZO VL doesn't get this right yet.  Fixing it will be harder
// than fixing most other stuff.

//+VL parameter undeclared_param1 = pkg1_decl1;

`ifndef VCS
// NCVerilog is able to resolve this even though pkg1 hasn't been declared yet.
// VCS complains here and says pkg1 is undeclared.
parameter unused_param2 = pkg1::pkg1_decl2;
`endif

parameter pkg1_decl3 = 4;

package pkg1;

  parameter pkg1_decl1 = 1;
  parameter pkg1_decl2 = 2;
  parameter pkg1_decl3 = 3;

endpackage

import pkg1::*;

parameter derived_param1 = pkg1_decl1;
parameter derived_param2 = pkg1::pkg1_decl2;


module subnames (output subname_out1, input subname_in1);
  assign subname_out1 = subname_in1;
endmodule

module m0 () ;

  wire w1_declared = 0;

  // Implicit wires in assignments
  assign a1_implicit = w1_declared;
  assign {a2_implicit,a3_implicit} = 0;
  //+VL  assign top_a1 = a4_undeclared;
  assign a5_implicit = a5_implicit;
  assign {a6_implicit,a7_implicit} = {a7_implicit,a6_implicit};

  wire [3:0] vec;

  // VCS says this is an error because a8_undeclared is an undeclared
  // identifier.
  //
  // NCV rejects this saying that a8_undeclared is an illegal operand for
  // constant expression.  But it is definitely inferring an implicit wire,
  // because when we add "parameter a8_undeclared = 0" afterwards, we get an
  // error about a8_undeclared being redeclared.
  //
  // Let's mimic VCS and treat this as undeclared.

  //+VL assign vec[a8_undeclared] = 0;

  // parameter a8_undeclared = 0;


  // NCV says this is an illegal operand for a constant expression.  By the
  // same parameter trick, we can see that it infers a wire for a9_implicit.
  //
  // VCS says this is an illegal structural left hand side.  By the same
  // parameter trick, we can tell that it also infers an implicit wire.
  //
  // Let's mimic them and infer a wire here.

  //+VL assign {a9_implicit,vec[a9_implicit]} = 0;

  // parameter a9_implicit = 0;

  // NCV and VCS reject this, saying it's not declared.
  parameter index = 0;
  //+VL assign a10_undeclared[index] = 0;



  // Some implicit gate stuff
  buf(g1_implicit, w1_declared);
  and(w1_declared, g2_implicit, g3_implicit);
  and(w1_declared, g4_implicit + g5_implicit);
  buf mybuf [1:0] ({g6_implicit,g7_implicit}, 2'b0);
  buf(top_g1, g8_implicit);
  buf(o, myfun(g9_implicit));
  buf(o, {4{g10_implicit}});

  // NCV says this is an illegal operand for constant expression
  // VCS complains that the multiplier needs to be a known constant value, but
  // also says: "implicit wire g11_implicit does not have any driver", so it
  // seems like it's inferring a wire here.
  //+VL buf(o, {g11_implicit{1'b0}});

  // NCV and VCS agree that these are implicit wires
  buf(o, a inside {0, g12_implicit, 1});
  buf(o, g13_implicit inside {0, 1});

  // VCS and NCV reject this saying that g14_implicit isn't a valid constant
  // expression.  We infer a wire for it and then complain later that we
  // failed to resolve the slice size.  That seems fine.
  //+VL buf(o, {<< g14_implicit {0, 1}});

  // VCS says streaming operators as gate expressions isn't supported yet
  // NCV is fine with this, says g15 is implicit.
  `ifndef VCS
  buf(o, {<< int {0, g15_implicit}});
  `endif

  `ifndef INCA
  // NCV rejects this and says it's an undeclared identifier.
  // VCS accepts this and infers an implicit wire for g16_undeclared, with the
  // usual warnings.
  // We think NCV's behavior is more consistent with the treatment of indexed
  // and part-selected expressions on the LHS of assignments such as a8_undeclared
  // above, so we will treat this as an undeclared identifier.
  and myand(o, g16_undeclared[0] + 1);
  `endif

  // Distressingly, NCV and VCS accept this and infer an implicit wire for
  // g17_undeclared.  This seems very inconsistent with the behavior above in
  // a8_undeclared.
  and myand2(o, vec[g17_undeclared]);

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


  // Implicit wires in aliases
  alias al_implicit1 = w1_declared;
  alias al_implicit2 = al_implicit3;
  alias al_implicit4 = al_implicit5;
  assign al_implicit4 = 0;
  alias al_implicit6 = al_implicit7;
  assign w1_declared = al_implicit7;


endmodule


module m1 () ;

  // VCS and NCV reject this, saying that w1_undeclared is undeclared.
  //+VL assign vec[w1_undeclared] = 0;

  // VCS and NCV reject this, saying that w2_undeclared is undeclared.
  //+VL assign {xxx,vec[w2_undeclared]} = 0;

  // NCV and VCS reject this, saying that w3_undeclared is undeclared.
  //+VL assign w3_undeclared[0] = 0;

  // Type casts are tricky
  wire w4_unset;
  wire w5_unused = triple_t'(w4_unset);

  // NCV and VCS reject this, saying undeclared_t is undeclared.
  //+VL wire xxx4 = undeclared_t'(w4_unset);

  wire w6_unused = pkg1_decl1;

  wire w7_unused = pkg1::pkg1_decl2;

endmodule


module m2 () ;

  // .name style connections to submodule are not allowed to introduce implicit wires

  // NCV complains that subname_in1 is undeclared.

  // VCS complains that subname_in1 is undeclared and also issues a warning
  // about there being too few port connections to the module (which just
  // seems silly).

  wire subname_out1;
  //+VL subnames mysubnames_dotnames (.subname_out1, .subname_in1);

endmodule


module m3 () ;

  // .* style connections should not add implicit wires

  // VCS gives a proper error about subname_out1 and subname_in1 being
  // undeclared.

  // NCV only gives us warnings and doesn't treat this as an error.

  `ifndef VCS
  subnames mysubnames_dotstar (.*);
  `endif

endmodule


module m4 () ;

  // Tricky case.  If we use .* connections, do the wires have to be declared
  // before that instance?

  // VCS seems to think it's OK to declare them afterward.
  // NCV seems to think so too.

  // I'm not sure whether this should work or not according to the standard.
  // Fortunately, VL doesn't check that .* connections are defined until after
  // introducing implicit wires, so this to work like the commercial tools.

  subnames mysubnames_later (.*);

  wire subname_out1, subname_in1;


endmodule


module m5 () ;

  // Like m4, but let's try to introduce them implicitly instead of explicitly.

  // Still works on NCV.
  // Still works on VCS.

  // So this suggests that these tools, like VL, are checking .* connections
  // some time after introducing implicit wires.

  subnames mysubnames_later (.*);
  buf(subname_out1, subname_in1);

endmodule



// Huh.  I wonder if this makes any sense with respect to scoping.

module messy (output messy_out, input messy_in) ;
  assign messy_out = messy_in;
endmodule

logic messy_in = 1'b0;

module m6 ();

  messy mymessy(.*);

  wire messy_out;
  wire messy_in = 1'b1;

  initial begin
    #10;
    // NCV and VCS say that this is 1.
    $display("m6: messy_out is %d", messy_out);
  end

endmodule

module m7 () ;

  messy mymessy(.*);
  wire messy_out;

  initial begin
    #10;
    // VCS says that this is 0.
    // NCV says this is Z.
    // Well, this just seems like a NCV bug.
    $display("m7: messy_out is %d", messy_out);
  end

endmodule

module m8 () ;

  task mytask;
    parameter filename = "check.rb";
    integer fd;
    begin
      $display("file is %s", filename);
      fd = $fopen(filename);
      $fclose(fd);
    end
  endtask

endmodule



// Some testing of scopes for ports.

// VCS and NCV agree that these types are not defined and hence all of these
// modules are not OK:

`ifdef VL

module m9 (input m9type_t in) ;
  typedef logic m9type_t;
endmodule

module m10 (input m10type_t in) ;
  parameter type m10type_t = logic;
endmodule

module m11 (in);
  input m11type_t in;
  parameter type m11type_t = logic;
endmodule

`endif

// However... VCS and NCV also also agree that the following are all just fine.
// So this is pretty tricky.  For port scoping we can make use of parameters
// only that come before the ports.

module m12 #(parameter type m12type_t = logic)
  (input m12type_t in) ;
endmodule

module m13 (in);
  parameter type m13type_t = logic;
  input m13type_t in;
endmodule


module m14;

  // As expected VCS and NCV are fine with this.
  typedef logic fun1type_t;
  function fun1type_t fun1 ;
    fun1 = 0;
  endfunction

  // NCV and VCS say that fun2type_t is not defined.  So it seems like the
  // return type is scoped outside the function.
`ifdef VL
  function fun2type_t fun2 ;
    typedef logic fun2type_t;
    fun2 = 0;
  endfunction

  // NCV and VCS say fun3width isn't declared.  So again it seems like the
  // return type is scoped outside the function.
  function logic[fun3width:0] fun3 ;
    parameter fun3width = 1;
    fun3 = 0;
  endfunction
`endif

  // NCV and VCS both accept the following.
  function fun4 ;
    parameter fun4width = 3;
    input [fun4width:0]   in;
    fun4 = in;
  endfunction

`ifdef VL
  // NCV and VCS both reject this, saying fun5width is not declared.
  function fun5 ;
    input [fun5width:0]   in;
    parameter fun5width = 3;
    fun5 = in;
  endfunction
`endif

  // As expected NCV and VCS are fine with this:
  typedef logic task1type_t;
  task task1 (output task1type_t out);
    out = 0;
  endtask

`ifdef VL
  // NCV and VCS reject this, saying that task2type_t isn't defined.
  task task2 (output task2type_t out);
    typedef logic task2type_t;
    out = 0;
  endtask

  // NCV and VCS reject this, saying that task3width isn't defined.
  task task3 (output [task3width:0] out);
    parameter task3width = 3;
    out = 0;
  endtask

`endif

  // NCV and VCS both accept the following
  task task4;
    typedef logic task4type_t;
    output task4type_t out;
    out = 0;
  endtask


  // NCV and VCS reject this, saying that task5type_t isn't defined.
`ifdef VL
  task task5;
    output task5type_t out;
    typedef logic task5type_t;
    out = 0;
  endtask
`endif


  // NCVerilog and VCS both accept this, saying that fun6 of -1 is 15.
  function logic [3:0] fun6 ;
    input [$bits(fun6)-1:0] in;
    fun6 = in;
  endfunction

  // NCVerilog and VCS both accept this, saying that fun7 of -1 is 15.
  function logic [3:0] fun7(input [$bits(fun7)-1:0] in);
    fun7 = in;
  endfunction

  initial begin
    #10;
    $display("fun6 of -1 is %d", fun6(-1));
    $display("fun7 of -1 is %d", fun7(-1));
  end

endmodule


interface i1;

  wire w1_declared = 0;

  // Implicit wires in assignments
  assign a1_implicit = w1_declared;
  assign {a2_implicit,a3_implicit} = 0;
  //+VL  assign top_a1 = a4_undeclared;
  assign a5_implicit = a5_implicit;
  assign {a6_implicit,a7_implicit} = {a7_implicit,a6_implicit};

// need modports in here

endinterface



