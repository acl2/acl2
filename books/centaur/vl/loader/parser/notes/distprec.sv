// Investigation into the dist operator.
//
// The dist operator in SystemVerilog-2012 is very confusingly mentioned in the
// operator precedence table (Table 11-2, Page 221).  However, per the grammar
// rules it appears that it only occurs within
//
//    expression_or_dist ::= expression [ 'dist' { dist_list } ]
//
// which usually occurs within parens or with a semicolon after it, but can
// also occur in a comma delimited list within a propery case item, or followed
// by a boolean_abbrev or 'throughout' in a sequence_expr.  But at any rate, an
// expression_or_dist definitely does not occur within an ordinary expression.
// So how does it make any sense for 'dist' to have a precedence?

// People on the Internet have discussed this but the discussion seems to mostly
// be talking past each other.
//    http://www.eda.org/sv-ec/hm/8433.html
//
// Well, let's try to figure out what NCVerilog and VCS do at least.

// Theory 1: Maybe dist really is supposed to be an operator that you can use
// everywhere.  But NCV and VCS both reject the following:
//
// $display("Temp is %d", dist { 3 := 1, 4 := 2 })
// $display("Temp is %d", foo dist { 3 := 1, 4 := 2 })
// $display("Temp is %d", (1 + foo dist { 3 := 1, 4 := 2 }))
//
// So that seems like fairly strong evidence that this is not a real operator.

// Theory 2. Maybe the inclusion of dist into the precedence table is just
// bogus and really dist is something outside of expresions.  The following
// tests explore this theory:

class testclass;

  rand bit [7:0] foo;

  // The following works on both NCVerilog and VCS.

  // constraint foo_range {
  //   foo inside {3, 4, 5};
  // }

  // The following also works on both NCVerilog and VCS.

  // constraint foo_range {
  //   foo dist { 3 := 1, 4 := 2, 5 := 1 };
  // }

  // The following works on both VCS and NCV.  Note that inside/dist are both
  // said to be lower precedence than +.

  // constraint foo_range {
  //   foo + 1 inside {3, 4, 5};
  // }


  // So how about &, which is lower precedence than inside/dist.  Here we
  // find a difference:
  //
  // VCS gives us constraint solver failures, which explicitly show the
  // precedence of the expression they are solving!!!
  //
  //=======================================================
  // Solver failed when solving following set of constraints
  //
  // rand bit[7:0] foo; // rand_mode = ON
  // constraint foo_range    // (from this) (constraint_mode = ON) (distprec.sv:57)
  // {
  //    (foo & (8'hFF inside {3, 4, 5}));
  // }
  // =======================================================
  //
  // NCVerilog happily accepts the syntax but then seems to produce completely
  // random crap for foo.

  // constraint foo_range {
  //   foo & 8'hFF inside {3, 4, 5};
  // }

  // In contrast, when we put explicit parens around the AND, we seem to get
  // the proper behavior out of both VCS and NCVerilog.  So I think the
  // takeaway is that we can expect NCVerilog to produce crap when given a
  // constraint it can't solve, and for VCS to produce warnings.

  // constraint foo_range {
  //   (foo & 8'hFF) inside {3, 4, 5};
  // }

  // So that's how an inside operator works.  How about with DIST.  For the
  // following, NCV and VCS both seem to work correctly as you'd expect.

  // constraint foo_range {
  //   foo + 1 dist { 3 := 1, 4 := 2, 5 := 1 };
  // }

  // However, interestingly, for the following, NCV and VCS both appear to
  // work and correctly produce values in the range of 3-5.  That seems to
  // me to rather strongly that dist is NOT being treated like a normal
  // inside-precedence operator.

  // constraint foo_range {
  //   foo & 8'hFF dist { 3 := 1, 4 := 2, 5 := 1 };
  // }

  // So let's try it with explicit parens.  Again NCV and VCS both seem to be
  // "correctly" producing values in 3-5, so that seems like more evidence the
  // concept of dist's precedence being the same as inside is bogus.

  // constraint foo_range {
  //   (foo & 8'hFF) dist { 3 := 1, 4 := 2, 5 := 1 };
  // }

  // What if we try to put in explicit parens around the dist part?  I think
  // this isn't even valid syntax.  Unfortunately, this somehow seems to work
  // on NCVerilog, with values of foo ending up between 3 and 5.  For VCS, we
  // get an error message that says this feature is not yet supported.

  // constraint foo_range {
  //   foo & (8'hFF dist { 3 := 1, 4 := 2, 5 := 1 });
  // }

  // Let's try something crazier.  VCS and NCVerilog both give parse errors
  // here and suggest that the +1 is not allowed.  Same thing if we add
  // explicit parens.

  // constraint foo_range {
  //   foo dist { 3 := 1, 4 := 2, 5 := 1 } + 1;
  // }

  // constraint foo_range {
  //   (foo dist { 3 := 1, 4 := 2, 5 := 1 }) + 1;
  // }

  // Very strangely, NCVerilog tolerates the following and seems to provide
  // values of foo between 2 and 4.  Meanwhile VCS complains that this is a
  // parse error.

  // constraint foo_range {
  //   1 + (foo dist { 3 := 1, 4 := 2, 5 := 1 });
  // }


  // One last thing I want to try before giving up on this.  Aha, this is
  // really nice!!!

  // constraint foo_range {
  //   foo | 8'hFF dist { 3 := 1, 4 := 2, 5 := 1 };
  // }

  //
  // NCVerilog fails to solve constraints and reports the following
  // error:
  //
  //   ncsim: *W,RNDOCS: These constraints contribute to the set of conflicting constraints:
  //
  //     foo | 8'hFF dist { 3 := 1, 4 := 2, 5 := 1 }; (./distprec.sv,141)
  //
  // VCS also fails to solve them and reports the follwoing error:
  //
  //   Solver failed when solving following set of constraints
  //
  //   rand bit[7:0] foo; // rand_mode = ON
  //   constraint foo_range    // (from this) (constraint_mode = ON) (distprec.sv:140)
  //   {
  //      ((foo | 8'hFF) dist {3 := 1, 4 := 2, 5 := 1});
  //   }
  //
  // So we can see in the VCS error message in particular that it has grouped
  // up the (foo | 8'hFF) together at a higher precedence than the dist, even
  // though | is listed in the table underneath the dist.  Meanwhile suppose
  // we put explicit parens in:

  constraint foo_range {
    (foo | 8'hFF) dist { 3 := 1, 4 := 2, 5 := 1 };
  }

  // Then we get identical error messages except that NCVerilog prints explicit
  // parens around the (foo | 8'hFF).

  // At any rate I think my official ruling is that dist is not a real operator
  // and that the idea that it has a precedence is crazy.

endclass

module top ;

  logic [7:0] foo;

  initial begin
    $display("Hello, world!");



    for(int i = 0;i < 30; ++i)
    begin
      testclass t1 = new;
      t1.randomize();
      #10;
      $display("T1.foo is %d", t1.foo);
    end

  end

endmodule


