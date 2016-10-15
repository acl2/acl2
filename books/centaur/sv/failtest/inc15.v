module top ;

  // NCV accepts but VCS doesn't tolerate expressions like ~a++.
  //
  // SystemVerilog-2012 Table 11-2 (page 221) says that all of the unary
  // operators have the same precedence and no associativity, so it doesn't
  // give an official ruling on whether this should be OK.
  //
  // But looking at the grammar we find:
  //
  // expression ::= ... | unary_operator {attribute_instance} primary
  //
  // And I think a primary cannot directly be an inc_or_dec_expression, so I
  // don't think it's legal to apply these unary operators to a postincrement,
  // and meanwhile we can't be meaning (~a)++ because ~a isn't an lvalue.

  function automatic integer foo (input integer a);
    begin
      integer b;
      b = ~a++;  // oops, parse error
      return b;
    end
  endfunction

  integer     i;
  assign out = foo(i);

endmodule
