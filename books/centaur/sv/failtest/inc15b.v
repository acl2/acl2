module top ;

  // Neither NCV nor VCS tolerates ++a++.  This shouldn't be legal
  // because (++a) isn't a valid lvalue.

  function automatic integer foo (input integer a);
    begin
      integer b;
      b = ++a++;  // oops, parse error
      return b;
    end
  endfunction

  integer     i;
  assign out = foo(i);

endmodule

