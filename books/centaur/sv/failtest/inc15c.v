module top ;

  function automatic integer foo (input integer a);
    begin
      integer b;
      integer c;
      integer d;
      b = a;
      c = a;
      d = (b + c)++; // oops, parse error
      return d;
    end
  endfunction

  integer     i;
  assign out = foo(i);

endmodule

