
module top ();

  function foo (input a) ;
  begin
    b = a;                  // oops, b not declared
    foo = b;
  end
  endfunction

endmodule
