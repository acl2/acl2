
module top ();

  function foo (input a, input a) ; // oops, input have the same name
    foo = a;
  endfunction

endmodule

