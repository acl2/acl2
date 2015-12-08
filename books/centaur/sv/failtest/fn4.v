
module top ();

  function foo (input a) ;
    foo = a;
  endfunction

  function foo (input a) ;  // oops, same name as previous function
    foo = a;
  endfunction

endmodule

