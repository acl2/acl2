
module top ();

  function foo (input a) ;
    foo = a;
  endfunction

  function foo (input a, input b) ; // oops, same name as previous function
    foo = a & b;
  endfunction

endmodule

