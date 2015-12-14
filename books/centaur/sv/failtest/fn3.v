
module top ();

  function foo (input a, input foo) ; // oops, input name same as function name
    foo = a;
  endfunction

endmodule

