module top (output [3:0] out, input [3:0] a, b);

  // This is possibly OK and is accepted by both NCV and VCS.
  // It is a bit scary though and not necessarily sensible.

  function automatic integer foo (input logic [3:0] a, input logic [3:0] b);
    foo = 0;
    if (a++)     // oops, increment in if condition?
       foo = b;
  endfunction

  assign out = foo(a,b);

endmodule
