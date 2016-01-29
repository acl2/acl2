module top (output integer out, input logic [3:0] in1, input logic [3:0] in2) ;

  function automatic integer foo (input logic [3:0] a, input logic [3:0] b);
    logic [3:0] tmp = b;
    logic [3:0] ans;
    case(a)
      tmp++: ans = 1;  // oops, incrementing during match expression?  seems crazy
      0:     ans = 2;
    endcase
    return ans;
  endfunction

  assign out = foo(in1, in2);

endmodule
