
module top (output logic [3:0] out, input logic [3:0] in);

  function integer foo (logic [3:0] w1, logic [3:0] w2);
    w1++ += w2;  // oops, this seems to be a parse error
    return w1;
  endfunction

  assign out = foo(in, 0);

endmodule

