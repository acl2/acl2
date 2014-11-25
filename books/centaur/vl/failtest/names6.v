// can't have ports with the same external names.

module top (.a(), .a(b));

  input b;

endmodule


