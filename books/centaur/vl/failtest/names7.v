module top (a);

  input a;

  wire 	o, i;

  // Can't have a port named the same as a gate
  buf a (o, i);

endmodule


