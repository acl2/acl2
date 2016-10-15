// NCVerilog rejects this.

// VCS accepts it but says it is ignoring the second declaration of i.
// But that's really weird and strange, and it seems much cleaner to
// follow NCVerilog's approach and say you just can't do this.

module top ;

  wire [3:0] i;
  genvar      i;   // oops, redeclaring i

endmodule
