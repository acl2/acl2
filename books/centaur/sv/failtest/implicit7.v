module top ;

  parameter version = 1;
  parameter mode = 2;
  parameter outer = 1;

  wire [3:0] foo, bar;

  // Implicit variable shouldn't be inferred from assignment RHS
  assign foo = a;

endmodule
