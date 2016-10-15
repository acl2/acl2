module top ;

  parameter version = 1;
  parameter mode = 2;
  parameter outer = 1;

  wire [3:0] foo, bar;

  // Implicit variable shouldn't be inferred from assignment RHS

  if (outer == 1)
     if (version == 1)
         if (mode == 2)
	 begin
	   assign foo = a; // oops, a isn't declared
 	 end

endmodule
