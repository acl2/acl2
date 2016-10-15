module top ;

  parameter version = 1;

  if (version == 1)
  begin : a
    wire b;
  end

  logic  a; // oops, declared above as the name of a generate block

endmodule
