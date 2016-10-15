module top ;

  logic a;
  parameter version = 1;

  begin : a // oops, previously declared as "logic a"
    wire b;
  end

endmodule
