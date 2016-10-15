module top ;

  logic a;

  begin
    wire a;   // oops, conflicts with above declaration of logic a
  end

endmodule
