module top ;

  begin
    wire a;
  end

  logic a; // oops, conflicts with above declaration of wire a

endmodule
