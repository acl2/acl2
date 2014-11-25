module top ;

  integer a;
  sub mysub (.a(a));

endmodule


module sub (input integer .a());  // invalid syntax, not a valid ansi_port_declaration 

endmodule
