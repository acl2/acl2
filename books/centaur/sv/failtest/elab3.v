// NCVerilog permits this but VCS does not.

module top ;
   sub #(mysub.f1()) mysub ();

endmodule // top

module sub ();
   parameter p1 = 2;
   parameter p2 = p1 * 2;

   function integer f1 () ;
     f1 = p2;
   endfunction

   initial begin
     #10;
     $display("p1 is %d", p1);
   end

endmodule

