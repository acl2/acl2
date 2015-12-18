// NCV says mysub.p2 is illegal
// VCS doesn't like using mysub.p2

module top ;
   sub #(mysub.p2) mysub ();

endmodule // top

module sub ();
   parameter p1 = 2;

   generate
     if (1) begin
       localparam p2 = 7;
     end
   endgenerate

   initial begin
     #10;
     $display("p1 is %d, p2 is %d", p1, p2);
   end

endmodule

