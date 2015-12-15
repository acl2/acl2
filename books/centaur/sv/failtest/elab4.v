// NCV tolerates this and resolves everything to 7.
// VCS also.

module top ;
   sub #(mysub.p2) mysub ();

endmodule // top

module sub ();
   parameter p1 = 2;

   generate
     begin
       localparam p2 = 7;
     end
   endgenerate

   initial begin
     #10;
     $display("p1 is %d, p2 is %d", p1, p2);
   end

endmodule

