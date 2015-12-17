module top ;
   sub #(3) mysub ();

endmodule // top

module sub ();
   parameter p1 = 2;

   wire [foo.p2-1:0] a;

   begin : foo
     localparam p2 = 7;
   end

   initial begin
     #10;
     $display("$bits(a) is %d", $bits(a));
   end
endmodule 

