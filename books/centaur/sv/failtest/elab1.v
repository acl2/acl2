module top ;
   sub #(mysub.block1.foo) mysub ();

endmodule // top

module sub ();
   parameter p1 = 2;

   if (p1 == 1) begin : block1
     localparam foo = 2;
   end else begin : block1
     localparam foo = 1;
   end

   initial begin
     #10;
     $display("p1 is %d, block1.foo is %d", p1, block1.foo);
   end

endmodule

