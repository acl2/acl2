// VCS and NCV don't allow this.

module top ;
   sub #(mysub.block1.foo) mysub ();  // HID into generate of submodule

endmodule // top

module sub ();
   parameter p1 = 2;

   begin : block1
     localparam foo = 2;
   end

   initial begin
     #10;
     $display("p1 is %d, block1.foo is %d", p1, block1.foo);
   end

endmodule

