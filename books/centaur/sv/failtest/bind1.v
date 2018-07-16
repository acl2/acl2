module sub1 ;
endmodule

module sub2 ;
   initial $display("Hello from %m");
endmodule

module top (input a);

   parameter SIZE=1;

   if (SIZE==1) begin
      sub1 mysub1 ();
   end

   bind mysub1 sub2 mysub2 ();

endmodule
