module sub #(parameter [3:0] foo [3] = 3) (output [3:0] o);
   assign o = foo[0];
endmodule

module top ;

   logic [3:0] o;
   sub #('{0,1,2}) mysub (o);

   initial begin
      #10;
      $display("o is %d", o);
   end


endmodule
