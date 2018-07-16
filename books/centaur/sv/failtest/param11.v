module sub #(parameter foo [3] = '{0,1,2}) (output [3:0] o);
   assign o = foo[0];
endmodule

module top ;

   logic [3:0] o;
   sub #('{1,2,3}) mysub (o);

   initial begin
      #10;
      $display("o is %d", o);
   end


endmodule
