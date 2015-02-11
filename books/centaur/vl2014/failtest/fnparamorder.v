
module top ();
   
   sub #(.width(4)) mysub ();

endmodule

module sub () ;

   parameter width = 4;

   function [3:0] f1 (input i) ;
     reg r1;
     reg [width-1:0] r2;   // horrifying -- width from outer scope used here
     parameter width = 3;  // but width from inner scope declared here...
     begin
       r1 = i;
       r2 = r1;
       f1 = r2;
     end
   endfunction

endmodule
