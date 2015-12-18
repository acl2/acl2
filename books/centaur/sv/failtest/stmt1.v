module top (output topout, input topin);


   always_comb
     begin
       logic bar;
       bar <= topin; // nonblocking assignment doesn't make sense for a local variable
     end

endmodule
