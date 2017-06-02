

module counter (input clk,
		input reset,
		input incr,
		output logic [3:0] count);
   
   always @(posedge clk) begin
     automatic logic [3:0] tmpcount = count;
     if (reset) begin
       tmpcount = 0;
     end else begin
       tmpcount = tmpcount + incr;
     end
     if (tmpcount == 10)
       tmpcount = 0;
     count <= tmpcount;
   end

endmodule
