module spec (input logic [127:0] in,
	     output logic [127:0] out);

  assign out [127:32] = 0;

  logic [31:0] mask_idx;

   always_comb
     begin
       mask_idx = in[6:0];
       if (mask_idx > 64) begin
	 mask_idx = 64;
       end
     end

   assign out[31:0] = mask_idx;

endmodule
