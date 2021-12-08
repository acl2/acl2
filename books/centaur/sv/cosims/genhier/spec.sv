// PLACEHOLDER for Intel copyright header




module spec (input logic [127:0] in,
	     output wire [127:0] out);

   genvar 			 i;

   for (i=0; i<8; i++) begin: myloop
      if (i[0]==0) begin: myif
	 logic [2:0] v;
	 assign v = in[(i>>1)*7+:3];
      end else begin: myif
	 logic [3:0] v;
	 assign v = in[(i>>1)*7+3+:4];
      end
   end

   assign out[0+:$bits(myloop[0].myif.v)] = myloop[0].myif.v;
   assign out[0+$bits(myloop[0].myif.v)+:$bits(myloop[1].myif.v)] = myloop[1].myif.v;

endmodule // spec

      
