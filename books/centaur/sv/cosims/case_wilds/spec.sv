module spec (input wire  [127:0] in,
	     output wire [127:0] out);


   wire a = in[0];
   reg[127:0] tmp;

   always @* begin
      case ({a})
	1'b0: tmp[0] = 1;
	default: tmp[0] = 0;
      endcase // case ({a})

      case ({a})
	1'b1: tmp[1] = 1;
	default: tmp[1] = 0;
      endcase // case ({a})

      case ({a})
	1'bx: tmp[2] = 1;
	default: tmp[2] = 0;
      endcase // case ({a})

      case ({a})
	1'bz: tmp[3] = 1;
	default: tmp[3] = 0;
      endcase // case ({a})

      case ({a})
	1'b?: tmp[4] = 1;
	default: tmp[4] = 0;
      endcase // case ({a})

      casex ({a})
	1'b0: tmp[10] = 1;
	default: tmp[10] = 0;
      endcase // casex ({a})

      casex ({a})
	1'b1: tmp[11] = 1;
	default: tmp[11] = 0;
      endcase // casex ({a})

      casex ({a})
	1'bx: tmp[12] = 1;
	default: tmp[12] = 0;
      endcase // casex ({a})

      casex ({a})
	1'bz: tmp[13] = 1;
	default: tmp[13] = 0;
      endcase // casex ({a})

      casex ({a})
	1'b?: tmp[14] = 1;
	default: tmp[14] = 0;
      endcase // casex ({a})

      casez ({a})
	1'b0: tmp[20] = 1;
	default: tmp[20] = 0;
      endcase // casez ({a})

      casez ({a})
	1'b1: tmp[21] = 1;
	default: tmp[21] = 0;
      endcase // casez ({a})

      casez ({a})
	1'bx: tmp[22] = 1;
	default: tmp[22] = 0;
      endcase // casez ({a})

      casez ({a})
	1'bz: tmp[23] = 1;
	default: tmp[23] = 0;
      endcase // casez ({a})

      casez ({a})
	1'b?: tmp[24] = 1;
	default: tmp[24] = 0;
      endcase // casez ({a})
   end

   assign out = tmp;


endmodule // spec

