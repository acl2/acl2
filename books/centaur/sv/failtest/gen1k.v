module top ;

  logic a;
  parameter version = 1;

  case (version)
    1: begin
          wire b;
       end

    default: begin : a // oops, previously declared as "logic a"
               wire c;
             end

  endcase

endmodule
