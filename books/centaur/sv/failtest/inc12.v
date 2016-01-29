module top ;


  for(genvar i = 0; i < 5; ++i)
  begin : foo
    function automatic integer foofn () ;
      return i;
    endfunction
  end

  logic clk;

  always @(posedge clk)
  begin
    integer j;
    integer ans;

    j = 0;
    for(integer i = 0; i < 5; ++i)
    begin
      ans += foo[j++].foofn();
    end
  end



endmodule
