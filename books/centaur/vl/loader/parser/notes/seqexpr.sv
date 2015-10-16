


module top ;

  // There is a master clock that is toggling.
  reg clk = 0;
  always #100 clk = ~clk;

  // Here are some delayed versions of the clock.
  wire #10 clk_del = clk;
  wire #20 clk_del20 = clk;

  // Some variables to mess with.
  integer r1 = 0;
  integer r2 = 0;

  // R1 and R2 will update shortly after the clock.  R2 will always be greater
  // than R1, but they start out the same.
  always @(posedge clk_del) r1 <= r1 + 1;
  always @(posedge clk_del) r2 <= r2 + 2;

  initial begin

    $display("Hello");
    // Run for awhile

    #3000;
    r1 = 0;
    r2 = 0;
    #1000;

    // Then something "bad" happens
    r2 = 0;
    #1000;

    $display("Done");

    $finish;
  end


  // Experiments for property versus sequence expressions

  // assert property (@(posedge clk)
  //                    1             // on the first cycle, just check True
  //                    ##1           // then in the next cycle
  //                    r1 < r2       // check that r1 < r2
  //                    ##1           // then on the next cycle
  //                    r2 < r1
  //                    );

  // NCVerilog and VCS both reject this.  NCV says it's a parse error.  VCS says
  // it's a property operator in a sequence context but also sort of appears to
  // have at least parsed it

  // assert property (@(posedge clk)
  //                    1
  //                    ##1
  //                    (not (r1 < r2))
  //                    ##1
  //                    r2 < r1
  //                    );


  // NCV says this fails at times 100, 3100, and 4100.  (why not 4300, 4500, ...?)
  // VCS says it fails at 100, 3100, 4100, 4300, 4500, etc., which makes more sense
  // assert property (@(posedge clk)
  //     (r1 < r2)
  // );


  // NCV says this fails at time 100, 3100, 4100.
  // VCS says this fails at 100, 3100, 4100, 4300, 4500, etc.
  // assert property (@(posedge clk)
  //      not (r2 <= r1)
  // );

  // NCV says this fails at 110, 3110, 4110
  // VCS says this fails at 110, 3110, 4110, 4310, 4510, etc.
  // assert property (@(posedge clk)
  //     ( @(posedge clk_del) r1 < r2 )
  // );

  // NCV says this fails at 110, 3110, 4110
  // VCS says this fails at 110, 3110, 4110, 4310, 4510, etc.
  // assert property (@(posedge clk)
  //      ( @(posedge clk_del) not (r2 <= r1) )
  // );


  // NCV says this fails at 110, 3110, 4110.
  // VCS says this is an error because there isn't a single leading clock
  // assert property (@(posedge clk)
  //      ( @(posedge clk_del) 1'b1 and not (r2 <= r1) )
  // );


  // NCV says this an error because the clock isn't completely specified
  // VCS says this is an error because there isn't a single leading clock.
  // assert property (@(posedge clk)
  //      (  (@(posedge clk_del) 1'b1)
  //             and
  //         (not (r2 <= r1))
  //      )
  // );

  // NCV says this fails at 110, 3110, 4110
  // VCS says this fails at 110, 3110, 4110, 4310.
  // assert property (@(posedge clk)
  //      (  (
  //            @(posedge clk_del)
  //                (1'b1 and not (r2 <= r1))
  //      )  )
  // );

  // Conclusions:
  //  - NCV is treating clocking events as having lower precedence than
  //    AND even for property expressions
  //  - VCS is treating clocking events as having higher precedence than
  //    AND even for property expressions.


  // The lowest precedence operator is allegedly always.  Let's try to
  // come up with an experiment for that.


  // NCV says this fails at 100, 3100, 3100, 4100, 4100, etc.
  // VCS says this is a parse error
  // assert property (@(posedge clk)
  //     always r1 < r2
  // );

  // NCV says this is fine
  // VCS says this is a parse error
  // assert property (@(posedge clk)
  //     always 1'b1
  // );

  // NCV says this fails at 100, 3100, 4100, 4100, 4300, 4500, 4700, 4900
  // assert property (@(posedge clk)
  //     always 1'b1 and r1 < r2
  // );

  // NCV says this fails at 110, 3110, 3110, 4110, 4110, 4310, 4510, ...
  // assert property (@(posedge clk)
  //     @(posedge clk_del) (always 1'b1 and r1 < r2)
  // );

  // NCV says this fails at 110, 3110, 3110, 4110, 4110, 4310, 4510, ...
  // assert property (@(posedge clk)
  //     @(posedge clk_del) always 1'b1 and r1 < r2
  // );

  // NCV says this is an error because the clock isn't completely specified
  // assert property (@(posedge clk)
  //     (@(posedge clk_del) always 1'b1) and r1 < r2
  // );


  // assert property (@(posedge clk)
  //     always (@(posedge clk_del) 1'b1 and r1 < r2)
  // );


  // NOT has higher precedence, so `not r1 until r2` is supposed to be `(not r1) until r2`
  // OK: it looks like NCV gets that correct.

  // assert property (@(posedge clk)
  //     not (r1 until r2)
  // );

  // So what about:  not always r1 until r2
  //  VCS doesn't understand it at all
  //  NCV seems to treat this as:
  //     not always (r1 until r2)
  //  Instead of:
  //     (not always r1) until r2

  // assert property (@(posedge clk)   /// 180
  //     not always r1 until r2
  // );

  // assert property (@(posedge clk)   /// 184
  //     (not always r1) until r2
  // );

  // assert property (@(posedge clk)   // 188
  //     not (always (r1 until r2))
  // );



  assert property (@(posedge clk) // 194
      not not r1 until r2
  );

  assert property (@(posedge clk) // 198
      not (not r1 until r2)
  );

  assert property (@(posedge clk) // 202
      (not not r1) until r2
  );




  



endmodule

