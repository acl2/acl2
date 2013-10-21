(ld "pcode.lsp")

(assign new-prog2
	'(

    ; v = u xor 12345
    (:node
     :label L_1
     :subst (
      (v  . (int_xor u 12345 32))
      )
     :branches ((t . L_2))
     :post t)

    ; w = v + 7
    (:node
     :label L_2
     :subst (
      (w  . (int_add v 7 32))
      (z  . 10)
      )
     :branches ((t . L_25))
     :post t)

    ; multiply by u^10
    (:node
     :label L_25
     :subst (
      (w  . (int_mult w u 32))
      (z  . (int_sub z 1 32))
      )

     :branches (((= z 0) . L_3)
		((not (= z 0)) . L_25))
     :pre (and (natp z) (<= z 10) (not (= z 0)))
     :post (natp z)
     )

    ; if ((u xor 12345) + 2345345299))*u^10 == 8281919194 then do something bad
    (:node
     :label L_3
     :subst t
     :branches (((= (int_equal w 11 32) 1). L_BAD)  ;; REMEMBER! int_equal returns a number!!!
      ((not (= (int_equal w 11 32) 1)) . L_END))
     :post t)
     
    (:node
     :label L_BAD
     :subst t
     :branches nil 
     :post t)

    ; end of program
    (:node
     :label L_END
     :subst t
     :branches nil
     :post nil
     )
    )

  )

