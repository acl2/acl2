
(ld "pcode.lsp")

(assign new-prog
        `(

; v = u xor 12345
          (:node
           :label L_1
           :subst (
                   (v  . (int_xor u 12345 32))
                   )
           :branches ((t . L_2))
           :post t)

; w = v + 2345345299
          (:node
           :label L_2
           :subst (
                   (w  . (int_add v 2345345299 32))
                   )
           :branches ((t . L_3))
           :post t)

; if w = (u xor 12345) + 2345345299 == 8281919193 then BAD!
          (:node
           :label L_3
           :subst t
           :branches (((= (int_equal w 8281919193 32) 1). L_BAD)
                      ((not (= (int_equal w 8281919193 32) 1)). L_END))
           :post t)
     
; bad program point
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

