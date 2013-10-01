(ld "pcode.lsp")

(assign false-prog
	'(
	  (:node
           :label L_INIT
           :subst t
           :branches ((t . L_280))
           :post nil
	   )

	  (:node
           :label L_280
           :subst (
                   (A . (COPY 0))
                   )
           :branches ((t . L_282))
           :post nil
	   )

	  (:node
           :label L_282
           :subst (
                   (C . (COPY 0))
                   )
           :branches ((t . L_283))
           :post nil
	   )

	  (:node
           :label L_283
           :subst (
                   (A . (int_add A X 32)) ; A + N
                   )
           :branches ((t . L_286))
           :post nil
	   )

	  (:node
           :label L_286
           :subst (
                   (X . (- X 1))
                   )
           :branches ((t . L_287))
           :post nil
	   )
	  (:node
           :label L_287
           :subst (
                   (Z . (= X 0))
                   )
           :branches (
                      ((not Z) . L_283)
                      (Z . L_291)
                      )
           :post nil
           )
	  (:node
           :label L_291
           :subst t
           :branches nil
           :post nil
	   )
	  )
	)
