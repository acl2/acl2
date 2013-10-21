(ld "pcode.lsp")

(assign sum-simple
	'(
	  (:node
           :label L_INIT
           :subst t
           :branches ((t . L_280))
           )

	  (:node
           :label L_280
           :subst (
                   (A . (COPY 0))
                   )
           :branches ((t . L_282))
           )

	  (:node
           :label L_282
           :subst (
                   (C . (COPY 0))
                   )
           :branches ((t . L_283))
           )

	  (:node
           :label L_283
           :subst (
                   (A . (int_add A X 32)) ; A + N
                   )
           :branches ((t . L_286))
           )

	  (:node
           :label L_286
           :subst (
                   (X . (int_sub X 1 32))
                   )
           :branches ((t . L_287))
           :pre (and (natp x)  (< x (expt 2 32)) (not (= x 0)))
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
           )
	  (:node
           :label L_291
           :subst  t
           :branches  nil
           :post  (= (* 2 a) (* nsave (+ 1 nsave)))
           )
          )
  )
