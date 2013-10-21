
;; An even simpler version of sum-program.lisp

(ld "pcode.lsp")
(assign sum-simpler
	'(
	  (:node
           :label L_INIT
           :subst t
           :branches ((t . L_280))
	   )

	  (:node
           :label L_280
           :subst (
                   (A . 0)
                   )
           :branches ((t . L_282))
	   )

	  (:node
           :label L_282
           :subst (
                   (C . 0)
                   )
           :branches ((t . L_283))
	   )

	  (:node
           :label L_283
           :subst (
                   (A . (+ A X)) ; A + N
                   )
           :branches ((t . L_286))
	   )

	  (:node
           :label L_286
           :subst (
                   (X . (- X 1))
                   )
           :branches ((t . L_287))
           :post (natp x)
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
           :subst t
           :branches nil
           :post (= (* 2 a) (* nsave (+ 1 nsave)))
           )
          )
        )
