(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-bytecode")

;; (skip-proofs (verify-guards inst-by-offset1))
;; (skip-proofs (verify-guards inst-by-offset))
;; (skip-proofs (verify-guards next-inst ))
;; (skip-proofs (verify-guards arg ))
;; (skip-proofs (verify-guards wff-one-arg ))
;; (skip-proofs (verify-guards local-at ))
;; (skip-proofs (verify-guards inst-size ))
;; (skip-proofs (verify-guards field-size))
;; (skip-proofs (verify-guards fatalSlotError))

(verify-guards inst-by-offset1)
(verify-guards inst-by-offset)
(verify-guards next-inst )
(verify-guards arg )
(verify-guards wff-one-arg )
(verify-guards local-at )
(verify-guards inst-size )
(verify-guards field-size)
(verify-guards fatalSlotError)

;; should all be redundant!! 