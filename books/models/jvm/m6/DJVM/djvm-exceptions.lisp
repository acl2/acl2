(in-package "DJVM")
(include-book "../M6-DJVM-shared/jvm-exceptions")
(include-book "../M6-DJVM-shared/jvm-exceptions-guard-verification")

(defun fix-exception-reference (s)
  (pushStack (cons 'REF (topStack s))
             (popStack s)))

(skip-proofs (verify-guards fix-exception-reference))


(defun raise-exception (any s)
  (fix-exception-reference (jvm::raise-exception any s)))


(skip-proofs (verify-guards raise-exception))

(in-theory (disable raise-exception))