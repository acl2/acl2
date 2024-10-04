(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives")


(skip-proofs (verify-guards wff-call-stack ))
(skip-proofs (verify-guards current-frame-guard ))
(skip-proofs (verify-guards current-frame ))
(skip-proofs (verify-guards current-method-ptr ))
(skip-proofs (verify-guards localx ))
(skip-proofs (verify-guards current-class ))
(skip-proofs (verify-guards alert ))
(skip-proofs (verify-guards push-stack-of-thread ))
(skip-proofs (verify-guards pushStack ))
(skip-proofs (verify-guards popStack-of-thread ))
(skip-proofs (verify-guards popStack ))
(skip-proofs (verify-guards set-local-at-of-thread ))
(skip-proofs (verify-guards state-set-local-at ))
(skip-proofs (verify-guards topStack-guard ))
(skip-proofs (verify-guards topStack ))
(skip-proofs (verify-guards secondStack ))
(skip-proofs (verify-guards pushFrame0 ))
(skip-proofs (verify-guards pushFrame ))
(skip-proofs (verify-guards popFrame ))
(skip-proofs (verify-guards make-method-ptr ))
(skip-proofs (verify-guards wff-method-ptr ))








