(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-exceptions")
(include-book "../M6-DJVM-shared/jvm-thread-primitives-guard-verification")
(include-book "../M6-DJVM-shared/jvm-object-type-hierachy-guard-verification")
(include-book "../M6-DJVM-shared/jvm-monitor-primitives-guard-verification")
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives-guard-verification")
(include-book "../M6-DJVM-shared/jvm-linker-guard-verification")
;;; similarly in jvm-thread-primitives-guard-verification.lisp
;; CHEAT!!
(skip-proofs (verify-guards JavaString-to-ACL2-str))
(skip-proofs (verify-guards throw-exception2))
(skip-proofs (verify-guards find-handler))
(skip-proofs (verify-guards getExceptionMessage))
(skip-proofs (verify-guards monitorExit))
(skip-proofs (verify-guards call-stack-depth))
(skip-proofs (verify-guards locked-stage))
(skip-proofs (verify-guards exception-measure))
(skip-proofs (verify-guards invariant-exception-handling-1))
(skip-proofs (verify-guards invariant-exception-handling-2))
(skip-proofs (verify-guards release-lock-invariant))
(skip-proofs (verify-guards release-lock-on-sync-obj))
(skip-proofs (verify-guards throw-exception1))
(skip-proofs (verify-guards throw-exception))
(skip-proofs (verify-guards raise-exception1))
(skip-proofs (verify-guards raise-exception))


;;; Thu Apr  8 21:39:53 2004. Note these operations has a guard 



















