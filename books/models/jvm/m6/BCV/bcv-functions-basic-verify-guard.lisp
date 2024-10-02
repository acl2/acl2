(in-package "BCV")

(include-book "bcv-functions-basic")

(skip-proofs (verify-guards make-static-class-decl))
(skip-proofs (verify-guards classClassName))
(skip-proofs (verify-guards classSuperClassName))
(skip-proofs (verify-guards classConstantPool))
(skip-proofs (verify-guards classFields))
(skip-proofs (verify-guards classMethods))
(skip-proofs (verify-guards classInterfaces))
(skip-proofs (verify-guards classAccessFlags))
;; (skip-proofs (verify-guards classAttributes))
;; We decide to not deal with classAttributes ;; 
;; Wed Jul 13 15:05:36 2005


(skip-proofs (verify-guards make-static-class-decl))
(skip-proofs (verify-guards wff-scl-decl-guard-weak))

(skip-proofs (verify-guards CLASSNAME-S))
(skip-proofs (verify-guards SUPER-S))
(skip-proofs (verify-guards  CONSTANTPOOL-S))
(skip-proofs (verify-guards  INTERFACES-S))
(skip-proofs (verify-guards  FIELDS-S))
(skip-proofs (verify-guards  METHODS-S))
(skip-proofs (verify-guards  ACCESSFLAGS-S))
(skip-proofs (verify-guards  ATTRIBUTES-S))
(skip-proofs (verify-guards MAKE-CLASS-TERM))


(skip-proofs (verify-guards make-class-def))
(skip-proofs (verify-guards scl-decl-bcv2jvm))
(skip-proofs (verify-guards scl-bcv2jvm))
(skip-proofs (verify-guards scl-jvm2bcv))

(skip-proofs (verify-guards class-by-name))
(skip-proofs (verify-guards isClassTerm))
(skip-proofs (verify-guards good-scl))

