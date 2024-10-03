(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "../M6-DJVM-shared/jvm-loader-guard-verification")

;;; Thu Apr 8 22:13:56 2004 CHEAT. IN JVM LOADER I DID SOMETHING SIMILIAR!!

(skip-proofs (verify-guards superClass1-measure))
(skip-proofs (verify-guards isSuperClass1-invariant))
(skip-proofs (verify-guards isSuperClass1))
(skip-proofs (verify-guards isSuperClass))
(skip-proofs (verify-guards unseen-class-count)) 
(skip-proofs (verify-guards classImplements-measure))
(skip-proofs (verify-guards classImplementsInterface1-invariant))
(skip-proofs (verify-guards classImplementsInterface1-aux-invariant))
(skip-proofs (verify-guards interfacesImplementsInterface1-inv))
(skip-proofs (verify-guards simple-inv1))
(skip-proofs (verify-guards implementInterface-x-measure))
(skip-proofs (verify-guards all-loaded?-x))
(skip-proofs (verify-guards implementInterface-x-guard))
(skip-proofs (verify-guards implementInterface-x))
(skip-proofs (verify-guards interfacesImplementsInterface))
(skip-proofs (verify-guards classImplementsInterface))
(skip-proofs (verify-guards isAssignableTo))


    