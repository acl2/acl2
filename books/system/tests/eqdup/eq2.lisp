(in-package "ACL2")
(include-book "eqbase")
(defthm ee-is-an-equivalence-again
  (and (booleanp (ee x y)) (ee x x)
       (implies (ee x y) (ee y x))
       (implies (and (ee x y) (ee y z)) (ee x z)))
  :rule-classes :equivalence)
