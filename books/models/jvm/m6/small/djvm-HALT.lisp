(in-package "ACL2")
(include-book "djvm-model")
(include-book "generic")
(include-book "consistent-state")


(defthm consistent-state-preserved-by-DJVM-HALT
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'HALT)
                (djvm-check-HALT inst st))
           (consistent-state
            (djvm-execute-HALT inst st))))
