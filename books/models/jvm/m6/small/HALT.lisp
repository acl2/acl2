(in-package "ACL2")
(include-book "jvm-model")
(include-book "generic")
(include-book "consistent-state")


(defthm consistent-state-preserved-by-HALT
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'HALT))
           (consistent-state
            (execute-HALT inst st))))
