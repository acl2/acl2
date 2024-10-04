(in-package "ACL2")
(include-book "djvm-model")
(include-book "bcv-simple-model")
(include-book "generic")

(include-book "consistent-state-properties")
(include-book "bcv-method-properties")


;--- EXPORT ----

(encapsulate () 
  (local (include-book "djvm-POP"))
  (defthm consistent-state-preserved-by-DJVM-POP
    (implies (and (consistent-state st)
                  (equal (next-inst st) inst)
                  (equal (op-code inst) 'POP)
                  (djvm-check-POP inst st))
             (consistent-state
              (djvm-execute-POP inst st)))))


;;(i-am-here) ;; Mon Nov 21 10:57:11 2005




(defthm bcv-simple-inst-implies-next-pc-bounded-POP
  (implies (and (bcv-simple-inst pc inst sig-vector)
                (equal (g 'pc (cdr (assoc-equal pc sig-vector))) pc)
                (equal (op-code inst) 'POP))
           (assoc-equal (+ 1 pc) sig-vector)))



(local (in-theory (disable collect-witness-bcv-method)))



(defthm bcv-simple-inst-implies-next-pc-bounded-POP-specific
  (implies (and (bcv-simple-inst pc (next-inst st)
                                 (collect-witness-bcv-method 
                                  (current-method st)
                                  (g 'method-table st)))
                (equal (g 'pc (cdr (assoc-equal pc 
                                                (collect-witness-bcv-method 
                                                 (current-method st)
                                                 (g 'method-table st)))))
                       pc)
                (equal (op-code (next-inst st)) 'POP))
           (assoc-equal (+ 1 pc) (collect-witness-bcv-method 
                                  (current-method st)
                                  (g 'method-table st)))))



(local (in-theory (disable current-method consistent-state 
                           collect-witness-bcv-method
                           bcv-simple-inst next-inst)))



(defthm bcv-simple-check-pop-implies-djvm-check
  (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                (equal (op-code (next-inst djvm-s)) 'POP)
                (BCV-SIMPLE-CHECK-POP (next-inst djvm-s)
                                         (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                            (G 'METHOD-TABLE DJVM-S))))
           (DJVM-CHECK-POP (next-inst djvm-s) djvm-s))
  :hints (("Goal" :in-theory (disable consistent-state))))







