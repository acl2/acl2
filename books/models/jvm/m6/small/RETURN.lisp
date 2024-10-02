(in-package "ACL2")
(include-book "djvm-model")
(include-book "bcv-simple-model")
(include-book "generic")

(include-book "consistent-state-properties")
(include-book "bcv-method-properties")


;--- EXPORT ----

(encapsulate () 
  (local (include-book "djvm-RETURN"))
  (defthm consistent-state-preserved-by-DJVM-RETURN
    (implies (and (consistent-state st)
                  (equal (next-inst st) inst)
                  (equal (op-code inst) 'RETURN)
                  (djvm-check-RETURN inst st))
             (consistent-state
              (djvm-execute-RETURN inst st)))))


;;(i-am-here) ;; Mon Nov 21 10:57:11 2005



(local (in-theory (disable current-method consistent-state 
                           collect-witness-bcv-method
                           bcv-simple-inst next-inst)))




(local 
 (defthm consistent-caller-frame-implies-frame-size
   (implies (consistent-caller-frame caller callee method-table)
            (<= (+ 1 (len (g 'op-stack caller)))
                (g 'max-stack caller)))
   :hints (("Goal" :in-theory (e/d (consistent-caller-frame)
                                   (bcv-method 
                                    sig-frame-compatible
                                    sig-method-init-frame
                                    collect-witness-bcv-method))))
   :rule-classes :forward-chaining))

(local 
 (defthm consistent-state-implies-consistent-caller-frame-f
   (implies (and (consp (cdr (g 'call-stack st)))
                 (consistent-state st))
            (consistent-caller-frame (cadr (g 'call-stack st))
                                     (car (g 'call-stack st))
                                     (g 'method-table st)))
   :hints (("Goal" :in-theory (e/d (consistent-state) 
                                   (consistent-caller-frame))))
   :rule-classes :forward-chaining))



(defthm bcv-simple-check-return-implies-djvm-check
  (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                (equal (op-code (next-inst djvm-s)) 'RETURN)
                (BCV-SIMPLE-CHECK-RETURN (next-inst djvm-s)
                                         (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                            (G 'METHOD-TABLE DJVM-S))))
           (DJVM-CHECK-RETURN (next-inst djvm-s) djvm-s))
  :hints (("Goal" :in-theory (disable consistent-state consistent-caller-frame))))







