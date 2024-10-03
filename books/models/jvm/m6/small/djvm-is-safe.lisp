(in-package "ACL2")
(include-book "djvm-model")
(include-book "consistent-state")


;----------------------------------------------------------------------


(encapsulate () 
 (local (include-book "djvm-INVOKE"))
 (defthm consistent-state-preserved-by-DJVM-INVOKE
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'INVOKE)
                 (djvm-check-INVOKE (next-inst st) st))
            (consistent-state
             (djvm-execute-INVOKE inst st)))))



(encapsulate () 
  (local (include-book "djvm-PUSH"))
  (defthm consistent-state-preserved-by-DJVM-PUSH
    (implies (and (consistent-state st)
                  (equal (next-inst st) inst)
                  (equal (op-code inst) 'PUSH)
                  (djvm-check-PUSH inst st))
             (consistent-state
              (djvm-execute-PUSH inst st)))))

(encapsulate ()
 (encapsulate () 
  (local (include-book "djvm-IFEQ"))
  (defthm consistent-state-preserved-by-DJVM-IFEQ
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'IFEQ)
                 (djvm-check-IFEQ inst st))
            (consistent-state
             (djvm-execute-IFEQ inst st))))))


(encapsulate ()
  (local (include-book "djvm-HALT"))            
  (defthm consistent-state-preserved-by-DJVM-HALT
    (implies (and (consistent-state st)
                  (equal (next-inst st) inst)
                  (equal (op-code inst) 'HALT)
                  (djvm-check-HALT inst st))
             (consistent-state
              (djvm-execute-HALT inst st)))))


(encapsulate () 
  (local (include-book "djvm-POP"))            
  (defthm consistent-state-preserved-by-DJVM-POP
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'POP)
                 (djvm-check-POP inst st))
            (consistent-state
             (djvm-execute-POP inst st)))))


(encapsulate ()
 (local (include-book "djvm-RETURN"))
 (defthm consistent-state-preserved-by-DJVM-RETURN
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'RETURN)
                 (djvm-check-RETURN inst st))
            (consistent-state
             (djvm-execute-RETURN inst st)))))

(local (in-theory (disable consistent-state
                           next-inst 
                           op-code
                           djvm-check-INVOKE
                           djvm-check-PUSH
                           djvm-check-IFEQ
                           djvm-check-HALT
                           djvm-check-POP
                           djvm-check-RETURN
                           djvm-execute-INVOKE
                           djvm-execute-PUSH
                           djvm-execute-IFEQ
                           djvm-execute-HALT
                           djvm-execute-POP
                           djvm-execute-RETURN)))

(defthm djvm-step-preserve-consistent-state
  (implies (consistent-state st)
           (consistent-state (djvm-step st))))

(local (in-theory (disable djvm-step)))

(defthm consistent-state-implies-opstack-is-in-range
  (implies (consistent-state st)
           (<= (len (g 'op-stack (topx (g 'call-stack st))))
               (g 'max-stack 
                  (current-method st))))
  :hints (("Goal" :in-theory (enable consistent-state))))


(local (in-theory (disable current-method topx)))


;----------------------------------------------------------------------


(defthm djvm-run-preserve-consistent-state
  (implies (consistent-state st)
           (consistent-state (djvm-run st any))))


;----------------------------------------------------------------------

(local (in-theory (disable djvm-run current-method topx)))

(local 
 (defthm verified-program-never-overflow-operand-stack-lemma
   (implies (consistent-state st)
            (<= (len (g 'op-stack (topx (g 'call-stack (djvm-run st n)))))
                (max-stack (current-method (djvm-run st n)))))))

;; in fact, we may still want to show that method-table does not change!! 
;; depend on whether people thing that this is straight forward! 

;; and current-method look up the current executing method in the original
;; method table


(defthm popStack-n-does-not-change-method-table
  (equal (g 'method-table (popStack-n st n))
         (g 'method-table st)))

(defthm method-table-does-not-change
  (equal (g 'method-table (djvm-step st))
         (g 'method-table st))
  :hints (("Goal" :in-theory (enable djvm-step
                                     djvm-execute-INVOKE
                                     djvm-execute-PUSH
                                     djvm-execute-IFEQ
                                     djvm-execute-POP
                                     djvm-execute-HALT
                                     djvm-execute-RETURN))))

;;
;; in more complicated cases, we will prove this above as a properties of
;; individual 
;;
;;   execute-XXXX
;;

(defthm method-table-does-not-change-m-run
  (equal (g 'method-table (djvm-run st n))
         (g 'method-table st))
  :hints (("Goal" :in-theory (enable djvm-run))))


(defthm verified-program-never-overflow-operand-stack-in-djvm
   (implies (and (consistent-state st)
                 (all-method-verified (g 'method-table st)))
            (<= (len (g 'op-stack (topx (g 'call-stack (djvm-run st n)))))
                (max-stack (binding (g 'method-name 
                                       (topx (g 'call-stack (djvm-run st n))))
                                    (g 'method-table st)))))
   :hints (("Goal" :use verified-program-never-overflow-operand-stack-lemma
            :in-theory (e/d (current-method)
                            (verified-program-never-overflow-operand-stack-lemma)))))

;----------------------------------------------------------------------
