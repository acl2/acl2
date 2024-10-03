(in-package "ACL2")
(include-book "bcv-simple-model")
(include-book "djvm-model")

;;;
;;; note the following is not true!! 
;;;

(local 
 (in-theory (disable bcv-simple-check-INVOKE 
                    bcv-simple-check-POP
                    bcv-simple-check-PUSH
                    bcv-simple-check-RETURN
                    bcv-simple-check-IFEQ
                    djvm-check-INVOKE
                    djvm-check-POP
                    djvm-check-PUSH
                    djvm-check-RETURN
                    djvm-check-IFEQ)))


(local 
 (in-theory (disable consistent-state next-inst
                     extract-sig-frame)))
                    

;; (defthm bcv-simple-check-implies-djvm-check-lemma
;;   (implies (and (consistent-state djvm-s)
;;                 (equal (car (g 'call-stack st)) sig-frame)
;;                 (bcv-simple-check-step-pre 
;;                  inst (extract-sig-frame sig-frame 
;;                                          method-table))
;;            (djvm-check-step-g inst djvm-s)))

(encapsulate () 
  (local (include-book "INVOKE"))
  (defthm bcv-simple-check-invoke-implies-djvm-check
    (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                  (equal (op-code (next-inst djvm-s)) 'INVOKE)
                  (BCV-SIMPLE-CHECK-INVOKE (next-inst djvm-s)
                                           (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                              (G 'METHOD-TABLE DJVM-S))))
             (DJVM-CHECK-INVOKE (next-inst djvm-s) djvm-s))))


(encapsulate () 
  (local (include-book "PUSH"))
  (defthm bcv-simple-check-push-implies-djvm-check
    (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                  (equal (op-code (next-inst djvm-s)) 'PUSH)
                  (BCV-SIMPLE-CHECK-PUSH (next-inst djvm-s)
                                         (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                            (G 'METHOD-TABLE DJVM-S))))
             (DJVM-CHECK-PUSH (next-inst djvm-s) djvm-s))))



(encapsulate () 
  (local (include-book "POP"))
  (defthm bcv-simple-check-pop-implies-djvm-check
  (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                (equal (op-code (next-inst djvm-s)) 'POP)
                (BCV-SIMPLE-CHECK-POP (next-inst djvm-s)
                                         (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                            (G 'METHOD-TABLE DJVM-S))))
           (DJVM-CHECK-POP (next-inst djvm-s) djvm-s))))


(encapsulate () 
  (local (include-book "IFEQ"))
  (defthm bcv-simple-check-ifeq-implies-djvm-check
    (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                  (equal (op-code (next-inst djvm-s)) 'IFEQ)
                  (BCV-SIMPLE-CHECK-IFEQ (next-inst djvm-s)
                                         (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                            (G 'METHOD-TABLE DJVM-S))))
             (DJVM-CHECK-IFEQ (next-inst djvm-s) djvm-s))))



(encapsulate () 
  (local (include-book "RETURN"))
  (defthm bcv-simple-check-return-implies-djvm-check
    (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                  (equal (op-code (next-inst djvm-s)) 'RETURN)
                  (BCV-SIMPLE-CHECK-RETURN (next-inst djvm-s)
                                           (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                              (G 'METHOD-TABLE DJVM-S))))
             (DJVM-CHECK-RETURN (next-inst djvm-s) djvm-s))))




(encapsulate () 
  (local (include-book "HALT"))
  (defthm consistent-state-preserved-by-HALT
    (implies (and (consistent-state st)
                  (equal (next-inst st) inst)
                  (equal (op-code inst) 'HALT))
             (consistent-state
              (execute-HALT inst st)))))



(defthm bcv-simple-check-implies-djvm-check
  (implies (and (consistent-state djvm-s)
                (bcv-simple-check-step-pre (next-inst djvm-s) 
                                           (extract-sig-frame
                                            (TOPX (G 'CALL-STACK DJVM-S))
                                            (G 'METHOD-TABLE DJVM-S))))
           (djvm-check-step djvm-s)))

