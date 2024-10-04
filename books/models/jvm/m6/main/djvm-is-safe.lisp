;------------------------------------------------------
; proof shows that DJVM in fact "safe"
;
; 1. Success in "guard verifing" of the DJVM 
; 2. Execution of DJVM preserves safety
;
;-----------------------------------------------------

(in-package "DJVM")
(include-book "djvm-simple")

;; step functions 
;; note here is the simplified version of the run function!
;;
;; With this approach, we can only show executions that do not create new call
;; frame.


(defthm all-instrs-wff-implies-wff-insts
  (implies (all-instrs-wff insts)
           (wff-insts insts))
  :hints (("Goal" :in-theory (disable wff-inst))))

(local 
 (in-theory (union-theories 
            '(djvm-step
              natp
              zp
              all-instrs-wff-implies-wff-insts
              consistent-state-strong-implies-consistent-state-f
              consistent-state-strong-implies-consistent-state-obj-init-f
              consistent-state-strong-implies-consistent-state-b
              consistent-state-strong-implies-consistent-state-obj-init-b
              consistent-state-strong-implied-by-b
              CONSISTENT-STATE-WFF-STATE
              ANEWARRAY-guard-implies-execute-ANEWARRAY-perserve-consistency
              check-ANEWARRAY-implies-guard-succeeds
              GETFIELD-guard-implies-execute-GETFIELD-perserve-consistency
              check-GETFIELD-implies-guard-succeeds
              ASTORE-guard-implies-execute-ASTORE-perserve-consistency
              check-ASTORE-implies-guard-succeeds
              ALOAD-guard-implies-execute-ALOAD-perserve-consistency
              check-ALOAD-implies-guard-succeeds
              AALOAD-guard-implies-execute-AALOAD-perserve-consistency
              check-AALOAD-implies-guard-succeeds
              AASTORE-guard-implies-execute-AASTORE-perserve-consistency
              check-AASTORE-implies-guard-succeeds
              ACONST_NULL-guard-implies-execute-ACONST_NULL-perserve-consistency
              check-ACONST_NULL-implies-guard-succeeds
              IFEQ-guard-implies-execute-IFEQ-perserve-consistency
              check-IFEQ-implies-guard-succeeds)
            (theory 'minimal-theory))))

;;; this should be generated!! 
;;;
;;; notice this consistency does not assert the execution matches up with 
;;; BCV execution!! 
;;; 

(defthm djvm-step-preserve-consistent-state
  (implies (consistent-state-strong s)
           (consistent-state-strong (djvm-step inst s))))
                 
(local (defthm wff-inst-strong-implies-wff-inst
         (implies (wff-inst-strong inst)
                  (wff-inst inst))
         :hints (("Goal" :in-theory (enable wff-inst-strong)))))

(verify-guards djvm-step)


;;;
;;; this take some time to verify!! 
;;;

;;
;; note need to write program to generate those theorems 
;; or properly define such theories!! 
;;

;----------------------------------------------------------------------

(in-theory (disable djvm-step))

(include-book "djvm-consistent-state-facts")


(defthm consistent-state-strong-implies-next-inst-guard
  (implies (consistent-state-strong jvm::s)
           (AND
            (WFF-STATE JVM::S)
            (CURRENT-FRAME-GUARD JVM::S)
            (WFF-CALL-FRAME (CURRENT-FRAME JVM::S))
            (WFF-METHOD-PTR (CURRENT-METHOD-PTR JVM::S))
            (WFF-CLASS-TABLE (CLASS-TABLE JVM::S))
            (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE JVM::S))
            (WFF-METHOD-DECL
             (DEREF-METHOD (CURRENT-METHOD-PTR JVM::S)
                           (INSTANCE-CLASS-TABLE JVM::S)))
            (WFF-CODE
             (METHOD-CODE
              (DEREF-METHOD (CURRENT-METHOD-PTR JVM::S)
                            (INSTANCE-CLASS-TABLE JVM::S))))
            (WFF-INSTS
             (CODE-INSTRS
              (METHOD-CODE
               (DEREF-METHOD (CURRENT-METHOD-PTR JVM::S)
                             (INSTANCE-CLASS-TABLE JVM::S)))))))
  :hints (("Goal" :in-theory (e/d (consistent-state-strong)
                                  (wff-state 
                                   current-frame-guard
                                   wff-call-frame
                                   wff-method-ptr
                                   current-method-ptr
                                   wff-class-table
                                   wff-instance-class-table
                                   wff-method-decl
                                   wff-code
                                   method-code
                                   code-instrs
                                   wff-insts)))))


;; (skip-proofs 
;;   (defthm consistent-state-strong-implies-wff-inst-next-inst
;;     (IMPLIES (CONSISTENT-STATE-STRONG S)
;;              (WFF-INST (NEXT-INST S)))))



;; ;; ;;;; ^^^^^^^^^^^^^^ 
;; ;; ;;;; this above is difficult!!! 
;; ;; ;;;; We need to assert that consistent-state implies not out of bound!!
;; ;; ;;;; 
;; ;; ;;;; this will obilge us either change the next-inst to always to return
;; ;; ;;;; a wff-inst? 
;; ;; ;;;; ....
;; ;; ;;;;
;; ;; ;;;; Or introduce BCV into the consistent-state itself. 
;; ;; ;;;; 


;;;; this above is not right!! 
;;;; 
;;;; because we don't know that next-inst will be always within bounds!!! 
;;;;
;;;; We can only know that if we know that the consistent-state-strong 
;;;; asserts something more, such as consistent-state-bcv-on-track !!!! 
;;;;
;;;; Even in that case, we need to assert that very first frame
;;;; has a halt instruction for a state to be a consistent-state...  
;;;;

;;;
;;; Just to assert that one can legally invoke (next-inst st)!!! 
;;; and invoke (djvm-step (next-inst st)) 
;;;
;;; note this above skip-proofs is not true!!  because so far, we have not
;;; asserted wff-inst-strong for all instructions that contained in method
;;;
;;; We can only prove this, when we add all method "verified" to
;;; consistent-state
;;; 
;;; Our current BCV does not check assert wff-inst-strong, because it accepts
;;; more instructions!!! 
;;;
;;; Tue Oct 25 15:57:23 2005 As a result I need to write a simpler version of
;;; the BCV that only accept the limit number of instructions!! 
;;; 
;;;
;;; Shall I write a model of the BCV that function like tiny jvm's BCV??? 
;;;
;;; suppose this can be proved. by directly assserting consistent-state that
;;; all instructions in state is ... 
;;;



;; (skip-proofs 
;;    (defthm consistent-state-strong-implies-wff-inst-next-inst
;;      (IMPLIES (and (CONSISTENT-STATE-STRONG S)
;;               (WFF-INST (NEXT-INST S)))))


(defun djvm-simple-run (n s)
  (declare (xargs :guard (and (natp n)
                              (consistent-state-strong s))))
  (if (zp n) s
    (mylet* ((inst (next-inst s))
             (ns   (djvm-step inst s)))
            (if (wff-inst inst)
                (djvm-simple-run (- n 1) ns)
              s))))
            
;----------------------------------------------------------------------

(defthm djvm-simple-run-preserve-consistent-state
  (implies (consistent-state-strong s)
           (consistent-state-strong (djvm-simple-run n s)))
  :hints (("Goal" :in-theory (disable djvm-step consistent-state-strong))))

;----------------------------------------------------------------------

;;
;; (defun djvm-simple-run (n program s)
;;   (declare (xargs :guard (and (natp n)
;;                               (consistent-state-strong s)
;;                               (all-instrs-wff program))))
;;   (if (zp n) s
;;     (mylet* ((inst (inst-by-offset1 (pc s) program))
;;              (ns   (djvm-step inst s)))
;;             (if (wff-inst-strong inst)
;;                 (djvm-simple-run (- n 1) program ns)
;;               s))))
;;      
;; ;----------------------------------------------------------------------
      

;; ;----------------------------------------------------------------------

;; (defthm djvm-simple-run-preserve-consistent-state
;;   (implies (consistent-state-strong s)
;;            (consistent-state-strong (djvm-simple-run n program s))))

;; ;----------------------------------------------------------------------


;; 
;; need to define a djvm-simple-run so that it read the next instruction 
;; from the state!! 






