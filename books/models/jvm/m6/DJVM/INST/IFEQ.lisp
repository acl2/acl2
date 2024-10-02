(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-extra")


(acl2::set-verify-guards-eagerness 2)
;----------------------------------------------------------------------

(include-book "base-branch-instrs")

(defun wff-IFEQ (inst)
  (and (wff-one-arg inst)
       (integerp (arg inst))))


;----------------------------------------------------------------------

(include-book "base-skip-proofs2")

;----------------------------------------------------------------------

(defun IFEQ-guard (inst s)
  (and (consistent-state-strong s)
       (wff-IFEQ inst)
       (not (mem '*native* (method-accessflags (current-method s))))
       (topStack-guard-strong s)
       (INT32p (value-of (topStack s)))
       (branch-target-exists (arg inst) (method-code (current-method s)))))

;----------------------------------------------------------------------

(defun execute-IFEQ (inst s)
  (declare (xargs :guard (IFEQ-guard inst s)))
  (BRANCHIF (= (value-of (topStack s)) 0)))

;----------------------------------------------------------------------

(defun check-IFEQ (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((cframe (current-frame s))
           (npc  (arg inst)))
          (and (wff-IFEQ inst)
               (topStack-guard-strong s)
               (equal (djvm-translate-int-type (tag-of (topStack s))) 'INT)
               (branch-target-exists npc
                                     (method-code (current-method s))))))

;----------------------------------------------------------------------

(defthm branch-target-found-implies-integerp
  (implies (and (branch-target-exists npc insts)
                (wff-insts insts))
           (integerp npc))
  :rule-classes :forward-chaining)
                 

(defthm consistent-state-not-method-native-topstackguard-implies-wff-instrs-f
  (implies (consistent-state s)
           (wff-insts (method-code (current-method s))))
  :rule-classes :forward-chaining)

               
(defthm IFEQ-guard-implies-execute-IFEQ-perserve-consistency
  (implies (IFEQ-guard inst s)
           (consistent-state-strong (execute-IFEQ inst s))))

;----------------------------------------------------------------------

;;
;; note our consistent-state does not assert that next instruction is within
;; bound!! 
;;
;; We may need to eventually add that assertion!! 
;; especially when we talk about invoke etc.
;; We do have an assertion about consistent-call-linkage!! 
;; 

(defthm check-IFEQ-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
               (check-IFEQ inst s))
          (IFEQ-guard inst s)))

       
;----------------------------------------------------------------------
;;; need proofs 

;;(i-am-here) ;; Thu Jul 28 02:11:41 2005

(encapsulate ()
 (local (include-book "base-bcv"))

 (local 
  (defthm bcv-target-is-safe-implies-in-range
    (implies (and (bcv::targetistypesafe (env-sig s)
                                         anyframe 
                                         offset)
                  (wff-insts (method-code (current-method s))))
             (branch-target-exists offset (method-code (current-method s))))))
 ;;
 ;; this theorem is not necessary here!! 
 ;;

 (local 
  (in-theory (disable bcv::targetistypesafe branch-target-exists current-method)))
                      
 ;; to be moved into base-bcv!!

  (defthm bcv-check-IFEQ-ensures-djvm-check-IFEQ
    (implies (and (bcv::check-IFEQ inst (env-sig s) 
                                   (frame-sig  (current-frame s)
                                               (instance-class-table s)
                                               (heap s)
                                               (heap-init-map (aux s))))
                  (wff-IFEQ inst)
                  (not (mem '*native* (method-accessflags (current-method s))))
                  (consistent-state s))
             (djvm::check-IFEQ inst s))
    :hints (("Goal" :in-theory (disable bcv::targetistypesafe 
                                        branch-target-exists
                                        current-method env-sig
                                        method-code
                                        wff-inst)))))


;----------------------------------------------------------------------


;;(i-am-here) ;; Thu Jul 28 01:49:19 2005

;-- BCV::check-IFEQ monotonic   -------------------------------------

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate () 
  (local (include-book "base-bcv-check-monotonic"))

   (defthm sig-check-IFEQ-on-more-general-implies-more-specific
     (implies (and (bcv::check-IFEQ inst env1 gframe)
                   (equal (bcv::classtableEnvironment env1) scl)
                   (bcv::icl-scl-compatible icl scl)
                   (bcv::good-icl icl)
                   (bcv::good-scl scl)
                   (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                   (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                   (bcv::consistent-sig-stack (bcv::frameStack 
                                               (bcv::STACKFRAMEATOFFSET env1
                                                                        (bcv::arg1 inst)))icl)
                   (bcv::consistent-sig-locals (bcv::frameLocals gframe) icl)
                   (bcv::consistent-sig-locals (bcv::frameLocals sframe) icl)
                   (bcv::consistent-sig-locals (bcv::frameLocals 
                                                (bcv::STACKFRAMEATOFFSET env1
                                                                         (bcv::arg1 inst))) icl)
                   (bcv::sig-frame-more-general gframe sframe env1))
              (bcv::check-IFEQ inst env1 sframe))))
      

;;;
;;; showing the next step is monotonic is more difficult!! 

;----------------------------------------------------------------------


;-- BCV::execute-IFEQ next step  monotonic ---------------------------

(encapsulate ()
  (local (include-book "base-bcv-step-monotonic"))

  (defthm IFEQ-monotonicity
   (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                (bcv::check-IFEQ inst env1 gframe) 
                (bcv::check-IFEQ inst env1 sframe))
           (bcv::sig-frame-more-general 
            (bcv::normal-frame (bcv::execute-IFEQ inst env gframe))
            (bcv::normal-frame (bcv::execute-IFEQ inst env sframe)) env1))))


;----------------------------------------------------------------------


(encapsulate ()
    (local (include-book "base-frame-sig-expansion"))   
    (defthm execute-IFEQ-frame-sig-is
      (mylet* ((ns (execute-IFEQ inst s)))
       (implies 
        (and (consistent-state s)
             (check-IFEQ inst s))
        (equal (frame-sig (current-frame ns)
                          (instance-class-table ns)
                          (heap ns)
                          (heap-init-map (aux ns)))
               (frame-sig (current-frame (popStack s))
                          (instance-class-table s)
                          (heap s)
                          (heap-init-map (aux s))))))))
                                                  


(encapsulate ()
  (local (include-book "base-bcv-frame-sig-expansion"))
  (defthm bcv-execute-IFEQ-is
    (implies (and (consistent-state s)
                  (check-IFEQ inst s)
                  (bcv::check-IFEQ inst (env-sig s) 
                                    (frame-sig (current-frame s)
                                               (instance-class-table s)
                                               (heap s)
                                               (heap-init-map (aux s)))))
             (equal (car (bcv::execute-IFEQ
                          inst (env-sig s) 
                          (frame-sig (current-frame s)
                                     (instance-class-table s)
                                     (heap s)
                                     (heap-init-map (aux s)))))
                    (frame-sig (current-frame (popStack s))
                               (instance-class-table s)
                               (heap s)
                               (heap-init-map (aux s)))))))



;--  bcv next-state is more general than djvm next-state ---------------


(encapsulate ()
  (local (include-book "base-next-state-more-specific"))
  (defthm next-state-no-more-general-IFEQ
    (mylet* ((oframe (frame-sig (current-frame s)
                                (instance-class-table s)
                                (heap s)
                                (heap-init-map (aux s))))
             (ns   (execute-IFEQ inst s))
             (nframe (frame-sig (current-frame ns)
                                (instance-class-table ns)
                                (heap ns)
                                (heap-init-map (aux ns)))))
            (implies (and (consistent-state s)
                          (bcv::check-IFEQ inst (env-sig s) oframe)
                          (check-IFEQ inst s))
                     (bcv::sig-frame-more-general 
                      (mv-nth 0 (bcv::execute-IFEQ
                                 inst 
                                 (env-sig s)
                                 oframe))
                      nframe
                      (env-sig s))))
    :hints (("Goal" :in-theory (disable execute-IFEQ bcv::execute-IFEQ)))))



;----------------------------------------------------------------------



(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")

;; Tue Aug  2 17:27:12 2005

;; (encapsulate ()
;;    (local (include-book "base-untag-state"))
;;    (defthm equal-IFEQ-when-guard-succeeds
;;      (implies (IFEQ-guard inst s)
;;               (equal (untag-state (djvm::execute-IFEQ inst s))
;;                      (m6::execute-IFEQ inst (untag-state s))))))


;; (i-am-here) ;; Tue Aug  2 17:27:52 2005

(encapsulate ()
   (local (include-book "base-state-equiv"))
   (defthm equal-IFEQ-when-guard-succeeds
      (implies (and (state-equiv M6::m6-s DJVM::djvm-s)
                    (IFEQ-guard inst DJVM::djvm-s))
               (state-equiv (m6::execute-IFEQ inst M6::m6-s)
                            (djvm::execute-IFEQ inst DJVM::djvm-s)))
      :hints (("Goal" :do-not '(generalize fertilize)))))


;; Tue Aug  2 17:28:59 2005
;----------------------------------------------------------------------

;; Mon Aug 15 21:53:41 2005

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-IFEQ-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-IFEQ inst s)))
           (method-ptr (current-frame s)))))

(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-IFEQ
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-IFEQ inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))

;----------------------------------------------------------------------

(in-theory (disable check-IFEQ IFEQ-guard execute-IFEQ wff-IFEQ))
