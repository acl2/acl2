(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-extra")

(acl2::set-verify-guards-eagerness 2)

;----------------------------------------------------------------------

(defun wff-anewarray (inst)
  (and (wff-one-arg inst)
       (wff-type-rep (arg inst))
       (not (primitive-type? (normalize-type-rep (arg inst))))))



;----------------------------------------------------------------------



(defun ANEWARRAY-guard (inst s)
  (declare (xargs :guard-hints (("Goal" 
             :in-theory (enable INT32p topStack-guard-strong
                                category1 max-stack-guard
                                topStack
                                topStack-guard)))))
  (and (wff-anewarray inst)
       (consistent-state-strong s)
       (not (mem '*native* (method-accessflags (current-method s))))
       (<= (len (operand-stack (current-frame s)))
           (max-stack s)) 
       ;;
       ;; Mon Oct 18 09:51:48 2004. in order to talk about max-stack
       ;; we assert that current method is not *native* method.
       ;;
       (topStack-guard-strong s)
       (INT32p (value-of (topStack s)))))



;----------------------------------------------------------------------

(defun dnew-array-guard (length s)
  (and (build-a-java-visible-instance-guard "java.lang.Object" s)
       (integerp length)
       (>= length 0)
       (wff-state s)
       (wff-heap (heap s))
       (wff-thread-table (thread-table s))
       (current-frame-guard s)
       (wff-call-frame (current-frame s))))



(defun dnew-array (element-type length S)
  (declare (xargs :guard (dnew-array-guard length s)))
    (mv-let (the-object new-s)
            (build-an-array-instance element-type length S)
            (let* ((old-heap (heap new-s))
                   (addr     (alloc old-heap))
                   (new-heap (bind addr the-object old-heap)))
              (pushStack (tag-REF addr) (update-trace addr (state-set-heap new-heap new-s))))))

;; (i-am-here) ;; Tue May 24 23:49:48 2005

(encapsulate () 
  (local (include-book "base-skip-proofs"))
   (defthm raise-exception-consistent-state-strong
     (implies (consistent-state-strong s)
              (consistent-state-strong (raise-exception any s)))))


;; (i-am-here) ;; Wed Jun  8 14:39:05 2005

(include-book "base-consistent-state-load-class")
(include-book "base-load-class-normalize")


(defun execute-ANEWARRAY (inst s)
  (declare (xargs :guard (ANEWARRAY-guard inst s)))
  (mylet* ((basetype (normalize-type-rep (arg inst)))
           (new-s    (resolveClassReference basetype s))
           (new-s2   (getArrayClass basetype new-s)))
          (if (not (no-fatal-error? new-s))
              new-s
            (if (pending-exception new-s)  ;; this check looks an efficiency issues
                ;; however if we have imperative language. this check isn't there. 
                (raise-exception (pending-exception new-s) new-s)
              (if (not (no-fatal-error? new-s2))
                  new-s2
                (if (< (value-of (topStack s)) 0)
                    (raise-exception "java.lang.NegativeArraySizeException" new-s2)
                  ;; check possible exception. 
                  ;; access permission is checked at resolution time. 
                  (ADVANCE-PC (dnew-array basetype (value-of (topStack s))
                                          (popStack new-s2)))))))))




;----------------------------------------------------------------------
           
(defun check-ANEWARRAY (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((cframe (current-frame s))
           (opstack (operand-stack cframe))
           (basetype (normalize-type-rep  (arg inst)))
           (bound  (topStack s)))
          (and (wff-ANEWARRAY inst)
               (topStack-guard-strong s)
               (equal (djvm-translate-int-type (tag-of bound)) 'INT))))


;----------------------------------------------------------------------

;; (i-am-here) ;; Sun Jun  5 15:46:30 2005

(include-book "base-consistent-state-update-trace")
(include-book "base-consistent-state-state-set-heap")
(include-book "base-build-an-array-instance-creates-consistent-object")

;;(i-am-here)

(defthm ANEWARRAY-guard-implies-execute-ANEWARRAY-perserve-consistency
  (implies (ANEWARRAY-guard inst s)
           (consistent-state-strong (execute-ANEWARRAY inst s))))


;----------------------------------------------------------------------

(defthm check-ANEWARRAY-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
               (check-ANEWARRAY inst s))
          (ANEWARRAY-guard inst s)))

;----------------------------------------------------------------------


;-- BCV::check-ANEWARRAY implies DJVM::check-ANEWARRAY on a corresponding state -----

;;; Fri Jul 22 16:14:32 2005
;;; we modifid value-sig to do the mapping from Byte to INT which may
;;; complicate the things!! 

;;;
;;; for example, djvm::check-ANEWARRAY should be more generous on what is
;;; considered as an INT type! 
;;;

;;; (i-am-here) ;; Fri Jul 22 16:26:52 2005 

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate ()
  (local (include-book "base-bcv"))
  (defthm bcv-check-ANEWARRAY-ensures-djvm-check-ANEWARRAY
    (implies (and (bcv::check-ANEWARRAY inst (env-sig s) 
                                     (frame-sig  (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s))))
                  (wff-anewarray inst)
                  (not (mem '*native* (method-accessflags (current-method s))))
                  (consistent-state s))
             (djvm::check-ANEWARRAY inst s))))



;-- BCV::check-ANEWARRAY monotonic   -------------------------------------

(encapsulate ()
    (local (include-book "base-bcv-check-monotonic"))
    (defthm sig-check-ANEWARRAY-on-more-general-implies-more-specific
      (implies (and (bcv::good-icl icl)
                    (bcv::good-scl (bcv::classtableEnvironment env1))
                    (bcv::sig-frame-more-general gframe sframe env1)
                    (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                    (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                    (bcv::check-ANEWARRAY inst env1 gframe)
                    (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
               (bcv::check-ANEWARRAY inst env1 sframe))))


;-- BCV::execute-ANEWARRAY next step  monotonic ---------------------------

(encapsulate () 
     (local (include-book "base-bcv-step-monotonic"))
     (defthm ANEWARRAY-monotonicity
       (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                     (bcv::check-ANEWARRAY inst env1 gframe) 
                     (bcv::check-ANEWARRAY inst env1 sframe) 
                     (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                     (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                     (bcv::good-icl icl)
                     (bcv::good-scl (bcv::classtableEnvironment env1))
                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
                (bcv::sig-frame-more-general 
                 (bcv::normal-frame (bcv::execute-ANEWARRAY inst env gframe))
                 (bcv::normal-frame (bcv::execute-ANEWARRAY inst env sframe))
                 env1))))



;----------------------------------------------------------------------


;-- DJVM::next-state more specific than BCV  ---------------------------

;;(i-am-here) ;; Sun Aug  7 22:46:10 2005

(encapsulate ()
    (local (include-book "base-frame-sig-expansion"))
    (defthm execute-ANEWARRAY-frame-sig-is
      (mylet* ((ns (execute-ANEWARRAY inst s)))
              (implies 
               (and (consistent-state s)
                    (not (< (value-of (topStack s)) 0))
                    (not (pending-exception (resolveClassReference 
                                             (normalize-type-rep (arg inst))
                                             S)))
                    (no-fatal-error? ns) 
                    ;;; we really only need to assert
                    ;;; no fatal-error after class loading. 
                    ;;; Sun Jun  5 20:30:41 2005
                    (check-ANEWARRAY inst s))
               (equal (frame-sig (current-frame ns)
                                 (instance-class-table ns)
                                 (heap ns)
                                 (heap-init-map (aux ns)))
                      (frame-push-value-sig (list 'ARRAY (arg inst))
                                            (frame-sig (current-frame (popStack s))
                                                       (instance-class-table s)
                                                       (heap s)
                                                       (heap-init-map (aux
                                                                       s)))))))))


;; (i-am-here) ;; Sun Jun  5 20:20:37 2005

(encapsulate () 
  (local (include-book "base-bcv-frame-sig-expansion"))
  (defthm bcv-execute-ANEWARRAY-is
    (implies (and (consistent-state s)
                  (check-ANEWARRAY inst s)
                  (bcv::check-ANEWARRAY inst (env-sig s) 
                                        (frame-sig (current-frame s)
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s)))))
             (equal (mv-nth 0 (bcv::execute-ANEWARRAY
                               inst (env-sig s) 
                               (frame-sig (current-frame s)
                                          (instance-class-table s)
                                          (heap s)
                                          (heap-init-map (aux s)))))
                    (frame-push-value-sig (list 'array (bcv::arg1 inst))
                                          (frame-sig (current-frame (popStack s))
                                                     (instance-class-table s)
                                                     (heap s)
                                                     (heap-init-map (aux s))))))))
  




(encapsulate () 
  (local (include-book "base-next-state-more-specific"))
  (defthm next-state-no-more-general-anewarray
    (mylet* ((oframe (frame-sig (current-frame s)
                                (instance-class-table s)
                           (heap s)
                           (heap-init-map (aux s))))
           (ns   (execute-ANEWARRAy inst s))
           (nframe (frame-sig (current-frame ns)
                              (instance-class-table ns)
                              (heap ns)
                              (heap-init-map (aux ns)))))
    (implies (and (consistent-state s)
                  (not (< (value-of (topStack s)) 0))
                  (no-fatal-error? ns)
                  (not (pending-exception (resolveClassReference 
                                           (normalize-type-rep (arg inst)) S)))
                  (bcv::check-ANEWARRAY inst (env-sig s) oframe)
                  (check-ANEWARRAY inst s))
             (bcv::sig-frame-more-general 
              (mv-nth 0 (bcv::execute-ANEWARRAY
                         inst 
                         (env-sig s)
                         oframe))
              nframe
              (env-sig s))))
    :hints (("Goal" :in-theory (disable execute-ANEWARRAY bcv::execute-ANEWARRAY)))))

;;;
;;; Sun Jun  5 20:27:13 2005
;;;
;;;


  
;----------------------------------------------------------------------


(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")

;;(i-am-here) ;; Tue Aug  2 16:15:14 2005

;;
;; (encapsulate ()
;;    (local (include-book "base-untag-state"))
;;    (defthm equal-ANEWARRY-when-guard-succeeds
;;      (implies (ANEWARRAY-guard inst s)
;;               (equal (untag-state (djvm::execute-ANEWARRAY inst s))
;;                      (m6::execute-ANEWARRAY inst (untag-state s))))))
;;


(encapsulate ()
   (local (include-book "base-state-equiv"))
   (defthm equal-ANEWARRAY-when-guard-succeeds  ;; fix the name 
      (implies (and (state-equiv M6::m6-s DJVM::djvm-s)
                    (ANEWARRAY-guard inst DJVM::djvm-s))
               (state-equiv (m6::execute-ANEWARRAY inst M6::m6-s)
                            (djvm::execute-ANEWARRAY inst DJVM::djvm-s)))
      :hints (("Goal" :do-not '(generalize fertilize)
               :in-theory (disable state-equiv)))))

;----------------------------------------------------------------------

; Mon Aug 15 21:41:54 2005

;; (i-am-here) ;; Mon Aug 15 21:42:15 2005

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-ANEWARRAY-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-ANEWARRAY inst s)))
           (method-ptr (current-frame s)))))

;;;
;;; we have enough rules that says the current-frame is not changed by class
;;; loading!! 
;;;

(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-ANEWARRAY
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-ANEWARRAY inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))




;----------------------------------------------------------------------
(in-theory (disable check-ANEWARRAY ANEWARRAY-guard execute-ANEWARRAY wff-ANEWARRAY)) 
