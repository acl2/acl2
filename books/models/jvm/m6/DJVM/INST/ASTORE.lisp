(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-locals")
(include-book "base-extra")

;----------------------------------------------------------------------
;
;  ASTORE  
;
;----------------------------------------------------------------------

;;(i-am-here) ;; Fri Aug  5 22:44:04 2005
;
; J2ME does not use returnAddress type to implement Finally clauses!! 
;
; So ASTORE only need to assign Reference Type into the local

(acl2::set-verify-guards-eagerness 2)

;----------------------------------------------------------------------



(defun wff-ASTORE (inst)
  (and  (wff-one-arg inst)
        (integerp (arg inst))
        (<= 0 (arg inst))
        (< (arg inst) *local-index-limit*)))

;----------------------------------------------------------------------

;; (defmacro SET-LP (index value)
;;   `(state-set-local-at ,index ,value s))


;----------------------------------------------------------------------


(defun ASTORE-guard (inst s)
     (mylet* ((cframe (current-frame s))
              (locals (locals cframe))
              (opstack (operand-stack cframe))
              (index  (arg inst)))
             (and (consistent-state-strong s)
                  (wff-ASTORE inst)
                  (<= 0 index)
                  (< index (len locals))
                  (topStack-guard-strong s)
                  (REFp (topStack s) (heap s))
                  (and (not (mem '*abstract* (method-accessflags (current-method s))))
                       ;; Mon Oct 18 09:33:08 2004. This above is implied by consistent-state 
                       (not (mem '*native* (method-accessflags (current-method s))))))))
                    ;; this is not implied by consistent-state




;----------------------------------------------------------------------

(include-book "base-state-set-local-at")
(include-book "base-consistent-state-more")

;;(in-theory (disable arg))

;; need to add something to base.lisp or base-consistent-state.lisp
;; to make sure the guard verification of this function go through! 


(defun execute-ASTORE (inst s)
   (declare (xargs :guard (ASTORE-guard inst s)))
   (mylet* ((index (arg inst))
            (v1 (topStack s)))
           (ADVANCE-PC (state-set-local-at index v1 
                                           (invalidate-category2-value
                                            (- index 1) (popStack s))))))

;; (defun execute-ASTORE (inst s)
;;    (declare (xargs :guard (ASTORE-guard inst s)))
;;    (mylet* ((index (arg inst))
;;             (v1 (topStack s)))
;;            (ADVANCE-PC (popStack 
;;                         (state-set-local-at index v1 
;;                                             (invalidate-category2-value
;;                                               (- index 1) s))))))

;;
;;         (ADVANCE-PC (state-set-local-at index v1 
;;                                           (invalidate-category2-value
;;                                            (- index 1) (popStack s)))
;; will make a difference!!! 
;;
;;
;; 
;; how we define ASTORE need to be examined!! 
;; setting one slot will destroy at most one size 2 value! 
;;
;; it will be different from ASTORE in M6.  In M6 we don't need to take care to
;; destory the size 2 value because after verification, we will know that those
;; slots will not read again before being written into!!


;----------------------------------------------------------------------

(defun check-ASTORE (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((cframe (current-frame s))
           (locals (locals cframe))
           (opstack (operand-stack cframe))
           (index  (arg inst)))
          (and (wff-ASTORE inst)
               (topStack-guard-strong s)
               (not (mem '*native* (method-accessflags (current-method s))))
               (< index (len locals)) 
               ;; (valid-local-index index locals) ;; this is not necessary 
               (REFp (topStack s) (heap s))
               (< index (max-local s)))))

;----------------------------------------------------------------------

(defthm check-ASTORE-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
               (check-ASTORE inst s))
          (ASTORE-guard inst s)))

;----------------------------------------------------------------------

;; the next is a more difficult! 
;; in fact our current definition using update-nth 
;; will not preserve the consistent-state!! 

;;; Thu Jul 28 16:06:34 2005


;; Fri Jul 29 01:14:12 2005

;; (skip-proofs 
;;  (defthm consistent-state-state-set-local-size-1-value
;;    (implies (and (consistent-state s)
;;                  (consistent-value-x v (instance-class-table s)
;;                                      (heap s))
;;                  (not (equal (type-size (tag-of v)) 2))
;;                  (<= 0 i)
;;                  (< i (len (locals (current-frame s)))))
;;             (consistent-state
;;              (STATE-SET-LOCAL-AT i v
;;                                  (INVALIDATE-CATEGORY2-VALUE (+ -1 i)
;;                                                             S))))))

;;(include-book "base-state-set-local-at")

;; (skip-proofs 
;;  (defthm topStack-guard-strong-preserved-by-invalidate-type-size-2
;;    (implies (topStack-guard-strong s)
;;             (topStack-guard-strong (invalidate-category2-value i s)))))

;; ;;(i-am-here) ;; Fri Aug  5 21:12:30 2005
;; (defthm len-update-nth-x
;;   (implies (and (integerp i)
;;                 (<= 0 i)
;;                 (< i (len locals)))
;;            (equal (len (update-nth i v locals))
;;                   (len locals))))
;; ;;
;; ;; shall only temporarily disable the following!! 
;; ;;
;; ;; (in-theory (disable LOCALS-INVALIDATE-CATEGORY2-VALUE-EFFECT-EXPANDER))
;; ;;



;; (skip-proofs 
;;  (defthm len-invalidate-category2-value
;;    (implies (and (integerp i)
;;                  (<=  -1  i)
;;                  (< i (len locals)))
;;             (equal (len (locals (current-frame (invalidate-category2-value i s))))
;;                    (len (locals (current-frame s)))))))

;; (skip-proofs 
;;  (defthm len-state-set-locals-at
;;    (implies (and (integerp i)
;;                  (<=  0  i)
;;                  (< i (len locals)))
;;             (equal (len (locals (current-frame (state-set-local-at i v s))))
;;                    (len (locals (current-frame s)))))))
                                     

;; (skip-proofs 
;;  (defthm invalidate-category2-value-thread-by-id
;;    (implies (thread-by-id id (thread-table s))
;;             (THREAD-BY-ID id (THREAD-TABLE (INVALIDATE-CATEGORY2-VALUE any
;;                                                                        s))))))


;; (skip-proofs 
;;  (defthm popStack-thread-by-id
;;    (implies (thread-by-id id (thread-table s))
;;             (THREAD-BY-ID id (THREAD-TABLE (popStack s))))))
                                                                      

;; (in-theory (disable NULLp initialized-ref))

;; (defthm len-update-nt-specific
;;   (implies (< i (len locals))
;;            (EQUAL
;;             (LEN (IF (< i '0)
;;                      locals
;;                      (IF (EQUAL (TYPE-SIZE (TAG-OF (NTH i locals)))
;;                                 '1)
;;                          locals
;;                          (UPDATE-NTH i
;;                                      '(TOPX . TOPX)
;;                                      locals))))
;;             (LEN locals))))

;; (defthm thread-by-id-back-chain-consistent-state
;;   (implies (and (consistent-state s)
;;                 (equal (current-thread s) id))
;;            (THREAD-BY-ID id (THREAD-TABLE s))))

;;;
;;; we have proved a lot theorems about consistent-state!!! 
;;;


(defthm ASTORE-guard-implies-execute-ASTORE-perserve-consistency
  (implies (ASTORE-guard inst s)
           (consistent-state-strong (execute-ASTORE inst s)))
  :hints (("Goal" :in-theory (e/d () 
                                  (state-set-local-at type-size arg locals
                                                      REFp)))))





;----------------------------------------------------------------------
;;(i-am-here)

(encapsulate ()
  (local (include-book "base-bcv"))
  (local (include-book "base-bcv-locals"))
  (defthm bcv-check-ASTORE-ensures-djvm-check-ASTORE
    (implies (and (bcv::check-ASTORE inst (env-sig s) 
                                     (frame-sig  (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s))))
                  
                  (wff-ASTORE inst) 
                  ;; implied by valid-local-index and in 
                  (not (mem '*native* (method-accessflags (current-method s))))
                  (consistent-state s))
             (djvm::check-ASTORE inst s))))


;----------------------------------------------------------------------




;-- BCV::check-ASTORE monotonic   -------------------------------------
;;
;; always the problem!! 
;;

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate ()
    (local (include-book "base-bcv-check-monotonic")) 
    (local (include-book "base-bcv-fact-isMatchingType-consp-stk"))
    (defthm sig-check-ASTORE-on-more-general-implies-more-specific
      (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                     (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                     (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                     (bcv::check-ASTORE inst env1 gframe) 
                     (bcv::good-icl icl)
                     (bcv::good-scl (bcv::classtableEnvironment env1))
                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
               (bcv::check-ASTORE inst env1 sframe))))

;----------------------------------------------------------------------


;-- BCV::execute-ASTORE next step  monotonic ---------------------------

(encapsulate () 
 (local (include-book "base-bcv-step-monotonic")) 
 ;; with new addition to base-bcv-step-monotonic.lisp
 ;; base-bcv-modify-local-variable.lisp
 (defthm ASTORE-monotonicity
   (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                 (bcv::consistent-sig-locals (bcv::frameLocals gframe) icl)
                 (bcv::consistent-sig-locals (bcv::frameLocals sframe) icl)
                 (bcv::check-ASTORE inst env1 gframe) 
                 (bcv::check-ASTORE inst env1 sframe))
            (bcv::sig-frame-more-general 
             (bcv::normal-frame (bcv::execute-ASTORE inst env gframe))
             (bcv::normal-frame (bcv::execute-ASTORE inst env sframe))
             env1))))



;----------------------------------------------------------------------

;-- DJVM::execute-ASTORE expansion -------------------------------------

;;
;; The key is to prove that 
;; 
;; (state-set-local-at ....  (invalidate-category2-value ....))
;;
;; produce the same effect of 
;;
;; (bcv::modifylocalvariable ....)
;;
;; unfortunately, these two functions are quite different!!! 
;;
;; Fri Jul 29 23:57:14 2005

;; (i-am-here) ;; Sat Jul 30 19:44:56 2005

;;(i-am-here) ;; Sun Jul 31 16:38:48 2005

(encapsulate ()
  (local (include-book "base-frame-sig-expansion"))
  (defthm execute-ASTORE-frame-sig-is
    (mylet* ((ns (execute-ASTORE inst s)))
            (implies 
             (and (consistent-state s)
                  (check-ASTORE inst s))
             (equal (frame-sig (current-frame ns)
                               (instance-class-table ns)
                               (heap ns)
                               (heap-init-map (aux ns)))
                    (let* ((locals 
                            (locals-sig (locals (current-frame s))
                                        (instance-class-table s)
                                        (heap s)
                                        (heap-init-map (aux s))
                                        (method-ptr (current-frame s))))
                           (opstack 
                            (opstack-sig (operand-stack (current-frame
                                                         (popStack s)))
                                         (instance-class-table s)
                                         (heap s)
                                         (heap-init-map (aux s))
                                         (method-ptr (current-frame s))))
                           (new-locals 
                            (bcv::modifylocalvariable 
                             (arg inst)
                             (value-sig (topStack s)
                                        (instance-class-table s)
                                        (heap s)
                                        (heap-init-map
                                         (aux s))
                                        (method-ptr
                                         (current-frame s))) locals)))
                    (make-sig-frame 
                     new-locals
                     opstack
                     (gen-frame-flags (current-frame s)
                                      (heap-init-map (aux s))))))))
    :hints (("Goal" :cases ((equal (arg inst) 0))
             :in-theory (disable bcv::make-sig-frame type-size)))))
                      
;; note that ASTORE may destroy some uninitialized value
;;
;; thus it the flag may change as a result!! 


;-- BCV::execute-ASTORE expansion -------------------------------------
;;(i-am-here) ;; Sat Aug  6 01:48:15 2005

(encapsulate ()
  (local (include-book "base-bcv-frame-sig-expansion"))  
  (defthm bcv-execute-ASTORE-is
    (implies (and (consistent-state s)
                  (check-ASTORE inst s)
                  (bcv::check-ASTORE inst (env-sig s) 
                                    (frame-sig (current-frame s)
                                               (instance-class-table s)
                                               (heap s)
                                               (heap-init-map (aux s)))))
             (equal (car (bcv::execute-ASTORE
                          inst (env-sig s) 
                          (frame-sig (current-frame s)
                                     (instance-class-table s)
                                     (heap s)
                                     (heap-init-map (aux s)))))
                    (let* ((locals 
                            (locals-sig (locals (current-frame s))
                                        (instance-class-table s)
                                        (heap s)
                                        (heap-init-map (aux s))
                                        (method-ptr (current-frame s))))
                           (opstack 
                            (opstack-sig (operand-stack (current-frame
                                                         (popStack s)))
                                         (instance-class-table s)
                                         (heap s)
                                         (heap-init-map (aux s))
                                         (method-ptr (current-frame s))))
                           (new-locals 
                            (bcv::modifylocalvariable 
                             (arg inst)
                             (value-sig (topStack s)
                                        (instance-class-table s)
                                        (heap s)
                                        (heap-init-map
                                         (aux s))
                                        (method-ptr
                                         (current-frame s))) locals)))
                      (make-sig-frame 
                       new-locals
                       opstack
                       (gen-frame-flags (current-frame s)
                                        (heap-init-map (aux s)))))))
    :hints (("Goal" :do-not '(preprocess)))))



;--  bcv next-state is more general than djvm next-state ---------------

(encapsulate ()
  (local (include-book "base-next-state-more-specific"))
  (defthm next-state-no-more-general-ASTORE
    (mylet* ((oframe (frame-sig (current-frame s)
                                (instance-class-table s)
                                (heap s)
                                (heap-init-map (aux s))))
             (ns   (execute-ASTORE inst s))
             (nframe (frame-sig (current-frame ns)
                                (instance-class-table ns)
                                (heap ns)
                                (heap-init-map (aux ns)))))
            (implies (and (consistent-state s)
                          (bcv::check-ASTORE inst (env-sig s) oframe)
                          (check-ASTORE inst s))
                     (bcv::sig-frame-more-general 
                      (mv-nth 0 (bcv::execute-ASTORE
                                 inst 
                                 (env-sig s)
                                 oframe))
                      nframe
                      (env-sig s))))
    :hints (("Goal" :in-theory (disable execute-ASTORE bcv::execute-ASTORE)))))


;----------------------------------------------------------------------

;;(i-am-here) 

(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")


(encapsulate ()
   (local (include-book "base-state-equiv"))
   (defthm equal-ASTORE-when-guard-succeeds
      (implies (and (state-equiv M6::m6-s DJVM::djvm-s)
                    (ASTORE-guard inst DJVM::djvm-s))
               (state-equiv (m6::execute-ASTORE inst M6::m6-s)
                            (djvm::execute-ASTORE inst DJVM::djvm-s)))
      :hints (("Goal" :do-not '(generalize fertilize)))))

;----------------------------------------------------------------------

; Mon Aug 15 21:37:16 2005

;; (i-am-here) ;; Mon Aug 15 21:38:49 2005

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-ASTORE-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-ASTORE inst s)))
           (method-ptr (current-frame s)))))

;;; next need to prove loaded class method-does-not-change! 


(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-ASTORE
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-ASTORE inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))



;----------------------------------------------------------------------

(in-theory (disable check-ASTORE ASTORE-guard execute-ASTORE wff-ASTORE))
