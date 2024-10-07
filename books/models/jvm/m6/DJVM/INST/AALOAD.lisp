(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-extra")

;-----------------------------------------------------------------
;
;  AALOAD
;
; 

;-- Define guard first -------------------------------------------

(acl2::set-verify-guards-eagerness 2)

(defun wff-AALOAD (inst) 
  (wff-inst inst))

(defun AALOAD-guard (inst s)
  ;; (declare (ignore inst)) 
  ;; this may not be ignored later. Fri Jan 16 00:45:47
  ;; 2004. 
  ;; 
  ;; Because there is a (inst-size inst). We need to assert inst
  ;; is wff-inst!!  we need guard verify the jvm-bytecode.lisp
  ;; ....  then strengthen the consistent-state and prove
  ;; consistent-state guarantees all instruction is well-formed!!
  ;;
  ;; TO FIX LATER: Wed Mar  9 11:35:41 2005. 
  ;;
  ;; Thu Jul 28 15:59:18 2005 FIXED 
  (mylet* ((index (safe-topStack s))
           (array-ref (safe-secondStack s)))
          (and (consistent-state-strong s)
               (wff-inst inst)
               (topStack-guard-strong s)
               (secondStack-guard-strong s)
               (wff-REFp array-ref)
               (INT32p (value-of index))
               (<= (len (operand-stack (current-frame s)))
                   (max-stack s))
               (or (CHECK-NULL array-ref)
                   (and (CHECK-ARRAY-guard (rREF array-ref) (heap s))
                        ;; One could replace check-array-guard with an
                        ;; assertion about
                        ;; consistent-array-object However under
                        ;; the hypothesis of "consistent-state"
                        ;; this is the same.
                        (not (primitive-type? 
                              (array-component-type 
                               (obj-type (binding (rREF array-ref) (heap
                                                                    s)))))))))))

;-- Definition of AALOAD---------------------------------

;; (i-am-here)  ;; Thu Jul 28 15:55:25 2005
;; Thu Jul 28 15:17:54 2005 We added the guard on functions to local-at
;; and related functions. now we need to get this to work!! 
;; Thu Jul 28 15:18:25 2005

(defun execute-AALOAD (inst s)
  (declare (xargs :guard (AALOAD-guard inst s)))
  (let* ((index (safe-topStack s)) 
         (array-ref (safe-secondStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array (rREF array-ref) (value-of index) s)
          (ADVANCE-PC (safe-pushStack (tag-REF (element-at-array (value-of index) (rREF array-ref) s))
                                 (safe-popStack (safe-popStack s))))
        (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))


;-- Runtime checking of the AALOAD ----------------------

;
; Note the difference between *-guard and check-* 
; 
; Tue Apr 19 10:10:29 2005

(defun check-AALOAD (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((index (safe-topStack s))
           (array-ref (safe-secondStack s)))
          (and (wff-inst inst)
               (topStack-guard-strong s)
               (secondStack-guard-strong s)
               (equal (tag-of array-ref)    'REF)
               (equal (djvm-translate-int-type (tag-of (safe-topStack s))) 'INT)
               (or (equal (value-of array-ref) -1)
                   (and (array-type-s (obj-type (deref2 array-ref (heap s)))
                                      (instance-class-table s))
                        (not (primitive-type? (array-component-type
                                              (obj-type (deref2 array-ref 
                                                                (heap
                                                                 s)))))))))))



;----------------------------------------------------------------------
;----------------------------------------------------------------------


;;; Strive to make sure that the proof of these theorems depend only on lemma
;;; in base-* !!
;;; 

;-- AALOAD-guard implies state consistency perserved -----------------



;; (defthm element-at-consistent-array-not-deref2-init
;;   (implies (and (consistent-array-object (deref2 array-ref (heap s))
;;                                          (heap s)
;;                                          (instance-class-table s)
;;                                          (array-class-table s))
;;                 (check-ARRAY (rREF array-ref) index s)  ;; we can assume this
;;                 (NOT (EQUAL (ELEMENT-AT-ARRAY INDEX (RREF ARRAY-REF) S) '-1))
;;                 (consistent-state s)
;;                 (not (primitive-type? (array-component-type (obj-type (deref2 array-ref (heap s)))))))
;;            (not (consp (deref2-init (tag-REF (element-at-array index (rREF array-ref) s))
;;                                     (heap-init-map (aux s))))))
;;   :hints (("Goal" :in-theory (e/d () (deref2-init tag-REF array-data
;;                                                   TAG-REF-TAG 
;;                                                   heap-init-map))
;;            :restrict ((array-content-initialized-mem-specific
;;                        ((data (array-data (deref2 array-ref (heap s))))))))))


;; (defthm |Subgoal 1.1'|
;;   (IMPLIES
;;    (AND
;;     (CONSISTENT-STATE-STRONG S)
;;     (TRUE-LISTP INST2)
;;     (EQUAL (+ 1 (LEN INST2)) 2)
;;     (INTEGERP INST1)
;;     (CONSP INST2)
;;     (CONSP (CAR INST2))
;;     (TRUE-LISTP (CAR INST2))
;;     (TOPSTACK-GUARD-STRONG S)
;;     (TOPSTACK-GUARD-STRONG (POPSTACK S))
;;     (WFF-REFP (TOPSTACK (POPSTACK S)))
;;     (INT32P (VALUE-OF (TOPSTACK S)))
;;     (<= (LEN (OPERAND-STACK (CURRENT-FRAME S)))
;;         (METHOD-MAXSTACK (CURRENT-METHOD S)))
;;     (CHECK-ARRAY-GUARD (RREF (TOPSTACK (POPSTACK S)))
;;                        (HEAP S))
;;     (NOT (PRIMITIVE-TYPE?
;;           (ARRAY-COMPONENT-TYPE (OBJ-TYPE (DEREF2 (TOPSTACK (POPSTACK S))
;;                                                   (HEAP S))))))
;;     (NOT (EQUAL (VALUE-OF (TOPSTACK (POPSTACK S)))
;;                 -1))
;;     (CHECK-ARRAY (RREF (TOPSTACK (POPSTACK S)))
;;                  (VALUE-OF (TOPSTACK S))
;;                  S))
;;    (CONSISTENT-STATE-STRONG
;;     (STATE-SET-PC
;;      (+ (PC S)
;;         (INST-SIZE (CONS INST1 INST2)))
;;      (PUSHSTACK
;;       (TAG (ELEMENT-AT-ARRAY (VALUE-OF (TOPSTACK S))
;;                              (RREF (TOPSTACK (POPSTACK S)))
;;                              S)
;;            (ARRAY-COMPONENT-TYPE (OBJ-TYPE (DEREF2 (TOPSTACK (POPSTACK S))
;;                                                    (HEAP S)))))
;;       (POPSTACK (POPSTACK S))))))
;;   :hints (("Goal" :do-not-induct t)))


;; (defthm |Subgoal 1.1'|
;;   (IMPLIES
;;  (AND
;;     (CONSISTENT-STATE-STRONG S)
;;     (TRUE-LISTP INST2)
;;     (EQUAL (+ 1 (LEN INST2)) 2)
;;     (INTEGERP INST1)
;;     (CONSP INST2)
;;     (CONSP (CAR INST2))
;;     (TRUE-LISTP (CAR INST2))
;;     (TOPSTACK-GUARD-STRONG S)
;;     (TOPSTACK-GUARD-STRONG (POPSTACK S))
;;     (WFF-REFP (TOPSTACK (POPSTACK S)))
;;     (INT32P (VALUE-OF (TOPSTACK S)))
;;     (<= (LEN (OPERAND-STACK (CURRENT-FRAME S)))
;;         (METHOD-MAXSTACK (CURRENT-METHOD S)))
;;     (CHECK-ARRAY-GUARD (RREF (TOPSTACK (POPSTACK S)))
;;                        (HEAP S))
;;     (NOT (PRIMITIVE-TYPE?
;;               (ARRAY-COMPONENT-TYPE (OBJ-TYPE (DEREF2 (TOPSTACK (POPSTACK S))
;;                                                       (HEAP S))))))
;;     (NOT (EQUAL (VALUE-OF (TOPSTACK (POPSTACK S)))
;;                 -1))
;;     (CHECK-ARRAY (RREF (TOPSTACK (POPSTACK S)))
;;                  (VALUE-OF (TOPSTACK S))
;;                  S))
;;  (CONSISTENT-STATE-STRONG
;;     (STATE-SET-PC
;;          (+ (PC S)
;;             (INST-SIZE (CONS INST1 INST2)))
;;          (PUSHSTACK (TAG-REF (ELEMENT-AT-ARRAY (VALUE-OF (TOPSTACK S))
;;                                                (RREF (TOPSTACK (POPSTACK S)))
;;                                                S))
;;                     (POPSTACK (POPSTACK S))))))
;;   :hints (("Goal" :do-not-induct t)))

(encapsulate () 
  (local (include-book "base-skip-proofs"))
  (defthm raise-exception-consistent-state-strong
    (implies (consistent-state-strong s)
             (consistent-state-strong (raise-exception any s)))))

(defthm aaload-guard-implies-execute-AALOAD-perserve-consistency
  (implies (AALOAD-guard inst s)
           (consistent-state-strong (execute-AALOAD inst s))))


;-- check-AALOAD implies AALOAD-guard in a consistent state ----------

(defthm check-AALOAD-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
                (check-AALOAD inst s))
          (AALOAD-guard inst s)))

;; this fairly automatic!! ;; Thu May 12 12:19:51 2005

;-- BCV::check-AALOAD implies DJVM::check-AALOAD on a corresponding state -----

;; (i-am-here) ;;  Fri Jul 22 19:58:56 2005

(encapsulate ()
  (local (include-book "base-bcv"))
  (defthm bcv-check-aaload-ensures-djvm-check-aaload
    (implies (and (bcv::check-AALOAD inst (env-sig s) 
                                     (frame-sig  (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s))))
                  (wff-inst inst)
                  (not (mem '*native* (method-accessflags (current-method s))))
                  (consistent-state s))
             (djvm::check-AALOAD inst s))))


;;
;; The function is base-bcv.lisp is to expand (frame-sig ...) when we know
;; consistent-state and bcv::check-* !!! 
;; 
;; this is one of the difficult lemma. We are showing that from tags and
;; consistent-state, we know something about the runtime state.
;; 

;-- BCV::check-AALOAD monotonic   -------------------------------------
;; (i-am-here)

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate ()
    (local (include-book "base-bcv-check-monotonic"))
    (defthm sig-check-AALOAD-on-more-general-implies-more-specific
      (implies (and (bcv::good-icl icl)
                    (bcv::good-scl (bcv::classtableEnvironment env1))
                    (bcv::sig-frame-more-general gframe sframe env1)
                    (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                    (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                    (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL)) ;; added
                    (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
                    (bcv::check-AALOAD inst env1 gframe)
                    (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
               (bcv::check-AALOAD inst env1 sframe))))


;;; showing the next step is monotonic is more difficult!! 

;-- BCV::execute-AALOAD next step  monotonic ---------------------------

(encapsulate () 
     (local (include-book "base-bcv-step-monotonic"))
     (defthm AALOAD-monotonicity
       (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                     (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                     (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                     (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
                     (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL))
                     (bcv::check-AALOAD inst env1 gframe) 
                     (bcv::check-AALOAD inst env1 sframe) 
                     (bcv::good-icl icl)
                     (bcv::good-scl (bcv::classtableEnvironment env1))
                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
                (bcv::sig-frame-more-general 
                 (bcv::normal-frame (bcv::execute-AALOAD inst env gframe))
                 (bcv::normal-frame (bcv::execute-AALOAD inst env sframe)) env1))))


;----------------------------------------------------------------------


;-- DJVM::next-state more specific than BCV  ---------------------------


(encapsulate ()
    (local (include-book "base-frame-sig-expansion"))
    (defthm execute-aaload-frame-sig-is
      (mylet* ((ns (execute-aaload inst s))
               (index (topStack s))
               (array-ref (topStack (popStack s))))
              (implies 
               (and (consistent-state s)
                    (not (check-NULL array-ref))
                    (check-array (RREF array-ref) (value-of index) s)
                    (check-aaload inst s))
               ;; the following is true only when we know no exceptions happens in this
               ;; case ARRAY's reference is not NULL, the index value is within
               ;; bound.
               ;;
               ;; otherwise, an exception would be thrown. 
               ;;
               (equal (frame-sig (current-frame ns)
                                 (instance-class-table ns)
                                 (heap ns)
                                 (heap-init-map (aux ns)))
                      (frame-push-value-sig 
                       (value-sig (TAG-REF (element-at-array
                                            (value-of index)
                                            (rREF array-ref) s))
                                  (instance-class-table s)
                                  (heap s)
                                  (heap-init-map (aux s))
                                  (method-ptr (current-frame s)))
                       (frame-sig (current-frame (popStack (popStack s)))
                                  (instance-class-table s)
                                  (heap s)
                                  (heap-init-map (aux s)))))))
      :hints (("Goal" :cases ((NULLp (tag-REF
                                      (element-at-array (value-of (topStack s))
                                                        (rREF (topStack (popStack s)))
                                                        s))))))))

;; note. :: Thu May 12 00:06:36 2005. Fixed to get rid of magic :) 
;;
;; there is some magic:
;; In first getting: 
;;           value-sig into fix-sig. 
;; then conclude 
;;          (consistent-value-x (element-at-array .... ))

;----------------------------------------------------------------------

;;; DONE !! 

;;(i-am-here) ;; Sun Jul 31 15:50:51 2005


(encapsulate ()
  (local (include-book "base-bcv-frame-sig-expansion"))
  (defthm bcv-execute-aaload-is
    (implies (and 
              (consistent-state s)
              (check-aaload inst s)
              (bcv::check-aaload inst (env-sig s) 
                                 (frame-sig (current-frame s)
                                            (instance-class-table s)
                                            (heap s)
                                            (heap-init-map (aux s))))
              (not (nullp (topStack (popStack s)))))
             (equal (car (bcv::execute-aaload inst (env-sig s) 
                                              (frame-sig (current-frame s)
                                                         (instance-class-table s)
                                                         (heap s)
                                                         (heap-init-map (aux s)))))
                    (frame-push-value-sig 
                     (fix-sig (array-component-type 
                               (obj-type (deref2 (topStack (popStack s)) 
                                                 (heap s)))))
                     (frame-sig (current-frame (popStack (popStack s)))
                                (instance-class-table s)
                                (heap s)
                                (heap-init-map (aux s))))))))


;----------------------------------------------------------------------
;;
;; Now we are ready to prove 
;;
;;           next-state-no-more-general-aaload
;;
                                         


;;; not now how to conclude 
;; (i-am-here)


;; (local   (include-book "base-next-state-more-specific"))

;; (i-am-here) ;; Tue May 17 15:38:53 2005


(encapsulate () 
       (local   (include-book "base-next-state-more-specific"))
       (defthm next-state-no-more-general-aaload
         (mylet* ((oframe (frame-sig (current-frame s)
                                     (instance-class-table s)
                                     (heap s)
                                     (heap-init-map (aux s))))
                  (ns   (djvm::execute-aaload inst s))
                  (nframe (frame-sig (current-frame ns)
                                     (instance-class-table ns)
                                     (heap ns)
                                     (heap-init-map (aux ns)))))
                 (implies (and (consistent-state s)
                               (bcv::check-aaload inst (env-sig s) oframe)
                               (djvm::check-aaload inst s)
                               (not (check-null (topStack (popStack s))))
                               (check-array (RREF (topStack (popStack s))) 
                                            (value-of (topStack s)) s))
                          (bcv::sig-frame-more-general 
                           (car (bcv::execute-aaload inst 
                                                     (env-sig s)
                                                     oframe))
                           nframe
                           (env-sig s))))
         :hints (("Goal" :in-theory (disable 
                                     ;;djvm::check-aaload
                                     ;;bcv::check-aaload
                                     djvm::execute-aaload
                                     bcv::execute-aaload
                                     bcv::isAssignable
                                     check-null
                                     frame-push-value-sig)
                  :cases ((NULLp (TAG-REF (ELEMENT-AT-ARRAY (VALUE-OF (TOPSTACK S))
                                                            (RREF (TOPSTACK (POPSTACK S)))
                                                            S))))))))


;-- M6-DJVM-equal-when-check-succeeds.lisp ------------------------------

;; (i-am-here) 
;; Tue Jul 26 11:29:39 2005. after dealing with 'topx issue. 
;; 

(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")

;; (i-am-here);; Mon Jun  6 00:24:08 2005

;; (local (include-book "base-untag-state"))
;; (encapsulate ()
;;    (local (in-theory (enable djvm::check-array)))
;;    (local (in-theory (enable djvm::element-at-array)))
;;    (defthm equal-AALOAD-when-guard-succeeds
;;      (implies (AALOAD-guard inst s)
;;               (equal (untag-state (djvm::execute-AALOAD inst s))
;;                      (m6::execute-AALOAD inst (untag-state s))))))



;;; Tue Aug  2 17:01:28 2005



;; (i-am-here) ;; Tue Aug  2 17:02:21 2005
(encapsulate ()
   (local (include-book "base-state-equiv"))
    (defthm equal-AALOAD-when-guard-succeeds
      (implies (and (AALOAD-guard inst djvm::djvm-s)
                    (state-equiv m6::m6-s djvm::djvm-s))
               (state-equiv (m6::execute-AALOAD inst m6::m6-s)
                            (djvm::execute-AALOAD inst djvm::djvm-s)))))

;----------------------------------------------------------------------
;
; Mon Aug 15 20:06:37 2005

;; (i-am-here) ;; Mon Aug 15 20:08:38 2005

;;; first need to prove method-ptr does not change

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-AALOAD-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-AALOAD inst s)))
           (method-ptr (current-frame s)))))

;;; next need to prove loaded class method-does-not-change! 


(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-AALOAD
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-aaload inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))

;----------------------------------------------------------------------


;; Tue Aug  2 17:17:54 2005
;----------------------------------------------------------------------
(in-theory (disable check-AALOAD AALOAD-guard execute-AALOAD wff-AALOAD))
