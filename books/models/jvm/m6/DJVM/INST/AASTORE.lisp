(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-extra")

;-----------------------------------------------------------------
;
;  AASTORE
;
; 


;----------------------------------------------------------------------
;
; AASTORE
; 
;----------------------------------------------------------------------
;
;;
;; aastore
;;
;; Operation
;;
;;     Store into reference array
;;
;;     Format
;;
;;     aastore 	
;;
;; Forms
;;
;;     aastore = 83 (0x53)
;;
;; Operand Stack
;;
;;     ..., arrayref, index, value ...
;;
;; Description
;;
;;     The arrayref must be of type reference and must refer to an array whose
;;     components are of type reference. The index must be of type int and
;;     value must be of type reference. The arrayref, index, and value are
;;     popped from the operand stack. The reference value is stored as the
;;     component of the array at index.
;;
;;     The type of value must be assignment compatible (\x{00A7}2.6.7) with the
;;     type of the components of the array referenced by arrayref. Assignment
;;     of a value of reference type S (source) to a variable of reference type
;;     T (target) is allowed only when the type S supports all the operations
;;     defined on type T. The detailed rules follow:
;;
;;     * If S is a class type, then:
;;
;;           o If T is a class type, then S must be the same class
;;           (\x{00A7}2.8.1) as T, or S must be a subclass of T;
;;
;;           o If T is an interface type, S must implement (\x{00A7}2.13)
;;           interface T.
;;
;;     * If S is an interface type, then:
;;
;;           o If T is a class type, then T must be Object (\x{00A7}2.4.7).
;;
;;           o If T is an interface type, then T must be the same interface as
;;           S or a superinterface of S (\x{00A7}2.13.2).
;;
;;     * If S is an array type, namely, the type SC[], that is, an array of
;;     components of type SC, then:
;;
;;           o If T is a class type, then T must be Object (\x{00A7}2.4.7).
;;
;;           o If T is an array type TC[], that is, an array of components of
;;           type TC, then one of the following must be true:
;;
;;                 + TC and SC are the same primitive type (\x{00A7}2.4.1).
;;
;;                 + TC and SC are reference types (\x{00A7}2.4.6), and type SC
;;                 is assignable to TC by these runtime rules.
;;
;;           o If T is an interface type, T must be one of the interfaces
;;           implemented by arrays (\x{00A7}2.15).
;;
;; Runtime Exceptions
;;
;;     If arrayref is null, aastore throws a NullPointerException.
;;
;;     Otherwise, if index is not within the bounds of the array referenced by
;;     arrayref, the aastore instruction throws an
;;     ArrayIndexOutOfBoundsException.
;;
;;     Otherwise, if arrayref is not null and the actual type of value is not
;;     assignment compatible (\x{00A7}2.6.7) with the actual type of the
;;     components of the array, aastore throws an ArrayStoreException.
;;
;;
;; Defensive machine will also check at runtime, the value to be assigned into
;; the array is always initialized!! 
;;
;; However this should not be a runtime exception!! It should be checked in the
;; check-aaload, and checked at aastore-guard.
;;  



;-- Define guard first -------------------------------------------

(acl2::set-verify-guards-eagerness 2)

(defun wff-AASTORE (inst)
  (wff-inst inst))

; in order to maintain consistent-state, we shall not allow 
; store a reference to an uninitialized object into an array!!
; 
; This is something enforced by the BCV. 
; We need to check for it? 
;
; However AASTORE at runtime checks isAssignableTo, could we expect that check
; for initialization status being checked at that time?
;
; No. It would be too expensive to maintain initialization status of an object.
; that would demand keep track of when the object's constructor finish
; execution!!
;


(defun AASTORE-guard (inst s)
  (mylet* ((value (safe-topStack s))
           (index (safe-secondStack s))
           (array-ref (safe-thirdStack s)))
          (and (consistent-state-strong s)
               (wff-inst inst)
               (topStack-guard-strong s)
               (secondStack-guard-strong s)
               (thirdStack-guard-strong s)
               (wff-REFp array-ref)
               (wff-REFp value)
               (INT32p (value-of index))
               (<= (len (operand-stack (current-frame s)))
                   (max-stack s))
               (or (CHECK-NULL array-ref)
                   (and (REFp array-ref (heap s))
                        (CHECK-ARRAY-guard (rREF array-ref) (heap s))
                        (not (primitive-type? 
                              (array-component-type 
                               (obj-type (deref2 array-ref (heap s))))))
                        (REFp value (heap s))
                        (or (NULLp value)
                            (not (bound? (rREF value) (heap-init-map (aux s))))
                            (not (consp (deref2-init value 
                                                     (heap-init-map (aux s)))))))))))
                            ;;; Sat May  7 03:02:50 2005
                            ;;; revealed after insights obtained
                            ;;; from proof of djvm AALOAD being more specific
                            ;;; than bcv AALOAD
                            






;-- Definition of AASTORE---------------------------------


(defun execute-AASTORE (inst s)
  (declare (xargs :guard (AASTORE-guard inst s)
                  :guard-hints (("Goal" :in-theory (e/d () (consistent-state array-bound))))))
  (let* ((value (safe-topStack s))
         (index (safe-secondStack s)) 
         (array-ref (safe-thirdStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (not (check-array (rREF array-ref) (value-of index) s))
          (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)
        (if (not (check-NULL value))
            (mylet* ((value-obj (deref2 value (heap s)))
                     (array-obj (deref2 array-ref (heap s)))
                     (array-type (obj-type array-obj))
                     (base-type (array-component-type array-type)))
                    (mv-let (status new-s)
                            (isAssignableTo (obj-type value-obj) base-type s)
                            (if status 
                                (ADVANCE-PC  (set-element-at-array (value-of index)
                                                                   (value-of value)
                                                                   (rREF array-ref)
                                                                   (safe-popStack 
                                                                    (safe-popStack
                                                                     (safe-popStack new-s)))))
                              (raise-exception "java.lang.ArrayStoreException" new-s))))
            ;;; this assignable is checked at runtime. 
            ;;; The current BCV specific could not deal with this in a good
            ;;; way. It only treat any array of type "java.lang.Object" when
            ;;; faced with AASTORE. 
            ;;;
            ;;; Notice that aaload magically put the correct type
            ;;; onto the opstack. For 'magical' to be correct, we
            ;;; rely on array remain consistent be maintained by
            ;;; doing runtime checking at AASTORE!!
          (ADVANCE-PC (set-element-at-array (value-of index) (value-of value)
                                            (rREF array-ref)
                                            (safe-popStack 
                                             (safe-popStack
                                              (safe-popStack s))))))))))




;-- Runtime checking of the AASTORE ----------------------

;
; Note the difference between *-guard and check-* 
; 
; Tue Apr 19 10:10:29 2005


(defun check-AASTORE (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((value (safe-topStack s))
           (index (safe-secondStack s))
           (array-ref (safe-thirdStack s)))
          (and (wff-inst inst)
               (topStack-guard-strong s)
               (secondStack-guard-strong s)
               (thirdStack-guard-strong s)
               (equal (tag-of value)    'REF)
               (equal (tag-of array-ref)    'REF)
               (equal (djvm-translate-int-type (tag-of index)) 'INT)
               (or (equal (rREF value) -1) ;; Sat May  7 22:47:34 2005
                   (not (bound? (rREF value) (heap-init-map (aux s))))
                   (not (consp (deref2-init value (heap-init-map (aux s))))))
               (or (CHECK-NULL array-ref)
                   (and (array-type-s (obj-type (deref2 array-ref (heap s)))
                                      (instance-class-table s))
                        (not (primitive-type? (array-component-type
                                              (obj-type (deref2 array-ref 
                                                                (heap s)))))))))))

;----------------------------------------------------------------------
;----------------------------------------------------------------------


;;; Strive to make sure that the proof of these theorems depend only on lemma
;;; in base-* !!
;;; 

;-- AASTORE-guard implies state consistency perserved -----------------

;; (i-am-here)

(local (encapsulate () 
                   (local (include-book "base-skip-proofs"))
       (defthm raise-exception-consistent-state-strong
             (implies (consistent-state-strong s)
                      (consistent-state-strong (raise-exception any s))))))

(local (in-theory (disable BUILD-A-JAVA-VISIBLE-INSTANCE deref2-init
                             state-set-heap set-element-at)))

(local (include-book "base-update-heap"))
(local (include-book "base-update-array"))




(encapsulate () 
  (defthm AASTORE-guard-implies-execute-AASTORE-perserve-consistency
     (implies (AASTORE-guard inst s)
              (consistent-state-strong (execute-AASTORE inst s)))))





;-- check-AASTORE implies AASTORE-guard in a consistent state ----------

(defthm check-AASTORE-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
                (check-AASTORE inst s))
          (AASTORE-guard inst s)))


;-- BCV::check-AASTORE implies DJVM::check-AASTORE on a corresponding state -----

;; (i-am-here) ;; Tue May 17 23:47:29 2005

(encapsulate ()
 (local (include-book "base-bcv"))
 (defthm bcv-check-AASTORE-ensures-djvm-check-AASTORE
   (implies (and (bcv::check-AASTORE inst (env-sig s) 
                                     (frame-sig  (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s))))
                 (wff-inst inst)
                 (not (mem '*native* (method-accessflags (current-method s))))
                 (consistent-state s))
            (djvm::check-AASTORE inst s))))



;;
;; The function is base-bcv.lisp is to expand (frame-sig ...) when we know
;; consistent-state and bcv::check-* !!! 
;; 
;; this is one of the difficult lemma. We are showing that from tags and
;; consistent-state, we know something about the runtime state.
;; 

;-- BCV::check-AASTORE monotonic   -------------------------------------

;;(i-am-here) ;; Sat Jul 16 19:55:53 2005
;; after introducing some extra lemmas in base-bcv-check-monotonic.lisp
;; for GETFIELD
;; the proof failed for AASTORE and AALOAD (at least)!!


; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate ()
  (local (include-book "base-bcv-check-monotonic"))
  (defthm sig-check-AASTORE-on-more-general-implies-more-specific
    (implies (and (bcv::good-icl icl)
                  (bcv::good-scl (bcv::classtableEnvironment env1))
                  (bcv::sig-frame-more-general gframe sframe env1)
                  (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                  (bcv::consistent-sig-stack (bcV::frameStack sframe) icl)
                  (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL)) ;; added
                  (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
                  (bcv::check-AASTORE inst env1 gframe)
                  (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
             (bcv::check-AASTORE inst env1 sframe))))



; avoided loading base-bcv-check-monotonic.lisp
;-- BCV::execute-AASTORE monotonic  ------------------------------------

(encapsulate () 
   (local (include-book "base-bcv-step-monotonic"))
   (defthm AASTORE-monotonicity
     (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                   (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                   (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                   (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
                   (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL))
                   (bcv::check-AASTORE inst env1 gframe) 
                   (bcv::good-icl icl)
                   (bcv::good-scl (bcv::classtableEnvironment env1))
                   (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
              (bcv::sig-frame-more-general 
               (bcv::normal-frame (bcv::execute-AASTORE inst env1 gframe))
               (bcv::normal-frame (bcv::execute-AASTORE inst env1 sframe)) env1))))

;;;
;;; still missing a big result that an exception frame being related! 
;;;

;;;
;;; note this does not talk about consistent-state at all!! 
;;; 


;-- DJVM::next-state more specific than BCV  ---------------------------

;; (i-am-here) ;; Wed May 18 00:03:46 2005

(encapsulate ()
    (local (include-book "base-frame-sig-expansion"))
    (local (include-book "base-update-heap"))
    (local (include-book "base-bcv-update-heap"))
    (defthm execute-aastore-frame-sig-is
      (mylet* ((ns (execute-aastore inst s))
               (value (topStack s))
               (index (topStack (popStack s)))
               (array-ref (topStack (popStack (popStack s)))))
              (implies 
               (and (consistent-state s)
                    (not (check-NULL array-ref)) 
                    (or (check-NULL value)
                        (car (isAssignableTo (OBJ-TYPE (DEREF2 VALUE (HEAP S)))
                                             (ARRAY-COMPONENT-TYPE
                                              (OBJ-TYPE (DEREF2 ARRAY-REF (HEAP S))))
                                             s)))
                    (check-array (RREF array-ref) (value-of index) s)
                    (check-aastore inst s))
               (equal (frame-sig (current-frame ns)
                                 (instance-class-table ns)
                                 (heap ns)
                                 (heap-init-map (aux ns)))
                      (frame-sig (current-frame (popStack (popStack (popStack s))))
                                 (instance-class-table s)
                                 (heap s)
                                 (heap-init-map (aux s))))))))

;----------------------------------------------------------------------

(encapsulate ()
  (local (include-book "base-bcv-frame-sig-expansion"))
  (defthm bcv-execute-AASTORE-is
    (implies (and 
              (consistent-state s)
              (check-AASTORE inst s)
              (bcv::check-AASTORE inst (env-sig s) 
                                 (frame-sig (current-frame s)
                                            (instance-class-table s)
                                            (heap s)
                                            (heap-init-map (aux s))))
              (not (nullp (topStack (popStack s)))))
             (equal (mv-nth 0 (bcv::execute-AASTORE inst (env-sig s) 
                                                   (frame-sig (current-frame s)
                                                              (instance-class-table s)
                                                              (heap s)
                                                              (heap-init-map (aux s)))))
                     (frame-sig (current-frame (popStack (popStack (popStack s))))
                                (instance-class-table s)
                                (heap s)
                                (heap-init-map (aux s)))))))

;----------------------------------------------------------------------

(encapsulate () 
       (local   (include-book "base-next-state-more-specific"))
       (defthm next-state-no-more-general-aastore
         (mylet* ((oframe (frame-sig (current-frame s)
                                     (instance-class-table s)
                                     (heap s)
                                     (heap-init-map (aux s))))
                  (ns   (execute-aastore inst s))
                  (value (topStack s))
                  (index (topStack (popStack S)))
                  (array-ref (topStack (popStack (popStack s))))
                  (nframe (frame-sig (current-frame ns)
                                     (instance-class-table ns)
                                     (heap ns)
                                     (heap-init-map (aux ns)))))
                 (implies (and (consistent-state s)
                               (bcv::check-aastore inst (env-sig s) oframe)
                               (not (check-null array-ref))
                               (check-array (RREF array-ref) (value-of index) s)
                               (or (check-NULL value)
                                   (car (isAssignableTo (OBJ-TYPE (DEREF2 VALUE (HEAP S)))
                                                        (ARRAY-COMPONENT-TYPE
                                                         (OBJ-TYPE (DEREF2 ARRAY-REF (HEAP S))))
                                                        s)))
                               (check-aastore inst s))
                          (bcv::sig-frame-more-general 
                           (mv-nth 0 (bcv::execute-aastore inst 
                                                           (env-sig s)
                                                           oframe))
                           nframe
                           (env-sig s))))
         :hints (("Goal" :in-theory (disable 
                                     djvm::execute-aastore
                                     bcv::execute-aastore
                                     bcv::isAssignable
                                     check-null)))))
             
;-- M6-DJVM-equal-when-check-succeeds.lisp ------------------------------


(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")


;; Tue Aug  2 17:17:35 2005


;; (encapsulate ()
;;    (local (include-book "base-update-heap"))
;;    (local (include-book "base-untag-state"))
;;    (local 
;;     (defthm rREF-is-value-of
;;       (equal (rREF v)
;;              (value-of v))
;;       :hints (("Goal" :in-theory (enable rREF value-of)))))

;;    (defthm equal-AASTORE-when-guard-succeeds
;;      (implies (AASTORE-guard inst s)
;;               (equal (untag-state (djvm::execute-AASTORE inst s))
;;                      (m6::execute-AASTORE inst (untag-state s))))
;;      :hints (("Goal" :in-theory (enable check-array)
;;               :do-not '(preprocess)))))


;;; some times the equal can't be established!! 
;;;

;;;
;;; We also need additional theorem to show that equiv state, the next step is
;;; still equiv!! 
;;;

;;; then we can prove that M6 starting from untag-state executing arbitrary
;;; number steps, the resulting state is still equiv-state!! 

;; (i-am-here) ;; Tue Aug  2 17:18:41 2005

(encapsulate ()
   (local (include-book "base-state-equiv"))
    (defthm equal-AASTORE-when-guard-succeeds
      (implies (and (AASTORE-guard inst djvm::djvm-s)
                    (state-equiv m6::m6-s djvm::djvm-s))
               (state-equiv (m6::execute-AASTORE inst m6::m6-s)
                            (djvm::execute-AASTORE inst djvm::djvm-s)))))

;----------------------------------------------------------------------

;;(i-am-here) ;; 

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-AASTORE-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-AASTORE inst s)))
           (method-ptr (current-frame s)))))

;;; next need to prove loaded class method-does-not-change! 


(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-AASTORE
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-AASTORE inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))


;----------------------------------------------------------------------
(in-theory (disable check-AASTORE AASTORE-guard execute-AASTORE wff-AASTORE))
