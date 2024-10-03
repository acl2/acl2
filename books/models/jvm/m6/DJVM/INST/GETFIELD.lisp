(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-extra")


(acl2::set-verify-guards-eagerness 2)

;----------------------------------------------------------------------


(defun wff-getfield (inst)
  (wff-one-arg inst))


(defun protectedAccessCheck(inst s)
  (declare (ignore inst s))
  ;; temporary implementation!! 
  t)

;;; Tue Jun  7 13:35:37 2005
;;; to be moved to base-djvm-functions.lisp??


;----------------------------------------------------------------------

;; Tue Jun  7 13:36:16 2005

(defun GETFIELD1-guard (field-rep s)
  (mylet* ((obj-ref   (safe-topStack s))
           (classname (field-classname field-rep))
           (fieldname (field-fieldname field-rep))
           (fieldtype (field-fieldtype field-rep))
           (value     (m6-getfield classname fieldname obj-ref s)))
          (and (wff-field field-rep)
               (topStack-guard-strong s)
               (wff-REFp obj-ref) 
               (consistent-state s)
               (<= (len (operand-stack (current-frame s))) (max-stack s))
               (or (check-NULL obj-ref)
                   (and (or (not  (equal (field-size field-rep) 2))
                            (<= (+ 1 (len (operand-stack (current-frame s))))
                                (max-stack s)))
                        (field-access-guard classname fieldname 
                                            (rREF obj-ref)
                                            s))))))

(defthm wff-getfield-implies-wff-inst
  (implies (wff-getfield inst)
           (wff-inst inst))
  :hints (("Goal" :in-theory (enable wff-getfield)))
  :rule-classes :forward-chaining)

(defthm wff-getfield-implies-len-inst
  (implies (wff-getfield inst)
           (equal (len inst) 2))
  :hints (("Goal" :in-theory (enable wff-getfield)))
  :rule-classes :forward-chaining)


(defthm wff-getfield-implies-len-inst-arg
  (IMPLIES (WFF-GETFIELD INST)
           (EQUAL (LEN (CDR (NTH 1 INST))) 1))
  :hints (("Goal" :in-theory (enable wff-getfield)))
  :rule-classes :forward-chaining)



(defthm wff-inst-implies-truelistp
  (implies (wff-inst inst)
           (true-listp inst))
  :hints (("Goal" :in-theory (enable wff-inst)))
  :rule-classes :forward-chaining)


(defthm wff-inst-implies-truelistp
  (implies (wff-inst inst)
           (true-listp inst))
  :hints (("Goal" :in-theory (enable wff-inst)))
  :rule-classes :forward-chaining)

(defthm wff-inst-implies-car-integerp
  (implies (wff-inst inst)
           (integerp (car inst)))
  :hints (("Goal" :in-theory (enable wff-inst)))
  :rule-classes :forward-chaining)

(defthm wff-inst-implies-true-listp-arg
  (implies (wff-inst inst)
           (true-listp (nth 1 inst)))
  :hints (("Goal" :in-theory (enable wff-inst)))
  :rule-classes :forward-chaining)


(defthm wff-inst-implies-consp-arg
  (implies (wff-inst inst)
           (consp (nth 1 inst)))
  :hints (("Goal" :in-theory (enable wff-inst)))
  :rule-classes :forward-chaining)


(defthm wff-inst-implies-consp-arg
  (implies (wff-inst inst)
           (consp (nth 1 inst)))
  :hints (("Goal" :in-theory (enable wff-inst)))
  :rule-classes :forward-chaining)


(local (in-theory (disable current-frame-guard 
                           max-stack-guard
                           fieldcp-classname
                           fieldcp-fieldname
                           fieldcp-fieldtype
                           fieldcp-to-field-ptr
                           wff-getfield
                           FIELD-CLASSNAME
                           FIELD-FIELDNAME
                           FIELD-FIELDTYPE
                           wff-fieldCP
                           wff-field
                           lookupField
                           deref-field
                           java-visible-portion
                           pending-exception
                           pending-exception-aux
                           field-size
                           resolveClassReference-guard)))


;;; to be moved into base-consistent-state !!! 

;; (defun GETFIELD-guard (inst s)
;;   (mylet* ((obj-ref (safe-topStack s))
;;            (fieldCP (arg inst)))
;;           (and (wff-getfield inst)
;;                (wff-fieldCP fieldCP)
;;                (consistent-state s)
;;                (topStack-guard-strong s)
;;                (not (mem '*abstract* (method-accessflags (current-method s))))
;;                (not (mem '*native* (method-accessflags (current-method s))))
;;                (resolveClassReference-guard s)
;;                (protectedAccessCheck inst s)
;;                (wff-REFp obj-ref)
;;                (mv-let (field-rep new-s)
;;                        (resolveFieldReference (arg inst) s)
;;                        (or (not field-rep)
;;                            (or (CHECK-NULL obj-ref)
;;                                (and (REFp obj-ref (heap new-s))
;;                                     (or (not (isArrayType 
;;                                               (obj-type (deref2 obj-ref (heap new-s)))))
;;                                         (equal (fieldcp-classname fieldCP) "java.lang.Object"))
;;                                     (mv-let (assignable new-s2)
;;                                             (isAssignableTo (obj-type (deref2 obj-ref (heap new-s)))
;;                                                             (fieldCP-classname fieldCP) new-s)
;;                                             (and assignable
;;                                                  (or (and (equal (field-size field-rep) 2)
;;                                                           (<= (+ 1 (len (operand-stack 
;;                                                                          (current-frame new-s2))))
;;                                                               (max-stack new-s2)))
;;                                                      (and (equal (field-size field-rep) 1)
;;                                                           (<= (len (operand-stack (current-frame new-s2)))
;;                                                               (max-stack new-s2)))))))))))))

;;;
;;; modify the above guard!! 
;;; check things in order. otherwise the guard does not verify!  
;;; 

;;
;;(i-am-here) ;; Thu Jul 28 20:14:43 2005
;;

;;
;; need to show that lookupfield if found then wff-field
;;
  
(include-book "base-consistent-state-load-class")
(include-book "base-consistent-state-lookupfield")

(defun GETFIELD-guard (inst s)
  (mylet* ((obj-ref (safe-topStack s))
           (fieldCP (arg inst)))
          (and (wff-getfield inst)
               (wff-fieldCP fieldCP)
               (consistent-state-strong s)
               (topStack-guard-strong s)
               (not (mem '*abstract* (method-accessflags (current-method s))))
               (not (mem '*native* (method-accessflags (current-method s))))
               (resolveClassReference-guard s)
               (protectedAccessCheck inst s)
               (wff-REFp obj-ref)
               (or (mv-let (field-rep new-s)
                           (resolveFieldReference (arg inst) s)
                           (declare (ignore new-s))
                           (not field-rep))  
                   ;; if the field does not exist
                   ;; then we won't assert anything! 
                   (or (CHECK-NULL obj-ref)
                       (and (REFp obj-ref (heap s))
                            ;; (not (isArrayType 
                            ;;       (obj-type (deref2 obj-ref (heap s)))))
                            ;; Fri May 12 15:59:21 2006??? 
                            ;; with this, our theorem does not prove! 
                            ;; 

                            ;; Mon Jun 20 13:49:47 2005 ... 
                            ;; (equal (fieldcp-classname fieldCP) "java.lang.Object"))
                            ;; JVM spec is slightly wrong. checked Thu Jun 16 14:22:38 2005
                            ;; added Thu Jun  9 18:10:51 2005
                            ;; check with JVM Spec. 
                            (mv-let (assignable new-s)
                                    (isAssignableTo (obj-type (deref2 obj-ref (heap s)))
                                                    (fieldCP-classname fieldCP) s)
                                    (declare (ignore new-s))
                                    assignable) ;; add a new assignable
                       ;;;
                       ;;; this is interesting!! 
                       ;;; Fri Jun 17 15:24:21 2005.
                       ;;; because we know if a field is ever found 
                       ;;; it is always assignable!!! Assuming that a object
                       ;;; exists. 
                       ;;; 
                       ;;;
                       ;;; Fri Jun 17 15:25:29 2005. 
                       ;;;
                       ;;; If it is found, we know FIELDCP-class/interface is a
                       ;;; subclass of the resulting class. 
                       ;;;
                       ;;; If here is assignable ...  Mon Jun 20 13:27:43
                       ;;; 2005!!! 
         
                                ;; requirement.
                                ;; we might checked isSuperClass.... 
                                ;; ....  ;; Sat Jun 11 22:13:57 2005
               ;; We should check the isAssignable 
               ;; after resolving the class... 
               ;;  
               ;; Do we? The Bytecode verifier will guarantee 
               ;; that it is in fact assignable. 
               ;; and that class exists!! 
               ;; and resolveFieldReference reduces to a read only lookup. It
               ;; will not change the JVM state!!! 
                            (mv-let (field-rep new-s)
                                    (resolveFieldReference (arg inst) s)
                                    (declare (ignore new-s))
                                    (or (and (equal (field-size field-rep) 2)
                                             (<= (+ 1 (len (operand-stack 
                                                            (current-frame s))))
                                                 (max-stack s)))
                                        (and (equal (field-size field-rep) 1)
                                             (<= (len (operand-stack (current-frame s)))
                                                 (max-stack s)))))))))))



;----------------------------------------------------------------------

(defun execute-getfield1 (field-rep s)
  (declare (xargs :guard (GETFIELD1-guard field-rep s)))
  (mylet* ((obj-ref   (safe-topStack s))
           (classname (field-classname field-rep))
           (fieldname (field-fieldname field-rep))
           (fieldtype (field-fieldtype field-rep))
           (value     (m6-getfield classname fieldname (rREF obj-ref) s)))
         (if (CHECK-NULL obj-ref)
             (state-set-pending-exception-safe "java.lang.NullPointerException" s)
           (if (equal (field-size field-rep) 2)
               (safe-pushCategory2 (tag value fieldtype) (popStack s))
             (safe-pushStack (tag value fieldtype) (popStack s))))))



(include-book "base-load-class-normalize")
(include-book "base-judgement-after-load-class-no-change")

;;; take quite some efforts to reason about class loading and why guard is
;;; true! for these operations!! 

(encapsulate () 
  (local (include-book "base-skip-proofs"))
   (defthm raise-exception-consistent-state-strong
     (implies (consistent-state-strong s)
              (consistent-state-strong (raise-exception any s)))))


(include-book "base-consistent-state-consistent-object")



(encapsulate ()
 (local (include-book "base-load-class-normalize-when-found"))
 (defthm resolveClassReference-no-change-if-already-loaded-if-not-array-Object
   (implies (and (consistent-object obj (heap s) (instance-class-table s))
                 (case-split (not (isArrayType (obj-type obj))))
                 (car (isAssignableTo (obj-type obj) typ2 s))
                 (consistent-state s))
            (equal (resolveClassReference typ2 s) s)))

 (defthm resolveClassReference-java-lang-Object-no-change
   (implies (consistent-state s)
            (equal (resolveClassReference "java.lang.Object" s) s))
   :hints (("Goal" :in-theory (e/d (resolveClassReference 
                                    class-loaded?)
                                   (isClassTerm))))))

;; (i-am-here) ;; Thu Jun 16 21:58:50 2005

(in-theory (disable m6-getfield jvm::jvp-access-field-guard))


(encapsulate () 
  (local (include-book "base-consistent-state-make-state-general"))
  (defthm consistent-state-make-state-x-general
    (implies (and (consistent-state s)
                  (equal (pc s) pc)
                  (equal (heap-init-map (aux s)) (heap-init-map aux))
                  (equal (heap s) hp)
                  (equal (thread-table s) tt)
                  (equal (env s) env)
                  (or err
                      (equal (error-flag s) err))
                  (equal (current-thread s) cid))
             (consistent-state (make-state pc 
                                           cid 
                                           hp 
                                           tt
                                           (class-table s)
                                           env
                                           err
                                           aux)))))


(defthm resolveClassReference-no-change-if-already-loaded-specific-further
  (implies (and (consistent-object (deref2 (topStack s) (heap s)) (heap s) (instance-class-table s))
                (case-split (not (isArrayType (obj-type (deref2 (topStack s) (heap s))))))
                (car (isAssignableTo (obj-type (deref2 (topStack s) (heap s)))
                                     (FIELDCP-CLASSNAME fieldcp)
                                     s))
                (consistent-state s))
           (equal (resolveClassReference 
                   (fieldcp-classname fieldcp) s) s)))


(defun execute-getfield (inst s)
  (declare (xargs :guard (GETFIELD-guard inst s)))
   (mylet* ((fieldCP (arg inst)))
    (mv-let (field-rep new-s)
            (resolveFieldReference fieldCP s)
            (if (not (no-fatal-error? new-s)) new-s
              ;; should not be an efficiency issue. 
              ;; the issue here is that we know 
              ;; if guard succeed, there will be no-fatal-error?
              ;; because when guard succed.
              ;; resolveClassReference will return a same state!! 
              (if (pending-exception s)
                  (raise-exception (pending-exception s) s)
                (if field-rep  
                    ;; if resolve failed, field-rep is nil
                    ;; may need to be changed to assert
                    ;; wff-field-rep. Fri Mar 11 15:45:10 2005 
                    (let ((new-s2 (execute-getfield1 field-rep new-s))) 
                      (if (pending-exception new-s2)
                          (raise-exception (pending-exception new-s2) new-s2)
                        (ADVANCE-PC new-s2))) 
                  (fatalSlotError fieldCP new-s)))))))
;;;
;;; take much more than we expected to even to get execute-getfield guard
;;; verified!!
;;;
;;; prove an implementation is correct. it does not violate its internal
;;; assertions!! 
;;;
;;; GETFIELD is a good example! m6-getfield needs a strong guard. 
;;;
;;;

;----------------------------------------------------------------------


;;(i-am-here) ;; Sun Jun 12 23:32:19 2005

;;(in-theory (disable m6-getfield))

(encapsulate ()
   (local (include-book "base-consistent-object-m6-getfield"))
   (defthm consistent-object-consistent-state-m6-getfield-consistent-value-x
     (implies (and (consistent-state s)
                   (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                        (fieldcp-classname fieldCP)
                                        s))
                   (REFp v (heap s))
                   (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                        S))
                          classname)
                   (lookupField (fieldcp-to-field-ptr fieldCP) s)
                   (not (NULLp v)))
              (CONSISTENT-VALUE-X
               (TAG (M6-GETFIELD classname
                     (fieldcp-fieldname fieldcp)
                     (RREF v)
                     S)
                    (fieldcp-fieldtype fieldcp))
               (INSTANCE-CLASS-TABLE S)
               (HEAP S)))))


(defthm if-type-size-2-category2
  (implies (and (not (consp v))
                (EQUAL (type-size type)
                       2))
           (category2 (tag v type)))
  :hints (("Goal" :in-theory (enable tag-of tag wff-tagged-value))))

(defthm if-type-size-1-category1
  (implies (and (not (consp v))
                (EQUAL (type-size type)
                       1))
           (category1 (tag v type)))
  :hints (("Goal" :in-theory (enable tag-of tag category1 wff-tagged-value))))


(defthm consistent-value-x-tag-imlplies-not-consp
  (implies (consistent-value-x (tag v type) cl hp)
           (not (consp v)))
  :hints (("Goal" :in-theory (enable consistent-value-x 
                                     rREF wff-REFp tag
                                     tag-of
                                     wff-tagged-value
                                     REFp consistent-value 
                                     value-of))))
                                     

(defthm consistent-value-x-tag-imlplies-not-consp-specific
  (implies (consistent-value-x (tag (m6-getfield classname
                                                 (FIELDCP-FIELDNAME fieldcp)
                                                 v 
                                                 s)
                                    (fieldcp-fieldtype fieldcp))
                               (instance-class-table s) 
                               (heap s))
           (not (consp (m6-getfield classname
                                    (FIELDCP-FIELDNAME fieldcp)
                                    v 
                                    s))))
  :hints (("Goal" :in-theory (enable consistent-value-x 
                                     rREF wff-REFp tag
                                     tag-of
                                     wff-tagged-value
                                     REFp consistent-value 
                                     value-of))))
                                     



(encapsulate ()
  (local (include-book "base-consistent-state-pushCategory2"))
  (DEFTHM
    CONSISTENT-STATE-PUSHSTACK-CONSISTENT-STATE-PUSHSTACK-2
    (IMPLIES (AND (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
                                      (HEAP S))
                  (CATEGORY2 V)
                  (<= (+ 2
                         (LEN (OPERAND-STACK (CURRENT-FRAME S))))
                      (MAX-STACK S))
                  (CONSISTENT-STATE S))
             (CONSISTENT-STATE (PUSHSTACK V (pushStack '(topx . topx) S))))))



(encapsulate () 
   (local (include-book "base-frame-sig-expansion"))
   (defthm object-field-is-always-initialized-m6-getfield
     (implies (and (case-split (not (primitive-type?
                                     (fieldcp-fieldtype fieldcp))))
                   (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                   (consistent-state s)
                   (consistent-object-init-state 
                    (deref2 v (heap s))
                    (instance-class-table s) (heap-init-map (aux s)))
                   (consistent-object (deref2 v (heap s))
                                      (heap s)
                                      (instance-class-table s))
                   (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                        (fieldcp-classname fieldcp) s)))
              (not (consp (deref2-init 
                           (tag (m6-getfield 
                                 (field-classname (lookupfield
                                                   (fieldcp-to-field-ptr fieldcp)
                                                   s))
                                 (fieldcp-fieldname fieldcp) 
                                 (rREF v) s)
                                (fieldcp-fieldtype fieldcp))
                           (heap-init-map (aux s))))))))

;; (i-am-here) ;; Sun Aug  7 23:13:33 2005

(encapsulate () 
  (local 
   (defthm tag-tag-ref-reduce
     (implies (not (primitive-type? type))
              (equal (tag v type)
                     (tag-REF v)))
     :hints (("Goal" :in-theory (enable tag tag-ref)))))

 (defthm not-primitive-deref2-init-specific
  (implies (and (case-split (not (primitive-type? (FIELDCP-FIELDtype (ARG INST)))))
                (NOT
                 (CONSP
                  (DEREF2-INIT
                   (TAG
                    (M6-GETFIELD
                     (FIELD-CLASSNAME
                      (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR (ARG INST)) s))
                     (FIELDCP-FIELDNAME (ARG INST))
                     (RREF (TOPSTACK S))
                     S)
                    (FIELDCP-FIELDTYPE (ARG INST)))
                   (HEAP-INIT-MAP (AUX S))))))
           (not (consp (deref2-init 
                        (TAG-REF 
                         (M6-GETFIELD
                          (FIELD-CLASSNAME
                           (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR (ARG INST)) s))
                          (FIELDCP-FIELDNAME (ARG INST))
                          (RREF (TOPSTACK S))
                          s))
                        (heap-init-map (aux s))))))))


(in-theory (disable category2))
(in-theory (e/d (field-size) (type-size)))

(include-book "base-m6-getfield-consistent-value")


(defthm GETFIELD-guard-implies-execute-GETFIELD-perserve-consistency
  (implies (GETFIELD-guard inst s)
           (consistent-state-strong (execute-GETFIELD inst s)))
  :hints (("Goal" :cases ((isArrayType (obj-type (deref2 (topstack s) 
                                                         (heap s))))))))

;----------------------------------------------------------------------

;;
;; (defun check-AASTORE (inst s)
;;   (declare (xargs :guard (consistent-state s)))
;;   (declare (ignore inst))
;;   (mylet* ((value (safe-topStack s))
;;            (index (safe-secondStack s))
;;            (array-ref (safe-thirdStack s)))
;;           (and (topStack-guard-strong s)
;;                (secondStack-guard-strong s)
;;                (thirdStack-guard-strong s)
;;                (equal (tag-of value)    'REF)
;;                (equal (tag-of array-ref)    'REF)
;;                (equal (tag-of index) 'INT)
;;                (or (equal (rREF value) -1) ;; Sat May  7 22:47:34 2005
;;                    (not (bound? (rREF value) (heap-init-map (aux s))))
;;                    (not (consp (deref2-init value (heap-init-map (aux s))))))
;;                (or (CHECK-NULL array-ref)
;;                    (and (array-type-s (obj-type (deref2 array-ref (heap s)))
;;                                       (instance-class-table s))
;;                         (not (primitive-type? (array-component-type
;;                                               (obj-type (deref2 array-ref 
;;                                                                 (heap s)))))))))))

;; old definition of check-AASTORE!! modified extensively during the proof
;; discovered problems about assertion! 
;; 
;; Mon Jul 25 17:12:24 2005
;;

;;(i-am-here) ;; Tue Jun 14 21:40:16 2005


(defthm consistent-state-implies-resolveClassReference-guard
  (implies (and (consistent-state s)
                (topStack-guard-strong s))
           (resolveClassReference-guard s))
  :hints (("Goal" :in-theory (enable resolveClassReference-guard))))



(defun check-GETFIELD (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((obj-ref (safe-topStack s))
           (fieldCP (arg inst)))
          (and (wff-getfield inst)
               (wff-fieldCP fieldCP)
               (consistent-state s)
               (topStack-guard-strong s)
               (equal (tag-of obj-ref) 'REF)
               (protectedAccessCheck inst s) 
               ;;; need to assert that field can be found!! 
               (or (mv-let (field-rep new-s)
                       (resolveFieldReference (arg inst) s)
                       (declare (ignore new-s))
                       (not field-rep))
                   (or (equal (rREF obj-ref) -1)
                       (and (or (not (isArrayType (obj-type (deref2 obj-ref (heap
                                                                             s)))))
                                (equal (fieldcp-classname fieldcp) 
                                       "java.lang.Object"))
                            (mv-let (assignable new-s)
                                    (isAssignableTo (obj-type (deref2 obj-ref (heap s)))
                                                    (fieldCP-classname fieldCP)
                                                    s)
                                    (declare (ignore new-s))
                                    assignable)
                            (or (and (equal (type-size (fieldcp-fieldtype fieldCP)) 1)
                                     (<= (len (operand-stack (current-frame s)))
                                         (max-stack s)))
                                (and (equal (type-size (fieldcp-fieldtype fieldCP)) 2)
                                     (<= (+ 1 (len (operand-stack (current-frame s))))
                                         (max-stack s))))))))))


;----------------------------------------------------------------------



(defthm check-GETFIELD-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
               (check-GETFIELD inst s))
          (GETFIELD-guard inst s)))


;----------------------------------------------------------------------


;-- BCV::check-GETFIELD implies DJVM::check-GETFIELD on a corresponding state -----

(encapsulate ()
 (local (include-book "base-bcv"))
 (local (include-book "base-bcv-djvm-getfield"))
 ;;
 ;; the most difficult part is to relate how BCV::isAssignable relates to to
 ;; DJVM::isAssignableTo
 ;;
 ;; The insight is that when fieldcp-classname is not 'java.lang.Object' nor
 ;; some interface type (and both type is loaded) These two different judgement
 ;; matches
 ;;
 ;; So we also need to spend efforts in showing when lookupfields succeeds 
 ;; then we can conclude that the fieldcp-classname is not java.lang.Object. 
 ;; 
 ;; A second thing is to show about every type is assignable to
 ;; 'java.lang.Object' if it is a type of some object that exists in a
 ;; consistent-state!
 ;;
 (defthm bcv-check-GETFIELD-ensures-djvm-check-GETFIELD
   (implies (and (bcv::check-GETFIELD inst (env-sig s) 
                                     (frame-sig  (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s))))
                 (wff-getfield inst)
                 (wff-fieldCP (arg inst))
                 (no-fatal-error? s)
                 ;;; need to assert that field is found!! 
                 ;;; otherwise this is not true!! Mon Jul 11 14:58:41 2005
                 (lookupField (fieldcp-to-field-ptr (arg inst)) s)
                 (not (mem '*native* (method-accessflags (current-method s))))
                 (consistent-state s))
            (djvm::check-GETFIELD inst s))
; Matt K. mod: Subgoal number changed from 10 to 5.
   :hints (("Subgoal 5" :cases ((isInterface (class-by-name (fieldcp-classname
                                                              (arg inst))
                                                             (instance-class-table s))))))))

;; Mon Aug 29 21:19:50 2005
;;
;; value-sig is complicated. It depends on the initialization Status!! 
;;

;-- BCV::check-GETFIELD monotonic   -------------------------------------

;;; A few important to steps:


; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate ()
    (local (include-book "base-bcv-check-monotonic"))
    (local (in-theory (disable bcv::good-scl)))
    (defthm sig-check-GETFIELD-on-more-general-implies-more-specific
      (implies (and (bcv::good-icl icl)
                    (bcv::sig-frame-more-general gframe sframe env1)
                    (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                    (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                    (bcv::good-java-type (bcv::fieldtypecp (bcv::arg1 inst)) icl)
                    (bcv::good-java-type 
                     (bcv::prefix-class
                      (bcv::fieldclassnamecp (bcv::arg1 inst))) icl)
                    (bcv::good-java-type 
                     (bcv::prefix-class
                      (bcv::classClassname (bcv::classenvironment env1))) icl)
                    (bcv::good-scl (bcv::classtableEnvironment env1))
                    (bcv::check-GETFIELD inst env1 gframe)
                    (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
               (bcv::check-GETFIELD inst env1 sframe))
      :hints (("Goal" :in-theory (e/d () (bcv::classenvironment bcv::classClassname))))))

;;
;; have to introduce extra concept such as good-java-type ...
;; because of the definition of bcv::isAssignable
;; it is transitive only on certain types!
;; 

;----------------------------------------------------------------------


;-- BCV::execute-GETFIELD next step  monotonic ---------------------------

(encapsulate () 
     (local (include-book "base-bcv-step-monotonic"))
     (defthm GETFIELD-monotonicity
       (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                     (bcv::check-GETFIELD inst env1 gframe) 
                     (bcv::check-GETFIELD inst env1 sframe) 
                     (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
                     (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
                     (bcv::good-icl icl)
                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
                (bcv::sig-frame-more-general 
                 (bcv::normal-frame (bcv::execute-GETFIELD inst env gframe))
                 (bcv::normal-frame (bcv::execute-GETFIELD inst env sframe))
                 env1))))



;----------------------------------------------------------------------


;-- DJVM::next-state more specific than BCV  ---------------------------

;; starting from a same state. 

;; (i-am-here) ;; Fri Jul 22 20:36:49 2005

(encapsulate () 
  (local (include-book "base-frame-sig-expansion"))
  (defthm execute-GETFIELD-frame-sig-is
    (mylet* ((ns (execute-GETFIELD inst s))
             (field-rep (car (resolveFieldReference (arg inst) s)))
             (classname (jvm::field-classname field-rep))
             (fieldname (jvm::field-fieldname field-rep))
             (fieldtype (jvm::field-fieldtype field-rep)))
            (implies 
             (and (consistent-state s)
                  (not (pending-exception (resolveClassReference 
                                           (normalize-type-rep (fieldcp-classname 
                                                                (arg inst))) s)))
                  (not (pending-exception (mv-nth 1 (resolveFieldReference (arg inst) S))))
                  (not (NULLp (topStack s)))
                  (no-fatal-error? (mv-nth 1 (resolveFieldReference (arg inst) s)))
                  (car (resolveFieldReference (arg inst) S))
                  (NO-FATAL-ERROR? (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
                                                          S))
                  (check-GETFIELD inst s))
             (equal (frame-sig (current-frame ns)
                               (instance-class-table ns)
                               (heap ns)
                               (heap-init-map (aux ns)))
                    (frame-push-value-sig-g (value-sig (tag (m6-getfield classname fieldname 
                                                                         (rREF (topStack s))
                                                                         s)
                                                            fieldtype)
                                                       (instance-class-table s)
                                                       (heap s)
                                                       (heap-init-map (aux s))
                                                       (method-ptr (current-frame s)))
                                            (frame-sig (current-frame (popStack s))
                                                       (instance-class-table s)
                                                       (heap s)
                                                       (heap-init-map (aux s)))))))
    :hints (("Goal" :in-theory (e/d (frame-push-value-sig-g frame-push-value-sig)
                                    (get-field-type
                                     consistent-object-init-state
                                     ))
             :cases ((not (primitive-type? (fieldcp-fieldtype 
                                            (arg inst))))))
            ("Subgoal 1" :cases ((NULLp 
                                  (TAG
                                   (M6-GETFIELD
                                    (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR (ARG INST))
                                                                  S))
                                    (FIELDCP-FIELDNAME (ARG INST))
                                    (RREF (TOPSTACK S))
                                    S)
                                   (FIELDCP-FIELDTYPE (ARG INST)))))))))

;;; We have adequate rules to simplify when the field-type is primitive-type?
;;; when the value is a NULL pointer
;;; when the value is a valid-pointer into the heap
;;;
;;; We show that the value is a consistent-value !!! <------- this is the most
;;; important part. in base-consistent-object-m6-getfield.lisp 

;;; Fri Jul 22 11:47:48 2005
;;; Wed Jul 20 15:16:05 2005
;;; Tue Jul 19 21:52:29 2005
;;;
;;;
;----------------------------------------------------------------------

;; (i-am-here) ;; Sat Jul 23 20:08:54 2005

(encapsulate () 
 (local (include-book "base-bcv-frame-sig-expansion"))
 (defthm bcv-execute-GETFIELD-is
   (implies (and (consistent-state s)
                 (not (pending-exception (resolveClassReference 
                                          (normalize-type-rep (fieldcp-classname 
                                                               (arg inst))) s)))
                 (not (pending-exception (mv-nth 1 (resolveFieldReference (arg inst) S))))
                 (not (NULLp (topStack s)))
                 (no-fatal-error? (mv-nth 1 (resolveFieldReference (arg inst) s)))
                 (car (resolveFieldReference (arg inst) S))
                 (NO-FATAL-ERROR? (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
                                                         S))
                 (check-GETFIELD inst s)
                 (bcv::check-GETFIELD inst (env-sig s) 
                                      (frame-sig (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s)))))
            (equal (car  (bcv::execute-GETFIELD
                          inst (env-sig s) 
                          (frame-sig (current-frame s)
                                     (instance-class-table s)
                                     (heap s)
                                     (heap-init-map (aux s)))))
                   (frame-push-value-sig-g (djvm-translate-int-type (bcv::fieldtypecp (arg inst)))
                                           (frame-sig (current-frame (popStack s))
                                                      (instance-class-table s)
                                                      (heap s)
                                                      (heap-init-map (aux
                                                                      s))))))
   :hints (("Goal" :in-theory (e/d () 
                                   (bcv::prefix-class
                                    bcv::translate-type
                                    normalize-type-rep))))))



;;----------------------------------------------------------------------
;;
;; Sat Jul 23 19:13:15 2005
;;
;; (i-am-here) ;; Mon Jul 25 19:58:21 2005
;; Mon Jul 25 19:59:39 2005

;; (i-am-here) ;; Tue Jul 26 01:15:05 2005

(local (include-book "base-next-state-more-specific"))

;;                           (WFF-TYPE-REP (BCV::FIELDTYPECP (ARG INST)))
;;                           (bcv::good-java-type (bcv::fieldtypecp (arg inst))
;;                                                (instance-class-table s))
;;                           (or (primitive-type? type)
;;                               (NULLp tagged-value)
;;                               (not (consp (deref2-init tagged-value (heap-init-map (aux s)))))))


(encapsulate () 
  (local (in-theory (disable BCV-FRAME-STACK-FRAME-SIG-IS-OPSTACK-SIG-specific)))
  (defthm next-state-no-more-general-GETFIELD
    (mylet* ((oframe (frame-sig (current-frame s)
                                (instance-class-table s)
                                (heap s)
                                (heap-init-map (aux s))))
             (ns   (execute-GETFIELD inst s))
             (nframe (frame-sig (current-frame ns)
                                (instance-class-table ns)
                                (heap ns)
                                (heap-init-map (aux ns)))))
            (implies (and (consistent-state s)
                          (not (< (value-of (topStack s)) 0))
                          (not (pending-exception s))
                          (no-fatal-error? s)
                          (not (NULLp (topStack s)))
                          (no-fatal-error? (mv-nth 1 (resolveFieldReference (arg inst) s)))
                          (car (resolveFieldReference (arg inst) S))
                          (NO-FATAL-ERROR? (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
                                                                  S))
                          (not (pending-exception (resolveClassReference
                                                   (normalize-type-rep 
                                                    (fieldcp-classname (arg
                                                                        inst))) s)))
                          (bcv::check-GETFIELD inst (env-sig s) oframe)
                          (check-GETFIELD inst s))
                     (bcv::sig-frame-more-general 
                      (mv-nth 0 (bcv::execute-GETFIELD
                                 inst 
                                 (env-sig s)
                                 oframe))
                      nframe
                      (env-sig s))))
    :hints (("Goal" :in-theory (disable execute-GETFIELD 
                                        bcv::execute-GETFIELD)))))

;----------------------------------------------------------------------




(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")

;; (i-am-here) ;; Tue Jul 26 20:40:27 2005

;; (local (include-book "base-untag-state"))

;; ;; (encapsulate ()
;; ;;    (defthm equal-GETFIELD-when-guard-succeeds
;; ;;      (implies (GETFIELD-guard inst s)
;; ;;               (equal (untag-state (djvm::execute-GETFIELD inst s))
;; ;;                      (m6::execute-GETFIELD inst (untag-state s))))))

;; ;; ;;
;; ;; ;; need to fix the untag-value!!! Tue Jul 26 02:00:00 2005
;; ;; ;;

;;(i-am-here) ;; Tue Aug  2 17:30:00 2005

;; (i-am-here) ;; Fri May 12 17:47:18 2006

(encapsulate ()
   (local (include-book "base-state-equiv"))
   (defthm equal-GETFIELD-when-guard-succeeds
      (implies (and (state-equiv M6::m6-s DJVM::djvm-s)
                    (GETFIELD-guard inst DJVM::djvm-s))
               (state-equiv (m6::execute-GETFIELD inst M6::m6-s)
                            (djvm::execute-GETFIELD inst DJVM::djvm-s)))
      :hints (("Goal" :do-not '(generalize fertilize)))))


;; Tue Aug  2 17:47:59 2005

;;;
;;; AT LAST!! 
;;;
;----------------------------------------------------------------------

;;(i-am-here) ;; Mon Aug 15 21:55:06 2005

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-GETFIELD-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-GETFIELD inst s)))
           (method-ptr (current-frame s)))))

(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-GETFIELD
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-GETFIELD inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))

;----------------------------------------------------------------------
(in-theory (disable check-GETFIELD GETFIELD-guard execute-GETFIELD wff-getfield))


