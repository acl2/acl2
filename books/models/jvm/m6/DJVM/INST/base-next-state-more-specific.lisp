(in-package "DJVM")

(include-book "base")
(include-book "base-bind-free")
(include-book "base-consistent-state")
(include-book "base-djvm-functions")



(include-book "base-frame-sig-expansion")
(include-book "base-bcv-frame-sig-expansion")



(encapsulate ()
   (local (include-book "base-bcv-check-monotonic-support"))
   (defthm pushOperandStack-TypeListAssignable
     (implies (and (bcv::TypeListAssignable sL gL env)
                   (not (equal g 'topx))
                   (bcv::isAssignable s g env))
              (bcv::TypeListAssignable (bcv::pushOperandStack s sL)
                                       (bcv::pushOperandStack g gL) env))))



;; we have rules to reduce value-sig into fix-sig
;; we only ned to say that fix-sig does not equal 'bcv::top

(defthm fix-sig-never-top
  (not (equal (fix-sig type) 'topx))
  :hints (("Goal" :in-theory (enable fix-sig))))



;; sig-frame-more-general 
;; also assert about the len of opstack
;; we need to show (len (bcv::frameStack (frame-push-value-sig .... ...)))
;;

;; (i-am-here) ;; Fri Jul 22 12:54:14 2005

;; after modification in base.lisp and base-frame-sig-expansion.lisp
;; here is a loop

(in-theory (disable BCV-MAKE-SIG-FRAME-NORMALIZE))

(local (in-theory (enable push)))

(defthm bcv-frame-Stack-frame-push-value-normalize
  (implies (and (equal (bcv::sizeof type) 1)
                (not (equal type 'void)))
           (equal (BCV::FRAMESTACK
                   (FRAME-PUSH-VALUE-SIG type
                                         (FRAME-SIG frame cl hp hp-init)))
                  (bcv::pushoperandstack type 
                                         (opstack-sig (operand-stack frame)
                                                      cl hp hp-init
                                                      (method-ptr frame)))))
  :hints (("Goal" :in-theory (enable frame-push-value-sig bcv::pushoperandstack))))


(defthm fix-sig-never-void
  (not (equal (fix-sig any) 'void))
  :hints (("Goal" :in-theory (enable fix-sig))))




(encapsulate ()
   (local (include-book "base-bcv-check-monotonic-support"))
   (defthm len-equal-pushOperand-stack
     (implies (and (equal (bcv::sizeof y) (bcv::sizeof x))
                   (not (equal x 'void))
                   (not (equal y 'void)))
              (equal (equal (len (bcv::pushOperandStack x stk))
                            (len (bcv::pushOperandStack y stk))) t))
     :hints (("Goal" :in-theory (enable bcv::pushOperandStack)))))


;; the way for getting bcv::sizeof being equal 
;; both rewriting them into 1. 
;; 


;----------------------------------------------------------------------


;;; (i-am-here) ;; Tue May 17 14:40:58 2005

(encapsulate () 
 (local (include-book "base-consistent-state-more"))
 (defthm fix-sig-size-1
   (implies (consistent-state s)
            (equal (bcv::sizeof (fix-sig (obj-type (deref2 v (heap s))))) 1))))




;----------------------------------------------------------------------

;; Specific for Array value


(encapsulate () 
 (local (include-book "base-bcv-djvm-assignable"))
 (defthm Array-element-type-is-more-specific-than-type-declaration
   (implies  (and (consistent-state s)
                  (not (NULLp (TAG-REF (ELEMENT-AT-ARRAY index (RREF v) S))))
                  (isArrayType (obj-type (deref2 v (heap s))))
                  (REFp v (heap s))
                  (not (NULLp v))
                  (not (primitive-type? 
                        (array-component-type (obj-type (deref2 v (heap s))))))
                  (check-array (rREF v) index s))
             (bcv::isAssignable
              (fix-sig (obj-type (deref2 (TAG-REF (ELEMENT-AT-ARRAY index (RREF v) S))
                                         (heap s))))
              (fix-sig (array-component-type 
                        (obj-type (deref2 v (heap s)))))
              (env-sig s)))))


(encapsulate () 
 (local (include-book "base-bcv-support"))
 (defthm TypeListAssignable-reflexive
   (bcv::typelistassignable anylist anylist env)))


(encapsulate ()
 (local (include-book "base-bcv-djvm-assignable"))
 (defthm isAssignable-NULL-not-primitive-type-specific
   (implies (and (not (primitive-type? type))
                 (bcv::good-java-type type (instance-class-table s))
                 (bcv::icl-scl-compatible (instance-class-table s)
                                          (bcv::classtableenvironment (env-sig s))))
            (bcv::isAssignable 'NULL type (env-sig s)))))



;; (defthm reference-type-s-implies-good-java-type
;;   (implies (and (reference-type-s type cl)
;;                 (consistent-class-table cl scl hp)
;;                 (not (equal type 'NULL)))
;;            (bcv::good-java-type (fix-sig type) cl))
;;   :hints (("Goal" :induct (bcv::good-java-type (fix-sig type) cl)
;;            :do-not '(generalize)
;;            :in-theory (e/d (array-type-s) (consistent-class-table
;;                                            component-type)))))

(local 
 (encapsulate () 
   (local (include-book "base-reference-type-s-good-java-type"))
   (defthm reference-type-s-implies-good-java-type
     (implies (and (reference-type-s type cl)
                   (consistent-class-table cl scl hp)
                   (not (equal type 'NULL)))
              (bcv::good-java-type (fix-sig type) cl)))))


(local 
 (defthm array-type-s-implies-good-java-type-g
   (implies (and (array-type-s type cl)
                 (consistent-class-table cl scl hp))
            (bcv::good-java-type (fix-sig (array-component-type type)) cl))
   :hints (("Goal" :in-theory (e/d (reference-type-s fix-sig array-type-s)
                                   (consistent-class-table))))))


(defthm array-type-s-implies-good-java-type
  (implies (and (array-type-s type (instance-class-table s))
                (consistent-state s))
           (bcv::good-java-type (fix-sig (array-component-type type))
                                (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (consistent-class-table)))))



(defthm not-primitive-type-not-fix-sig-primitive-type
  (implies (not (primitive-type? type))
           (not (primitive-type? (fix-sig type))))
  :hints (("Goal" :in-theory (enable fix-sig primitive-type?))))


(defthm consistent-state-implies-icl-scl-compatible
  (implies (consistent-state s)
           (BCV::ICL-SCL-COMPATIBLE (INSTANCE-CLASS-TABLE S)
                                    (BCV::CLASSTABLEENVIRONMENT (env-sig s))))
  :hints (("Goal" :in-theory (enable bcv::icl-scl-compatible env-sig 
                                     bcv::classtableenvironment
                                     makeenvironment
                                     consistent-state))))

;----------------------------------------------------------------------


(defthm mv-nth-1-of-resolve-field
  (equal  (MV-NTH '1
                  (CONS any (cons x nil)))
          x))


;----------------------------------------------------------------------


;; (skip-proofs 
;;  (defthm bcv-stack-frame-push-value-sig-g
;;    (implies (and (


;; (BCV::SIG-FRAME-MORE-GENERAL
;;   (FRAME-PUSH-VALUE-SIG-G g 
;;                           (FRAME-SIG (CURRENT-FRAME s)
;;                                      cl hp hp-init))

;;   (FRAME-PUSH-VALUE-SIG-G s
;;                           (frame-sig (current-frame s)
;;                                      cl hp hp-init))
;;   env))


;----------------------------------------------------------------------

;;  (EQUAL
;;   (LEN
;;    (BCV::FRAMESTACK
;;     (FRAME-PUSH-VALUE-SIG-G
;;      (VALUE-SIG
;;       (TAG
;;        (M6-GETFIELD
;;         (FIELD-CLASSNAME
;;            (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR (ARG INST))
;;                         (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
;;                                                S)))
;;         (FIELDCP-FIELDNAME (ARG INST))
;;         (RREF (TOPSTACK S))
;;         S)
;;        (FIELDCP-FIELDTYPE (ARG INST)))
;;       (INSTANCE-CLASS-TABLE S)
;;       (HEAP S)
;;       (HEAP-INIT-MAP (AUX S))
;;       (METHOD-PTR (CURRENT-FRAME S)))
;;      (FRAME-SIG (CURRENT-FRAME (POPSTACK S))
;;                 (INSTANCE-CLASS-TABLE S)
;;                 (HEAP S)
;;                 (HEAP-INIT-MAP (AUX S))))))
;;   (LEN
;;     (BCV::FRAMESTACK (FRAME-PUSH-VALUE-SIG-G
;;                           (BCV::TRANSLATE-TYPE (BCV::FIELDTYPECP (ARG INST)))
;;                           (FRAME-SIG (CURRENT-FRAME (POPSTACK S))
;;                                      (INSTANCE-CLASS-TABLE S)
;;                                      (HEAP S)
;;                                      (HEAP-INIT-MAP (AUX S)))))))).

;; Sun Jul 24 21:25:51 2005





(encapsulate ()
  (local (include-book "base-consistent-object-m6-getfield"))
  (local 
   (defthm consistent-object-consistent-state-m6-getfield-consistent-value
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
              (CONSISTENT-VALUE
               (TAG (M6-GETFIELD classname
                                 (fieldcp-fieldname fieldcp)
                                 (RREF v)
                                 S)
                    (fieldcp-fieldtype fieldcp))
               (fieldcp-fieldtype fieldcp)
               (INSTANCE-CLASS-TABLE S)
               (HEAP S)))))


  (defthm consistent-object-consistent-state-m6-getfield-consistent-value-general
    (implies (and (consistent-state s)
                  (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                       (fieldcp-classname fieldCP)
                                       s))
                  (REFp v (heap s))
                  (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                       S))
                         classname)
                  (lookupField (fieldcp-to-field-ptr fieldCP) s)
                  (equal (instance-class-table s) cl)
                  (equal (heap s) hp)
                  (not (NULLp v)))
             (CONSISTENT-VALUE
              (TAG (M6-GETFIELD classname
                                (fieldcp-fieldname fieldcp)
                                (RREF v)
                                S)
                   (fieldcp-fieldtype fieldcp))
              (fieldcp-fieldtype fieldcp)
              cl hp))
    :hints (("Goal" :use ((:instance
                           consistent-object-consistent-state-m6-getfield-consistent-value))))))



;;;
;;; the following will be a bit difficult to complete and prove!! 
;;; Sun Jul 24 22:06:12 2005
;;;

;; (i-am-here) ;; Mon Jul 25 17:22:10 2005


(local 
 (defthm consistent-value-implies-assignmentCompatible-case-primitive-type
   (implies (and (primitive-type? type)
                 (consistent-value tagged-value type cl hp))
            (equal (value-sig tagged-value cl hp hp-init method-ptr)
                   (bcv::translate-type type)))
   :hints (("Goal" :in-theory (enable consistent-value 
                                      wff-REFp tag tag-of value-of
                                      value-sig REFp NULLp 
                                      fix-sig)))))



(defthm bcv-isAssignable-reflexive
  (BCV::ISASSIGNABLE any any (ENV-SIG S))
  :hints (("Goal" :in-theory (enable bcv::isassignable))))

            
(local 
 (defthm wff-type-rep-implies-primitive-type-primitive-type
   (implies (and (not (primitive-type? type))
                 (wff-type-rep type))
            (not (primitive-type? (normalize-type-rep type))))
   :hints (("Goal" :in-theory (enable primitive-type?)))))
            


;; (defthm consistent-value-not-primitive-type-REFp
;;   (implies (and (not (primitive-type? type))
;;                 (consistent-value (tag v type) type (instance-class-table s)
;;                                   (heap s)))
;;            (REFp (tag v type) (heap s)))
;;   :hints (("Goal" :in-theory (e/d (consistent-value) (primitive-type? NULLp REFp)))))
;;
;; from base.lisp!! 
;;

(local 
 (defthm consistent-value-not-primitive-type-REFp-general
   (implies (and (not (primitive-type? type))
                 (consistent-value tagged-value type cl hp))
            (REFp tagged-value hp))
   :hints (("Goal" :in-theory (enable consistent-value REFp)))))





;; ;; (defthm djvm-assignment-compatible-cl-implies-BCV-isAssignable
;; ;;   (implies (and (AssignmentCompatible rtype type cl)
;; ;;                 (bcv::good-java-type (fix-sig rtype) cl)
;; ;;                 (bcv::good-java-type (fix-sig type) cl)
;; ;;                 (bcv::good-icl cl)
;; ;;                 (bcv::icl-scl-compatible cl scl))
;; ;;            (bcv::isAssignable (fix-sig rtype) (fix-sig type) (fake-env scl)))
;; ;;   :hints (("Goal" :in-theory (e/d (assignmentcompatible bcv::isAssignable)
;; ;;                                   (isJavaAssignmentCompatible bcv::good-icl
;; ;;                                                               bcv::isjavaassignable))
;; ;;            :do-not-induct t
;; ;;            :do-not '(fertilize)
;; ;;            :restrict
;; ;;            ((djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable
;; ;;              ((cl cl))))))))





(local 
 (defthm consistent-value-implies-assignmentCompatible-case-NULLp
   (implies (and (not (primitive-type? type))
                 (wff-type-rep type))
            (bcv::isAssignable 'NULL
                               type
                               (env-sig s)))
   :hints (("Goal" :in-theory (enable bcv::isAssignable)))))


(local 
 (defthm not-primitive-type-translate-type-reduce
   (implies (not (primitive-type? type))
            (equal (bcv::translate-type type) type))
   :hints (("Goal" :in-theory (enable primitive-type? bcv::translate-type)))))





(local 
 (encapsulate () 
   (local (defthm if-REFp-non-NULL-implies-value-sig
           (implies (and (REFp v hp)
                         (not (nullp v))
                         (not (consp (deref2-init v hp-init))))
                    (equal (value-sig v cl hp hp-init method-ptr)  
                           (fix-sig (obj-type (deref2 v hp)))))
           :hints (("Goal" :in-theory (enable value-sig)))))


   (local 
    (encapsulate () 
      (local (include-book "base-bcv-isAssignable-facts"))
      (defthm djvm-assignment-compatible-cl-implies-BCV-isAssignable
        (implies (and (AssignmentCompatible rtype type cl)
                      (bcv::good-java-type (fix-sig rtype) cl)
                      (bcv::good-java-type (fix-sig type) cl)
                      (bcv::good-icl cl)
                      (bcv::icl-scl-compatible cl scl))
                 (bcv::isAssignable (fix-sig rtype) (fix-sig type) (fake-env scl))))))


   (local 
    (defthm fix-sig-normalize-type-rep-fix-id
      (implies (wff-type-rep type)
               (equal (fix-sig (normalize-type-rep type))
                      type))
      :hints (("Goal" :in-theory (enable wff-type-rep
                                         array-component-type
                                         isArrayType
                                         fix-sig primitive-type?)))))


   (local 
    (encapsulate () 
       (local (include-book "base-bcv-djvm-assignable"))
       (defthm same-scl-judgement-same-specific-x
         (implies (bcv::isassignable (fix-sig typ1) (fix-sig typ2) (fake-env (bcv::classtableEnvironment
                                                                              (env-sig s))))
                  (bcv::isassignable (fix-sig typ1) (fix-sig typ2) (env-sig s))))))



   (local 
    (defthm djvm-assignment-compatible-cl-implies-BCV-isAssignable-specific
        (implies (and (AssignmentCompatible rtype (normalize-type-rep type) 
                                            (instance-class-table s))
                      (wff-type-rep type)
                      (bcv::good-java-type (fix-sig rtype) (instance-class-table s))
                      (bcv::good-java-type type (instance-class-table s))
                      (bcv::good-icl (instance-class-table s))
                      (bcv::icl-scl-compatible (instance-class-table s)
                                               (BCV::CLASSTABLEENVIRONMENT (env-sig s))))
                 (bcv::isAssignable (fix-sig rtype) type (env-sig s)))
        :hints (("Goal" :in-theory (disable fake-env bcv::icl-scl-compatible
                                            assignmentcompatible 
                                            bcv::good-icl bcv::good-java-type)
                 :use ((:instance
                        djvm-assignment-compatible-cl-implies-BCV-isAssignable
                        (cl  (instance-class-table s))
                        (scl (bcv::classtableenvironment (env-sig s)))
                        (type (normalize-type-rep type)))
                       (:instance same-scl-judgement-same-specific-x
                                  (typ1 rtype)
                                  (typ2 (normalize-type-rep type))))))))

   (local               
    (encapsulate () 
      (local (include-book "base-bcv-djvm-assignable"))                        
     (defthm bcv-good-java-type-if-converted-from-type-of-consistent-object
       (implies (and (consistent-state s)
                     (REFp v (heap s))
                     (not (NULLp v)))
                (bcv::good-java-type (fix-sig (obj-type (deref2 v (heap s))))
                                     (instance-class-table s)))
       :hints (("Goal" :in-theory (e/d () (REFp fix-sig bcv::good-java-type))
                :cases ((isArrayType (obj-type (deref2 v (heap s))))))))))


   (local 
    (encapsulate ()
      (local (include-book "base-consistent-state-good-icl-etc"))
      (defthm consistent-state-implies-good-icl
        (implies (consistent-state s)
                 (bcv::good-icl (instance-class-table s))))

      (defthm consistent-state-implies-icl-scl-compatible
        (implies (consistent-state s)
                 (BCV::ICL-SCL-COMPATIBLE (INSTANCE-CLASS-TABLE S)
                                          (BCV::CLASSTABLEENVIRONMENT (env-sig s))))
        :hints (("Goal" :in-theory (enable consistent-state))))))


   (defthm consistent-value-implies-assignmentCompatible-case-REFp
      (implies (and (REFp tagged-value (heap s))
                    (consistent-state s)
                    (not (NULLp tagged-value))
                    (wff-type-rep type)
                    (bcv::good-java-type type (instance-class-table s))
                    (not (primitive-type? type))
                    (not (consp (deref2-init tagged-value (heap-init-map
                                                           (aux s)))))
                    (consistent-value tagged-value (normalize-type-rep type) (instance-class-table s)
                                      (heap s)))
               (bcv::isAssignable (value-sig tagged-value
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                  type
                                  (env-sig s)))
      :hints (("Goal" :in-theory (e/d (consistent-value) (bcv::translate-type 
                                                          bcv::good-icl
                                                          bcv::icl-scl-compatible
                                                          assignmentcompatible))
               :do-not '(generalize))))))




(local 
 (defthm consistent-value-not-primitive-type-REFp-general-specific
   (implies (and (not (primitive-type? type))
                 (consistent-value tagged-value type (instance-class-table s)
                                   (heap s)))
            (REFp tagged-value (heap s)))))

;; (i-am-here) ;; Mon Jul 25 23:27:10 2005

(defthm consistent-value-implies-assignmentCompatible
  (implies (and (consistent-value tagged-value (normalize-type-rep type) (instance-class-table s)
                                  (heap s))
                (wff-type-rep type)
                (consistent-state s)
                ;; we need to get rid of the this assertion here!! 
                ;; however this is difficult, we do have some result about 
                ;; when we know something is isAssignableTo into type, 
                ;; we know type is a valid-type-s!
                (or (primitive-type? type)
                    (NULLp tagged-value)
                    (and (bcv::good-java-type type (instance-class-table s))
                         (not (consp (deref2-init tagged-value (heap-init-map (aux
                                                                               s))))))))
           ;; reverse the order!! 
           (bcv::isAssignable (value-sig tagged-value
                                         (instance-class-table s)
                                         (heap s)
                                         (heap-init-map (aux s))
                                         (method-ptr (current-frame s)))
                              (bcv::translate-type type)
                              (env-sig s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable VALUE-SIG-BEING-FIX-SIG)
           :cases ((not (primitive-type? type))))
          ("Subgoal 1" :cases ((not (NULLp tagged-value))))
          ("Subgoal 1.1" :restrict ((consistent-value-not-primitive-type-REFp-general-specific
                                     ((type (normalize-type-rep type))))))))
           

(defthm bcv-isAssignable-topx-topx
  (BCV::ISASSIGNABLE 'TOPX 'TOPX ENV)
  :hints (("Goal" :in-theory (enable bcv::isassignable))))




(defthm type-list-assignable-frame-push-sig-frame-g
  (implies (and (equal (bcv::sizeof g) (bcv::sizeof s))
                (bcv::isAssignable s g env))
           (bcv::typelistassignable 
            (bcv::framestack (frame-push-value-sig-g s sig-frame))
            (bcv::framestack (frame-push-value-sig-g g sig-frame))
            env))
  :hints (("Goal" :in-theory (enable frame-push-value-sig
                                     frame-push-value-sig-g))))

                                          
;----------------------------------------------------------------------


(defthm bcv-size-of-value-sig
  (implies (and (consistent-value (tag v type)
                                  type cl hp)
                (not (equal type 'TWOWORD))) 
           ;; because out tag function will
           ;; tag any non-primitive type as REF ;; Sat Jul 23 23:42:12 2005
           (equal (bcv::sizeof (value-sig (tag v type) cl hp hp-init method-ptr))
                  (bcv::sizeof type)))
  :hints (("Goal" :in-theory (enable bcv::sizeof
                                     NULLp wff-REFp REFp
                                     rREF
                                     tag value-of tag-of
                                     value-sig primitive-type?
                                     consistent-value))))

                                 

;----------------------------------------------------------------------
(defthm wff-type-rep-implies-not-TWOWORD
  (implies (wff-type-rep type)
           (not (equal type 'TWOWORD))))


;----------------------------------------------------------------------

(defthm wff-type-implies-not-normal-type-rep-twoword
  (implies (wff-type-rep type)
           (not (equal (normalize-type-rep type) 'TWOWORD))))


(defthm type-size-fieldcp-type-implies-bcv-sizeof-1-x
  (implies (and (equal (type-size (fieldcp-fieldtype fieldcp)) 1)
                (wff-fieldcp fieldcp))
           (equal (bcv::sizeof (fieldcp-fieldtype fieldcp)) 1))
  :hints (("Goal" :in-theory (enable type-size bcv::sizeof 
                                     fieldcp-fieldtype
                                     wff-type-rep
                                     wff-fieldcp bcv::fieldtypecp
                                     normalize-type-rep))))




(defthm framelocals-frame-push-sig-stack-g
  (equal (bcv::framelocals (frame-push-value-sig-g any frame))
         (bcv::framelocals frame))
  :hints (("Goal" :in-theory (enable frame-push-value-sig-g))))



(defthm frameflags-frame-push-sig-stack-g
  (equal (bcv::frameflags (frame-push-value-sig-g any frame))
         (bcv::frameflags frame))
  :hints (("Goal" :in-theory (enable frame-push-value-sig-g))))
                                     



(defthm normalize-type-rep-bcv-fieldtype-cp-normalize
  (equal (NORMALIZE-TYPE-REP (BCV::FIELDTYPECP fieldcp))
         (fieldcp-fieldtype fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-fieldtype bcv::fieldtypecp))))




(local 
 (defthm typelistassignable-implies-list-len
   (implies (bcv::typelistassignable sl gl env)
            (equal (equal (len sl) 
                          (len gl)) t))
   :hints (("Goal" :in-theory (enable bcv::typelistassignable)))))
 


(defthm typelistassignable-implies-list-len-specific
  (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness
                                                           "DJVM"))
                           (s))
                (bcv::typelistassignable sl gl (env-sig s)))
           (equal (equal (len sl) 
                         (len gl)) t))
  :hints (("Goal" :in-theory (enable bcv::typelistassignable))))


;----------------------------------------------------------------------

(local 
 (defthm wff-type-refp-implies-normalize-type-equal
   (implies (and (equal (type-size (normalize-type-rep type)) 2)
                 (wff-type-rep type))
            (equal (normalize-type-rep type) type))
   :hints (("Goal" :in-theory (enable type-size)))))

(local 
 (defthm type-size-2-implies-fieldcp-field-type-equal
   (implies (and (EQUAL (TYPE-SIZE (FIELDCP-FIELDTYPE fieldcp))
                        2)
                 (wff-fieldcp fieldcp))
            (equal (fieldcp-fieldtype fieldcp)
                   (bcv::fieldtypecp fieldcp)))
   :hints (("Goal" :in-theory (e/d (fieldcp-fieldtype 
                                    wff-fieldcp 
                                    wff-type-rep
                                    bcv::fieldtypecp) (type-size))))
   :rule-classes nil))

(defthm fieldcp-fieldtype-normalize
  (implies (and (EQUAL (TYPE-SIZE (FIELDCP-FIELDTYPE fieldcp))
                       2)
                (wff-fieldcp fieldcp))
           (equal (BCV::TRANSLATE-TYPE (FIELDCP-FIELDTYPE fieldcp))
                  (BCV::TRANSLATE-TYPE (BCV::FIELDTYPECP fieldcp))))
  :hints (("Goal" :use type-size-2-implies-fieldcp-field-type-equal)))


;----------------------------------------------------------------------


(encapsulate ()
 (local (include-book "base-load-class-normalize-when-found"))
 (local (defthm resolveClassReference-no-change-if-already-loaded-if-not-array-Object
          (implies (and (consistent-object obj (heap s) (instance-class-table s))
                        (case-split (not (isArrayType (obj-type obj))))
                        (car (isAssignableTo (obj-type obj) typ2 s))
                        (consistent-state s))
                   (equal (resolveClassReference typ2 s) s))))
 (defthm
   resolveClassReference-no-change-if-already-loaded-if-not-array-Object-specific
   (implies (and (consistent-object (deref2 (topStack s) (heap s)) (heap s) (instance-class-table s))
                 (case-split (not (isArrayType (obj-type (deref2 (topStack s) (heap s))))))
                 (car (isAssignableTo (obj-type (deref2 (topStack s) (heap s))) typ2 s))
                 (consistent-state s))
            (equal (resolveClassReference typ2 s) s))))


;; we include these following, we don't want it any more!! 
;; 

(defthm wff-fieldcp-implies-not-TWOWORD
  (implies (WFF-FIELDCP fieldcp)
           (not (equal (fieldcp-fieldtype fieldcp) 'TWOWORD)))
  :hints (("Goal" :in-theory (enable wff-type-rep fieldcp-fieldtype wff-fieldcp))))



;; because we disabled 
;;;             BCV-FRAME-STACK-FRAME-SIG-IS-OPSTACK-SIG
;; ACONST_NULL failed
;; We prove a specific version of it. 
;; 
;; Mon Jul 25 16:56:23 2005

(defthm BCV-FRAME-STACK-FRAME-SIG-IS-OPSTACK-SIG-specific
  (equal (BCV::FRAMESTACK (FRAME-SIG (CURRENT-FRAME S)
                                     (INSTANCE-CLASS-TABLE S)
                                     (HEAP S)
                                     (HEAP-INIT-MAP (AUX S))))
         (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                      (INSTANCE-CLASS-TABLE S)
                      (HEAP S)
                      (HEAP-INIT-MAP (AUX S))
                      (METHOD-PTR (CURRENT-FRAME S))))
  :hints (("Goal" :in-theory (enable
                              bcv-frame-stack-frame-sig-is-opstack-sig))))

;; Mon Jul 25 16:56:18 2005
;; so far we only need this above! 
;;

;; (defthm BCV-FRAME-LOCALS-FRAME-SIG-IS-LOCALS-SIG-specific
;;   (equal (BCV::FRAMESTACK (FRAME-SIG (CURRENT-FRAME S)
;;                                      (INSTANCE-CLASS-TABLE S)
;;                                      (HEAP S)
;;                                      (HEAP-INIT-MAP (AUX S))))
;;          (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
;;                       (INSTANCE-CLASS-TABLE S)
;;                       (HEAP S)
;;                       (HEAP-INIT-MAP (AUX S))
;;                       (METHOD-PTR (CURRENT-FRAME S))))
;;   :hints (("Goal" :in-theory (enable bcv-frame-locals-frame-sig-is-locals-sig))))


(in-theory (disable 
            BCV-FRAME-FLAGS-FRAME-SIG-IS-GENFLAGS-SIG
            BCV-FRAME-STACK-FRAME-SIG-IS-OPSTACK-SIG
            BCV-FRAME-LOCALS-FRAME-SIG-IS-LOCALS-SIG))



(in-theory (disable frame-push-value-sig-g 
                    bcv::prefix-class
                    bcv::translate-type))


(defthm wff-fieldcp-implies-wff-type-rep
  (implies (wff-fieldcp fieldcp)
           (WFF-TYPE-REP (BCV::FIELDTYPECP fieldcp)))
  :hints (("Goal" :in-theory (enable wff-fieldcp
                                     bcv::fieldtypecp))))


;----------------------------------------------------------------------
;
; prove an result for showing good-java-type
;


;; (encapsulate ()

;; (i-am-here)  ;;Tue Jul 26 00:54:29 2005

(encapsulate () 
   (local (include-book "base-good-java-type-valid-type-s"))
   (local (defthm valid-type-strong-implies-good-java-type-specific
               (implies (and (wff-type-rep type)
                             (consistent-state s)
                             (valid-type-strong (normalize-type-rep type) 
                                                (instance-class-table s)))
                        (bcv::good-java-type type (instance-class-table s)))))

   (local 
    (encapsulate ()
       (local (include-book "base-reference-type-s-good-java-type"))
       (defthm reference-type-s-implies-good-java-type
         (implies (and (reference-type-s type cl)
                       (consistent-class-table cl scl hp)
                       (not (equal type 'NULL)))
                  (bcv::good-java-type (fix-sig type) cl)))))

   (local 
    (defthm wff-fieldcp-implies-wff-type-rep
      (implies (wff-fieldcp fieldcp)
               (wff-type-rep (bcv::fieldtypecp fieldcp)))))

   (local 
    (defthm normalize-type-rep-bcv-fieldtypecp-normalize
      (equal (normalize-type-rep (bcv::fieldtypecp fieldcp))
             (fieldcp-fieldtype fieldcp))
      :hints (("Goal" :in-theory (enable fieldcp-fieldtype
                                         bcv::fieldtypecp)))))

   (local 
    (defthm consistent-state-implies-consistent-class-table
      (implies (consistent-state s)
               (consistent-class-table (instance-class-table s)
                                       (env-class-table (env s))
                                       (heap s)))
      :hints (("Goal" :in-theory (e/d (consistent-state)
                                      (consistent-class-table))))
      :rule-classes :forward-chaining))

   (local 
    (defthm wff-type-rep-implies-not-NULL-type
      (implies (wff-type-rep type)
               (not (equal (normalize-type-rep type) 'NULL)))
      :hints (("Goal" :in-theory (enable wff-type-rep fieldcp-fieldtype normalize-type-rep)))))


   (local 
    (defthm wff-fieldcp-implies-not-NULL-type
      (implies (wff-fieldcp fieldcp)
               (not (equal (fieldcp-fieldtype fieldcp) 'NULL)))
      :hints (("Goal" :in-theory (enable wff-type-rep fieldcp-fieldtype normalize-type-rep)))))


   (local 
    (defthm fix-sig-normalize-type-rep-fix-id
      (implies (wff-type-rep type)
               (equal (fix-sig (normalize-type-rep type))
                      type))
      :hints (("Goal" :in-theory (enable wff-type-rep
                                         array-component-type
                                         isArrayType
                                         fix-sig primitive-type?)))))


   (local 
    (defthm fix-sig-fieldcp-fieldtype-is-bcv-fieldtypecp
      (implies (wff-fieldcp fieldcp)
               (equal (FIX-SIG (FIELDCP-FIELDTYPE FIELDCP))
                      (bcv::fieldtypecp fieldcp)))
      :hints (("Goal" :in-theory (e/d (fieldcp-fieldtype bcv::fieldtypecp)
                                      ())))))

   (local 
    (defthm reference-type-s-implies-good-java-type-specific
      (implies (and (reference-type-s (fieldcp-fieldtype fieldcp)
                                      (instance-class-table s))
                    (consistent-state s)
                    (wff-fieldcp fieldcp))
               (bcv::good-java-type (bcv::fieldtypecp fieldcp) (instance-class-table s)))
      :hints (("Goal" :in-theory (e/d ()
                                      (consistent-class-table 
                                       reference-type-s
                                       reference-type-s-implies-good-java-type
                                       wff-fieldcp))
               :use ((:instance reference-type-s-implies-good-java-type
                                (type (normalize-type-rep (bcv::fieldtypecp fieldcp)))
                                (cl (instance-class-table s))
                                (scl (env-class-table (env s)))
                                (hp (heap s))))))))


   (local 
    (defthm assignmentcompatible-implies-reference-type-s
      (implies (and (assignmentcompatible (obj-type obj)
                                          type
                                          (instance-class-table s))
                    (not (primitive-type? type)))
               (reference-type-s type (instance-class-table s)))))
               
                                     
   (defthm fieldcptype-is-good-java-type
      (implies (and (wff-fieldcp fieldcp)
                    (consistent-state s)
                    (not (NULLP TAGGED-VALUE))
                    (not (primitive-type? (fieldcp-fieldtype fieldcp)))
                    (consistent-value tagged-value
                                      (fieldcp-fieldtype fieldcp)
                                      (instance-class-table s)
                                      (heap s)))
               (bcv::good-java-type (bcv::fieldtypecp fieldcp)
                                    (instance-class-table s)))
      :hints (("Goal" :in-theory (e/d (consistent-value)
                                      (bcv::good-java-type 
                                       isAssignableTo
                                       fieldcp-fieldtype
                                       bcv::fieldtypecp
                                       reference-type-s
                                       consistent-object
                                       wff-fieldcp
                                       obj-type))))))


;;;
;;; we expect this obj is instantiated with what m6-getfield returns!! 
;;; which is 
;;;
                   
;;; We need to assert that when fieldcp-type is not primitive-type 
;;; then, we know it is a valid reference into the heap!! 
;;;
;;; we will use the consistent-value fact! 
;;;



;; (local 
;;  (defthm consistent-value-not-primitive-type-REFp-general
;;    (implies (and (not (primitive-type? type))
;;                  (consistent-value tagged-value type cl hp))
;;             (REFp tagged-value hp))
;;    :hints (("Goal" :in-theory (enable consistent-value REFp)))))




;; (defthm REFp-consistent-state-not-null
;;   (implies (and (REFp v (heap s))
;;                 (consistent-state s)
;;                 (equal (instance-class-table s) cl)
;;                 (not (nullp v)))
;;            (consistent-object (deref2 v (heap s)) (heap s) cl))
;;   :hints (("Goal" :in-theory (e/d (REFp consistent-heap deref2) (binding-rref-normalize)))))



;; (REFP
;;     (TAG (M6-GETFIELD
;;               (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR (ARG INST))
;;                                             S))
;;               (FIELDCP-FIELDNAME (ARG INST))
;;               (RREF (TOPSTACK S))
;;               S)
;;          (FIELDCP-FIELDTYPE (ARG INST)))
;;     (HEAP S)).


;; export this one!! 

;; (defthm consistent-value-not-primitive-type-REFp-general-specific-futher
;;   (implies (and (not (primitive-type? (fieldcp-fieldtype fieldcp)))
;;                 (consistent-value (tag (m6-getfield classname 
;;                                                     fieldname 
;;                                                     obj-ref
;;                                                     s)
;;                                        (fieldcp-fieldtype fieldcp))
;;                                   (fieldcp-fieldtype fieldcp)
;;                                   (instance-class-table s)
;;                                   (heap s)))
;;            (REFp (tag (m6-getfield classname 
;;                                    fieldname 
;;                                    obj-ref
;;                                    s)
;;                       (fieldcp-fieldtype fieldcp))
;;                  (heap s))))


(defthm not-primitive-type-not-primitive-type-specific
  (implies (and (not (primitive-type? (BCV::FIELDTYPECP fieldcp)))
                (wff-fieldcp fieldcp))
           (not (primitive-type? (fieldcp-fieldtype fieldcp))))
  :hints (("Goal" :in-theory (enable fieldcp-fieldtype
                                     bcv::fieldtypecp))))





;; 3 (:REWRITE CONSISTENT-VALUE-NOT-PRIMITIVE-TYPE-REFP-GENERAL-SPECIFIC-FUTHER)
;; produced 'T.
;; 3)

;; (3 Breaking (:REWRITE 
;;              CONSISTENT-VALUE-NOT-PRIMITIVE-TYPE-REFP-GENERAL-SPECIFIC-FUTHER)
;; on (REFP (TAG (M6-GETFIELD # # # ...) (FIELDCP-FIELDTYPE #)) (HEAP S)):
;; 3 DJVM >:go

;; 3 (:REWRITE CONSISTENT-VALUE-NOT-PRIMITIVE-TYPE-REFP-GENERAL-SPECIFIC-FUTHER)
;; produced 'T.
;; 3)

;; 2x (:REWRITE FIELDCPTYPE-IS-GOOD-JAVA-TYPE) failed because :HYP 4 rewrote
;; to 
;; (CAR
;;  (ISASSIGNABLETO
;;   (OBJ-TYPE
;;    (DEREF2
;;     (TAG (M6-GETFIELD
;;               (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR (ARG INST))
;;                                             S))
;;               (FIELDCP-FIELDNAME (ARG INST))
;;               (RREF (TOPSTACK S))
;;               S)
;;          (FIELDCP-FIELDTYPE (ARG INST)))
;;     (HEAP S)))
;;   (FIELDCP-FIELDTYPE (ARG INST))
;;   S)).
;; 2)

;;; now we need to conclude from consistent-value to conclude 
;;; isAssignableTo
;;; !!! 



