(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")


(include-book "base-bind-free")

;;; Mon May  9 01:51:42 2005
;;; Redo using the "structure" development method!! 
;;;


(in-theory (disable bcv::good-icl 
                    bcv::consistent-sig-stack 
                    bcv::arrayelementtype
                    BCV::FRAMEFLAGS
                    BCV::FRAMELOCALS 
                    BCV::FRAMESTACK
                    BCV::sizeof
                    bcv::isMatchingType
                    make-sig-frame
                    bcv::good-icl
                    bcv::popMatchingType
                    bcv::consistent-sig-type
                    BCV::NTH1OPERANDSTACKIS
                    BCV::MAXSTACKENVIRONMENT
                    bcv::good-java-type
                    bcv::classtableEnvironment
                    bcv::icl-scl-compatible))





(defthm frame-accessor 
  (and (equal (frameLocals (make-sig-frame l s f)) l)
       (equal (frameStack  (make-sig-frame l s f)) s)
       (equal (frameFlags  (make-sig-frame l s f)) f))
  :hints (("Goal" :in-theory (enable  make-sig-frame frameFlags frameStack frameLocals))))



(encapsulate ()
   (local (include-book "base-bcv-check-monotonic-support"))
   (defthm TypeListAssignable-implies-len-equal-with-bind
     (implies (and (bind-free (acl2::default-bind-free 'env 'env1 
                                                       (acl2::pkg-witness "DJVM"))
                              (env))
                   (TypeListAssignable l1 l2 env))
              (equal (equal (len l1) (len l2)) t)))

   (defthm popMatchingType-preserve-TypeListAssignable
     (implies (TypeListAssignable l1 l2 env)
              (TypeListAssignable (popMatchingType any l1)
                                  (popMatchingType any l2) env))))




(include-book "base-bcv-fact-isMatchingType-consp-stk")

(in-theory (enable nth1OperandStackIs))
(include-book "base-bcv-fact-nth-opstack")
(include-book "base-bcv-fact-isMatchingType-array")

(in-theory (disable bcv::isAssignable))


(defthm popMatchingType-size-1-implies-len-decrease
  (implies (and (equal (sizeof type) 1)
                (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM")) (env))
                (isMatchingType type stk env)
                (consp stk)
                type)
           (equal (len (popMatchingType type stk))
                  (- (len stk) 1)))
  :hints (("Goal" :in-theory (enable popMatchingType))))



(encapsulate ()
 (local (include-book "base-bcv-check-monotonic-support"))
 (defthm assignable-assignable
   (implies (and (bcv::isassignable typ1 typ2 env)
                 (bcv::isArrayType typ1)
                 (bcv::isArrayType typ2))
            (bcv::isassignable (bcv::arrayElementType typ1)
                               (bcv::arrayElementType typ2) env))))



(defthm TypeListAssignable-implies-car-isAssignable
  (implies (and (TypeListAssignable sl gl env)
                (consp sl)
                (consp gl))
           (isAssignable (car sl)
                         (car gl) env)))



(local (encapsulate ()
 (defthm isAssignable-expander
   (implies (syntaxp (and (eq (car bcv::t1) 'QUOTE)
                          (eq (car bcv::t2) 'QUOTE)))
            (equal (bcv::isAssignable bcv::t1 bcv::t2 bcv::env)
                   (LET
                    ((BCV::CL (BCV::CLASSTABLEENVIRONMENT BCV::ENV)))
                    (IF
                     (EQUAL BCV::T1 BCV::T2)
                     T
                     (COND
                      ((AND (EQUAL BCV::T1 'ONEWORD)
                            (EQUAL BCV::T2 'topx))
                       T)
                      ((AND (EQUAL BCV::T1 'TWOWORD)
                            (EQUAL BCV::T2 'topx))
                       T)
                      ((EQUAL BCV::T1 'INT)
                       (BCV::ISASSIGNABLE 'ONEWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'FLOAT)
                       (BCV::ISASSIGNABLE 'ONEWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'LONG)
                       (BCV::ISASSIGNABLE 'TWOWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'DOUBLE)
                       (BCV::ISASSIGNABLE 'TWOWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL BCV::T1 'REFERENCE)
                       (BCV::ISASSIGNABLE 'ONEWORD
                                          BCV::T2 BCV::ENV))
                      ((EQUAL 'UNINITIALIZED BCV::T1)
                       (BCV::ISASSIGNABLE 'REFERENCE
                                          BCV::T2 BCV::ENV))
                      ((BCV::ISCLASSTYPE BCV::T1)
                       (OR (BCV::ISASSIGNABLE 'REFERENCE
                                              BCV::T2 BCV::ENV)
                           (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL)))
                      ((BCV::ISARRAYTYPE BCV::T1)
                       (OR
                        (BCV::ISASSIGNABLE 'REFERENCE
                                           BCV::T2 BCV::ENV)
                        (AND (BCV::ISCLASSTYPE BCV::T2)
                             (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))
                        (AND (BCV::ISARRAYTYPE BCV::T2)
                             (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))))
                      ((EQUAL BCV::T1 'UNINITIALIZEDTHIS)
                       (BCV::ISASSIGNABLE 'UNINITIALIZED
                                          BCV::T2 BCV::ENV))
                      ((BCV::ISUNINITIALIZEDOBJECT BCV::T1)
                       (BCV::ISASSIGNABLE 'UNINITIALIZED
                                          BCV::T2 BCV::ENV))
                      ((BCV::ISNULLTYPE BCV::T1)
                       (OR (BCV::ISCLASSTYPE BCV::T2)
                           (BCV::ISARRAYTYPE BCV::T2)
                           (BCV::ISASSIGNABLE '(CLASS "java.lang.Object")
                                              BCV::T2 BCV::ENV)))
                      (T NIL))))))
   :hints (("Goal" :in-theory (disable isAssignable)
            :expand (isAssignable t1 t2 env))))))





(local 
 (defthm not-reference-isAssignable
   (not (isAssignable 'reference (cons 'ARRAY any) env))
   :hints (("Goal" :in-theory (enable isAssignable)
            :expand (isAssignable 'reference (cons 'ARRAY any) env)))))


;; (local 
;;  (defthm isMatchingType-ARRAY-not-NULLp-implies-bcv-ARRAY-type
;;    (implies (and (bind-free (acl2::default-bind-free 'env 'env1
;;                                                      (acl2::pkg-witness "DJVM"))
;;                             (env))
;;                  (true-listp any)
;;                  (isMatchingType (cons 'array any) stk env)
;;                  (not (equal (car stk) 'NULL)))
;;             (bcv::isArrayType (car stk)))
;;    :hints (("Goal" :in-theory (enable bcv::isMatchingType
;;                                       bcv::sizeof
;;                                       bcv::isassignable)))))





(defthm isMatchingType-ARRAY-not-NULLp-implies-bcv-ARRAY-type-ARRRAY
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM"))
                           (env))
                (isMatchingType '(array (class "java.lang.Object")) stk env)
                (not (equal (car stk) 'NULL)))
           (bcv::isArrayType (car stk)))
    :hints (("Goal" :in-theory (enable bcv::isMatchingType
                                       bcv::sizeof
                                       bcv::isassignable))))


(in-theory (disable bcv::isArrayType))





(defthm consistent-sig-type-fact-1
  (consistent-sig-type 'INT icl)
  :hints (("Goal" :in-theory (enable consistent-sig-type good-bcv-type good-java-type))))


(defthm consistent-sig-type-fact-2
  (implies (bcv::good-icl icl)
           (bcv::consistent-sig-type '(array (class "java.lang.Object"))  icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-type 
                                     bcv::good-bcv-type
                                     bcv::good-icl bcv::good-java-type))))

;; Tue May 17 16:35:36 2005

(defthm consistent-sig-type-fact-3
  (implies (bcv::good-icl icl)
           (bcv::consistent-sig-type '(class "java.lang.Object")  icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-type 
                                     bcv::good-bcv-type
                                     bcv::good-icl bcv::good-java-type))))



(include-book "base-bcv-fact-nth-opstack")
(include-book "base-bcv-fact-isMatchingType-array")
(include-book "base-bcv-fact-isMatchingType-consp-stk")

(in-theory (disable JVM::MEM-BASE-TYPES-IMPLIES-NOT-EQUAL))
(in-theory (disable bcv::isMatchingType))

(include-book "base-bcv-check-monotonic")

;----------------------------------------------------------------------

(in-theory (disable bcv::isassignable bcv::arg1))

 
(local 
 (defthm isAssignable-fact-nil-nil-local
   (bcv::isAssignable nil nil env)
   :hints (("Goal" :in-theory (enable bcv::isAssignable)))))

(defthm TypeListAssignable-implies-element-assignable
  (implies (bcv::TypeListAssignable l1 l2 env)
           (bcv::isAssignable (nth i l1) (nth i l2) env))
  :hints (("Goal" :in-theory (e/d (bcv::typelistassignable)
                                  (bcv::isAssignable)))))


;----------------------------------------------------------------------

(defthm isAssignable-fact-same-same
  (BCV::ISASSIGNABLE x x ENV1)
  :hints (("Goal" :in-theory (enable bcv::isassignable))))

;----------------------------------------------------------------------

;; (i-am-here) ;; Thu Jul 28 01:45:53 2005

;;(i-am-here) ;; 

(defthm bcv-typelist-assignable-if-push-same
  (implies (bcv::typelistassignable sl gl env1)
           (BCV::TYPELISTASSIGNABLE
            (BCV::PUSHOPERANDSTACK any sl)
            (BCV::PUSHOPERANDSTACK any gl)
            ENV1))
  :hints (("Goal" :in-theory (enable bcv::typelistassignable))))


(in-theory (enable bcv::typelistassignable))


;----------------------------------------------------------------------

(encapsulate ()
 (local (include-book "base-bcv-modify-local-variable"))

 (defthm bcv-typelistAssignable-modify-local-variable-slot
   (implies (and (bind-free (acl2::default-bind-free 'icl 'icl
                                                     (acl2::pkg-witness "DJVM")))
                 (bcv::typelistassignable sl gl env1)
                 (consistent-sig-locals sl icl)
                 (consistent-sig-locals gl icl)
                 (integerp i)
                 (<= 0 i)
                 (< i (len gl))
                 (bcv::isAssignable s g env1)
                 (not (equal g 'topx)))
            (bcv::typelistassignable (bcv::modifylocalvariable i s sl) 
                                     (bcv::modifylocalvariable i g gl) env1)))

 (in-theory (disable bcv::modifylocalvariable))
 (defthm isMatchingType-reference-implies-car-not-topx
   (implies (and (bind-free (acl2::default-bind-free 'env1 'env1
                                                     (acl2::pkg-witness "DJVM")))
                 (bcv::isMatchingType 'REFERENCE stack env1))
            (not (equal (car stack) 'topx)))))
           



