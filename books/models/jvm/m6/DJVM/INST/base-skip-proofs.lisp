(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/djvm-exceptions")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")
(include-book "../../DJVM/consistent-state-to-sig-state")
(include-book "../../DJVM/consistent-state-strong")

(skip-proofs 
 (defthm raise-exception-consistent-state
   (implies (consistent-state s)
            (consistent-state (raise-exception any s)))))


(skip-proofs 
 (defthm raise-exception-consistent-state-strong
   (implies (consistent-state-strong s)
            (consistent-state-strong (raise-exception any s)))))


(skip-proofs 
 (defthm bcv-isJavaAssignable-fact-2
   (BCV::ISJAVAASSIGNABLE '(ARRAY (CLASS "java.lang.Object"))
                          '(ARRAY (CLASS "java.lang.Object"))
                          (BCV::CLASSTABLEENVIRONMENT ENV))))



(skip-proofs 
 (defthm djvm-isjavaassignment-compatible-cl-implies-BCV-isJavaAssignable
   (implies (and (isJavaAssignmentCompatible rtype type cl)
                 (reference-type-s rtype cl)
                 (reference-type-s type cl)
                 (consistent-class-hierachy cl)
                 (class-table-is-loaded-from cl (bcv::scl-bcv2jvm scl)))
            (bcv::isjavaassignable (fix-sig rtype) (fix-sig type) scl))
   :hints (("Goal" :induct (isJavaAssignmentCompatible rtype type cl)
            :in-theory (e/d () (array-component-type component-type))
            :do-not '(generalize)))))

;;; this may be proved in context of consistent-properties.lisp
;;; or base-bcv!! 


;----------------------------------------------------------------------

(skip-proofs 
 (defthm isAssignableTo-isAssignableTo-if-class-table-same
   (implies (equal (instance-class-table s2) 
                   (instance-class-table s1))
            (iff (car (isAssignableTo typ1 typ2 s2))
                 (car (isAssignableTo typ1 typ2 s1))))))


;----------------------------------------------------------------------


; this need updates to consistent-state to assert consistent-instrs!! 


(skip-proofs 
 (defthm method-ptr-no-change-after-raise-exception
   (equal (METHOD-PTR
           (CURRENT-FRAME (RAISE-EXCEPTION any S)))
          (METHOD-PTR (CURRENT-FRAME S)))))


;----------------------------------------------------------------------

(skip-proofs 
  (defthm deref-method-no-change-after-raise-exception
    (implies (class-loaded? (method-ptr-classname method-ptr) s)
             (equal (deref-method method-ptr (instance-class-table 
                                              (raise-exception any s)))
                    (deref-method method-ptr (instance-class-table s))))))