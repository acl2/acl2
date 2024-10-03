(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base-bind-free")



;; Fri Jul 29 19:42:00 2005
;; deal with modify!! 
(defthm bcv-isAssignable-size-equal
  (implies (and (bcv::isAssignable s g env1)
                (not (equal g 'topx)))
           (equal (bcv::sizeof s)
                  (bcv::sizeof g)))
  :hints (("Goal" :in-theory (enable bcv::isAssignable)))
  :rule-classes :forward-chaining)

(defthm bcv-size-1-or-2
   (implies (not (equal (bcv::sizeof any) 2))
           (equal (bcv::sizeof any) 1))
  :hints (("Goal" :in-theory (enable bcv::sizeof))))


(defthm bcv-size-1-or-2-altern
   (implies (equal (bcv::sizeof any) 2)
            (not (equal (bcv::sizeof any) 1)))
  :hints (("Goal" :in-theory (enable bcv::sizeof)))
  :rule-classes :forward-chaining)


;; (defthm bcv-isAssignable-size-equal-1-x
;;    (implies (and (equal (bcv::sizeof g) 2) 
;;                  (bcv::isAssignable s g env1)
;;                  (not (equal g 'topx)))
;;             (not (equal (bcv::sizeof s) 1)))
;;    :rule-classes :forward-chaining)


;; (skip-proofs 
;;  (defthm bcv-isAssignable-size-equal-1-x2
;;    (implies (and (equal (bcv::sizeof g) 2) 
;;                  (bcv::isAssignable s g env1)
;;                  (bcv::consistent-sig-type s icl)
;;                  (bcv::consistent-sig-type g icl)
;;                  (bcv::good-icl icl)
;;                  (bcv::good-scl (bcv::classtableEnvironment env1))
;;                  (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
;;             (equal (bcv::sizeof s) 2))
;;    :hints (("Goal" :in-theory (enable bcv::isAssignable)))
;;    :rule-classes :forward-chaining))


;; (skip-proofs 
;;  (defthm bcv-isAssignable-size-equal-2-x2
;;    (implies (and (equal (bcv::sizeof g) 1) 
;;                  (bcv::isAssignable s g env1)
;;                  (bcv::consistent-sig-type s icl)
;;                  (bcv::consistent-sig-type g icl)
;;                  (bcv::good-icl icl)
;;                  (bcv::good-scl (bcv::classtableEnvironment env1))
;;                  (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
;;             (not (equal (bcv::sizeof s) 2)))
;;    :hints (("Goal" :in-theory (enable bcv::isAssignable)))
;;    :rule-classes :forward-chaining))


;; (skip-proofs 
;;  (defthm bcv-isAssignable-size-equal-2-x
;;    (implies (and (equal (bcv::sizeof g) 1) 
;;                  (bcv::isAssignable s g env1)
;;                  (bcv::consistent-sig-type s icl)
;;                  (bcv::consistent-sig-type g icl)
;;                  (bcv::good-icl icl)
;;                  (bcv::good-scl (bcv::classtableEnvironment env1))
;;                  (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
;;             (not (equal (bcv::sizeof s) 2)))
;;    :hints (("Goal" :in-theory (enable bcv::isAssignable)))
;;    :rule-classes :forward-chaining))



(local 
 (defthm isAssignable-expander
   (implies (syntaxp 
             (and (or (eq (len (cdr bcv::t1)) 1)
                      (eq (len (cdr bcv::t2)) 1))
                  (or (eq (car bcv::t1) 'QUOTE)
                      (eq (car bcv::t2) 'QUOTE))))
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
   :hints (("Goal" :expand (bcv::isassignable bcv::t1 bcv::t2 bcv::env)))))



(defthm consistent-sig-type-implies-assignable-to-topx
    (implies (bcv::consistent-sig-type sl1 icl)
             (BCV::ISASSIGNABLE SL1 'TOPX ENV1)))


(defthm bcv-isAssignable-size-2-into-size-1-topx
  (implies (and (BCV::ISASSIGNABLE SL1 GL1 ENV1)
                (equal (bcv::sizeof sl1) 2)
                (equal (bcv::sizeof gl1) 1))
           (equal gl1 'topx))
  :rule-classes :forward-chaining)


(defthm consistent-sig-local-implies-cdr-consistent
  (implies (bcv::consistent-sig-locals gl icl)
           (BCV::CONSISTENT-SIG-LOCALS (CDR GL) icl)))
  

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
                                    (bcv::modifylocalvariable i g gl) env1))
  :hints (("Goal" :in-theory (e/d ( ) (bcv::sizeof bcv::isAssignable))
           :do-not '(generalize))))

(in-theory (disable bcv::modifylocalvariable))

(defthm isMatchingType-reference-implies-car-not-topx
  (implies (and (bind-free (acl2::default-bind-free 'env1 'env1
                                                    (acl2::pkg-witness "DJVM")))
                (bcv::isMatchingType 'REFERENCE stack env1))
           (not (equal (car stack) 'topx))))
           
