(in-package "DJVM")
(include-book "../../BCV/typechecker")
(include-book "../../DJVM/consistent-state-to-sig-state")

(include-book "base-bind-free")

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




(local 
 (defthm not-equal-double-not-assignable
   (implies (not (equal type 'DOUBLE))
            (not (bcv::isassignable type 'DOUBLE env)))
   :hints (("Goal" :in-theory (enable bcv::isjavaassignable)))))

(local 
 (defthm not-equal-LONG-not-assignable
   (implies (not (equal type 'LONG))
            (not (bcv::isassignable type 'LONG env)))
   :hints (("Goal" :in-theory (enable bcv::isjavaassignable)))))


(local 
 (defthm not-equal-VOID-not-assignable
   (implies (not (equal type 'VOID))
            (not (bcv::isassignable type 'VOID env)))
   :hints (("Goal" :in-theory (enable bcv::isjavaassignable)))))


(local 
 (defthm not-equal-twoword-not-assignable
   (implies (and (not (equal type 'TWOWORD))
                 (not (equal type 'LONG))
                 (not (equal type 'DOUBLE)))
            (not (bcv::isassignable type 'TWOWORD env)))
   :hints (("Goal" :in-theory (enable bcv::isjavaassignable)))))

(local 
 (defthm len-bcv-pushoperandstack-reduce
   (implies (and (bcv::isAssignable t1 t2 env)
                 (syntaxp (equal (car t2) 'QUOTE))
                 (not (equal t2 'topx)))
            (equal (len (bcv::pushoperandstack t1 stk))
                   (len (bcv::pushoperandstack t2 stk))))))



;----------------------------------------------------------------------
;
;   FACTS 
; 

(defthm len-bcv-pushoperandstack-reference-env-sig-s
  (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM"))
                           (s))
                (bcv::isAssignable t1 'reference (env-sig s)))
           (equal (len (bcv::pushoperandstack t1 stk))
                  (+ 1 (len stk)))))



