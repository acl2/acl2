(in-package "DJVM")
(include-book "base")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")
(include-book "../../DJVM/consistent-state")
(include-book "base-djvm-functions")

;; doesn't hurt to have this expander exported!! 
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
                      (T NIL)))))))

;;; this above can be exported! 


(defthm primitive-type-primitive-type-equal
  (implies (and (djvm::primitive-type? typ1)
                (djvm::primitive-type? typ2))
           (equal (bcv::isAssignable typ1 typ2 any-env)
                  (equal typ1 typ2)))
  :hints (("Goal" :in-theory (enable primitive-type?))))

;;; this is also a nice rule! 



(local 
 (encapsulate ()
              (local (include-book "base-skip-proofs"))
              (defthm djvm-isjavaassignment-compatible-cl-implies-BCV-isJavaAssignable
                (implies (and (isJavaAssignmentCompatible rtype type cl)
                              (reference-type-s rtype cl)
                              (reference-type-s type cl)
                              (consistent-class-hierachy cl)
                              (class-table-is-loaded-from cl (bcv::scl-bcv2jvm scl)))
                         (bcv::isjavaassignable (fix-sig rtype) (fix-sig type) scl))
                :hints (("Goal" :do-not-induct t
                         :in-theory (e/d () (bcv::isJavaAssignable
                                             fix-sig
                                             isJavaAssignmentCompatible
                                             reference-type-s
                                             array-component-type component-type))
                         :do-not '(generalize))))))
;;;
;;; skip proof this!!  Sat Apr 30 17:58:16 2005
;;;

(local (defthm primitive-type-isJavaAssignment-compatible
         (implies (and (PRIMITIVE-TYPE? RTYPE)
                       (not (equal rtype type)))
                  (not (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL)))))


(local (defthm primitive-type-isJavaAssignment-compatible-2
         (implies (and (not (PRIMITIVE-TYPE? RTYPE))
                       (primitive-type? type))
                  (not (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL)))
         :hints (("Goal" :in-theory (enable primitive-type?)))))

;;; (i-am-here) ;; Mon May  2 20:57:20 2005


(local 
 (defthm wff-icl-fact
   (implies (bcv::wff-icl icl)
            (not (class-exists? 'NULL icl)))
   :hints (("Goal" :in-theory (enable class-exists? classname)))))

(local 
 (defthm good-icl-fact-1
   (implies (bcv::good-icl icl)
            (not (class-exists? 'NULL icl)))
   :hints (("Goal" :in-theory (enable bcv::good-icl)))))


(local (defthm not-primitive-type-not-fix-sig-primitive-type
  (implies (not (primitive-type? type))
           (not (primitive-type? (fix-sig type))))
  :hints (("Goal" :in-theory (enable primitive-type?)))))



(local (defthm good-icl-implies-consistent-class-hierachy
  (implies (bcv::good-icl icl)
           (consistent-class-hierachy icl))
  :hints (("Goal" :in-theory (enable bcv::good-icl)))
  :rule-classes :forward-chaining))

;;; not sure why we need these simple theorems

(local (defthm icl-scl-compatible-implies-class-table-loaded-from
         (implies (bcv::icl-scl-compatible icl scl)
                  (class-table-is-loaded-from icl (bcv::scl-bcv2jvm scl)))
         :hints (("Goal" :in-theory (e/d (bcv::icl-scl-compatible)
                                         (class-table-is-loaded-from))))
         :rule-classes :forward-chaining))

(local 
 (defthm icl-scl-compatible-implies-class-table-loaded-from-b
   (implies (bcv::icl-scl-compatible icl scl)
            (class-table-is-loaded-from icl (bcv::scl-bcv2jvm scl)))
   :hints (("Goal" :in-theory (e/d (bcv::icl-scl-compatible)
                                   (class-table-is-loaded-from))))))

(local 
 (defthm good-java-type-not-top-fact
   (implies (bcv::good-java-type type icl)
            (not (equal type 'topx)))))


(local 
 (defthm primitive-is-java-assignable-implies-equal
   (implies (and (primitive-type? rtype)
                 (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL))
            (equal (equal rtype type) t))
   :hints (("Goal" :in-theory (enable isjavaassignmentcompatible)))))


(local (defthm primitive-is-java-assignable-implies-equal-specific
  (implies (and (primitive-type? rtype)
                (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL))
           (equal (fix-sig type) rtype))
  :hints (("Goal" :in-theory (enable isjavaassignmentcompatible)))))
           

(defthm reference-type-s-implied-by-existing
  (implies (class-exists? typ cl)
           (reference-type-s typ cl)))


(local 
 (defthm not-stringp-implies-not-class-exists
   (implies (and (not (stringp typ))
                 (bcv::wff-icl cl))
            (not (class-exists? typ cl)))
   :hints (("Goal" :in-theory (enable class-exists? 
                                      classname
                                      bcv::good-icl)))))


;; (defthm class-exists-good-icl
;;   (implies (and (CLASS-EXISTS? TYPE CL)
;;                 (bcv::good-icl icl))
;;            (NOT (PRIMITIVE-TYPE? TYPE)))
;;   :hints (("Goal" :in-theory (enable primitive-type?))))


(local (defthm bcv-good-scl-equal-equal
  (implies (bcv::good-scl scl)
           (equal (BCV::SCL-JVM2BCV (BCV::SCL-BCV2JVM SCL)) scl))))

;; (i-am-here) ;; Mon May  2 22:00:52 2005


(defthm classtableEnvironment-fake-env
  (equal (bcv::classtableEnvironment (fake-env scl))
         scl)
  :hints (("Goal" :in-theory (enable bcv::classtableEnvironment))))

(in-theory (disable fake-env))


(local (defthm |Subgoal 4'|
  (IMPLIES (AND (CLASS-EXISTS? RTYPE CL)
                (CLASS-EXISTS? TYPE CL)
              (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL)
              (BCV::GOOD-JAVA-TYPE (FIX-SIG RTYPE) CL)
              (BCV::GOOD-JAVA-TYPE (FIX-SIG TYPE) CL)
              (BCV::GOOD-ICL CL)
              (EQUAL (BCV::SCL-JVM2BCV (BCV::SCL-BCV2JVM SCL))
                     SCL)
              (CLASS-TABLE-IS-LOADED-FROM CL (BCV::SCL-BCV2JVM SCL)))
         (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                            (FIX-SIG TYPE)
                            (FAKE-ENV SCL)))
  :hints (("Goal" 
           :in-theory (disable bcv::good-scl bcv::good-icl
                               djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable)
           :use
           djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable
           :do-not-induct t
           :expand (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                                      (FIX-SIG TYPE)
                                      (FAKE-ENV SCL))))))

(local (defthm |Subgoal 3'|
  (IMPLIES (AND (CLASS-EXISTS? RTYPE CL)
              (NOT (PRIMITIVE-TYPE? TYPE))
              (ARRAY-TYPE-S TYPE CL)
              (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL)
              (BCV::GOOD-JAVA-TYPE (FIX-SIG RTYPE) CL)
              (BCV::GOOD-JAVA-TYPE (FIX-SIG TYPE) CL)
              (BCV::GOOD-ICL CL)
              (EQUAL (BCV::SCL-JVM2BCV (BCV::SCL-BCV2JVM SCL))
                     SCL)
              (CLASS-TABLE-IS-LOADED-FROM CL (BCV::SCL-BCV2JVM SCL)))
         (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                            (FIX-SIG TYPE)
                            (FAKE-ENV SCL)))
  :hints (("Goal" 
           :in-theory (disable bcv::good-scl bcv::good-icl
                               djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable)
           :use
           djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable
           :do-not-induct t
           :expand (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                                      (FIX-SIG TYPE)
                                      (FAKE-ENV SCL))))))


(local (defthm |Subgoal 2'|
  (IMPLIES (AND (ARRAY-TYPE-S RTYPE CL)
                (NOT (PRIMITIVE-TYPE? TYPE))
                (CLASS-EXISTS? TYPE CL)
                (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL)
                (BCV::GOOD-JAVA-TYPE (FIX-SIG RTYPE) CL)
                (BCV::GOOD-JAVA-TYPE (FIX-SIG TYPE) CL)
                (BCV::GOOD-ICL CL)
                (EQUAL (BCV::SCL-JVM2BCV (BCV::SCL-BCV2JVM SCL))
                       SCL)
                (CLASS-TABLE-IS-LOADED-FROM CL (BCV::SCL-BCV2JVM SCL)))
           (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                              (FIX-SIG TYPE)
                              (FAKE-ENV SCL)))
  :hints (("Goal" 
           :in-theory (disable bcv::good-scl bcv::good-icl
                               djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable)
           :use
           djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable
           :do-not-induct t
           :expand (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                                      (FIX-SIG TYPE)
                                      (FAKE-ENV SCL))))))


(local (defthm |Subgoal 1'|
  (IMPLIES (AND (ARRAY-TYPE-S RTYPE CL)
                (NOT (PRIMITIVE-TYPE? TYPE))
                (ARRAY-TYPE-S TYPE CL)
                (ISJAVAASSIGNMENTCOMPATIBLE RTYPE TYPE CL)
                (BCV::GOOD-JAVA-TYPE (FIX-SIG RTYPE) CL)
                (BCV::GOOD-JAVA-TYPE (FIX-SIG TYPE) CL)
                (BCV::GOOD-ICL CL)
                (EQUAL (BCV::SCL-JVM2BCV (BCV::SCL-BCV2JVM SCL))
                       SCL)
              (CLASS-TABLE-IS-LOADED-FROM CL (BCV::SCL-BCV2JVM SCL)))
           (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                              (FIX-SIG TYPE)
                              (FAKE-ENV SCL)))
  :hints (("Goal" 
           :in-theory (disable bcv::good-scl bcv::good-icl
                               djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable)
           :use
           djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable
           :do-not-induct t
           :expand (BCV::ISASSIGNABLE (FIX-SIG RTYPE)
                                      (FIX-SIG TYPE)
                                      (FAKE-ENV SCL))))))


;;;; this is the rule that we want to export to 
;;;;
;;;; base-consistent-state.lisp
;;;;
;;;; Mon May  2 21:33:38 2005


(defthm djvm-assignment-compatible-cl-implies-BCV-isAssignable
  (implies (and (AssignmentCompatible rtype type cl)
                (bcv::good-java-type (fix-sig rtype) cl)
                (bcv::good-java-type (fix-sig type) cl)
                (bcv::good-icl cl)
                (bcv::icl-scl-compatible cl scl))
           (bcv::isAssignable (fix-sig rtype) (fix-sig type) (fake-env scl)))
  :hints (("Goal" :in-theory (e/d (assignmentcompatible bcv::isAssignable)
                                  (isJavaAssignmentCompatible bcv::good-icl
                                                              bcv::isjavaassignable))
           :do-not-induct t
           :do-not '(fertilize)
           :restrict
           ((djvm-isJavaAssignment-compatible-cl-implies-BCV-isJavaAssignable
             ((cl cl)))))))

