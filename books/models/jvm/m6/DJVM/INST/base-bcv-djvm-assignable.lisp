(in-package "DJVM")

;;
;; to reason about relation between djvm::assignment-compatible between bcv::isAssignable
;;
;; To be included by AALOAD.lisp 
;;
;; Mon May  2 22:23:38 2005


(include-book "base-consistent-state")

(defthm consistent-value-value-type-array-declare-type
  (implies (and (consistent-value v type cl hp)
                (REFp v hp)
                (not (NULLp v)))
           (AssignmentCompatible (obj-type (deref2 v hp)) type cl))
  :hints (("Goal" :in-theory (e/d (consistent-value REFp) 
                                  (AssignmentCompatible)))))


(acl2::set-verify-guards-eagerness 0)

(include-book "base-djvm-functions")
;; (defun fake-env (scl)
;;   (bcv::makeenvironment 'class 'method 'returntype 'mergedcode 'maxstack
;;                         'handlers scl)))

(defthm classtableEnvironment-fake-env
  (equal (bcv::classtableEnvironment (fake-env scl))
         scl)
  :hints (("Goal" :in-theory (enable bcv::classtableEnvironment))))

(in-theory (disable fake-env))

(encapsulate () 
  (local (include-book "base-bcv-isAssignable-facts"))
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
               ((cl cl))))))))


(local 
 (defthm same-scl-judgement-same
   (implies (equal (bcv::classtableEnvironment env2) 
                   (bcv::classtableEnvironment env1))
            (equal (bcv::isassignable typ1 typ2  env2)
                   (bcv::isassignable typ1 typ2  env1)))
   :rule-classes nil))


(defthm classTableEnv-of-fake-env
  (equal (bcv::classtableEnvironment (fake-env scl))
         scl))

(local 
 (defthm same-scl-judgement-same-specific
   (implies (bcv::isassignable typ1 typ2 (fake-env (bcv::classtableEnvironment
                                                    (env-sig s))))
            (bcv::isassignable typ1 typ2 (env-sig s)))
   :hints (("Goal" :in-theory (e/d (fake-env) (bcv::isassignable 
                                               fake-env
                                               bcv::classtableEnvironment
                                               env-sig))
            :use ((:instance same-scl-judgement-same
                             (env2 (fake-env (bcv::classtableEnvironment
                                              (env-sig s))))
                             (env1 (env-sig s))))))))


(defthm same-scl-judgement-same-specific-x
  (implies (bcv::isassignable (fix-sig typ1) (fix-sig typ2) (fake-env (bcv::classtableEnvironment
                                                   (env-sig s))))
           (bcv::isassignable (fix-sig typ1) (fix-sig typ2) (env-sig s)))
  :hints (("Goal" :in-theory (e/d (fake-env) (bcv::isassignable 
                                              fake-env
                                              bcv::classtableEnvironment
                                              env-sig)))))





(defthm value-sig-being-fix-sig
  (implies (and (REFp v hp)
                (not (NULLp v))
                (not (consp (deref2-init v hp-init))))
           (equal (value-sig v cl hp hp-init method-ptr)
                  (fix-sig (obj-type (deref2 v hp))))))






(in-theory (disable TAG-REF-TAG))

(local (defthm tag-tag-REF
  (implies (not (primitive-type? type))
           (equal (tag v type)
                  (tag-REF v)))
  :hints (("Goal" :in-theory (enable tag tag-REF)))))


(defthm tag-tag-REF-specific
  (implies (not (primitive-type? (array-component-type (obj-type (deref2 v hp)))))
           (equal (tag x (array-component-type (obj-type (deref2 v hp))))
                  (tag-REF x)))
  :hints (("Goal" :in-theory (enable tag tag-REF))))




;; ;----------------------------------------------------------------------

(local 
 (encapsulate ()
  (local (include-book "base-reference-type-s-good-java-type"))
     (defthm reference-type-s-implies-good-java-type
       (implies (and (reference-type-s type cl)
                     (consistent-class-table cl scl hp)
                     (not (equal type 'NULL)))
                (bcv::good-java-type (fix-sig type) cl)))))


(local 
 (defthm reference-type-s-implies-good-java-type-specific
   (implies (and (reference-type-s type (instance-class-table s))
                 (consistent-state s)
                 (not (equal type 'NULL)))
            (bcv::good-java-type (fix-sig type) (instance-class-table s)))
   :hints (("Goal" :in-theory (e/d (consistent-state) (consistent-class-table))))))


(local 
 (encapsulate () 
  (local (include-book "base-REFp-reference-type-s"))
  (defthm REFp-implies-reference-type-s
    (implies (and (consistent-state s)
                  (REFp v (heap s))
                  (not (NULLp v)))
             (reference-type-s (obj-type (deref2 v (heap s)))
                               (instance-class-table s)))
    :hints (("Goal" :in-theory (disable reference-type-s REFp))))))

(local 
 (defthm consistent-object-implies-obj-type-not-NULL
   (implies (and (consistent-state s)
                 (consistent-object obj (heap s) (instance-class-table s)))
            (not (equal (obj-type obj) 'NULL)))
   :hints (("Goal" :in-theory (enable consistent-object)))))

(local 
 (defthm REFp-not-NULL-implies-obj-type-not-NULL
   (implies (and (consistent-state s)
                 (REFp v (heap s))
                 (not (NULLp v)))
            (not (equal (obj-type (deref2 v (heap s))) 'NULL)))))


(defthm bcv-good-java-type-if-converted-from-type-of-consistent-object
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v)))
           (bcv::good-java-type (fix-sig (obj-type (deref2 v (heap s))))
                                (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d () (REFp fix-sig bcv::good-java-type))
           :cases ((isArrayType (obj-type (deref2 v (heap s))))))))



(local (defthm bcv-good-java-type-if-converted-from-type-of-consistent-object-2-lemma
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v))
                (array-type-s (obj-type (deref2 v (heap s)))
                              (instance-class-table s)))
           (bcv::good-java-type (fix-sig (array-component-type (obj-type (deref2 v (heap s)))))
                                (instance-class-table s)))
  :hints (("Goal" :in-theory (enable array-type-s)))))



(defthm bcv-good-java-type-if-converted-from-type-of-consistent-object-2
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v))
                (isArrayType (obj-type (deref2 v (heap s)))))
           (bcv::good-java-type (fix-sig (array-component-type (obj-type (deref2 v (heap s)))))
                                (instance-class-table s)))
  :hints (("Goal" :cases ((primitive-type? (array-component-type (obj-type
                                                                  (deref2 v
                                                                          (heap s)))))))))


(local (defthm consistent-class-table-implies-bcv-wff-icl
         (implies (consistent-class-decls cl1 cl hp)
                  (bcv::wff-icl cl1))
         :rule-classes :forward-chaining))

;; Fri Jul 15 14:38:25 2005
;; this following proof fails. 
;; as our modification to good-icl!! 
;;
;; to get rid of the skip-proofs in bcv-isAssignable-transitive.lisp!! 
;;

(encapsulate ()
  (local (include-book "base-consistent-state-good-icl-etc"))
  (defthm consistent-state-implies-good-icl
    (implies (consistent-state s)
             (bcv::good-icl (instance-class-table s))))

  (defthm consistent-state-implies-icl-scl-compatible
    (implies (consistent-state s)
             (BCV::ICL-SCL-COMPATIBLE (INSTANCE-CLASS-TABLE S)
                                      (BCV::CLASSTABLEENVIRONMENT (env-sig s))))
    :hints (("Goal" :in-theory (enable consistent-state)))))

(local 
 (defthm isAssignable-NULL-not-primitive-type
   (implies (and (not (primitive-type? type))
                 (bcv::good-java-type type icl)
                 (bcv::icl-scl-compatible icl (bcv::classtableenvironment env)))
            (bcv::isAssignable 'NULL type env))))


(defthm isAssignable-NULL-not-primitive-type-specific
  (implies (and (not (primitive-type? type))
                (bcv::good-java-type type (instance-class-table s))
                (bcv::icl-scl-compatible (instance-class-table s)
                                         (bcv::classtableenvironment (env-sig s))))
           (bcv::isAssignable 'NULL type (env-sig s))))

;----------------------------------------------------------------------

;;; (i-am-here)

;;;; 

(defthm consistent-value-tag-REF-implies-REFp-specific-x-specific
   (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness
                                                            "DJVM")) (s))
                 (consistent-value-x (tag-REF v) (instance-class-table s) (heap s))
                 (equal (heap s) hp))
            (REFp (tag-REF v) hp))
   :hints (("Goal" :in-theory (e/d () (REFp)))))


(encapsulate ()
 (local (include-book "base-array"))
 (local 
  (defthm element-of-array-is-consistent-value-specific
    (implies (and (consistent-array-object (deref2 v (heap s)) 
                                           (heap s)
                                           (instance-class-table s)
                                           (array-class-table s))
                  (check-array (rREF v) index s)
                  (equal (instance-class-table s) cl)
                  (equal (heap s) hp))
             (consistent-value (tag (element-at-array index (rREF v) s)
                                    (array-component-type (obj-type (deref2 v
                                                                            (heap s)))))
                               (array-component-type (obj-type (deref2 v (heap s))))
                               cl hp))))

  (defthm element-of-array-is-consistent-value-tag-REF-specific
    (implies (and (consistent-array-object (deref2 v (heap s)) 
                                           (heap s)
                                           (instance-class-table s)
                                           (array-class-table s))
                  (check-array (rREF v) index s)
                  (not (primitive-type? 
                        (array-component-type (obj-type (deref2 v (heap s))))))
                  (equal (instance-class-table s) cl)
                  (equal (heap s) hp))
             (consistent-value (tag-REF (element-at-array index (rREF v) s))
                               (array-component-type (obj-type (deref2 v (heap s))))
                               cl hp))
    :hints (("Goal" :use element-of-array-is-consistent-value-specific))))




(encapsulate () 
   (local (include-book "base-array-facts"))
   (defthm element-of-array-is-consistent-value-specific-AARARY
     (implies (and (isArrayType (obj-type (deref2 v (heap s))))
                   (not (primitive-type? (array-component-type (obj-type (deref2 v
                                                                                 (heap s))))))
                   (check-array (rREF v) index s)
                   (consistent-state s)
                   (equal (instance-class-table s) cl)
                   (equal (heap s) hp))
              (consistent-value-x  (tag-REF (element-at-array index (rREF v) s))
                                   cl hp))))

;; (i-am-here) ;; Tue May 17 14:03:16 2005


(local 
 (encapsulate () 
              (local (include-book "base-consistent-state-more"))
              (defthm consistent-state-null-not-bounded?
                (implies (and (consistent-state s)
                              (nullp v))
                         (not (deref2 v (heap s)))))))


(defthm isArrayType-implies-not-NULLp
  (implies (and (consistent-state s)
                (isArrayType (obj-type (deref2 v (heap s)))))
           (not (NULLp v)))
  :hints (("Goal" :in-theory (e/d (isArrayType obj-type) (deref2))))
  :rule-classes :forward-chaining)


(defthm not-primitive-type-primitive-type
  (implies (NOT (PRIMITIVE-TYPE? type))
           (not (primitive-type? (fix-sig type))))
  :hints (("Goal" :in-theory (enable primitive-type?))))

;;(i-am-here) ;; Thu May  5 14:13:38 2005


(local 
 (encapsulate () 
              (local (include-book "base-array-facts"))
              (defthm isArrayType-in-consistent-state-consistent-array-object
                (implies (and (isArrayType (obj-type (deref2 v (heap s))))
                              (consistent-state s)
                              (equal (instance-class-table s) cl)
                              (equal (array-class-table s) acl))
                         (consistent-array-object (deref2 v (heap s))
                                                  (heap s)
                                                  cl acl)))))





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
             (env-sig s)))
  :hints (("Goal" :in-theory (e/d () (bcv::isAssignable heap-init-map 
                                                        env-sig fake-env
                                                        deref2-init
                                                        array-data
                                                        bcv::good-java-type
                                                        frame-sig
                                                        bcv::good-icl
                                                        bcv::isarraytype
                                                        bcv::isclasstype
                                                        bcv::icl-scl-compatible
                                                        Assignmentcompatible
                                                        bcv::classtableenvironment
                                                        BCV::ARRAYELEMENTTYPE
                                                        REFp nullp
                                                        isarraytype))
           :restrict ((djvm-assignment-compatible-cl-implies-BCV-isAssignable
                       ((cl (instance-class-table s))))))))


(defthm value-sig-tag-primitive-type
  (implies (primitive-type? type)
           (equal (value-sig (tag v type) cl hp hp-init current-method)
                  (djvm-translate-int-type type)))
  :hints (("Goal" :in-theory (enable primitive-type? value-sig REFp
                                     wff-tagged-value
                                     tag-of tag wff-REFp NULLp))))
           

;; (defthm Array-element-type-is-more-specific-than-type-declaration-2-primitive-type
;;   (implies  (and (consistent-state s)
;;                  (isArrayType (obj-type (deref2 v (heap s))))
;;                  (primitive-type? 
;;                   (array-component-type (obj-type (deref2 v (heap s)))))
;;                  (check-array (rREF v) index s))
;;             (bcv::isAssignable
;;              (VALUE-SIG
;;               (TAG (ELEMENT-AT-ARRAY index (RREF v) S)
;;                    (array-component-type (obj-type (deref2 v (heap s)))))
;;               (instance-class-table s)
;;               (heap s)
;;               (heap-init-map (aux s))
;;               (method-ptr (current-frame s)))
;;              (array-component-type 
;;               (obj-type (deref2 v (heap s))))
;;              (env-sig s)))
;;   :hints (("Goal" :in-theory (e/d () (bcv::isAssignable heap-init-map 
;;                                                         env-sig fake-env
;;                                                         deref2-init
;;                                                         array-data
;;                                                         bcv::good-java-type
;;                                                         frame-sig
;;                                                         bcv::good-icl
;;                                                         bcv::isarraytype
;;                                                         bcv::isclasstype
;;                                                         bcv::icl-scl-compatible
;;                                                         Assignmentcompatible
;;                                                         bcv::classtableenvironment
;;                                                         BCV::ARRAYELEMENTTYPE
;;                                                         REFp nullp
;;                                                         isarraytype)))))



