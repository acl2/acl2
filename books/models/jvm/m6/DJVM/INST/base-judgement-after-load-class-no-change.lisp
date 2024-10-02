(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")


(local 
 (encapsulate ()
   (local (include-book "base-load-class-normalize-deref2"))

   (defthm deref2-no-change-after-resolveClassReference
      (implies (and (not (NULLp v))
                    (consistent-state s)
                    (REFp v (heap s)))
               (equal (deref2 v (heap (resolveclassreference any s)))
                      (deref2 v (heap s)))))

   (defthm REFp-remains-REFp-resolveCalssReference
      (implies (REFp v (heap s))
               (REFp v (heap (resolveClassReference any s))))
      :hints (("Goal" :in-theory (e/d (resolveClassReference) (REFp)))))))
   

(local 
 (encapsulate ()
   (local (include-book "base-load-class-normalize-assignmentcompatible"))
   (defthm assignmentCompatible-remain-assignmentCompatible-after-loading
     (implies (and (consistent-state s)
                   (assignmentCompatible from to (instance-class-table s)))
              (assignmentCompatible from to 
                                    (instance-class-table 
                                     (resolveClassreference any s)))))))

;;;;
;;;; Note: 
;;;;
;;;; we proved resolveClassreference preserves consistent-state 
;;;; However this is different from proving above lemma. 
;;;; 
;;;; We follow a different approach We proved the consistent-state is preserved
;;;; by load_class2 load_class_x ...  We keep the big properties and decompose
;;;; the operation.
;;;;
;;;; here we want to prove small properties of big operations
;;;; 
;;;; We could have proved resolveClassreference preserve consistency this way!!



(defthm
   consistent-value-remain-consistent-value-after-resolveClassReference
   (implies (and (consistent-state s)
                 (consistent-value v type (instance-class-table s) (heap s)))
            (consistent-value v type
                              (instance-class-table 
                               (resolveClassReference any s))
                             (heap (resolveClassReference any s))))
  :hints (("Goal" :in-theory (e/d () 
                                  (resolveClassReference 
                                   obj-type
                                   assignmentcompatible
                                   REFp NULLp primitive-type?
                                   consistent-state
                                   REFp)))))



(defthm
  consistent-value-x-remain-consistent-value-x-after-resolveClassReference
  (implies (and (consistent-state s)
                (consistent-value-x v (instance-class-table s) (heap s)))
           (consistent-value-x v 
                               (instance-class-table 
                                (resolveClassReference any s))
                               (heap (resolveClassReference any s))))
  :hints (("Goal" :in-theory (e/d () (resolveClassReference)))))






(local 
 (encapsulate ()
   (local (include-book "base-load-class-normalize-class-by-name"))
   (defthm class-by-name-no-change-after-resolveClassReference
   (implies (isClassTerm (class-by-name name (instance-class-table s)))
            (equal (class-by-name name (instance-class-table
                                        (resolveclassreference any s)))
                   (class-by-name name (instance-class-table s)))))))

(local (in-theory (disable classname super obj-type isClassTerm resolveClassReference)))                                               


(local 
 (defthm consistent-field-remain-consistent-field-resolveClassReference
   (implies (and (consistent-state s)
                 (consistent-field field field-decl (instance-class-table s) (heap s))
                 (equal (heap (resolveClassReference any s)) hp))
            (consistent-field field field-decl
                            (instance-class-table 
                             (resolveClassReference any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (resolveClassReference
                                    assignmentcompatible
                                    isClassTerm
                                    consistent-state))))))






(local 
 (defthm consistent-fields-remain-consistent-fields-resolveClassReference
   (implies (and (consistent-state s)
                 (consistent-fields fields field-decls (instance-class-table s) (heap s))
                 (equal (heap (resolveClassReference any s)) hp))
            (consistent-fields fields field-decls
                            (instance-class-table 
                             (resolveClassReference any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (resolveClassReference
                                    consistent-field
                                    isClassTerm
                                    consistent-state))))))





(local 
 (defthm consistent-immedidate-instance-remain-consistent-immedidate-instance-resolveClassReference
   (implies (and (consistent-state s)
                 (consistent-immedidate-instance type instance (instance-class-table s) (heap s))
                 (equal (heap (resolveClassReference any s)) hp))
            (consistent-immedidate-instance type instance
                            (instance-class-table 
                             (resolveClassReference any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (resolveClassReference
                                    consistent-field
                                    isClassTerm
                                    consistent-state))))))



(local
 (defthm consistent-immedidate-instance-implies-bounded?
   (implies (consistent-immedidate-instance type instance 
                                            (instance-class-table s)
                                            (heap s))
            (isClassTerm (class-by-name type (instance-class-table s))))))

                                                           


(local 
 (defthm loaded-remain-loaded
   (implies (and (isClassTerm (class-by-name name (instance-class-table s)))
                 (consistent-state s))
            (isClassTerm 
             (class-by-name name 
                            (instance-class-table
                             (resolveClassReference any s)))))))





(local 
 (defthm consistent-jvp-remain-consistent-jvp-resolveClassReference
   (implies (and (consistent-state s)
                 (consistent-jvp type obj (instance-class-table s) (heap s))
                 (equal (heap (resolveClassReference any s)) hp))
            (consistent-jvp type  obj
                            (instance-class-table 
                             (resolveClassReference any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (resolveClassReference
                                    isClassTerm
                                    consistent-immedidate-instance
                                    consistent-state))
            :do-not '(generalize)))))



(defthm consistent-object-remain-consistent-object-resolveClassReference
  (implies (and (consistent-state s)
                (consistent-object obj (heap s) (instance-class-table s))
                (equal (heap (resolveClassReference any s)) hp))
           (consistent-object obj
                              hp
                              (instance-class-table 
                               (resolveClassReference any s))))
  :hints (("Goal" :in-theory (e/d (consistent-object)
                                  (resolveClassReference
                                   consistent-jvp
                                   isClassTerm
                                   obj-type
                                   consistent-state)))))

;----------------------------------------------------------------------




(local 
 (encapsulate ()
   (local (include-book "base-load-class-normalize-deref2"))


   (defthm deref2-no-change-after-getArrayClass 
     (implies (and (not (NULLp v))
                   (consistent-state s)
                   (REFp v (heap s)))
              (equal (deref2 v (heap (getArrayClass any s)))
                     (deref2 v (heap s)))))

   (defthm REFp-remains-REFp-getArrayClass
      (implies (REFp v (heap s))
               (REFp v (heap (getArrayClass any s)))))))
   

(local 
 (encapsulate ()
   (local (include-book "base-load-class-normalize-assignmentcompatible"))
   (defthm assignmentCompatible-remain-assignmentCompatible-after-loading-2
     (implies (and (consistent-state s)
                   (assignmentCompatible from to (instance-class-table s)))
              (assignmentCompatible from to 
                                    (instance-class-table 
                                     (getArrayClass any s)))))))

;;;;
;;;; Note: 
;;;;
;;;; we proved resolveClassreference preserves consistent-state 
;;;; However this is different from proving above lemma. 
;;;; 
;;;; We follow a different approach We proved the consistent-state is preserved
;;;; by load_class2 load_class_x ...  We keep the big properties and decompose
;;;; the operation.
;;;;
;;;; here we want to prove small properties of big operations
;;;; 
;;;; We could have proved resolveClassreference preserve consistency this way!!



(defthm
   consistent-value-remain-consistent-value-after-getArrayClass
   (implies (and (consistent-state s)
                 (consistent-value v type (instance-class-table s) (heap s)))
            (consistent-value v type
                              (instance-class-table 
                               (getArrayClass any s))
                             (heap (getArrayClass any s))))
  :hints (("Goal" :in-theory (e/d () 
                                  (getArrayClass 
                                   obj-type
                                   assignmentcompatible
                                   REFp NULLp primitive-type?
                                   consistent-state
                                   REFp)))))



(defthm
  consistent-value-x-remain-consistent-value-x-after-getArrayClass
  (implies (and (consistent-state s)
                (consistent-value-x v (instance-class-table s) (heap s)))
           (consistent-value-x v 
                               (instance-class-table 
                                (getArrayClass any s))
                               (heap (getArrayClass any s))))
  :hints (("Goal" :in-theory (e/d () (getArrayClass)))))






(local 
 (encapsulate ()
   (local (include-book "base-load-class-normalize-class-by-name"))
   (defthm class-by-name-no-change-after-getArrayClass
   (implies (isClassTerm (class-by-name name (instance-class-table s)))
            (equal (class-by-name name (instance-class-table
                                        (getArrayClass any s)))
                   (class-by-name name (instance-class-table s)))))))

(local (in-theory (disable classname super obj-type isClassTerm getArrayClass)))                                               


(local 
 (defthm consistent-field-remain-consistent-field-getArrayClass
   (implies (and (consistent-state s)
                 (consistent-field field field-decl (instance-class-table s) (heap s))
                 (equal (heap (getArrayClass any s)) hp))
            (consistent-field field field-decl
                            (instance-class-table 
                             (getArrayClass any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (getArrayClass
                                    assignmentcompatible
                                    isClassTerm
                                    consistent-state))))))


(local 
 (defthm consistent-fields-remain-consistent-fields-getArrayClass
   (implies (and (consistent-state s)
                 (consistent-fields fields field-decls (instance-class-table s) (heap s))
                 (equal (heap (getArrayClass any s)) hp))
            (consistent-fields fields field-decls
                            (instance-class-table 
                             (getArrayClass any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (getArrayClass
                                    consistent-field
                                    isClassTerm
                                    consistent-state))))))





(local 
 (defthm consistent-immedidate-instance-remain-consistent-immedidate-instance-getArrayClass
   (implies (and (consistent-state s)
                 (consistent-immedidate-instance type instance (instance-class-table s) (heap s))
                 (equal (heap (getArrayClass any s)) hp))
            (consistent-immedidate-instance type instance
                            (instance-class-table 
                             (getArrayClass any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (getArrayClass
                                    consistent-field
                                    isClassTerm
                                    consistent-state))))))



;; (local
;;  (defthm consistent-immedidate-instance-implies-bounded?
;;    (implies (consistent-immedidate-instance type instance 
;;                                             (instance-class-table s)
;;                                             (heap s))
;;             (isClassTerm (class-by-name type (instance-class-table s))))))


(local 
 (defthm loaded-remain-loaded-2
   (implies (and (isClassTerm (class-by-name name (instance-class-table s)))
                 (consistent-state s))
            (isClassTerm 
             (class-by-name name 
                            (instance-class-table
                             (getArrayClass any s)))))))





(local 
 (defthm consistent-jvp-remain-consistent-jvp-getArrayClass
   (implies (and (consistent-state s)
                 (consistent-jvp type obj (instance-class-table s) (heap s))
                 (equal (heap (getArrayClass any s)) hp))
            (consistent-jvp type  obj
                            (instance-class-table 
                             (getArrayClass any s))
                             hp))
   :hints (("Goal" :in-theory (e/d ()
                                   (getArrayClass
                                    isClassTerm
                                    consistent-immedidate-instance
                                    consistent-state))
            :do-not '(generalize)))))






(defthm consistent-object-remain-consistent-object-getArrayClass
  (implies (and (consistent-state s)
                (consistent-object obj (heap s) (instance-class-table s))
                (equal (heap (getArrayClass any s)) hp))
           (consistent-object obj
                              hp
                              (instance-class-table 
                               (getArrayClass any s))))
  :hints (("Goal" :in-theory (e/d (consistent-object)
                                  (getArrayClass
                                   consistent-jvp
                                   isClassTerm
                                   obj-type
                                   consistent-state)))))


(include-book "base-valid-type-s")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")


(encapsulate () 
  (local (include-book "base-load-class-normalize-isAssignableTo"))
  (defthm isAssignableTo-isAssignableTo-resolveClassReference
    (implies (and (car (isAssignableTo typ1 typ2 s))
                  (valid-type-strong typ1 (instance-class-table s))
                  (consistent-state s)
                  (no-fatal-error? (resolveClassReference any s)))
             (car (isAssignableTo typ1 typ2 (resolveClassReference any s))))))

                               


