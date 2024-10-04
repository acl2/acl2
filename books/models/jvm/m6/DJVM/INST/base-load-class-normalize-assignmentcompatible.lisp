(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")


(local (include-book "base-load-class-normalize-class-by-name"))
(local (in-theory (e/d (class-exists? class-loaded?) (isClassTerm))))
(local (include-book "base-valid-type-s"))

(local 
 (defthm valid-type-s-still-valid-type-s-after-resolveClassReference
   (implies (valid-type-s any (instance-class-table s) mode)
            (valid-type-s any (instance-class-table 
                               (resolveClassreference name s)) mode))
   :hints (("Goal" :do-not '(generalize)))))


(local 
 (defthm reference-type-s-still-reference-type-s-after-resolveClassReferenc
   (implies (reference-type-s any (instance-class-table s))
            (reference-type-s any (instance-class-table (resolveClassreference name s))))
   :hints (("Goal" :use ((:instance valid-type-s-is
                                    (type any)
                                    (cl (instance-class-table s)))
                         (:instance valid-type-s-is
                                    (type any)
                                    (cl (instance-class-table
                                         (resolveClassreference name s)))))))))


(local 
 (encapsulate () 
      (local (include-book "base-consistent-state-load-class"))
      (defthm resolveClassReference-preserve-consistency
        (implies (consistent-state s)
                 (consistent-state (resolveClassReference any s))))))


(local 
 (defthm consistent-class-hierachy-implied-by-consistent-state
   (implies (consistent-state s)
            (CONSISTENT-CLASS-HIERACHY
             (INSTANCE-CLASS-TABLE s)))
   :hints (("Goal" :in-theory (enable consistent-state)))))


(local 
 (defthm isJavaSubclassOf1-remains-isJavaSubclassOf-after-loading
   (implies (and (consistent-state s)
                 (isJavaSubclassOf1 from to (instance-class-table s) seen))
            (isJavaSubclassOf1 from to 
                               (instance-class-table 
                                (resolveClassreference any s)) seen))
   :hints (("Goal" :do-not '(generalize)))))



(local 
 (defthm isJavaAssignmentcompatible-remain-isJavaAssignmentCompatible-after-loading
   (implies (and (consistent-state s)
                 (isJavaAssignmentCompatible from to (instance-class-table s)))
            (isJavaAssignmentCompatible from to  (instance-class-table 
                                                  (resolveClassreference any
                                                                         s))))
   :hints (("Goal" :do-not '(generalize)))))



(defthm assignmentCompatible-remain-assignmentCompatible-after-loading
  (implies (and (consistent-state s)
                (assignmentCompatible from to (instance-class-table s)))
           (assignmentCompatible from to 
                                 (instance-class-table 
                                  (resolveClassreference any s)))))



;----------------------------------------------------------------------

(local (in-theory (disable getArrayClass)))


(local 
 (defthm valid-type-s-still-valid-type-s-after-getArrayClass
   (implies (valid-type-s any (instance-class-table s) mode)
            (valid-type-s any (instance-class-table 
                               (getArrayClass name s)) mode))
   :hints (("Goal" :do-not '(generalize)))))


(local 
 (defthm reference-type-s-still-reference-type-s-after-getArrayClass
   (implies (reference-type-s any (instance-class-table s))
            (reference-type-s any (instance-class-table (getArrayClass name s))))
   :hints (("Goal" :use ((:instance valid-type-s-is
                                    (type any)
                                    (cl (instance-class-table s)))
                         (:instance valid-type-s-is
                                    (type any)
                                    (cl (instance-class-table
                                         (getArrayClass name s)))))))))


(local 
 (encapsulate () 
      (local (include-book "base-consistent-state-load-class"))
      (defthm getArrayClass-preserve-consistency
        (implies (consistent-state s)
                 (consistent-state (getArrayClass any s))))))



(local 
 (defthm isJavaSubclassOf1-remains-isJavaSubclassOf-after-loading-2
   (implies (and (consistent-state s)
                 (isJavaSubclassOf1 from to (instance-class-table s) seen))
            (isJavaSubclassOf1 from to 
                               (instance-class-table 
                                (getArrayClass any s)) seen))
   :hints (("Goal" :do-not '(generalize)))))



(local 
 (defthm isJavaAssignmentcompatible-remain-isJavaAssignmentCompatible-after-loading-2
   (implies (and (consistent-state s)
                 (isJavaAssignmentCompatible from to (instance-class-table s)))
            (isJavaAssignmentCompatible from to  (instance-class-table 
                                                  (getArrayClass any s))))
   :hints (("Goal" :do-not '(generalize)))))



(defthm assignmentCompatible-remain-assignmentCompatible-after-loading-2
  (implies (and (consistent-state s)
                (assignmentCompatible from to (instance-class-table s)))
           (assignmentCompatible from to 
                                 (instance-class-table 
                                  (getArrayClass any s)))))


