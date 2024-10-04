(in-package "DJVM")
(include-book "base-consistent-state")


(local (defthm REFp-not-NULLp-implies-consistent-object
  (implies (and (REFp v (heap s))
                (not (NULLp v))
                (consistent-state s))
           (consistent-object (deref2 v (heap s)) (heap s)
                              (instance-class-table s)))))


(local (defthm consistent-object-obj-heap-cl
  (implies (and (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj))))
           (reference-type-s (obj-type obj) cl))
  :hints (("Goal" :in-theory (e/d (consistent-object) (isClassTerm))))))


(local (defthm consistent-object-obj-heap-cl-specific
  (implies (and (consistent-object obj (heap s) (instance-class-table s))
                (not (isArrayType (obj-type obj))))
           (reference-type-s (obj-type obj) (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-object) (isClassTerm))))))




(local (defthm consistent-array-object-consistent-state
  (implies (and (not (NULLp v))
                (REFp v (heap s))
                (isArrayType (obj-type (deref2 v (heap s))))
                (consistent-state s))
           (consistent-array-object
            (deref2 v (heap s))
            (heap s)
            (instance-class-table s)
            (array-class-table s)))
  :rule-classes :forward-chaining))


(local (defthm consistent-array-object-implies-reference-type-s
  (implies (consistent-array-object obj hp cl acl)
           (reference-type-s (obj-type obj) cl))
  :hints (("Goal" :in-theory (enable consistent-array-object)))
  :rule-classes :forward-chaining))

(defthm obj-type-deref-consistent-state
    (implies (and (not (NULLp v))
                  (REFp v (heap s))
                  (consistent-state s))
             (reference-type-s (obj-type (deref2 v (heap s)))
                               (instance-class-table s)))
    :hints (("Goal" :cases ((isArrayType (obj-type (deref2 v (heap s)))))
             :in-theory (disable NULLp reference-type-s REFp))))
