(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")

(include-book "base-valid-type-s")
(include-book "base-consistent-state")

(local (include-book "base-consistent-state-consistent-object-support"))

(defthm consistent-object-valid-type-strong
  (implies (and (consistent-object obj (heap s) (instance-class-table s))
                (or (not (isArrayType (obj-type obj)))
                    (consistent-array-object obj (heap s) 
                                             (instance-class-table s)
                                             (array-class-table s)))
                (consistent-state s))
           (valid-type-strong (obj-type obj) (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-object 
                                   consistent-array-object) ()))))



(defthm class-loaded-consistent-state-implies-valid-type-strong
  (implies (and (class-loaded? any s)
                (consistent-state s))
           (valid-type-strong any (instance-class-table s)))
  :hints (("Goal" :in-theory (enable class-loaded?))))



