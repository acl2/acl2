(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-bytecode")

(encapsulate ()
  (local (include-book "base-consistent-state-load-class-support"))
  (defthm consistent-state-add-new-object-generalized-x
    (implies (and (consistent-state s)
                  (consistent-object obj hp (instance-class-table s))
                  (equal (heap s) hp)
                  (or (not (isArrayType (obj-type obj)))
                      (and (consistent-array-object obj hp
                                                    (instance-class-table s)
                                                    (array-class-table s))
                           (or (primitive-type? (array-component-type (obj-type obj)))
                               (array-content-initialized (array-data obj) (heap-init-map
                                                                            (aux s)))))))
             (consistent-state  (state-set-heap 
                                 (bind (len hp)
                                       obj hp) s)))
    :hints (("Goal" :in-theory (disable state-set-heap)))))
