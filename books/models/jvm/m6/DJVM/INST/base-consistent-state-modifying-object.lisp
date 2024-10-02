(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")

(local (include-book "base-consistent-state-modifying-object-support"))

                
(defthm wff-heap-strong-bind
  (implies (and (wff-heap-strong hp)
                (wff-obj-strong new-obj))
           (wff-heap-strong (bind vx new-obj hp)))
  :hints (("Goal" :in-theory (enable wff-heap))))

(defthm not-NULLp-REFp-implies-bound?
  (implies (and (REFp v hp)
                (not (NULLp v)))
           (bound? (rREF v) hp)))

(defthm bind-bounded-consistent-heap
  (implies (and (consistent-heap hp cl acl)
                (consistent-object new-obj hp cl)
                (or (not (isArrayType (obj-type new-obj)))
                    (consistent-array-object new-obj hp cl acl))
                (equal (obj-type new-obj) (obj-type (binding vx hp)))
                (bound? vx hp))
           (consistent-heap (bind vx new-obj hp) cl acl))
  :hints (("Goal" :in-theory (e/d (consistent-heap) (consistent-object
                                                     consistent-heap1 consistent-heap2))
           :do-not-induct t)))

(defthm bind-bound-consistent-heap-init-state
   (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp)))
                 (or (not (isArrayType (obj-type new-obj)))
                     (and (wff-internal-array new-obj)
                          (OR (PRIMITIVE-TYPE? (array-component-type (obj-type new-obj)))
                              (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA new-obj)
                                                         HP-INIT)))))
            (consistent-heap-array-init-state (bind vx new-obj hp)
                                              cl acl hp-init)))




(defthm bind-bounded-consistent-decls 
  (implies (and (consistent-class-decls cl1 cl hp)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-class-decls cl1 cl (bind vx new-obj hp))))



(defthm bind-bounded-consistent-thread-table
   (implies (and (consistent-thread-table threads cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-thread-table threads cl (bind vx new-obj hp)))
  :hints (("Goal" :in-theory (disable consistent-thread-entry))))




(defthm bind-bound-consistent-heap-init-state
  (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp)))
                (or (not (isArrayType (obj-type new-obj)))
                    (and (wff-internal-array new-obj)
                         (OR (PRIMITIVE-TYPE? (array-component-type (obj-type new-obj)))
                             (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA new-obj)
                                                        HP-INIT)))))
           (consistent-heap-array-init-state (bind vx new-obj hp)
                                             cl acl hp-init)))










