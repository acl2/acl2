(in-package "DJVM")

(include-book "base-consistent-state")



(local 
 (skip-proofs 
  (defthm consistent-class-table-not-stringp-not-class-exists?-f
    (implies (and (consistent-class-table cl scl hp)
                  (not (stringp type)))
             (not (class-exists? type cl)))
    :rule-classes :forward-chaining)))

(local 
 (defthm consistent-class-table-not-stringp-not-class-exists?-b
   (implies (and (consistent-class-table cl scl hp)
                 (not (stringp type)))
            (not (class-exists? type cl)))))


(local 
 (defthm consistent-class-table-implies-not-class-exists
   (implies  (consistent-class-table cl scl hp)
             (not (CLASS-EXISTS? 'NULL Cl)))
   :hints (("Goal" :in-theory (disable consistent-class-table)))))

(local 
 (defthm array-component-type-is-component-type
   (equal (array-component-type type)
          (component-type type))
   :hints (("Goal" :in-theory (enable array-component-type component-type)))))


(local 
 (defthm not-component-type-null-bound
   (implies (and (consistent-class-table cl scl hp)
                 (CLASS-EXISTS? TYPE CL))
            (not (equal (component-type type) 'NULL)))
   :hints (("Goal" :in-theory (e/d (component-type)
                                   (consistent-class-table))))))

(local 
 (defthm isArrayType-not-class-exists
   (implies (and (consistent-class-table cl scl hp)
                 (isArrayType type))
            (not (class-exists? type cl)))
   :hints (("Goal" :in-theory (e/d (isArrayType) (consistent-class-table))))))
            

(defthm reference-type-s-implies-good-java-type
  (implies (and (reference-type-s type cl)
                (consistent-class-table cl scl hp)
                (not (equal type 'NULL)))
           (bcv::good-java-type (fix-sig type) cl))
  :hints (("Goal" :induct (bcv::good-java-type (fix-sig type) cl)
           :do-not '(generalize)
           :in-theory (e/d (array-type-s) (consistent-class-table
                                           component-type)))))



