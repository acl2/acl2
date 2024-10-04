(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")
(include-book "../../BCV/typechecker")




(local (defthm isArrayType-in-consistent-heap-means-consistent-array-object
  (implies (and (isArrayType (obj-type (deref2 ref hp1)))
                (consistent-heap2 hp1 hp cl acl id))
           (consistent-array-object (deref2 ref hp1) hp cl acl))
  :hints (("Goal" :in-theory (e/d (rref binding deref2 obj-type)
                                  (consistent-array-object))
           :do-not '(generalize)))))


(local (defthm isArrayType-in-consistent-heap-means-consistent-array-object-real
  (implies (and (isArrayType  (obj-type (deref2 ref hp)))
                (consistent-heap hp cl acl)) 
           ;; here it has a free avariable ACL if used as a forward chaining
           (consistent-array-object (deref2 ref hp) hp cl acl))
  :hints (("Goal" :in-theory (enable consistent-heap)))
  :rule-classes :forward-chaining))


(defthm isArrayType-in-consistent-state-consistent-array-object
  (implies (and (isArrayType (obj-type (deref2 v (heap s))))
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl))
           (consistent-array-object (deref2 v (heap s))
                                    (heap s)
                                    cl acl))
  :hints (("Goal" :in-theory (enable consistent-state))))


(encapsulate ()
  (local (include-book "base-array"))
  (defthm element-at-consistent-array-not-deref2-init
    (implies (and (consistent-array-object (deref2 array-ref (heap s))
                                           (heap s)
                                           (instance-class-table s)
                                           (array-class-table s))
                  (check-ARRAY (rREF array-ref) index s) ;; we can assume this
                  (NOT (EQUAL (ELEMENT-AT-ARRAY INDEX (RREF ARRAY-REF) S) '-1))
                  (consistent-state s)
                  (not (primitive-type? (array-component-type (obj-type (deref2 array-ref (heap s)))))))
             (not (consp (deref2-init (tag-REF (element-at-array index (rREF array-ref) s))
                                      (heap-init-map (aux s))))))
    :hints (("Goal" :in-theory (e/d () (deref2-init tag-REF array-data
                                                    TAG-REF-TAG 
                                                    heap-init-map))))))

(in-theory (disable TAG-REF-TAG isArrayType array-type-s deref2-init REFp
                    reference-type-s
                    nullp))


(defthm isArrayType-componenent-type-not-primitive-implies-initialized
  (implies (and (isArrayType (obj-type (deref2 v (heap s)))) 
                (not (primitive-type? (array-component-type  
                                       (obj-type (deref2 v (heap s))))))
                (consistent-state s)
                (not (equal (element-at-array index (rREF v) s) -1))
                (check-array (rREF v) index s))
           (NOT (CONSP (DEREF2-INIT (TAG-REF (ELEMENT-AT-ARRAY INDEX
                                                               (rREF v)
                                                               S))
                                      (heap-init-map (aux s)))))))



(local (in-theory (disable TAG-REF-TAG)))
(local  (defthm tag-tag-REF-specific
          (implies (not (primitive-type? (array-component-type (obj-type (deref2 v hp)))))
                   (equal (tag x (array-component-type (obj-type (deref2 v hp))))
                          (tag-REF x)))
          :hints (("Goal" :in-theory (enable tag tag-REF)))))

;; this following is a better rule to export!! 

(defthm element-of-array-is-consistent-value-specific-AARARY
  (implies (and (isArrayType (obj-type (deref2 v (heap s))))
                (not (primitive-type? (array-component-type (obj-type (deref2 v
                                                                              (heap s))))))
                (check-array (rREF v) index s)
                (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp))
           (consistent-value-x  (tag-REF (element-at-array index (rREF v) s))
                                cl hp))
  :hints (("Goal" :use ((:instance
                         element-of-array-is-consistent-value-specific))
           :in-theory (disable element-of-array-is-consistent-value-specific))))







