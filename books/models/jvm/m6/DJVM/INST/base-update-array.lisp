(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")


(local 
 (defthm consistent-heap-array-init-state3-array-content-initialized
   (implies (and (consistent-heap-array-init-state3 hp hp-init)
                 (bound? v hp)
                 (isArrayType (obj-type (binding v hp)))
                 (wff-internal-array (binding v hp))
                 (not (primitive-type? (array-component-type 
                                        (obj-type (binding v hp))))))
            (array-content-initialized 
             (array-data (binding v hp)) hp-init))
   :hints (("Goal" 
            :in-theory (enable binding bound? 
                               array-content-initialized)
            :do-not '(generalize)))))



(local 
 (defthm isArrayType-implied-by-wff-internal-array
   (implies (wff-internal-array obj)
            (isArrayType (obj-type obj)))))


(defthm consistent-state-array-content-initialized
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v))
                (not (primitive-type? (array-component-type
                                       (obj-type (deref2 v (heap s))))))
                (check-array-guard (rREF v) (heap s))
                (equal (heap-init-map (aux s)) hp-init))
           (array-content-initialized
            (array-data (deref2 v (heap s)))
            hp-init))
  :hints (("Goal" :in-theory (e/d (REFp NULLp check-array-guard
                                        deref2)
                                  (binding-rref-normalize)))))

(local 
 (defthm array-content-initialized-set-element-at-lemma
   (implies (and (array-content-initialized l hp-init)
                 (integerp index)                
                 (<= 0 index)
                 (< index (len l)))
            (array-content-initialized 
             (update-nth index -1 l)
             hp-init))
   :hints (("Goal" :in-theory (enable array-data binding)))))
                                      

(defthm array-content-initialized-set-element-at
  (implies (and (array-content-initialized (array-data array) hp-init)
                (integerp index)                
                (<= 0 index)
                (< index (len (array-data array))))
           (array-content-initialized 
            (array-data
             (car (set-element-at 
                   index -1 
                   array s)))
            hp-init))
  :hints (("Goal" :in-theory (enable array-data binding))))
                                      

(local 
 (defthm array-content-initialized-set-element-at-2-lemma
   (implies (and (array-content-initialized l hp-init)
                 (integerp index)                
                 (<= 0 index)
                 (< index (len l))
                 (or (not (bound? (rREF v) hp-init))
                     (not (consp (deref2-init v hp-init)))))
            (array-content-initialized 
             (update-nth index (value-of v) l)
             hp-init))
   :hints (("Goal" :in-theory (e/d 
                               (array-data deref2 
                                           bound? binding
                                           rREF value-of
                                           deref2-init)
                               (binding-rref-normalize))))))
                              

(defthm array-content-initialized-set-element-at-2
  (implies (and (array-content-initialized (array-data array) hp-init)
                (integerp index)                
                (<= 0 index)
                (< index (len (array-data array)))
                (or (not (bound? (rREF v) hp-init))
                    (not (consp (deref2-init v hp-init)))))                
           (array-content-initialized 
            (array-data
             (car (set-element-at 
                   index (value-of v)
                   array s)))
            hp-init))
  :hints (("Goal" :in-theory (enable array-data))))

                                      
(defthm wff-internal-array-implies-within-bound
  (implies (wff-internal-array obj)
           (equal (len (array-data obj))
                  (array-bound obj)))
  :hints (("Goal" :in-theory (enable wff-internal-array
                                     array-bound
                                     array-data))))


