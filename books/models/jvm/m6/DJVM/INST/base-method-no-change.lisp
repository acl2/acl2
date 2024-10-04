(in-package "DJVM")
(include-book "base")


(encapsulate () 
 (local (include-book "base-load-class-normalize"))
 (defthm deref-method-not-changing-if-exist-getArrayClass
  (implies (and (consistent-state s)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (deref-method method-ptr (instance-class-table
                                            (getArrayClass any s)))
                  (deref-method method-ptr (instance-class-table s)))))
                                 
 
 (defthm deref-method-not-changing-if-exist-resolveClassReference
   (implies (and (consistent-state s)
                 (equal (method-ptr (current-frame s)) method-ptr))
            (equal (deref-method method-ptr (instance-class-table
                                             (resolveClassReference any s)))
                   (deref-method method-ptr (instance-class-table s))))))


(defthm valid-method-ptr-implies-class-loaded
  (implies (valid-method-ptr method-ptr (instance-class-table s))
           (class-loaded? (method-ptr-classname method-ptr) s))
  :hints (("Goal" :in-theory (e/d (deref-method class-exists? 
                                                class-loaded?
                                                valid-method-ptr)
                                  (isClassTerm)))))


(defthm consistent-state-not-native-implies-valid-method-ptr
  (implies (and (consistent-state s)
                (equal (method-ptr (current-frame s)) method-ptr))
           (valid-method-ptr method-ptr 
                             (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (deref-method class-exists? 
                                                class-loaded?
                                                valid-method-ptr)
                                  (isClassTerm)))))












(encapsulate () 
   (local (include-book "base-skip-proofs"))
   (defthm deref-method-no-change-after-raise-exception
     (implies (class-loaded? (method-ptr-classname method-ptr) s)
              (equal (deref-method method-ptr (instance-class-table 
                                               (raise-exception any s)))
                     (deref-method method-ptr (instance-class-table s))))))



