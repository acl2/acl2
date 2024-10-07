(in-package "DJVM")
(include-book "../../DJVM/consistent-state")

(in-theory (disable isClassTerm consistent-object
                    java-visible-portion
                    fields deref2 rREF isArrayType
                    class-exists? super binding bound?))

(local (include-book "base-object-field-always-initialized-support"))



(defthm object-field-is-always-initialized
  (implies (and (case-split (not (primitive-type? 
                                  (get-field-type
                                   fieldclassname
                                   fieldname cl))))
                (not (isArrayType (obj-type (deref2 v (heap s)))))
                (not (bound? nil hp-init))
                (not (bound? -1 hp-init))
                (consistent-object-init-state 
                 (deref2 v (heap s))
                 cl hp-init)
                (consistent-object (deref2 v (heap s))
                                   (heap s)
                                   cl))
           (not (bound? (m6-getfield fieldclassname
                                     fieldname
                                     (rREF v) s)
                        hp-init)))
  :hints (("Goal" :in-theory (e/d () (fields m6-getfield consistent-object-init-state))
           :cases ((binding fieldclassname (java-visible-portion (binding (rREF
                                                                           v)
                                                                          (heap s))))))))


