(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")


(local (include-book "base-bcv-support"))
;; The problem we want to avoid all reference to isAssignable
 ;; part of strategy!! 
(local 
 (defthm isAssignable-to-array-class-java-lang-Object-implies-not-deref2-init-specific
   (implies (and (bcv::isAssignable (value-sig (topStack s)
                                               (instance-class-table s)
                                               (heap s)
                                               (heap-init-map (aux s))
                                               (method-ptr (current-frame s)))
                                    '(array (class "java.lang.Object"))
                                    (env-sig s))
                 (not (nullp (topStack s)))
                 (consistent-value-x (topStack s) (instance-class-table s)
                                     (heap s))
                 (equal (heap-init-map (aux s)) hp-init))
            (not (consp (deref2-init (topStack s) hp-init))))))

(local (include-book "base-bcv-fact-isMatchingType-isAssignable"))
 
(local 
  (defthm bcv-isMatchingType-bcv-isAssignable-specific
   (implies (and (bcv::isMatchingType typ (opstack-sig 
                                           (operand-stack (current-frame s))
                                           cl hp hp-init method-ptr) env)
                 (canPopCategory1 (operand-stack (current-frame s)))
                 (equal (bcv::sizeof typ) 1))
            (bcv::isAssignable (value-sig (topStack s)
                                          cl hp hp-init method-ptr) typ env))))

(defthm isMatchingType-to-array-class-java-lang-Object-implies-not-deref2-init-specific
   (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
                                      (opstack-sig (operand-stack (current-frame s))
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame s)))
                                    (env-sig s))
                 (not (nullp (topStack s)))
                 (consistent-value-x (topStack s) (instance-class-table s)
                                     (heap s))
                 (equal (heap-init-map (aux s)) hp-init))
            (not (consp (deref2-init (topStack s) hp-init))))
   :hints (("Goal" :in-theory (disable consistent-value-x))))



(skip-proofs 
 (defthm isMatchingType-to-java-lang-Object-implies-not-deref2-init-specific
   (implies (and (bcv::isMatchingType '(class "java.lang.Object")
                                      (opstack-sig (operand-stack (current-frame s))
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame s)))
                                    (env-sig s))
                 (not (nullp (topStack s)))
                 (consistent-value-x (topStack s) (instance-class-table s)
                                     (heap s))
                 (equal (heap-init-map (aux s)) hp-init))
            (not (consp (deref2-init (topStack s) hp-init))))
   :hints (("Goal" :in-theory (disable consistent-value-x)))))

;; this above is subsumed by the following: Sat Jul 23 17:33:22 2005


;----------------------------------------------------------------------

;;
;; Sat Jul 23 17:32:55 2005
;;

(skip-proofs 
 (defthm isMatchingType-to-class-type-implies-not-deref2-init-specific
   (implies (and (bcv::isMatchingType (bcv::prefix-class any)
                                      (opstack-sig (operand-stack (current-frame s))
                                                    (instance-class-table s)
                                                    (heap s)
                                                    (heap-init-map (aux s))
                                                    (method-ptr (current-frame
                                                                 s)))
                                       (env-sig s))
                  (not (nullp (topStack s)))
                  (consistent-value-x (topStack s) (instance-class-table s)
                                      (heap s))
                  (equal (heap-init-map (aux s)) hp-init))
             (not (consp (deref2-init (topStack s) hp-init))))
   :hints (("Goal" :in-theory (disable consistent-value-x)))))


(in-theory (disable deref2-init))



