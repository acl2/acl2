(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")


(local 
 (encapsulate ()
    (local (include-book "base-bcv-support"))
    (defthm isMatchingType-INT-implies-canPopCategory1 
         (implies (bcv::isMatchingType 'INT (opstack-sig stack cl hp hp-init method-ptr) env)
                  (canPopCategory1 stack))
         :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) ())))
         :rule-classes :forward-chaining)

    (defthm isMatchingType-AARRAY-implies-canPopCategory1 
      (implies (bcv::isMatchingType '(ARRAY (class "java.lang.Object")) 
                                    (opstack-sig stack cl hp hp-init method-ptr) env)
               (canPopCategory1 stack))
      :hints (("Goal" :in-theory (enable bcv::isMatchingType canPopCategory1)))
      :rule-classes :forward-chaining)))


(defthm isMatchingType-INT-implies-canPopCategory1-fact
  (implies (bcv::isMatchingType 'INT 
                                (opstack-sig (operand-stack (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (e/d (bcv::isMatchingType) ()))))



(defthm isMatchingType-AARRAY-implies-canPopCategory1-fact
  (implies (bcv::isMatchingType '(ARRAY (class "java.lang.Object")) 
                                (opstack-sig (operand-stack (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s)))))


;; (i-am-here) ;; Tue May 17 23:01:25 2005

(local 
 (defthm isMatchingType-size-of-1-type-opstack-sig-implies-canPopCategory1
   (implies (and (bcv::ismatchingtype type (opstack-sig stk cl hp hp-init
                                                        method-ptr) env)
                 type
                 (equal (bcv::sizeof type) 1)
                 (not (equal type 'topx)))
            (canpopcategory1 stk))
   :hints (("Goal" :in-theory (e/d (bcv::sizeof bcv::ismatchingtype) (canpopcategory1))))))

(defthm isMatchingType-java-lang-Object-implies-canPopCategory1-fact
  (implies (bcv::isMatchingType '(class "java.lang.Object")
                                (opstack-sig (operand-stack (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (e/d (bcv::sizeof) (canpopcategory1
                                                 bcv::isMatchingType)))))



;----------------------------------------------------------------------
;; (i-am-here) ;; Fri Jun 17 13:01:49 2005 a month later!! 

(defthm isMatchingType-prefix-class-implies-canPopCategory1-fact
  (implies (bcv::isMatchingType (BCV::PREFIX-CLASS any)
                                (opstack-sig (operand-stack (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))
                                (env-sig s))
           (canPopCategory1 (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (e/d (bcv::sizeof) (canpopcategory1
                                                 bcv::isMatchingType)))))


;----------------------------------------------------------------------


(skip-proofs  ;; Fri Jul 29 15:56:51 2005!! 
 (defthm isMatchingType-REFERENCE-implies-canPopCategory1-fact
   (implies (bcv::isMatchingType 'REFERENCE
                                 (opstack-sig (operand-stack (current-frame s))
                                              (instance-class-table s)
                                              (heap s)
                                              (heap-init-map (aux s))
                                              (method-ptr (current-frame s)))
                                 (env-sig s))
            (canPopCategory1 (operand-stack (current-frame s))))))

