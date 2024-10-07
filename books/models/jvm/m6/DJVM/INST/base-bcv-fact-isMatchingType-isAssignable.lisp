(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")

;----------------------------------------------------------------------

(local (include-book "base-bcv-support"))

(local 
 (defthm bcv-isMatchingType-bcv-isAssignable
   (implies (and (bcv::isMatchingType typ stk env)
                 (equal (bcv::sizeof typ) 1))
            (bcv::isAssignable (car stk) typ env))
   :hints (("Goal" :in-theory (enable bcv::isMatchingType)))))


(defthm bcv-isMatchingType-bcv-isAssignable-specific
  (implies (and (bcv::isMatchingType typ (opstack-sig 
                                          (operand-stack (current-frame s))
                                          cl hp hp-init method-ptr) env)
                (canPopCategory1 (operand-stack (current-frame s)))
                (equal (bcv::sizeof typ) 1))
           (bcv::isAssignable (value-sig (topStack s)
                                         cl hp hp-init method-ptr) typ env)))


;----------------------------------------------------------------------


;----------------------------------------------------------------------


;; (defthm isMatchingType-isAssignableTo
;;   (implies 
;;    (BCV::ISMATCHINGTYPE
;;     (BCV::PREFIX-CLASS (BCV::FIELDCLASSNAMECP (BCV::ARG1 INST)))
;;     (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
;;                  (INSTANCE-CLASS-TABLE S)
;;                  (HEAP S)
;;                  (HEAP-INIT-MAP (AUX S))
;;                  (METHOD-PTR (CURRENT-FRAME S)))
;;     (ENV-SIG S))
;;    (bcv::isAssignable (value-sig (topStack s)
;;                                  cl hp hp-init method-ptr) 
;;                       typ env)))

