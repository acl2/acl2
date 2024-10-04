(in-package "DJVM")
(include-book "djvm-simple")


(defthm consistent-state-wff-state-f 
  (implies (consistent-state s)
           (wff-state s))
  :rule-classes :forward-chaining)



(defthm consistent-state-wff-thread-table-f 
  (implies (consistent-state s)
           (wff-thread-table (thread-table s)))
  :rule-classes :forward-chaining)


(defthm consistent-state-wff-thread-f 
  (implies (consistent-state s)
           (wff-thread (thread-by-id (current-thread s)
                                     (thread-table s))))
  :rule-classes :forward-chaining)


(defthm consistent-state-wff-thread-call-stack-f 
  (implies (consistent-state s)
           (wff-call-stack 
            (thread-call-stack (thread-by-id (current-thread s)
                                             (thread-table s)))))
  :rule-classes :forward-chaining)


(defthm consistent-state-current-frame-guard-f
  (implies (consistent-state s)
           (current-frame-guard s))
  :hints (("Goal" :in-theory (enable current-frame-guard)))
  :rule-classes :forward-chaining)



(defthm consistent-state-current-frame-f
  (implies (consistent-state s)
           (wff-call-frame (current-frame s)))
  :hints (("Goal" :in-theory (enable current-frame)))
  :rule-classes :forward-chaining)



(defthm consistent-state-wff-method-ptr-f
  (implies (consistent-state s)
           (wff-method-ptr (current-method-ptr s)))
  :rule-classes :forward-chaining)


(defthm consistent-state-wff-class-table-f
  (implies (consistent-state s)
           (wff-class-table (class-table s)))
  :rule-classes :forward-chaining)


(defthm consistent-state-wff-instance-class-table-f
  (implies (consistent-state s)
           (wff-instance-class-table (instance-class-table s)))
  :rule-classes :forward-chaining)



(defthm consistent-state-wff-method-decl-f
  (implies (consistent-state s)
           (wff-method-decl (deref-method (current-method-ptr s)
                                          (instance-class-table s))))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------
;----------------------------------------------------------------------


(skip-proofs 
 (defthm consistent-state-wff-code-f
   (implies (consistent-state s)
            (wff-code (method-code (deref-method (current-method-ptr s)
                                                 (instance-class-table s)))))
   :rule-classes :forward-chaining))



(skip-proofs 
 (defthm consistent-state-wff-insts-f
   (implies (consistent-state s)
            (wff-insts (code-instrs (method-code (deref-method (current-method-ptr s)
                                                               (instance-class-table s))))))
   :rule-classes :forward-chaining))


;;; these two that I have not added into the consistent-state assertions!!! 
 
;----------------------------------------------------------------------
;----------------------------------------------------------------------


;; (defthm consistent-state-strong-implies-next-inst-guard
;;   (implies (consistent-state-strong jvm::s)
;;            (AND
;;             (WFF-STATE JVM::S)
;;             (CURRENT-FRAME-GUARD JVM::S)
;;             (WFF-CALL-FRAME (CURRENT-FRAME JVM::S))
;;             (WFF-METHOD-PTR (CURRENT-METHOD-PTR JVM::S))
;;             (WFF-CLASS-TABLE (CLASS-TABLE JVM::S))
;;             (WFF-INSTANCE-CLASS-TABLE (INSTANCE-CLASS-TABLE JVM::S))
;;             (WFF-METHOD-DECL
;;              (DEREF-METHOD (CURRENT-METHOD-PTR JVM::S)
;;                            (INSTANCE-CLASS-TABLE JVM::S)))
;;             (WFF-CODE
;;              (METHOD-CODE
;;               (DEREF-METHOD (CURRENT-METHOD-PTR JVM::S)
;;                             (INSTANCE-CLASS-TABLE JVM::S))))
;;             (WFF-INSTS
;;              (CODE-INSTRS
;;               (METHOD-CODE
;;                (DEREF-METHOD (CURRENT-METHOD-PTR JVM::S)
;;                              (INSTANCE-CLASS-TABLE JVM::S)))))))
;;   :hints (("Goal" :in-theory (e/d (consistent-state-strong)
;;                                   (wff-state 
;;                                    method-code
;;                                    code-instrs
;;                                    current-method-ptr
;;                                    current-frame-guard
;;                                    wff-call-frame
;;                                    wff-method-ptr
;;                                    wff-class-table
;;                                    wff-instance-class-table
;;                                    wff-method-decl
;;                                    wff-code
;;                                    wff-insts)))))

