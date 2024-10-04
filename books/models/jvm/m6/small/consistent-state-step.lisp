(in-package "ACL2")
(include-book "jvm-model")
(include-book "consistent-state")

(defun consistent-state-step (st)
  (let*  ((method-table (g 'method-table st))
          (call-stack   (g 'call-stack st)))
    (and (pc-in-range st)
         (wff-method-table (g 'method-table st))
         (consistent-call-stack call-stack method-table)
         (all-method-verified method-table))))



;; (defun consistent-state-step (st) 
;;   (let*  ((method-table (g 'method-table st))
;;           (call-stack   (g 'call-stack st)))
;;     (and (consistent-call-stack call-stack method-table)
;;          (all-method-verified method-table))))

(defthm consistent-state-step-implies-implies-consistent-state
  (implies (consistent-state-step s)
           (consistent-state s))
  :rule-classes nil)

;--- EXPORT --- 
(defthm consistent-call-stack-implied-by-consistent-state
  (implies (consistent-state st)
           (consistent-call-stack (g 'call-stack st)
                                  (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-all-method-verified
  (implies (consistent-state st)
           (all-method-verified (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-pc-in-range
  (implies (consistent-state st)
           (pc-in-range st))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)



(defthm consistent-state-wff-method-table
  (implies (consistent-state st)
           (wff-method-table (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-call-stack-implied-by-consistent-state-b
  (implies (consistent-state st)
           (consistent-call-stack (g 'call-stack st)
                                  (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state))))

(defthm consistent-state-all-method-verified-b
  (implies (consistent-state st)
           (all-method-verified (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-pc-in-range-b
  (implies (consistent-state st)
           (pc-in-range st))
  :hints (("Goal" :in-theory (enable consistent-state))))



(defthm consistent-state-wff-method-table-b
  (implies (consistent-state st)
           (wff-method-table (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state))))


;----------------------------------------------------------------------

(defthm consistent-state-current-method-bound
  (implies (consistent-state st)
           (bound? (G 'METHOD-NAME
                      (topx (G 'CALL-STACK ST)))
                   (G 'METHOD-TABLE ST)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-current-method-bound-b
  (implies (consistent-state st)
           (assoc-equal (G 'METHOD-NAME
                           (car (G 'CALL-STACK ST)))
                        (G 'METHOD-TABLE ST)))
  :hints (("Goal" :in-theory (enable consistent-state))))

