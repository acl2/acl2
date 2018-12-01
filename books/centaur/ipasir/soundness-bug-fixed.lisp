
;; This used to illustrate a soundness bug in ipasir; now, the second-to-last
;; event fails because we can't functionally instantiate ipasir-solve$a due to
;; its unknown constraint from the define-trusted-clause-processor form.

(in-package "IPASIR")

(include-book "ipasir-logic")
(include-book "ipasir-backend")

;; This is just a minimal function that returns something that is not
;; determined by the constraints on ipasir-solve -- i.e. (for any sane solver)
;; it just returns :sat, but it could also produce :failed according to the
;; ipasir-solve constraint.
(define ipasir-example (state)
  (with-local-ipasir
    (mv-let (ans ipasir state)
      (mv-let (ans ipasir)
        (ipasir-solve ipasir)
        (mv ans ipasir state))
      (mv ans state))))

;; We'll use execution to prove that there exists some ACL2 state for which the
;; above function produces :sat. (Namely, all of them, but we only have to show
;; it for one.)  The only way I know how to do that is with a clause processor...
(defun-sk exists-state-where-ipasir-example-is-sat ()
  (exists (st)
          (equal (mv-nth 0 (ipasir-example st)) :sat)))

;; If we execute ipasir-example and it produces sat, that proves that it
;; produces sat on some state.
(define exists-state-cp ((clause pseudo-term-listp) hint state)
  (declare (ignore hint))
  (if (equal clause '((exists-state-where-ipasir-example-is-sat)))
      (b* (((mv ans state) (ipasir-example state)))
        (if (equal ans :sat)
            ;; we showed there exists a state -- the clause is proved
            (value nil)
          ;; failed -- return the clause
          (value (list clause))))
    ;; failed -- return the clause
    (value (list clause))))

(defevaluator exists-state-ev exists-state-ev-lst
  ((exists-state-where-ipasir-example-is-sat)
   (ipasir-example st)
   (if a b c)
   (not a)
   (equal a b)))

;; prove the clause processor correct...
(encapsulate nil
  (local (include-book "clause-processors/join-thms" :dir :system))
  (local (acl2::def-join-thms exists-state-ev))


  (defthm exists-state-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp alist)
                  (exists-state-ev (acl2::conjoin-clauses
                                    (acl2::clauses-result (exists-state-cp clause hint state)))
                                   alist))
             (exists-state-ev (acl2::disjoin clause) alist))
    :hints(("Goal" :in-theory (enable exists-state-cp)))
    :rule-classes :clause-processor))


(defthm exists-state
  (exists-state-where-ipasir-example-is-sat)
  :hints (("goal" :clause-processor (exists-state-cp acl2::clause nil state))))

;; Now, we'll invent a second implementation of ipasir-solve$a that satisfies
;; its constraint but provably NEVER produces SAT, and use that to prove a
;; contradiction.

;; Solver "implementation" that always fails
(define ipasir-solve-impl ((ipasir$a ipasir$a-p))
  (mv :failed
      (change-ipasir$a ipasir$a
                       :status :input
                       :new-clause nil
                       :assumption nil
                       :history (cons :solve (ipasir$a->history ipasir$a)))))

;; Same example (though non-executable) using the always-failing implemetation
(defun-nx ipasir-example-impl (st)
  (WITH-LOCAL-STOBJ
    IPASIR
    (MV-LET (ANS IPASIR ST)
      (MV-LET (ANS IPASIR ST)
        (MV-LET (IPASIR ST)
          (non-exec (IPASIR-INIT IPASIR ST))
          (MV-LET (ANS IPASIR)
            (NON-EXEC (IPASIR-SOLVE-IMPL IPASIR))
            (MV ANS IPASIR ST)))
        (LET* ((IPASIR (IPASIR-RELEASE IPASIR)))
              (MV ANS IPASIR ST)))
      (MV ANS ST))))

(defun-sk exists-state-where-ipasir-example-impl-is-sat ()
  (exists (st)
          (equal (mv-nth 0 (ipasir-example-impl st)) :sat)))



(defthm not-exists-state-impl
  (not (exists-state-where-ipasir-example-impl-is-sat))
  :hints (("goal" 
           :in-theory (enable exists-state-where-ipasir-example-impl-is-sat
                              ipasir-example-impl
                              ipasir-solve-impl)))
  :rule-classes nil)

;; For whatever reason we have to supply a functional substitution for
;; ipasir-solve$c additionally...
(defun-nx ipasir-solve$c-impl (ipa)
  (b* (((mv status solver)
        (ipasir-solve-impl (ipasir-get ipa)))
       (ipa (ipasir-set solver ipa)))
    (mv status ipa)))

(make-event
 (b* (((mv erp ?val state)
       (with-output :off :all
         (progn
           ;; Functionally instantiate the exists-state theorem to show that there really
           ;; should exist a state on which the above returns :sat...
           ;; This now fails due to the use of define-trusted-clause-processor
           ;; on the encapsulate introducing ipasir-solve$a.
           (defthm exists-state-impl
             (exists-state-where-ipasir-example-impl-is-sat)
             :hints (("goal" :use ((:functional-instance exists-state
                                    (exists-state-where-ipasir-example-is-sat
                                     exists-state-where-ipasir-example-impl-is-sat)
                                    (ipasir-example ipasir-example-impl)
                                    (ipasir-solve$a ipasir-solve-impl)
                                    (ipasir-solve ipasir-solve-impl)
                                    (ipasir-solve$c ipasir-solve$c-impl))))
                     (and stable-under-simplificationp
                          '(:in-theory (enable ipasir-solve-impl ipasir-example-impl))))
             :rule-classes nil)

           (defthm bad
             nil
             :hints (("goal" :use (not-exists-state-impl
                                   exists-state-impl)))
             :rule-classes nil))))
      ((unless erp)
       (er soft 'ipasir-soundness-bug-check "Proof of unsoundness unexpectedly passed!~%")))
   (value '(value-triple :proof-of-nil-did-not-succeed))))


  

