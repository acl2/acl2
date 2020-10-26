;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 6th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
;; Meta-extract stuff
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)

(include-book "hint-please")
(include-book "hint-interface")
(include-book "computed-hints")
(include-book "expand-cp")
(include-book "return-type")
(include-book "evaluator")

(include-book "ordinals/lexicographic-ordering" :dir :system)
(set-state-ok t)

(defsection uninterpreted-fn-cp
  :parents (verified)
  :short "Verified clause-processor for proving return types of uninterpreted
  functions."

  (define fix-thm-meta-extract ((func smt-function-p)
                                (fixtypes smt-fixtype-list-p)
                                (fixinfo smt-fixtype-info-p)
                                state)
    :returns (new-term pseudo-termp)
    :guard-debug t
    (b* ((func (smt-function-fix func))
         (fixtypes (smt-fixtype-list-fix fixtypes))
         (fixinfo (smt-fixtype-info-fix fixinfo))
         (return-type (return-type-of-function func fixinfo))
         (fixtype (is-type return-type fixtypes))
         ((unless fixtype)
          (er hard? 'uninterpreted-fn-cp=>fix-thm-meta-extract "~p0 is not a
                              fixtype.~%" return-type))
         (type-fix-when-type
          (type-thm->name
           (smt-fixtype->fixer-when-recognizer-thm fixtype)))
         (fix-thm (acl2::meta-extract-formula-w type-fix-when-type
                                                (w state)))
         ((unless (and (pseudo-termp fix-thm) (not (equal fix-thm ''t))))
          (er hard? 'uninterpreted-fn-cp=>fix-thm-meta-extract "Type theorem
                              type-of-f is not of the expected shape: ~p0 for ~p1~%"
              fix-thm type-fix-when-type)))
      fix-thm))

  (defthm fix-thm-meta-extract-correct
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a))
             (or (null (fix-thm-meta-extract func fixtypes fixinfo state))
                 (ev-smtcp (fix-thm-meta-extract func fixtypes fixinfo state) a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fix-thm-meta-extract
                              ev-smtcp-of-fncall-args)
                             (pseudo-term-listp
                              pseudo-termp
                              car-cdr-elim
                              w))
             )))

  (define fix-thm-full ((term pseudo-termp)
                        (func smt-function-p)
                        (fixtypes smt-fixtype-list-p)
                        (fixinfo smt-fixtype-info-p)
                        state)
    :returns (new-term pseudo-termp)
    :guard-debug t
    (b* ((term (pseudo-term-fix term))
         (fix-thm (fix-thm-meta-extract func fixtypes fixinfo state))
         ((unless fix-thm)
          (er hard? 'uninterpreted-fn-cp=>fix-thm-full
              "Something is wrong with fix-thm-meta-extract."))
         (vars (reverse (acl2::simple-term-vars fix-thm)))
         ((unless (and (consp vars) (null (cdr vars))))
          (er hard? 'uninterpreted-fn-cp=>fix-thm-full
              "Free vars from fix-thm: ~q0" vars)))
      (acl2::substitute-into-term fix-thm (pairlis$ vars (list term)))))

  (defthm fix-thm-full-correct
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (pseudo-termp term))
             (or (null (fix-thm-full term func fixtypes fixinfo state))
                 (ev-smtcp (fix-thm-full term func fixtypes fixinfo state) a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fix-thm-full)
                             (fix-thm-meta-extract-correct))
             :use ((:instance fix-thm-meta-extract-correct
                              (func func)
                              (fixtypes fixtypes)
                              (fixinfo fixinfo)
                              (a (list
                                  (cons (car (reverse
                                              (acl2::simple-term-vars
                                               (fix-thm-meta-extract
                                                func fixtypes fixinfo state))))
                                        (ev-smtcp term a))))))
             )))

  (define find-fixer ((term pseudo-termp)
                      (func smt-function-p)
                      (fixtypes smt-fixtype-list-p)
                      (fixinfo smt-fixtype-info-p)
                      state)
    :returns (fixer pseudo-termp)
    (b* ((type-thm (type-thm-full term func state))
         ((unless type-thm)
          (er hard? 'uninterpreted-fn-cp=>find-fixer
              "Something is wrong with type-thm-full."))
         (fix-thm (fix-thm-full term func fixtypes fixinfo state))
         ((unless fix-thm)
          (er hard? 'uninterpreted-fn-cp=>find-fixer
              "Something is wrong with fix-thm-full."))
         ((mv ok fixed)
          (case-match fix-thm
            (('implies !type-thm
                       ('equal fixed !term))
             (mv t fixed))
            (& (mv nil nil))))
         ((unless (and ok (pseudo-termp fixed)))
          (er hard? 'uninterpreted-fn-cp=>find-fixer
              "Fixer wrong: ~q0" fixed)))
      fixed))

  (defthm find-fixer-correct
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (pseudo-termp term))
             (or (null (find-fixer term func fixtypes fixinfo state))
                 (equal (ev-smtcp (find-fixer term func fixtypes fixinfo state) a)
                        (ev-smtcp term a))))
    :hints (("Goal"
             :in-theory (e/d (find-fixer
                              ev-smtcp-of-fncall-args)
                             (pseudo-term-listp
                              pseudo-termp
                              car-cdr-elim
                              w
                              fix-thm-full-correct))
             :use ((:instance fix-thm-full-correct
                              (a a)
                              (term term)
                              (func func))
                   (:instance type-thm-full-correct
                              (a a)
                              (term term)
                              (func func)))
             )))

  (defines uninterpreted
    :well-founded-relation l<
    :flag-local nil
    :flag-defthm-macro defthm-uninterpreted
    :verify-guards nil

    (define uninterpreted-list ((term-lst pseudo-term-listp)
                                (fn-lst smt-function-list-p)
                                (fixtypes smt-fixtype-list-p)
                                (fixinfo smt-fixtype-info-p)
                                state)
      :returns (new-term-lst pseudo-term-listp)
      :measure (acl2-count (pseudo-term-list-fix term-lst))
      :hints (("Goal" :in-theory (enable pseudo-term-list-fix
                                         pseudo-term-fix)))
      (b* ((term-lst (pseudo-term-list-fix term-lst))
           ((unless (consp term-lst)) term-lst)
           ((cons first rest) term-lst)
           (first-term (uninterpreted first fn-lst fixtypes fixinfo state)))
        (cons first-term
              (uninterpreted-list rest fn-lst fixtypes fixinfo state))))

    (define uninterpreted ((term pseudo-termp)
                           (fn-lst smt-function-list-p)
                           (fixtypes smt-fixtype-list-p)
                           (fixinfo smt-fixtype-info-p)
                           state)
      :returns (new-term pseudo-termp)
      :measure (acl2-count (pseudo-term-fix term))
      (b* ((term (pseudo-term-fix term))
           ;; If first term is a symbolp or is quoted, return the current facts
           ((if (or (acl2::variablep term) (acl2::fquotep term))) term)
           ;; The first term is now a function call:
           ;; Cons the function call and function actuals out of term
           ((cons fn-call fn-actuals) term)
           ;; If fn-call is a pseudo-lambdap, transform the body
           ((if (pseudo-lambdap fn-call))
            (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted "There still
                           exists lambda in the term. Very strange.~%~q0~%" term)
                    term))
           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (mbt (symbolp fn-call))) nil)
           ((if (equal fn-call 'type-hyp)) term)

           ;; -----------------------------------------------------------
           ;; Now the term is a function call
           (basic-function (member-equal fn-call *SMT-basics*))
           (flex? (fncall-of-fixtypes fn-call fixinfo))
           ((if (or basic-function flex?))
            (cons fn-call
                  (uninterpreted-list fn-actuals fn-lst fixtypes fixinfo state)))
           ;; fn-call is not a basic function nor a flex function
           (user-defined (is-function fn-call fn-lst))
           ((unless user-defined)
            (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted "User hasn't
defined the uninterpreted function: ~q0" fn-call)
                    term))
           (fixed (find-fixer term user-defined fixtypes fixinfo state))
           ((mv ok fixer)
            (case-match fixed
              ((fixer (!fn-call . !fn-actuals))
               (mv t fixer))
              (& (mv nil nil))))
           ((unless (and ok (symbolp fixer)
                         (not (equal fixer 'quote))))
            (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted "Fixer wrong: ~q0" fixer)
                    term)))
        (list fixer
              (cons fn-call (uninterpreted-list fn-actuals fn-lst
                                                fixtypes fixinfo state)))))
    )

  (verify-guards uninterpreted)

  (defthm-uninterpreted
    (defthm uninterpreted-term
      (implies (and (ev-smtcp-meta-extract-global-facts)
                    (alistp a)
                    (pseudo-termp term))
               (equal (ev-smtcp
                       (uninterpreted term fn-lst fixtypes fixinfo state) a)
                      (ev-smtcp term a)))
      :hints ('(:expand ((uninterpreted term fn-lst fixtypes fixinfo state))
                        :in-theory (e/d (ev-smtcp-of-fncall-args)
                                        (find-fixer-correct
                                         member-equal
                                         pseudo-term-listp
                                         pseudo-termp
                                         acl2::member-of-cons))
                        :use ((:instance find-fixer-correct
                                         (term term)
                                         (a a)
                                         (func (is-function (car term) fn-lst))))))
      :flag uninterpreted)
    (defthm uninterpreted-term-lst
      (implies (and (ev-smtcp-meta-extract-global-facts)
                    (alistp a)
                    (pseudo-term-listp term-lst))
               (equal (ev-smtcp-lst
                       (uninterpreted-list term-lst fn-lst fixtypes fixinfo state)
                       a)
                      (ev-smtcp-lst term-lst a)))
      :hints ('(:expand ((uninterpreted-list term-lst fn-lst fixtypes fixinfo state)
                         (uninterpreted-list nil fn-lst fixtypes fixinfo state))))
      :flag uninterpreted-list))

  (define uninterpreted-fn ((cl pseudo-term-listp)
                            (smtlink-hint t)
                            state)
    :returns (new-term pseudo-term-list-listp)
    (b* (((unless (pseudo-term-listp cl)) nil)
         ((unless (smtlink-hint-p smtlink-hint)) (list cl))
         ((smtlink-hint h) smtlink-hint)
         (fn-lst h.functions)
         (fixtypes h.types)
         (fixinfo h.types-info)
         (new-term (uninterpreted (disjoin cl) fn-lst fixtypes fixinfo state))
         (next-cp (if h.custom-p
                      (cdr (assoc-equal 'uninterpreted-custom
                                        *SMT-architecture*))
                    (cdr (assoc-equal 'uninterpreted *SMT-architecture*))))
         ((if (null next-cp)) (list cl))
         (the-hint
          `(:clause-processor (,next-cp clause ',h state)))
         (hinted-goal `((hint-please ',the-hint) ,new-term)))
      (list hinted-goal)))

  (define uninterpreted-fn-cp ((cl pseudo-term-listp)
                               (hints t)
                               state)
    (b* ((fixed-clause (uninterpreted-fn cl hints state)))
      (value fixed-clause)))

  (local (in-theory (enable uninterpreted-fn-cp uninterpreted-fn)))

  (defthm uninterpreted-fn-correct
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp clause)
                  (alistp a)
                  (ev-smtcp (conjoin-clauses
                         (acl2::clauses-result
                          (uninterpreted-fn-cp clause hints state)))
                        a))
             (ev-smtcp (disjoin clause) a))
    :rule-classes :clause-processor)
  )
