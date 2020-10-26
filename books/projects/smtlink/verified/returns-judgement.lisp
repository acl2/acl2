;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "typed-term-fns")
(include-book "judgement-fns")

(set-state-ok t)

(defprod returns
  ((formals symbol-listp)
   (returns-thm pseudo-termp)
   (replace-thm pseudo-termp)))

(deflist returns-list
  :elt-type returns-p
  :true-listp t)

;;-------------------------------------------------------
;; Returns judgmenets

(encapsulate ()
  (local (in-theory (disable (:definition assoc-equal)
                             (:definition symbol-listp)
                             (:rewrite consp-of-pseudo-lambdap)
                             (:definition pseudo-termp))))

(define construct-returns-judgement ((fn symbolp)
                                     (actuals pseudo-term-listp)
                                     (actuals-judgements pseudo-termp)
                                     (return-spec return-spec-p)
                                     (path-cond pseudo-termp)
                                     (supertype type-to-types-alist-p)
                                     state)
  :returns (mv (judgement pseudo-termp)
               (returns-thms returns-p))
  :guard (not (equal fn 'quote))
  :ignore-ok t
  (b* ((fn (symbol-fix fn))
       ((unless (mbt (not (equal fn 'quote)))) (mv nil (make-returns)))
       (actuals (pseudo-term-list-fix actuals))
       (return-spec (return-spec-fix return-spec))
       (formals (return-spec->formals return-spec))
       (returns-name (return-spec->returns-thm return-spec))
       (replace-name (return-spec->replace-thm return-spec))
       (return-type (return-spec->return-type return-spec))
       (returns-thm
        (acl2::meta-extract-formula-w returns-name (w state)))
       ((unless (pseudo-termp returns-thm))
        (mv (er hard? 'returns-judgement=>construct-returns-judgement
                "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                returns-name returns-thm)
            (make-returns)))
       (replace-thm
        (acl2::meta-extract-formula-w replace-name (w state)))
       ((unless (pseudo-termp replace-thm))
        (mv (er hard? 'returns-judgement=>construct-returns-judgement
                "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                replace-name replace-thm)
            (make-returns)))
       ((mv ok return-judge)
        (case-match returns-thm
          ((!return-type (!fn . !formals))
           (mv t `(,return-type (,fn ,@actuals))))
          ((('lambda (r) conclusions) (!fn . !formals))
           (b* ((substed-conclusions
                 (term-substitution conclusions `((,r . (,fn ,@actuals))) t))
                (return-judge
                 (look-up-path-cond `(,fn ,@actuals) substed-conclusions supertype)))
             (mv t return-judge)))
          (('implies type-predicates conclusions)
           (b* ((substed
                 (term-substitution type-predicates (pairlis$ formals actuals)
                                    t))
                (yes?
                 (path-test-list `(if ,path-cond ,actuals-judgements 'nil)
                                 substed state))
                ((unless yes?)
                 (mv nil (er hard? 'returns-judgement=>construct-returns-judgement
                             "Hypotheses of returns theorem is not discharged.~%")))
                (substed-conclusions
                 (term-substitution conclusions
                                    `(((,fn ,@formals) . (,fn ,@actuals)))
                                    t))
                (return-judge
                 (look-up-path-cond `(,fn ,@actuals) substed-conclusions
                                    supertype)))
             (mv t return-judge)))
          (& (b* ((substed-conclusions
                   (term-substitution returns-thm `(((,fn ,@formals) . (,fn ,@actuals))) t))
                  (return-judge
                   (look-up-path-cond `(,fn ,@actuals) substed-conclusions supertype)))
               (mv t return-judge)))))
       ((unless ok)
        (mv (er hard? 'returns-judgement=>construct-returns-judgement
                "The returns theorem for function ~p0 is of the wrong syntactic ~
               form ~p1~%" fn returns-thm)
            (make-returns))))
    (mv return-judge
        (make-returns :formals formals :returns-thm returns-thm
                      :replace-thm replace-thm))))
)

(local
 (defthm acl2-count-of-arg-decl-next->next
   (implies (and (not (equal (arg-decl-kind arg-decl) :done)))
            (< (acl2-count (arg-decl-next->next arg-decl))
               (acl2-count (arg-decl-fix arg-decl))))
   :hints (("Goal" :in-theory (enable arg-decl-fix arg-decl-next->next)))))

(defines returns-judgement
  :well-founded-relation l<
  :verify-guards nil

(define returns-judgement-single-arg ((fn symbolp)
                                      (actuals pseudo-term-listp)
                                      (actuals-total pseudo-term-listp)
                                      (actuals-judgements pseudo-termp)
                                      (actuals-judgements-total pseudo-termp)
                                      (arg-check arg-check-p)
                                      (path-cond pseudo-termp)
                                      (supertype type-to-types-alist-p)
                                      (acc pseudo-termp)
                                      (thm-acc returns-list-p)
                                      state)
  :returns (mv (judgements pseudo-termp)
               (returns-thms returns-list-p))
  :guard (and (consp actuals)
              (not (equal actuals-judgements ''t))
              (not (equal fn 'quote)))
  :measure (list (len (pseudo-term-list-fix actuals))
                 (acl2-count (arg-check-fix arg-check)))
  (b* (((unless (mbt (not (equal fn 'quote)))) (mv nil nil))
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       (acc (pseudo-term-fix acc))
       (thm-acc (returns-list-fix thm-acc))
       ((unless (is-conjunct? actuals-judgements))
        (mv (er hard? 'returns-judgement=>returns-judgement-single-arg
                "Actuals judgements is not a conjunct ~p0.~%"
                actuals-judgements)
            nil))
       (arg-check (arg-check-fix arg-check))
       ((unless (consp arg-check)) (mv acc thm-acc))
       ((cons check-hd check-tl) arg-check)
       ((cons type arg-decl) check-hd)
       ((unless (mbt (and (consp actuals)
                          (not (equal actuals-judgements ''t)))))
        (mv nil nil))
       ((cons actual actuals-tl) actuals)
       ((list & actual-judge actuals-judge-tl &) actuals-judgements)
       ((if (equal type 't))
        (returns-judgement fn actuals-tl actuals-total
                           actuals-judge-tl actuals-judgements-total arg-decl
                           path-cond supertype acc thm-acc state))
       (guard-term `(,type ,actual))
       (yes? (path-test actual-judge guard-term state))
       ((unless yes?)
        (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                      actuals-judgements-total check-tl
                                      path-cond supertype acc thm-acc state))
       ((mv new-acc new-thm-acc)
        (returns-judgement fn actuals-tl actuals-total
                           actuals-judge-tl actuals-judgements-total arg-decl
                           path-cond supertype acc thm-acc state)))
    (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                  actuals-judgements-total check-tl path-cond
                                  supertype new-acc new-thm-acc state)))

(define returns-judgement ((fn symbolp)
                           (actuals pseudo-term-listp)
                           (actuals-total pseudo-term-listp)
                           (actuals-judgements pseudo-termp)
                           (actuals-judgements-total pseudo-termp)
                           (arg-decl arg-decl-p)
                           (path-cond pseudo-termp)
                           (supertype type-to-types-alist-p)
                           (acc pseudo-termp)
                           (thm-acc returns-list-p)
                           state)
  :returns (mv (judgements pseudo-termp)
               (returns-thms returns-list-p))
  :measure (list (len (pseudo-term-list-fix actuals))
                 (acl2-count (arg-decl-fix arg-decl)))
  :guard (not (equal fn 'quote))
  (b* (((unless (mbt (not (equal fn 'quote)))) (mv nil nil))
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       (arg-decl (arg-decl-fix arg-decl))
       (acc (pseudo-term-fix acc))
       (thm-acc (returns-list-fix thm-acc))
       ((if (and (equal (arg-decl-kind arg-decl) :done)
                 (null actuals)
                 (equal actuals-judgements ''t)))
        (b* (((mv the-judge the-thm)
              (construct-returns-judgement fn actuals-total
                                           actuals-judgements-total
                                           (arg-decl-done->r arg-decl)
                                           path-cond supertype state)))
          (mv `(if ,the-judge ,acc 'nil) (cons the-thm thm-acc))))
       ((if (and (equal (arg-decl-kind arg-decl) :done)
                 (or actuals (not (equal actuals-judgements ''t)))))
        (mv (er hard? 'returns-judgement=>returns-judgement
                "Run out of arg-decls.~%")
            nil))
       ((if (or (null actuals)
                (equal actuals-judgements ''t)))
        (mv (er hard? 'returns-judgement=>returns-judgement
                "Run out of actuals or actuals-judgements.~%")
            nil))
       (arg-check (arg-decl-next->next arg-decl)))
    (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                  actuals-judgements-total arg-check path-cond
                                  supertype acc thm-acc state)))
)

(verify-guards returns-judgement
  :hints (("Goal"
           :in-theory (disable pseudo-termp))))

(skip-proofs
 (defthm correctness-of-returns-judgement
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (pseudo-termp term)
                 (alistp a)
                 (symbolp fn)
                 (pseudo-term-listp actuals)
                 (pseudo-term-listp actuals-total)
                 (pseudo-termp actuals-judgements)
                 (pseudo-termp actuals-judgements-total)
                 (arg-decl-p arg-decl)
                 (pseudo-termp path-cond)
                 (type-to-types-alist-p supertype)
                 (pseudo-termp acc)
                 (returns-list-p thm-acc)
                 (ev-smtcp acc a))
            (ev-smtcp (mv-nth 0 (returns-judgement fn actuals actuals-total actuals-judgements
                                                   actuals-judgements-total
                                                   arg-decl path-cond supertype
                                                   acc thm-acc state))
                      a)))
 )
