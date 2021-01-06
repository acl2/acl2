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
(include-book "lambda-substitution")

(set-state-ok t)

(defprod returns
  ((returns-thm pseudo-termp)
   (replace-thm pseudo-termp)))

(deflist returns-list
  :elt-type returns-p
  :true-listp t)

;;-------------------------------------------------------
;; Returns judgements

(encapsulate ()
  (local (in-theory (disable pseudo-termp
                             assoc-equal
                             symbol-listp)))

(define get-formals ((fn symbolp) state)
  :returns (formals symbol-listp)
  :ignore-ok t
  (b* ((fn (symbol-fix fn))
       (formula (acl2::meta-extract-formula-w fn (w state)))
       ((unless (pseudo-termp formula))
        (prog2$
         (er hard? 'returns-judgement=>get-formals
             "Formula got by meta-extract ~p0 is not a pseudo-termp."
             fn)
         nil))
       ((mv ok formals)
        (case-match formula
          (('equal (!fn . formals) &)
           (mv t formals))
          (& (mv nil nil))))
       ((unless (and ok (symbol-listp formals)))
        (prog2$ (er hard? 'returns-judgement=>get-formals
                    "Formula got by meta-extract ~p0 is not an equality."
                    fn)
                nil)))
    formals))
)

(define hypotheses-implies ((thm pseudo-termp)
                            (fn symbolp)
                            (actuals pseudo-term-listp)
                            (judgements pseudo-termp)
                            (path-cond pseudo-termp))
  :returns (mv (ok booleanp)
               (judge pseudo-termp))
  (b* ((thm (pseudo-term-fix thm))
       (fn (symbol-fix fn))
       (actuals (pseudo-term-list-fix actuals))
       (judgements (pseudo-term-fix judgements))
       (path-cond (pseudo-term-fix path-cond)))
    (case-match thm
      ((& (!fn . !actuals)) (mv t thm))
      (('implies hypotheses return-judge)
       (if (path-test-list `(if ,judgements ,path-cond 'nil)
                           hypotheses)
           (mv t return-judge)
         (mv nil ''t)))
      (& (mv nil ''t)))))

(defthm correctness-of-path-test-list-corollary
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judgements)
                (pseudo-termp path-cond)
                (pseudo-termp expr-conj)
                (alistp a)
                (ev-smtcp judgements a)
                (ev-smtcp path-cond a)
                (path-test-list `(if ,judgements ,path-cond 'nil) expr-conj))
           (ev-smtcp expr-conj a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable correctness-of-path-test-list)
           :use ((:instance correctness-of-path-test-list
                            (path-cond `(if ,judgements ,path-cond 'nil))
                            (expr-conj expr-conj))))))

(defthm correctness-of-hypotheses-implies
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp thm)
                (alistp a)
                (symbolp fn)
                (pseudo-term-listp actuals)
                (pseudo-termp judgements)
                (pseudo-termp path-cond)
                (ev-smtcp thm a)
                (ev-smtcp judgements a)
                (ev-smtcp path-cond a)
                (mv-nth 0 (hypotheses-implies thm fn actuals judgements
                                              path-cond)))
           (ev-smtcp (mv-nth 1 (hypotheses-implies thm fn actuals judgements
                                                   path-cond))
                     a))
  :hints (("Goal"
           :in-theory (e/d ()
                           (pseudo-termp))
           :expand (hypotheses-implies thm fn actuals judgements path-cond))))

(define expand-lambda ((thm pseudo-termp))
  :returns (expanded-thm pseudo-termp)
  (b* ((thm (pseudo-term-fix thm)))
    (if (and (not (acl2::variablep thm))
             (not (acl2::quotep thm))
             (pseudo-lambdap (car thm)))
        (lambda-substitution (car thm) (cdr thm))
      thm)))

(defthm correctness-of-expand-lambda
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp thm)
                (alistp a)
                (ev-smtcp thm a))
           (ev-smtcp (expand-lambda thm) a))
  :hints (("Goal"
           :in-theory (e/d ()
                           ())
           :expand (expand-lambda thm))))

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
                                     ;; (supertype type-to-types-alist-p)
                                     state)
  :returns (mv (judgement pseudo-termp)
               (returns-thms returns-p))
  :guard (not (equal fn 'quote))
  (b* ((fn (symbol-fix fn))
       ((unless (mbt (not (equal fn 'quote)))) (mv ''t (make-returns)))
       (actuals (pseudo-term-list-fix actuals))
       (return-spec (return-spec-fix return-spec))
       (returns-name (return-spec->returns-thm return-spec))
       (replace-name (return-spec->replace-thm return-spec))
       (returns-thm-raw
        (acl2::meta-extract-formula-w returns-name (w state)))
       ((unless (pseudo-termp returns-thm-raw))
        (prog2$ (er hard? 'returns-judgement=>construct-returns-judgement
                    "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                    returns-name returns-thm-raw)
                (mv ''t (make-returns))))
       (replace-thm
        (acl2::meta-extract-formula-w replace-name (w state)))
       ((unless (pseudo-termp replace-thm))
        (prog2$ (er hard? 'returns-judgement=>construct-returns-judgement
                    "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                    replace-name replace-thm)
                (mv ''t (make-returns))))
       (returns-thm-expanded (expand-lambda returns-thm-raw))
       (formals (get-formals fn state))
       (alst (pairlis$ formals actuals))
       (returns-thm-substed
        (acl2::substitute-into-term returns-thm-expanded alst))
       (replace-thm-substed
        (acl2::substitute-into-term replace-thm alst))
       ((mv ok return-judge)
        (hypotheses-implies returns-thm-expanded fn actuals actuals-judgements
                            path-cond))
       ((unless ok)
        (prog2$ (er hard? 'returns-judgement=>construct-returns-judgement
                    "Hypotheses for returns-judgements aren't satisfied.~%")
                (mv ''t (make-returns)))))
    (mv return-judge
        (make-returns :returns-thm returns-thm-substed
                      :replace-thm replace-thm-substed))))
)

(defthm correctness-of-construct-returns-judgement
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (pseudo-termp term)
                 (alistp a)
                 (symbolp fn)
                 (pseudo-term-listp actuals)
                 (pseudo-termp actuals-judgements)
                 (return-spec-p return-spec)
                 (pseudo-termp path-cond)
                 (ev-smtcp actuals-judgements a)
                 (ev-smtcp path-cond a))
            (ev-smtcp (mv-nth 0 (construct-returns-judgement fn actuals
                                                             actuals-judgements
                                                             return-spec
                                                             path-cond
                                                             state))
                      a))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d ()
                            (w symbol-listp
                             assoc-equal
                             correctness-of-path-test-list-corollary
                             acl2::pseudo-termp-opener))
            :expand (construct-returns-judgement fn actuals
                                                 actuals-judgements
                                                 return-spec
                                                 path-cond
                                                 state))))

;; (local
;;  (defthm acl2-count-of-arg-decl-next->next
;;    (implies (and (not (equal (arg-decl-kind arg-decl) :done)))
;;             (< (acl2-count (arg-decl-next->next arg-decl))
;;                (acl2-count (arg-decl-fix arg-decl))))
;;    :hints (("Goal" :in-theory (enable arg-decl-fix arg-decl-next->next)))))

;; (defines returns-judgement
;;   :well-founded-relation l<
;;   :verify-guards nil

;; (define returns-judgement-single-arg ((fn symbolp)
;;                                       (actuals pseudo-term-listp)
;;                                       (actuals-total pseudo-term-listp)
;;                                       (actuals-judgements pseudo-termp)
;;                                       (actuals-judgements-total pseudo-termp)
;;                                       (arg-check arg-check-p)
;;                                       (path-cond pseudo-termp)
;;                                       (supertype type-to-types-alist-p)
;;                                       (acc pseudo-termp)
;;                                       (thm-acc returns-list-p)
;;                                       state)
;;   :returns (mv (judgements pseudo-termp)
;;                (returns-thms returns-list-p))
;;   :guard (and (consp actuals)
;;               (not (equal actuals-judgements ''t))
;;               (not (equal fn 'quote)))
;;   :measure (list (len (pseudo-term-list-fix actuals))
;;                  (acl2-count (arg-check-fix arg-check)))
;;   (b* (((unless (mbt (not (equal fn 'quote)))) (mv ''t nil))
;;        (actuals (pseudo-term-list-fix actuals))
;;        (actuals-judgements (pseudo-term-fix actuals-judgements))
;;        (acc (pseudo-term-fix acc))
;;        (thm-acc (returns-list-fix thm-acc))
;;        ((unless (is-conjunct? actuals-judgements))
;;         (prog2$ (er hard? 'returns-judgement=>returns-judgement-single-arg
;;                 "Actuals judgements is not a conjunct ~p0.~%"
;;                 actuals-judgements)
;;             (mv ''t nil)))
;;        (arg-check (arg-check-fix arg-check))
;;        ((unless (consp arg-check)) (mv acc thm-acc))
;;        ((cons check-hd check-tl) arg-check)
;;        ((cons type arg-decl) check-hd)
;;        ((unless (mbt (and (consp actuals)
;;                           (not (equal actuals-judgements ''t)))))
;;         (mv ''t nil))
;;        ((cons actual actuals-tl) actuals)
;;        ((list & actual-judge actuals-judge-tl &) actuals-judgements)
;;        ((if (equal type 't))
;;         (returns-judgement fn actuals-tl actuals-total
;;                            actuals-judge-tl actuals-judgements-total arg-decl
;;                            path-cond supertype acc thm-acc state))
;;        (guard-term `(,type ,actual))
;;        (yes? (path-test actual-judge guard-term))
;;        ((unless yes?)
;;         (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
;;                                       actuals-judgements-total check-tl
;;                                       path-cond supertype acc thm-acc state))
;;        ((mv new-acc new-thm-acc)
;;         (returns-judgement fn actuals-tl actuals-total
;;                            actuals-judge-tl actuals-judgements-total arg-decl
;;                            path-cond supertype acc thm-acc state)))
;;     (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
;;                                   actuals-judgements-total check-tl path-cond
;;                                   supertype new-acc new-thm-acc state)))

;; (define returns-judgement ((fn symbolp)
;;                            (actuals pseudo-term-listp)
;;                            (actuals-total pseudo-term-listp)
;;                            (actuals-judgements pseudo-termp)
;;                            (actuals-judgements-total pseudo-termp)
;;                            (arg-decl arg-decl-p)
;;                            (path-cond pseudo-termp)
;;                            (supertype type-to-types-alist-p)
;;                            (acc pseudo-termp)
;;                            (thm-acc returns-list-p)
;;                            state)
;;   :returns (mv (judgements pseudo-termp)
;;                (returns-thms returns-list-p))
;;   :measure (list (len (pseudo-term-list-fix actuals))
;;                  (acl2-count (arg-decl-fix arg-decl)))
;;   :guard (not (equal fn 'quote))
;;   (b* (((unless (mbt (not (equal fn 'quote)))) (mv ''t nil))
;;        (actuals (pseudo-term-list-fix actuals))
;;        (actuals-judgements (pseudo-term-fix actuals-judgements))
;;        (arg-decl (arg-decl-fix arg-decl))
;;        (acc (pseudo-term-fix acc))
;;        (thm-acc (returns-list-fix thm-acc))
;;        ((if (and (equal (arg-decl-kind arg-decl) :done)
;;                  (null actuals)
;;                  (equal actuals-judgements ''t)))
;;         (b* (((mv the-judge the-thm)
;;               (construct-returns-judgement fn actuals-total
;;                                            actuals-judgements-total
;;                                            (arg-decl-done->r arg-decl)
;;                                            path-cond state)))
;;           (mv `(if ,the-judge ,acc 'nil) (cons the-thm thm-acc))))
;;        ((if (and (equal (arg-decl-kind arg-decl) :done)
;;                  (or actuals (not (equal actuals-judgements ''t)))))
;;         (prog2$ (er hard? 'returns-judgement=>returns-judgement
;;                     "Run out of arg-decls.~%")
;;                 (mv ''t nil)))
;;        ((if (or (null actuals)
;;                 (equal actuals-judgements ''t)))
;;         (prog2$ (er hard? 'returns-judgement=>returns-judgement
;;                     "Run out of actuals or actuals-judgements.~%")
;;                 (mv ''t nil)))
;;        (arg-check (arg-decl-next->next arg-decl)))
;;     (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
;;                                   actuals-judgements-total arg-check path-cond
;;                                   supertype acc thm-acc state)))
;; )

;; (verify-guards returns-judgement
;;   :hints (("Goal"
;;            :in-theory (disable pseudo-termp))))

(define returns-judgement((fn symbolp)
                          (actuals pseudo-term-listp)
                          (actuals-judgements pseudo-termp)
                          (respec-lst return-spec-list-p)
                          (path-cond pseudo-termp)
                          state)
  :measure (len respec-lst)
  :returns (mv (judge pseudo-termp)
               (thms returns-list-p))
  :guard (not (equal fn 'quote))
  (b* (((unless (mbt (not (equal fn 'quote)))) (mv ''t nil))
       (fn (symbol-fix fn))
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       (respec-lst (return-spec-list-fix respec-lst))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (consp respec-lst)) (mv ''t nil))
       ((cons respec-hd respec-tl) respec-lst)
       ((mv judge-hd thm-hd)
        (construct-returns-judgement fn actuals actuals-judgements
                                     respec-hd path-cond state))
       ((mv judge-tl thm-tl)
        (returns-judgement fn actuals actuals-judgements
                           respec-tl path-cond state)))
    (mv `(if ,judge-hd ,judge-tl 'nil) (cons thm-hd thm-tl))))

(defthm correctness-of-returns-judgement
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (alistp a)
                (symbolp fn)
                (pseudo-term-listp actuals)
                (pseudo-termp actuals-judgements)
                (pseudo-termp path-cond)
                (return-spec-list-p respec-lst)
                (ev-smtcp actuals-judgements a)
                (ev-smtcp path-cond a))
           (ev-smtcp
            (mv-nth 0 (returns-judgement fn actuals actuals-judgements
                                         respec-lst path-cond state))
            a))
  :hints (("Goal" :in-theory (enable returns-judgement))))
