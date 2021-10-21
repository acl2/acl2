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

(include-book "../utils/basics")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "lambda-substitution")

(set-state-ok t)

(set-induction-depth-limit 1)
(local (in-theory (disable pseudo-termp pseudo-term-listp)))

;;-------------------------------------------------------
;; Returns judgements

(define get-hypotheses-and-conclusion ((thm pseudo-termp)
                                       (fn symbolp)
                                       (actuals pseudo-term-listp))
  :returns (mv (ok booleanp)
               (hypo pseudo-termp)
               (concl pseudo-termp))
  (b* ((thm (pseudo-term-fix thm))
       (fn (symbol-fix fn))
       (actuals (pseudo-term-list-fix actuals)))
    (case-match thm
      ((& (!fn . !actuals)) (mv t ''t thm))
      (('implies hypo concl) (mv t hypo concl))
      (& (mv nil nil nil)))))

#|
(get-hypotheses-and-conclusion '(implies (and (rationalp i1) (rational-list-p al))
                                         (and (rational-list-p (cons i1 al))
                                              (cons i1 al)))
                               'cons '(i1 al))
|#

(defthm correctness-of-get-hypotheses-and-conclusion
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp thm)
                (alistp a)
                (ev-smtcp thm a)
                (ev-smtcp
                 (mv-nth 1 (get-hypotheses-and-conclusion thm fn actuals))
                 a))
           (ev-smtcp
            (mv-nth 2 (get-hypotheses-and-conclusion thm fn actuals))
            a))
  :hints (("Goal"
           :in-theory (e/d (get-hypotheses-and-conclusion)
                           (symbol-listp
                            pseudo-term-listp-of-symbol-listp)))))

(define get-substed-theorem ((respec thm-spec-p)
                             (actuals pseudo-term-listp)
                             state)
  :returns (substed-thm pseudo-termp)
  (b* ((respec (thm-spec-fix respec))
       (actuals (pseudo-term-list-fix actuals))
       (returns-name (thm-spec->thm respec))
       (returns-thm-raw
        (acl2::meta-extract-formula-w returns-name (w state)))
       ((unless (pseudo-termp returns-thm-raw))
        (prog2$ (er hard? 'returns-judgement=>get-substed-theorem
                    "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                    returns-name returns-thm-raw)
                ''t))
       (returns-thm-expanded (expand-lambda returns-thm-raw))
       (formals (thm-spec->formals respec)))
    (acl2::substitute-into-term returns-thm-expanded
                                (pairlis$ formals actuals))))

#|
(deflist rational-list
  :elt-type rationalp
  :true-listp t)
(defthm return-of-cons
  (implies (and (rationalp x)
                (rational-list-p y))
           (and (rational-list-p (cons x y))
                (cons x y))))
(get-substed-theorem '((FORMALS X Y)
                       (RETURNS-THM . RETURN-OF-CONS))
                     '(i1 l1)
                     state)
|#

(defthm correctness-of-get-substed-theorem
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (alistp a)
                 (pseudo-term-listp actuals)
                 (thm-spec-p respec))
            (ev-smtcp (get-substed-theorem respec actuals state) a))
   :hints (("Goal"
            :in-theory (e/d () (w))
            :expand (get-substed-theorem respec actuals state))))

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

(encapsulate ()
  (local (in-theory (disable (:definition assoc-equal)
                             (:definition symbol-listp)
                             (:rewrite consp-of-pseudo-lambdap)
                             (:definition pseudo-termp))))

(define construct-returns-judgement ((fn symbolp)
                                     (actuals pseudo-term-listp)
                                     (actuals-judgements pseudo-termp)
                                     (return-spec thm-spec-p)
                                     (path-cond pseudo-termp)
                                     (acc pseudo-termp)
                                     state)
  :returns (judgement pseudo-termp)
  :guard (not (equal fn 'quote))
  (b* ((fn (symbol-fix fn))
       (acc (pseudo-term-fix acc))
       (- (cw "return-spec: ~q0" return-spec))
       (- (cw "actuals: ~q0" actuals))
       (returns-thm-substed
        (get-substed-theorem return-spec actuals state))
       ((mv ok hypo return-judge)
        (get-hypotheses-and-conclusion returns-thm-substed fn actuals))
       ((unless ok)
        (prog2$ (er hard? 'returns-judgement=>construct-returns-judgement
                    "Malformed returns theorem ~p0 for ~p1. Path-cond: ~p2~%"
                    returns-thm-substed
                    `(,fn ,@actuals)
                    path-cond)
                ''t))
       (hypo-implied
        (path-test-list `(if ,actuals-judgements ,path-cond 'nil) hypo))
       ((unless hypo-implied) acc))
    `(if ,return-judge ,acc 'nil)))
)

#|
(construct-returns-judgement 'cons '(i1 l1)
                             '(IF (IF (RATIONALP I1)
                                      (IF (MAYBE-INTEGERP I1)
                                          (IF (INTEGERP I1) 'T 'NIL)
                                          'NIL)
                                      'NIL)
                                  (IF (IF (RATIONAL-LIST-P L1) 'T 'NIL)
                                      'T
                                      'NIL)
                                  'NIL)
                             '((FORMALS X Y)
                               (RETURNS-THM . RETURN-OF-CONS))
                             '(IF (IF (RATIONAL-LIST-P L1)
                                      (IF (INTEGERP I1) L1 'NIL)
                                      'NIL)
                                  'T
                                  'NIL)
                             ''t
                             state)
|#

(defthm correctness-of-construct-returns-judgement
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (pseudo-termp term)
                 (alistp a)
                 (symbolp fn)
                 (pseudo-term-listp actuals)
                 (pseudo-termp actuals-judgements)
                 (thm-spec-p return-spec)
                 (pseudo-termp path-cond)
                 (pseudo-termp acc)
                 (ev-smtcp actuals-judgements a)
                 (ev-smtcp path-cond a)
                 (ev-smtcp acc a))
            (ev-smtcp
             (construct-returns-judgement fn actuals actuals-judgements
                                          return-spec path-cond acc state)
             a))
   :hints (("Goal"
            :in-theory (e/d () (w))
            :expand (construct-returns-judgement fn actuals
                                                 actuals-judgements
                                                 return-spec
                                                 path-cond
                                                 acc state))))

(define returns-judgement ((fn symbolp)
                           (actuals pseudo-term-listp)
                           (actuals-judgements pseudo-termp)
                           (respec-lst thm-spec-list-p)
                           (path-cond pseudo-termp)
                           (acc pseudo-termp)
                           state)
  :measure (len respec-lst)
  :returns (judge pseudo-termp)
  :guard (not (equal fn 'quote))
  (b* (((unless (mbt (not (equal fn 'quote)))) ''t)
       (fn (symbol-fix fn))
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       (respec-lst (thm-spec-list-fix respec-lst))
       (path-cond (pseudo-term-fix path-cond))
       (acc (pseudo-term-fix acc))
       ((unless (consp respec-lst)) acc)
       ((cons respec-hd respec-tl) respec-lst)
       (acc-hd
        (construct-returns-judgement fn actuals actuals-judgements
                                     respec-hd path-cond acc state)))
    (returns-judgement fn actuals actuals-judgements
                       respec-tl path-cond acc-hd state)))

#|
(returns-judgement 'cons '(i1 l1)
                  '(IF (IF (RATIONALP I1)
                           (IF (MAYBE-INTEGERP I1)
                               (IF (INTEGERP I1) 'T 'NIL)
                               'NIL)
                           'NIL)
                       (IF (IF (RATIONAL-LIST-P L1) 'T 'NIL)
                           'T
                           'NIL)
                       'NIL)
                  '(((FORMALS X Y)
                     (RETURNS-THM . RETURN-OF-CONS)))
                  '(IF (IF (RATIONAL-LIST-P L1)
                           (IF (INTEGERP I1) L1 'NIL)
                           'NIL)
                       'T
                       'NIL)
                  ''t
                  state)
|#

(defthm correctness-of-returns-judgement
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (alistp a)
                (symbolp fn)
                (pseudo-term-listp actuals)
                (pseudo-termp actuals-judgements)
                (pseudo-termp path-cond)
                (thm-spec-list-p respec-lst)
                (pseudo-termp acc)
                (ev-smtcp actuals-judgements a)
                (ev-smtcp path-cond a)
                (ev-smtcp acc a))
           (ev-smtcp
            (returns-judgement fn actuals actuals-judgements
                               respec-lst path-cond acc state)
            a))
  :hints (("Goal" :in-theory (enable returns-judgement))))

;;---------------------------------------------------------------
;; Choose returns judgements (the inverse of returns-judgement)
(define filter-judges ((judge pseudo-termp)
                       (filter pseudo-termp)
                       (supertypes type-to-types-alist-p)
                       (acc pseudo-termp))
  :returns (new-judge pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (filter (pseudo-term-fix filter))
       (acc (pseudo-term-fix acc))
       ((if (and (type-predicate-p judge supertypes)
                 (path-test filter judge)))
        `(if ,judge ,acc 'nil))
       ((if (type-predicate-p judge supertypes)) acc)
       ((unless (is-conjunct? judge)) `(if ,judge ,acc 'nil))
       ((if (equal judge ''t)) acc)
       ((list & judge-left judge-right &) judge)
       (left-acc (filter-judges judge-left filter supertypes acc)))
    (filter-judges judge-right filter supertypes left-acc)))

(verify-guards filter-judges)

(defthm correctness-of-filter-judges
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp judge)
                  (pseudo-termp acc)
                  (alistp a)
                  (ev-smtcp judge a)
                  (ev-smtcp acc a))
             (ev-smtcp (filter-judges judge filter supertype acc) a))
    :hints (("Goal" :in-theory (enable filter-judges))))

(define generate-judge-alist-one ((judges pseudo-termp)
                                  (term pseudo-termp)
                                  (supertypes type-to-types-alist-p)
                                  (acc pseudo-termp))
  :returns (term-judge pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judges))
  :verify-guards nil
  (b* ((judges (pseudo-term-fix judges))
       (term (pseudo-term-fix term))
       (acc (pseudo-term-fix acc))
       ((if (judgement-of-term judges term supertypes))
        `(if ,judges ,acc 'nil))
       ((unless (is-conjunct? judges)) acc)
       ((if (equal judges ''t)) acc)
       ((list & judge-left judge-right &) judges)
       (new-acc (generate-judge-alist-one judge-left term supertypes acc)))
    (generate-judge-alist-one judge-right term supertypes new-acc)))

(verify-guards generate-judge-alist-one)

(defthm correctness-of-generate-judge-alist-one
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judges)
                (pseudo-termp term)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp judges a)
                (ev-smtcp acc a))
           (ev-smtcp (generate-judge-alist-one judges term supertypes acc) a))
  :hints (("Goal"
           :in-theory (enable generate-judge-alist-one))))

(define generate-judge-alist ((judges pseudo-termp)
                              (actuals pseudo-term-listp)
                              (supertypes type-to-types-alist-p))
  :returns (judge-alst pseudo-term-alistp)
  :measure (len actuals)
  (b* ((actuals (pseudo-term-list-fix actuals))
       ((unless (consp actuals)) nil)
       ((cons ac-hd ac-tl) actuals))
    (acons ac-hd
           (generate-judge-alist-one judges ac-hd supertypes ''t)
           (generate-judge-alist judges ac-tl supertypes))))

(defthm correctness-of-generate-judge-alist
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judges)
                (pseudo-term-listp actuals)
                (alistp a)
                (ev-smtcp judges a))
           (or (ev-smtcp-lst
                (strip-cdrs
                 (generate-judge-alist judges actuals supertypes))
                a)
               (null (generate-judge-alist judges actuals supertypes))))
  :hints (("Goal"
           :in-theory (enable generate-judge-alist))))

(encapsulate ()
  (local
   (in-theory (disable symbol-listp
                       pseudo-term-listp-of-symbol-listp
                       equal-fixed-and-x-of-pseudo-termp)))

  (local
   (defthm crock
     (implies (and (pseudo-term-alistp x))
              (pseudo-term-listp (strip-cdrs x))))
   )

(define choose-returns ((returns-judge pseudo-termp)
                        (fn symbolp)
                        (actuals pseudo-term-listp)
                        (actuals-judge pseudo-termp)
                        (path-cond pseudo-termp)
                        (respec-lst thm-spec-list-p)
                        (options type-options-p)
                        state)
  :ignore-ok t
  :returns (expected-judge-lst pseudo-term-listp)
  :measure (len respec-lst)
  :guard (not (equal fn 'quote))
  (b* ((returns-judge (pseudo-term-fix returns-judge))
       (fn (symbol-fix fn))
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judge (pseudo-term-fix actuals-judge))
       (path-cond (pseudo-term-fix path-cond))
       (respec-lst (thm-spec-list-fix respec-lst))
       (options (type-options-fix options))
       (supertypes (type-options->supertype options))
       ((unless (consp respec-lst)) nil)
       ((cons respec-hd respec-tl) respec-lst)
       (returns-thm-substed (get-substed-theorem respec-hd actuals state))
       ((mv ok hypo concl)
        (get-hypotheses-and-conclusion returns-thm-substed fn actuals))
       (extended-concl (extend-judgements concl path-cond options state))
       ((unless ok)
        (er hard? 'returns-judgement=>choose-returns
            "Malformed returns theorem ~p0.~%" returns-thm-substed))
       ;; (conclusion returns-thm-substed) => returns-judge
       (ok1 (path-test-list extended-concl returns-judge))
       ;; actuals-judge & path-cond => (hypotheses returns-thm-substed)
       (ok2 (path-test-list `(if ,actuals-judge ,path-cond 'nil) hypo))
       ;; if returns-judge includes the conclusion of returns-thm-substed
       ;; and actuals-judge satisfy the hypotheses of returns-thm-substed
       ((unless (and ok1 ok2))
        (choose-returns returns-judge fn actuals actuals-judge path-cond
                        respec-tl options state))
       (judges (filter-judges actuals-judge hypo supertypes ''t))
       (judge-alst (generate-judge-alist judges actuals nil)))
    (strip-cdrs judge-alst)))
)

(defthm correctness-of-choose-returns
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp returns-judge)
                (symbolp fn)
                (pseudo-term-listp actuals)
                (pseudo-termp actuals-judge)
                (pseudo-termp path-cond)
                (thm-spec-list-p respec-lst)
                (type-to-types-alist-p supertypes)
                (alistp a)
                (ev-smtcp returns-judge a)
                (ev-smtcp actuals-judge a)
                (ev-smtcp path-cond a))
           (or (ev-smtcp-lst (choose-returns returns-judge fn actuals
                                             actuals-judge path-cond
                                             respec-lst supertypes state)
                             a)
               (null (choose-returns returns-judge fn actuals
                                     actuals-judge path-cond
                                     respec-lst supertypes state))))
  :hints (("Goal" :in-theory (enable choose-returns))))
