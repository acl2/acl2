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

(include-book "path-cond")
(include-book "evaluator")

(set-state-ok t)

;;-------------------------------------------------------
;;  Intersect judgements
(define intersect-judgements-acc ((judge1 pseudo-termp)
                                  (judge2 pseudo-termp)
                                  (acc pseudo-termp)
                                  state)
  :returns (intersect pseudo-termp)
  :verify-guards nil
  :measure (acl2-count (pseudo-term-fix judge2))
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       (acc (pseudo-term-fix acc))
       ((if (and (not (is-conjunct? judge2))
                 (path-test judge1 judge2)))
        `(if ,judge2 ,acc 'nil))
       ((unless (is-conjunct? judge2)) acc)
       ((if (equal judge2 ''t)) acc)
       ((list & judge-hd judge-tl &) judge2)
       (acc-hd (intersect-judgements-acc judge1 judge-hd acc state)))
    (intersect-judgements-acc judge1 judge-tl acc-hd state)))

(verify-guards intersect-judgements-acc)

(defthm correctness-of-intersect-judgements-acc-judge1
  (implies (and (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judge1 a))
           (ev-smtcp (intersect-judgements-acc judge1 judge2 acc state) a))
  :hints (("Goal"
           :in-theory (e/d (intersect-judgements-acc is-conjunct?)
                           (pseudo-termp
                            implies-of-is-conjunct?
                            acl2::pseudo-termp-opener
                            symbol-listp
                            consp-of-is-conjunct?
                            acl2::symbolp-of-car-when-symbol-listp
                            acl2::symbol-listp-of-cdr-when-symbol-listp)))))

(defthm correctness-of-intersect-judgements-acc-judge2
  (implies (and (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judge2 a))
           (ev-smtcp (intersect-judgements-acc judge1 judge2 acc state) a))
  :hints (("Goal"
           :in-theory (e/d (intersect-judgements-acc is-conjunct?)
                           (pseudo-termp
                            implies-of-is-conjunct?
                            acl2::pseudo-termp-opener
                            symbol-listp
                            consp-of-is-conjunct?
                            acl2::symbolp-of-car-when-symbol-listp
                            acl2::symbol-listp-of-cdr-when-symbol-listp)))))

(define intersect-judgements ((judge1 pseudo-termp)
                              (judge2 pseudo-termp)
                              state)
  :returns (intersect pseudo-termp)
  (intersect-judgements-acc judge1 judge2 ''t state)
  ///
  (defthm correctness-of-intersect-judgements-judge1
    (implies (and (pseudo-termp judge1)
                  (pseudo-termp judge2)
                  (alistp a)
                  (ev-smtcp judge1 a))
             (ev-smtcp (intersect-judgements judge1 judge2 state) a))
    :hints (("Goal"
             :in-theory (enable intersect-judgements))))

  (defthm correctness-of-intersect-judgements-judge2
    (implies (and (pseudo-termp judge1)
                  (pseudo-termp judge2)
                  (alistp a)
                  (ev-smtcp judge2 a))
             (ev-smtcp (intersect-judgements judge1 judge2 state) a))
    :hints (("Goal"
             :in-theory (enable intersect-judgements)))))

#|
(defthm test (implies (integerp x) (rationalp x)))
(intersect-judgements '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                      '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                      state)

(intersect-judgements '(if (rationalp x) 't 'nil)
                      '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                      state)
|#

;; --------------------------------------------------------------------
;; Another way to intersect judgements that should be easier for proofs

(define substitute-term-in-type-predicate ((single-judge pseudo-termp)
                                           (term pseudo-termp)
                                           (new-var symbolp)
                                           (supertype-alst type-to-types-alist-p))
  :returns (new-judge pseudo-termp)
  :guard (type-predicate-of-term single-judge term supertype-alst)
  :ignore-ok t
  (b* ((single-judge (pseudo-term-fix single-judge))
       ((unless (type-predicate-of-term single-judge term supertype-alst))
        (er hard? 'judgement-fns=>substitute-term-in-type-predicate
            "Type predicate judgement is malformed: ~q0" single-judge))
       (new-var (symbol-fix new-var))
       ((mv okp type)
        (case-match single-judge
          ((type &) (mv t type))
          (& (mv nil nil))))
       ((unless (mbt okp)) nil))
    `(,type ,new-var)))

(define substitute-term-in-args ((args pseudo-term-listp)
                                 (term pseudo-termp)
                                 (new-var symbolp))
  :returns (new-args pseudo-term-listp)
  (b* ((args (pseudo-term-list-fix args))
       (new-var (symbol-fix new-var))
       ((unless (consp args)) nil)
       ((cons first-arg rest-args) args)
       ((if (equal first-arg term)) (cons new-var rest-args)))
    (cons first-arg (substitute-term-in-args rest-args term new-var))))

(define substitute-term-in-single-var-fncall ((single-judge pseudo-termp)
                                              (term pseudo-termp)
                                              (new-var symbolp))
  :returns (new-judge pseudo-termp)
  :guard (single-var-fncall-of-term single-judge term)
  (b* ((single-judge (pseudo-term-fix single-judge))
       ((unless (single-var-fncall-of-term single-judge term))
        (er hard? 'judgement-fns=>substitute-term-in-single-var-fncall
            "Single-var fncall judgement is malformed: ~q0" single-judge))
       ((mv okp fn args)
        (case-match single-judge
          ((fn . args) (mv t fn args))
          (& (mv nil nil nil))))
       ((unless (mbt okp)) nil))
    `(,fn ,@(substitute-term-in-args args term new-var))))

(define substitute-term-in-judge ((single-judge pseudo-termp)
                                  (term pseudo-termp)
                                  (new-var symbolp)
                                  (supertype-alst type-to-types-alist-p))
  :returns (new-judge pseudo-termp)
  :guard (judgement-of-term single-judge term supertype-alst)
  (b* ((single-judge (pseudo-term-fix single-judge))
       (new-var (symbol-fix new-var)))
    (cond ((equal single-judge term) new-var)
          ((type-predicate-of-term single-judge term supertype-alst)
           (substitute-term-in-type-predicate single-judge term new-var supertype-alst))
          ((single-var-fncall-of-term single-judge term)
           (substitute-term-in-single-var-fncall single-judge term new-var))
          (t nil))))

#|
(substitute-term-in-judge '(rationalp (foo x))
                          '(foo x)
                          'x0
                          `((rationalp . (,(make-type-tuple)))))

(substitute-term-in-judge '(< (foo x) '0)
                          '(foo x)
                          'x0
                          `((rationalp . (,(make-type-tuple)))))

(substitute-term-in-judge '(foo x)
                          '(foo x)
                          'x0
                          `((rationalp . (,(make-type-tuple)))))
|#

(define make-fast-judgements ((judge pseudo-termp)
                              (term pseudo-termp)
                              (new-var symbolp)
                              (supertype-alst type-to-types-alist-p)
                              (alst pseudo-term-integerp)
                              (count integerp))
  :returns (mv (new-alst pseudo-term-integerp)
               (new-cnt integerp))
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (supertype-alst (type-to-types-alist-fix supertype-alst))
       (count (ifix count))
       (alst (pseudo-term-integer-fix alst))
       ((unless (is-judgements? judge term supertype-alst))
        (mv (er hard? 'judgement-fns=>make-fast-judgements
                "Judgement for term ~p0 is malformed: ~p1~%" term judge)
            0))
       ((if (equal judge ''t)) (mv alst count))
       ((if (judgement-of-term judge term supertype-alst))
        (mv (acons (substitute-term-in-judge judge term new-var supertype-alst)
                   count alst)
            (1+ count)))
       ((unless (consp judge)) (mv alst count))
       ((list & judge-hd judge-tl &) judge)
       ((mv new-alst new-cnt)
        (make-fast-judgements judge-hd term new-var supertype-alst alst count)))
    (make-fast-judgements judge-tl term new-var supertype-alst
                          new-alst new-cnt)))

(verify-guards make-fast-judgements)

#|
(make-fast-judgements '(if (integerp (foo x))
                           (rationalp (foo x))
                         'nil)
                      '(foo x)
                      'x0
                      `((rationalp . (,(make-type-tuple)))
                        (integerp . (,(make-type-tuple))))
                      nil
                      0)
|#

(define map-judgements-helper ((judge pseudo-termp)
                               (term pseudo-termp)
                               (new-var symbolp)
                               (supertype-alst type-to-types-alist-p)
                               (alst pseudo-term-integerp)
                               (acc maybe-integer-listp))
  :returns (ind-list maybe-integer-listp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (supertype-alst (type-to-types-alist-fix supertype-alst))
       (alst (pseudo-term-integer-fix alst))
       (acc (maybe-integer-list-fix acc))
       ((unless (is-judgements? judge term supertype-alst))
        (er hard? 'judgement-fns=>map-judgements-helper
            "Judgement for term ~p0 is malformed: ~p1~%" term judge))
       ((if (equal judge ''t)) acc)
       ((if (judgement-of-term judge term supertype-alst))
        (b* ((new-judge
              (substitute-term-in-judge judge term new-var supertype-alst))
             (exist? (assoc-equal new-judge alst))
             ((if exist?) (cons (cdr exist?) acc)))
          (cons nil acc)))
       ((unless (consp judge)) acc)
       ((list & judge-hd judge-tl &) judge)
       (new-acc (map-judgements-helper judge-hd term new-var supertype-alst alst acc)))
    (map-judgements-helper judge-tl term new-var supertype-alst alst new-acc)))

(verify-guards map-judgements-helper)

(define map-judgements ((judge pseudo-termp)
                        (term pseudo-termp)
                        (new-var symbolp)
                        (supertype-alst type-to-types-alist-p)
                        (alst pseudo-term-integerp))
  :returns (ind-list maybe-integer-listp)
  (reverse (map-judgements-helper judge term new-var supertype-alst alst nil)))

#|
(map-judgements '(if (integerp (bar x))
                     (if (acl2-numberp (bar x))
                         (rationalp (bar x))
                       'nil)
                   'nil)
                '(bar x)
                'x0
                `((rationalp . (,(make-type-tuple)))
                  (integerp . (,(make-type-tuple)))
                  (acl2-numberp . (,(make-type-tuple))))
                '(((rationalp x0) . 1)
                  ((integerp x0) . 0)))
|#

;; else judgements
(define construct-judge-by-list ((judge pseudo-termp)
                                 (term pseudo-termp)
                                 (supertype-alst type-to-types-alist-p)
                                 (ind-lst maybe-integer-listp)
                                 (acc pseudo-termp))
  :returns (mv (new-judge pseudo-termp)
               (rest-ind maybe-integer-listp))
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (supertype-alst (type-to-types-alist-fix supertype-alst))
       (ind-lst (maybe-integer-list-fix ind-lst))
       (acc (pseudo-term-fix acc))
       ((unless (is-judgements? judge term supertype-alst))
        (mv ''t
            (er hard? 'judgement-fns=>construct-judge-by-list
                "Judgement for term ~p0 is malformed: ~p1~%" term judge)))
       ((if (equal judge ''t)) (mv acc ind-lst))
       ((if (judgement-of-term judge term supertype-alst))
        (b* (((unless (consp ind-lst))
              (mv ''t
                  (er hard? 'judgement-fns=>construct-judge-by-list
                      "Run out of indices.~%")))
             ((cons curr-ind rest-ind) ind-lst)
             ((unless curr-ind) (mv acc rest-ind)))
          (mv `(if ,judge ,acc 'nil) rest-ind)))
       ((unless (consp judge)) (mv acc ind-lst))
       ((list & judge-hd judge-tl &) judge)
       ((mv new-acc new-ind)
        (construct-judge-by-list judge-hd term supertype-alst ind-lst acc)))
    (construct-judge-by-list judge-tl term supertype-alst new-ind new-acc)))

(verify-guards construct-judge-by-list)

#|
(construct-judge-by-list '(if (integerp (bar x))
                              (if (acl2-numberp (bar x))
                                  (rationalp (bar x))
                                'nil)
                            'nil)
                         '(bar x)
                         `((rationalp . (,(make-type-tuple)))
                           (integerp . (,(make-type-tuple)))
                           (acl2-numberp . (,(make-type-tuple))))
                         '(0 nil 1)
                         ''t)
|#

(defthm correctness-of-is-judgements?
  (implies (and (pseudo-termp judge)
                (pseudo-termp term)
                (type-to-types-alist-p supertype-alst)
                (alistp a)
                (ev-smtcp judge a)
                (is-judgements? judge term supertype-alst)
                (not (equal judge ''t))
                (not (judgement-of-term judge term supertype-alst))
                (consp judge))
           (and (ev-smtcp (cadr judge) a)
                (ev-smtcp (caddr judge) a)))
  :hints (("Goal"
           :in-theory (e/d (is-judgements?)
                           (pseudo-termp
                            symbol-listp)))))

(defthm correctness-of-construct-judge-by-list
  (implies (and (pseudo-termp judge)
                (pseudo-termp term)
                (pseudo-termp acc)
                (type-to-types-alist-p supertype-alst)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp acc a))
           (ev-smtcp
            (mv-nth 0 (construct-judge-by-list judge term supertype-alst ind-lst acc)) a))
  :hints (("Goal"
           :in-theory (enable construct-judge-by-list))))

(define find-nth-judge ((judge pseudo-termp)
                        (term pseudo-termp)
                        (supertype-alst type-to-types-alist-p)
                        (nth integerp))
  :returns (mv (the-judge pseudo-termp)
               (new-nth integerp))
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (supertype-alst (type-to-types-alist-fix supertype-alst))
       (nth (ifix nth))
       ((unless (is-judgements? judge term supertype-alst))
        (mv (er hard? 'judgement-fns=>find-nth-judge
                "Judgement for term ~p0 is malformed: ~p1~%" term
                judge)
            0))
       ((if (and (<= nth 0) (equal judge ''t)))
        (mv nil nth))
       ((if (and (<= nth 0)
                 (judgement-of-term judge term supertype-alst)))
        (mv judge 0))
       ((if (equal judge ''t)) (mv nil nth))
       ((if (judgement-of-term judge term supertype-alst)) (mv nil (1- nth)))
       ((if (<= nth 0)) (mv (cadr judge) 0))
       ((unless (consp judge))
        (mv (er hard? 'judgement-fns=>find-nth-judge
                "Can't find ~p0th term in judge ~p1~%" nth judge)
            0))
       ((list & judge-hd judge-tl &) judge)
       ((mv new-judge new-nth)
        (find-nth-judge judge-hd term supertype-alst nth))
       ((if new-judge) (mv new-judge new-nth)))
    (find-nth-judge judge-tl term supertype-alst new-nth)))

(verify-guards find-nth-judge)

#|
(find-nth-judge '(if (integerp (foo x))
                     (rationalp (foo x))
                   'nil)
                '(foo x)
                `((rationalp . (,(make-type-tuple)))
                  (integerp . (,(make-type-tuple)))
                  (acl2-numberp . (,(make-type-tuple))))
                1)

(find-nth-judge '(if (integerp (foo x))
                     (rationalp (foo x))
                   'nil)
                '(foo x)
                `((rationalp . (,(make-type-tuple)))
                  (integerp . (,(make-type-tuple)))
                  (acl2-numberp . (,(make-type-tuple))))
                2)
|#

(defthm correctness-of-find-nth-judge
  (implies (and (pseudo-termp judge)
                (pseudo-termp term)
                (type-to-types-alist-p supertype-alst)
                (alistp a)
                (ev-smtcp judge a)
                (mv-nth 0 (find-nth-judge judge term supertype-alst nth)))
           (ev-smtcp
            (mv-nth 0 (find-nth-judge judge term supertype-alst nth)) a))
  :hints (("Goal"
           :in-theory (enable find-nth-judge))))

(define construct-judge-by-find ((judge pseudo-termp)
                                 (term pseudo-termp)
                                 (supertype-alst type-to-types-alist-p)
                                 (ind-lst maybe-integer-listp)
                                 (acc pseudo-termp))
  :returns (new-judge pseudo-termp)
  :measure (len ind-lst)
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (supertype-alst (type-to-types-alist-fix supertype-alst))
       (ind-lst (maybe-integer-list-fix ind-lst))
       (acc (pseudo-term-fix acc))
       ((unless (consp ind-lst)) acc)
       ((cons curr-ind rest-ind) ind-lst)
       ((unless curr-ind)
        (construct-judge-by-find judge term supertype-alst rest-ind acc))
       ((mv j &) (find-nth-judge judge term supertype-alst curr-ind))
       ((unless j)
        (prog2$ (er hard? 'judgement-fns=>construct-judge-by-find
                    "Can't find ~p0-th judgement in judgements ~p1~%"
                    curr-ind judge)
                ''t)))
    (construct-judge-by-find judge term supertype-alst rest-ind
                             `(if ,j ,acc 'nil))))

#|
(construct-judge-by-find '(if (integerp (foo x))
                              (rationalp (foo x))
                            'nil)
                         '(foo x)
                         `((rationalp . (,(make-type-tuple)))
                           (integerp . (,(make-type-tuple)))
                           (acl2-numberp . (,(make-type-tuple))))
                         '(0 nil 1)
                         ''t)
|#

(defthm correctness-of-construct-judge-by-find
  (implies (and (pseudo-termp judge)
                (pseudo-termp term)
                (pseudo-termp acc)
                (type-to-types-alist-p supertype-alst)
                (maybe-integer-listp ind-lst)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp acc a))
           (ev-smtcp
            (construct-judge-by-find judge term supertype-alst ind-lst acc)
            a))
  :hints (("Goal"
           :in-theory (enable construct-judge-by-find))))

;; slow return type theorem
(encapsulate ()
  (local
   (in-theory (e/d (pseudo-term-fix)
                   (symbol-listp
                    pseudo-termp
                    acl2::pseudo-termp-car
                    pseudo-term-listp-of-symbol-listp
                    (:rewrite consp-of-is-conjunct?)))))

(define rearrange-if-judgements ((judge pseudo-termp))
  :returns (res pseudo-termp)
  :verify-guards nil
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       ((mv okp if-cond then-judge else-judge)
        (case-match judge
          (('if if-cond then-judge else-judge)
           (mv t if-cond then-judge else-judge))
          (& (mv nil nil nil nil))))
       ((unless okp)
        (prog2$ (er hard? 'judgement-fns=>rearrange-if-judgements
                    "Judgements are malformed.~%")
                ''t))
       ((unless (and (is-conjunct? then-judge)
                     (is-conjunct? else-judge)))
        (prog2$ (er hard? 'judgement-fns=>rearragen-if-judgements
                    "Then or else judges is malformed.~%")
                ''t))
       ((if (and (equal then-judge ''t) (equal else-judge ''t))) ''t)
       ((if (and (not (equal then-judge ''t))
                 (not (equal else-judge ''t))))
        (b* (((list & first-then rest-then &) then-judge)
             ((list & first-else rest-else &) else-judge)
             (first `(if ,if-cond ,first-then ,first-else))
             (rest (rearrange-if-judgements
                    `(if ,if-cond ,rest-then ,rest-else))))
          `(if ,first ,rest 'nil))))
    (prog2$ (er hard? 'judgement-fns=>combine-judgements
                "Judgements are malformed.~%")
            ''t)))
)

(verify-guards rearrange-if-judgements
  :hints (("Goal" :in-theory (disable symbol-listp))))

#|
(rearrange-if-judgements '(if (cond x)
                              (if (rationalp (foo x))
                                  (if (integerp (foo x)) 't 'nil)
                                'nil)
                            (if (rationalp (bar x))
                                (if (integerp (bar x)) 't 'nil)
                              'nil)))
|#

(defthm correctness-of-rearrange-if-judgements
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge)
                (alistp a)
                (ev-smtcp judge a))
           (ev-smtcp (rearrange-if-judgements judge) a))
  :hints (("Goal"
           :in-theory (e/d (rearrange-if-judgements)
                           (symbol-listp)))))

;; One problem: what to return when args are of different lengths
(define commute-if-for-args ((if-cond pseudo-termp)
                             (then-args pseudo-term-listp)
                             (else-args pseudo-term-listp))
  :returns (new-args pseudo-term-listp)
  (b* ((if-cond (pseudo-term-fix if-cond))
       (then-args (pseudo-term-list-fix then-args))
       (else-args (pseudo-term-list-fix else-args))
       ((unless (or (and then-args else-args)
                    (and (not then-args) (not else-args))))
        (er hard? 'judgement-fns=>commute-if-for-args
            "Then and else should be of the same lengths.~%"))
       ((unless (and (consp then-args) (consp else-args))) nil)
       ((cons then-hd then-tl) then-args)
       ((cons else-hd else-tl) else-args)
       (rest-args
        (commute-if-for-args if-cond then-tl else-tl))
       (if-term `(if ,if-cond ,then-hd ,else-hd))
       ((if (equal then-hd else-hd)) `(,then-hd ,@rest-args)))
    `(,if-term ,@rest-args)))

(encapsulate ()
(local
 (defthm lemma
   (implies (and (pseudo-term-listp x) x)
            (not (equal (len x) 0))))
 )

(defthm correctness-of-commute-if-for-args-cond
  (implies (and (pseudo-termp if-cond)
                (pseudo-term-listp then-args)
                (pseudo-term-listp else-args)
                (alistp a)
                (ev-smtcp if-cond a)
                (equal (len then-args) (len else-args)))
           (equal (ev-smtcp-lst (commute-if-for-args if-cond then-args else-args) a)
                  (ev-smtcp-lst then-args a)))
  :hints (("Goal"
           :in-theory (enable commute-if-for-args)
           :induct (commute-if-for-args if-cond then-args else-args)
           )))

(defthm correctness-of-commute-if-for-args-notcond
  (implies (and (pseudo-termp if-cond)
                (pseudo-term-listp then-args)
                (pseudo-term-listp else-args)
                (alistp a)
                (not (ev-smtcp if-cond a))
                (equal (len then-args) (len else-args)))
           (equaL (ev-smtcp-lst (commute-if-for-args if-cond then-args else-args) a)
                  (ev-smtcp-lst else-args a)))
  :hints (("Goal"
           :in-theory (enable commute-if-for-args)
           :induct (commute-if-for-args if-cond then-args else-args)
           )))
)

#|
(commute-if-for-args '(cond x) '((foo x)) '((bar x)))
|#

(define commute-if ((judge pseudo-termp)
                    (then-term pseudo-termp)
                    (else-term pseudo-termp)
                    (supertype-alst type-to-types-alist-p))
  :returns (new-judge pseudo-termp
                      :hints (("Goal"
                               :in-theory (disable symbol-listp
                                                   true-list-listp
                                                   acl2::true-listp-of-car-when-true-list-listp))))
  :guard-hints (("Goal"
                 :in-theory (disable symbol-listp true-list-listp
                                     acl2::true-listp-of-car-when-true-list-listp)))
  (b* ((judge (pseudo-term-fix judge))
       (then-term (pseudo-term-fix then-term))
       (else-term (pseudo-term-fix else-term))
       ((mv okp if-cond then-judge else-judge)
        (case-match judge
          (('if if-cond then-judge else-judge)
           (mv t if-cond then-judge else-judge))
          (& (mv nil nil nil nil))))
       ((unless okp)
        (prog2$ (er hard? 'judgement-fns=>commute-if
                    "If judge is malformed.~%")
                ''t))
       (if-term `(if ,if-cond ,then-term ,else-term))
       ((unless (and (judgement-of-term then-judge then-term supertype-alst)
                     (judgement-of-term else-judge else-term supertype-alst)))
        (prog2$ (er hard? 'judgement-fns=>commute-if
                    "Then or else judgement is malformed.~%")
                ''t)))
    (cond ((and (equal then-judge then-term) (equal else-judge else-term)) if-term)
          ((and (not (equal then-judge then-term))
                (not (equal else-judge else-term))
                (equal (car then-judge) (car else-judge))
                (equal (len (cdr then-judge)) (len (cdr else-judge))))
           `(,(car then-judge)
             ,@(commute-if-for-args if-cond (cdr then-judge) (cdr else-judge))))
          (t (prog2$ (er hard? 'judgement-fns=>commute-if
                         "Then or else judgement is malformed.~%")
                     ''t)))))

#|
(commute-if '(if (cond x)
                 (rationalp (foo x))
               (rationalp (bar x)))
            '(foo x)
            '(bar x)
            `((rationalp . (,(make-type-tuple)))
              (integerp . (,(make-type-tuple)))
              (acl2-numberp . (,(make-type-tuple)))))
|#

;; It takes a while
(defthm correctness-of-commute-if
  (implies (and (pseudo-termp judge)
                (pseudo-termp then-term)
                (pseudo-termp else-term)
                (type-to-types-alist-p supertype-alst)
                (alistp a)
                (ev-smtcp judge a))
           (ev-smtcp (commute-if judge then-term else-term supertype-alst) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (commute-if)
                           (correctness-of-is-judgements?
                            correctness-of-path-test-list
                            correctness-of-path-test
                            consp-of-pseudo-lambdap
                            pseudo-lambdap-of-fn-call-of-pseudo-termp
                            symbolp-of-car-when-member-equal-of-type-to-types-alist-p
                            ev-smtcp-of-booleanp-call
                            ev-smtcp-of-lambda
                            pseudo-termp
                            symbol-listp
                            pseudo-term-listp
                            pseudo-term-listp-of-symbol-listp
                            acl2::pseudo-termp-list-cdr
                            consp-of-is-conjunct?
                            ev-smtcp-of-fncall-args
                            correctness-of-commute-if-for-args-cond
                            correctness-of-commute-if-for-args-notcond
                            lambda-of-pseudo-lambdap
                            pseudo-term-listp-of-cdr-of-pseudo-termp
                            ev-smtcp-of-return-last-call
                            ev-smtcp-of-rationalp-call
                            ev-smtcp-of-not-call
                            ev-smtcp-of-integerp-call
                            ev-smtcp-of-implies-call
                            ev-smtcp-of-iff-call
                            ev-smtcp-of-hint-please-call
                            ev-smtcp-of-equal-call
                            ev-smtcp-of-cons-call
                            ev-smtcp-of-binary-+-call
                            acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp))
           :use ((:instance ev-smtcp-of-fncall-args
                            (x (cons (car (caddr judge))
                                     (commute-if-for-args (cadr judge)
                                                          (cdr (caddr judge))
                                                          (cdr (cadddr judge)))))
                            (a a))
                 (:instance ev-smtcp-of-fncall-args
                            (x (caddr judge))
                            (a a))
                 (:instance ev-smtcp-of-fncall-args
                            (x (cons (car (cadddr judge))
                                     (commute-if-for-args (cadr judge)
                                                          (cdr (caddr judge))
                                                          (cdr (cadddr judge)))))
                            (a a))
                 (:instance ev-smtcp-of-fncall-args
                            (x (cadddr judge))
                            (a a))
                 (:instance correctness-of-commute-if-for-args-cond
                            (if-cond (cadr judge))
                            (then-args (cdr (caddr judge)))
                            (else-args (cdr (cadddr judge)))
                            (a a))
                 (:instance correctness-of-commute-if-for-args-notcond
                            (if-cond (cadr judge))
                            (then-args (cdr (caddr judge)))
                            (else-args (cdr (cadddr judge)))
                            (a a))))))

(define merge-if-judgements ((judge pseudo-termp)
                             (then-term pseudo-termp)
                             (else-term pseudo-termp)
                             (supertype-alst type-to-types-alist-p))
  :returns (new-judge pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       ((unless (is-conjunct? judge))
        (prog2$ (er hard? 'judgement-fns=>merge-if-judgements
                    "Judgement is malformed.~%")
                ''t))
       ((if (equal judge ''t)) ''t)
       ((list & first-judge rest-judge &) judge)
       (new-first (commute-if first-judge then-term else-term supertype-alst))
       (new-rest
        (merge-if-judgements rest-judge then-term else-term supertype-alst)))
    `(if ,new-first ,new-rest 'nil)))

#|
(merge-if-judgements '(if (if (cond x)
                              (rationalp (foo x))
                              (rationalp (bar x)))
                          (if (if (cond x)
                                  (integerp (foo x))
                                  (integerp (bar x)))
                              't
                              'nil)
                        'nil)
                     '(foo x)
                     '(bar x)
                     `((rationalp . (,(make-type-tuple)))
                       (integerp . (,(make-type-tuple)))
                       (acl2-numberp . (,(make-type-tuple)))))
|#

(defthm correctness-of-merge-if-judgements
  (implies (and (pseudo-termp judge)
                (pseudo-termp then-term)
                (pseudo-termp else-term)
                (type-to-types-alist-p supertype-alst)
                (alistp a)
                (ev-smtcp judge a))
           (ev-smtcp (merge-if-judgements judge then-term else-term supertype-alst) a))
  :hints (("Goal"
           :in-theory (e/d (merge-if-judgements)
                           ()))))

;;------------------------------------------------------
;; Union judgements

(define union-judgements-acc ((judge pseudo-termp)
                              (acc pseudo-termp)
                              state)
  :returns (union pseudo-termp)
  :verify-guards nil
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       ((if (and (not (is-conjunct? judge))
                 (not (path-test acc judge))))
        `(if ,judge ,acc 'nil))
       ((unless (is-conjunct? judge)) acc)
       ((if (equal judge ''t)) acc)
       ((list & judge-hd judge-tl &) judge)
       (acc-hd (union-judgements-acc judge-hd acc state)))
    (union-judgements-acc judge-tl acc-hd state)))

(verify-guards union-judgements-acc)

(defthm correctness-of-union-judgements-acc
  (implies (and (pseudo-termp judge)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judge a))
           (ev-smtcp (union-judgements-acc judge acc state) a))
  :hints (("Goal"
           :in-theory (e/d (union-judgements-acc is-conjunct?)
                           ()))))

(define union-judgements ((judge1 pseudo-termp)
                          (judge2 pseudo-termp)
                          state)
  :returns (union pseudo-termp)
  (union-judgements-acc judge2 judge1 state))

(defthm correctness-of-union-judgements
  (implies (and (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp judge1 a)
                (ev-smtcp judge2 a))
           (ev-smtcp (union-judgements judge1 judge2 state) a))
  :hints (("Goal"
           :in-theory (e/d (union-judgements)
                           ()))))


#|
(defthm test (implies (integerp x) (rationalp x)))
(union-judgements '(if (integerp x) 't 'nil)
'(if (rationalp x) (< x '0) 'nil)
state)
(union-judgements ''t
'(if (integerp x) (if (rationalp x) (< x '0) 'nil)
'nil)
state)
(union-judgements '(if (rationalp x) 't 'nil)
'(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
state)
|#

;;-------------------------------------------------------
;; Super/subtype judgements

(encapsulate ()
  (local
   (in-theory (disable assoc-equal lambda-of-pseudo-lambdap symbol-listp
                       pseudo-term-listp-of-symbol-listp
                       acl2::symbol-listp-of-cdr-when-symbol-listp
                       consp-of-is-conjunct?
                       acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
                       acl2::pseudo-lambda-listp-of-cdr-when-pseudo-lambda-listp
                       pseudo-lambdap-of-fn-call-of-pseudo-termp
                       nil-of-assoc-equal-of-pseudo-term-alistp
                       pseudo-term-alistp-when-not-consp
                       consp-of-pseudo-lambdap
                       acl2::pseudo-lambdap-of-car-when-pseudo-termp
                       acl2::pseudo-termp-list-cdr
                       pseudo-term-listp-of-cdr-of-pseudo-termp)))

(define construct-one-super/subtype ((type-judge pseudo-termp)
                                     (type-tuple type-tuple-p)
                                     (type-alst type-to-types-alist-p)
                                     (path-cond pseudo-termp)
                                     state)
  :ignore-ok t
  :returns (super/subtype-judge pseudo-termp)
  (b* ((type-judge (pseudo-term-fix type-judge))
       ((type-tuple tu) (type-tuple-fix type-tuple))
       (path-cond (pseudo-term-fix path-cond))
       (type-thm (acl2::meta-extract-formula-w tu.thm (w state)))
       ((unless (and type-thm (pseudo-termp type-thm)))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
             tu.thm type-thm)
         ''t))
       ((unless (type-predicate-p type-judge type-alst))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "~p0 is not a type-predicate-p. Smtlink doesn't know how to ~
              calculate super/subtype for it.~%"
             type-judge)
         ''t))
       ((list root-type term) type-judge)
       ((unless (equal root-type tu.type))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "The judgement's type ~p0 doesn't match the type-tuple's type ~
             ~p1~%" root-type tu.type)
         ''t))
       ((unless (equal (len tu.formals) 1))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "The number of free variables in the type theorem must be one, ~
              but we find ~p0~%" tu.formals)
         ''t))
       (substed-thm
        (acl2::substitute-into-term type-thm `((,(car tu.formals) . ,term))))
       ((unless (pseudo-termp substed-thm))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "Substituted theorem is not pseudo-term ~p0~%" substed-thm)
         ''t)))
    (case-match substed-thm
      (('implies type-predicates (!tu.neighbour-type !term))
       (b* (((if (equal tu.neighbour-type 'quote)) ''t)
            ((unless (path-test-list `(if ,type-judge ,path-cond 'nil)
                                     type-predicates))
             ''t))
         (caddr substed-thm)))
      (& ''t))))
)

#|
(defthm test (implies (integerp x) (rationalp x)))
(defoption maybe-integerp integerp :pred maybe-integerp)
(defthm test1 (implies (integerp x) (maybe-integerp x)))
(defthm test2 (implies (and (maybe-integerp y) y) (integerp y)))
(construct-one-super/subtype '(maybe-integerp x)
                             (make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                              :formals '(y)
                                              :thm 'test2)
                             `((maybe-integerp . (,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                                                    :formals '(y)
                                                                    :thm 'test2))))
                             '(if x 't 'nil) state)
|#

(encapsulate ()
  (local
   (defthm crock
     (implies (and (pseudo-termp term)
                   (alistp a)
                   (consp term)
                   (consp (cdr term))
                   (equal (car term) 'implies)
                   (ev-smtcp term a)
                   (ev-smtcp (cadr term) a))
              (ev-smtcp (caddr term) a))))

  (local
   (defthm crock1
     (implies (and (pseudo-termp x)
                   (consp x)
                   (not (equal (car x) 'quote))
                   (consp (cdr x)))
              (pseudo-termp (cadr x)))
     :hints (("Goal"
              :in-theory (enable pseudo-termp)))))

(defthm correctness-of-construct-one-super/subtype
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp type-judge)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp type-judge a)
                (ev-smtcp path-cond a))
           (ev-smtcp (construct-one-super/subtype
                      type-judge type-tuple type-alst path-cond state)
                     a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (construct-one-super/subtype)
                           (w
                            symbol-listp
                            pseudo-term-listp-of-symbol-listp
                            pseudo-term-listp
                            consp-of-is-conjunct?
                            acl2::pseudo-termp-car
                            acl2::symbol-listp-of-cdr-when-symbol-listp
                            pseudo-termp
                            correctness-of-path-test
                            consp-of-pseudo-lambdap
                            acl2::pseudo-termp-opener
                            ev-smtcp-of-booleanp-call
                            ev-smtcp-of-lambda
                            implies-of-is-conjunct?
                            correctness-of-path-test-list
                            crock))
           :use ((:instance correctness-of-path-test-list
                            (path-cond `(if ,type-judge ,path-cond 'nil))
                            (expr-conj (cadr (acl2::substitute-into-term
                                              (meta-extract-formula (type-tuple->thm type-tuple)
                                                                    state)
                                              (list (cons (car (type-tuple->formals type-tuple))
                                                          (cadr type-judge))))))
                            (a a))
                 (:instance crock
                            (term (acl2::substitute-into-term
                                   (meta-extract-formula (type-tuple->thm type-tuple)
                                                         state)
                                   (list (cons (car (type-tuple->formals type-tuple))
                                               (cadr type-judge)))))
                            (a a))))))
)

(define construct-closure ((type-judge pseudo-termp)
                           (super/subtype-tuple type-tuple-list-p)
                           (type-alst type-to-types-alist-p)
                           (path-cond pseudo-termp)
                           (acc pseudo-termp)
                           state)
  :returns (new-acc pseudo-termp)
  :measure (len super/subtype-tuple)
  (b* ((acc (pseudo-term-fix acc))
       (type-judge (pseudo-term-fix type-judge))
       (super/subtype-tuple (type-tuple-list-fix super/subtype-tuple))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (consp super/subtype-tuple)) acc)
       ((cons first rest) super/subtype-tuple)
       (one (construct-one-super/subtype type-judge first type-alst path-cond
                                         state))
       ((if (equal one ''t))
        (construct-closure type-judge rest type-alst path-cond acc state)))
    (construct-closure type-judge rest type-alst path-cond
                       `(if ,one ,acc 'nil)
                       state)))

#|
(construct-closure '(integerp x)
                   `(,(make-type-tuple :type 'integerp :neighbour-type 'rationalp
                                       :formals '(x)
                                       :thm 'test)
                     ,(make-type-tuple :type 'integerp :neighbour-type
                                       'maybe-integerp
                                       :formals '(x)
                                       :thm 'test1))
                   `((integerp . (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp
                                                    :formals '(x)
                                                    :thm 'test)
                                  ,(make-type-tuple :type 'integerp :neighbour-type
                                                    'maybe-integerp
                                                    :formals '(x)
                                                    :thm 'test1)))
                     (rationalp . nil)
                     (maybe-integerp . nil))
                   ''t ''t state)

(construct-closure '(maybe-integerp x)
                   `(,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                       :formals '(y)
                                       :thm 'test2))
                   `((maybe-integerp . (,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                                          :formals '(y)
                                                          :thm 'test2))))
                   '(if x 't 'nil) ''t state)
|#

(defthm correctness-of-construct-closure
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp type-judge)
                (type-tuple-list-p super/subtype-tuple)
                (pseudo-termp path-cond)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp type-judge a)
                (ev-smtcp path-cond a)
                (ev-smtcp acc a))
           (ev-smtcp (construct-closure
                      type-judge super/subtype-tuple
                      type-alst path-cond acc state)
                     a))
  :hints (("Goal"
           :in-theory (enable construct-closure))))

(defines super/subtype-transitive-closure
  :well-founded-relation l<
  :verify-guards nil
  :flag-local nil

  (define super/subtype ((type-judge pseudo-termp)
                         (path-cond pseudo-termp)
                         (type-alst type-to-types-alist-p)
                         (closure pseudo-termp)
                         (clock natp)
                         state)
    ;; clock is the length of the supertype-alst
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix type-judge)))
    :returns (closure pseudo-termp)
    (b* ((type-judge (pseudo-term-fix type-judge))
         (closure (pseudo-term-fix closure))
         (type-alst (type-to-types-alist-fix type-alst))
         (clock (nfix clock))
         ((if (zp clock)) closure)
         (exist? (path-test closure type-judge))
         ((if exist?) closure)
         (new-closure `(if ,type-judge ,closure 'nil))
         ((unless (type-predicate-p type-judge type-alst))
          (prog2$
           (er hard? 'type-inference-bottomup=>super/subtype
               "Term ~p0 is not a type-predicate-p.~%" type-judge)
           ''t))
         ((cons type &) type-judge)
         (item (assoc-equal type type-alst))
         ((unless item)
          (prog2$
           (er hard? 'type-inference-bottomup=>super/subtype
               "Type ~p0 doesn't exist in the supertype alist.~%" type)
           ''t))
         ((unless (cdr item)) new-closure)
         (type-judge-lst
          (construct-closure type-judge (cdr item) type-alst path-cond
                             new-closure state)))
      (super/subtype-list type-judge-lst path-cond type-alst new-closure
                          (1- clock) state)))

  (define super/subtype-list ((type-judge-lst pseudo-termp)
                              (path-cond pseudo-termp)
                              (type-alst type-to-types-alist-p)
                              (closure pseudo-termp)
                              (clock natp)
                              state)
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix type-judge-lst)))
    :returns (closure pseudo-termp)
    (b* ((type-judge-lst (pseudo-term-fix type-judge-lst))
         (path-cond (pseudo-term-fix path-cond))
         (type-alst (type-to-types-alist-fix type-alst))
         (closure (pseudo-term-fix closure))
         (clock (nfix clock))
         ((unless (is-conjunct? type-judge-lst)) closure)
         ((if (equal type-judge-lst ''t)) closure)
         ((list & type-hd type-tl &) type-judge-lst)
         (new-closure
          (super/subtype type-hd path-cond type-alst closure clock state)))
      (super/subtype-list type-tl path-cond type-alst new-closure clock
                          state)))
  )

(verify-guards super/subtype)

#|
(super/subtype '(integerp x) ''t
               `((integerp . (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp
                                                :formals '(x)
                                                :thm 'test)
                              ,(make-type-tuple :type 'integerp :neighbour-type
                                                'maybe-integerp
                                                :formals '(x)
                                                :thm 'test1)))
                 (rationalp . nil)
                 (maybe-integerp . nil))
               ''t 4 state)

(super/subtype '(maybe-integerp x) '(if x 't 'nil)
               `((integerp . nil)
                 (rationalp . nil)
                 (maybe-integerp . (,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                                      :formals '(y)
                                                      :thm 'test2))))
               ''t 4 state)
|#

(encapsulate ()
  (local (in-theory (disable symbol-listp
                             pseudo-termp
                             pseudo-term-listp-of-symbol-listp
                             consp-of-is-conjunct?
                             acl2::symbol-listp-of-cdr-when-symbol-listp
                             acl2::symbol-listp-when-not-consp
                             consp-of-pseudo-lambdap
                             correctness-of-path-test-list
                             consp-of-cddr-of-pseudo-lambdap
                             ev-smtcp-of-variable)))

(defthm-super/subtype-transitive-closure-flag
  correctness-of-super/subtype-thms
  (defthm correctness-of-syper/subtype
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp type-judge)
                  (pseudo-termp path-cond)
                  (pseudo-termp closure)
                  (alistp a)
                  (ev-smtcp type-judge a)
                  (ev-smtcp path-cond a)
                  (ev-smtcp closure a))
             (ev-smtcp (super/subtype
                        type-judge path-cond type-alst
                        closure clock state)
                       a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (super/subtype) ()))))
    :flag super/subtype)
  (defthm correctness-of-super/subtype-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp type-judge-lst)
                  (pseudo-termp path-cond)
                  (pseudo-termp closure)
                  (alistp a)
                  (ev-smtcp type-judge-lst a)
                  (ev-smtcp path-cond a)
                  (ev-smtcp closure a))
             (ev-smtcp (super/subtype-list
                        type-judge-lst path-cond type-alst
                        closure clock state)
                       a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (super/subtype-list) ()))))
    :flag super/subtype-list))
)

(define super/subtype-judgements-acc ((judge pseudo-termp)
                                      (path-cond pseudo-termp)
                                      (type-alst type-to-types-alist-p)
                                      (acc pseudo-termp)
                                      state)
  :returns (judgements pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       ((if (type-predicate-p judge type-alst))
        (super/subtype judge path-cond type-alst acc (len type-alst) state))
       ((unless (is-conjunct? judge)) `(if ,judge ,acc 'nil))
       ((if (equal judge ''t)) acc)
       ((list* & cond then &) judge)
       (first-acc
        (super/subtype-judgements-acc cond path-cond type-alst acc state)))
    (super/subtype-judgements-acc then path-cond type-alst first-acc state)))

(verify-guards super/subtype-judgements-acc)

(defthm correctness-of-super/subtype-judgements-acc
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge)
                (pseudo-termp path-cond)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp path-cond a)
                (ev-smtcp acc a))
           (ev-smtcp (super/subtype-judgements-acc judge path-cond type-alst acc state)
                     a))
  :hints (("Goal"
           :in-theory (enable super/subtype-judgements-acc))))

(define super/subtype-judgements-fn ((judge pseudo-termp)
                                     (path-cond pseudo-termp)
                                     (type-alst type-to-types-alist-p)
                                     state)
  :returns (judgements pseudo-termp)
  (super/subtype-judgements-acc judge path-cond type-alst ''t state))

(defthm correctness-of-super/subtype-judgements-fn
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp path-cond a))
           (ev-smtcp (super/subtype-judgements-fn judge path-cond type-alst state)
                     a))
  :hints (("Goal"
           :in-theory (enable super/subtype-judgements-fn))))

#|
(super/subtype-judgements-fn '(if (integerp x) 't 'nil) ''t
                             `((integerp . (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp
                                                              :formals '(x)
                                                              :thm 'test)
                                            ,(make-type-tuple :type 'integerp :neighbour-type
                                                              'maybe-integerp
                                                              :formals '(x)
                                                              :thm 'test1)))
                               (rationalp . nil)
                               (maybe-integerp . nil))
                             state)

(super/subtype-judgements-fn '(if (maybe-integerp x) 't 'nil) '(if x 't 'nil)
                             `((integerp . nil)
                               (rationalp . nil)
                               (maybe-integerp . (,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                                                    :formals '(y)
                                                                    :thm 'test2))))
                             state)
|#

(defmacro super/subtype-judgements (judgements path-cond type-alst state
                                               &key which)
  `(if (equal ,which :super)
       (super/subtype-judgements-fn ,judgements ,path-cond
                                    ,type-alst ,state)
     (super/subtype-judgements-fn ,judgements ,path-cond
                                  ,type-alst ,state)))

#|
(super/subtype-judgements '(if (integerp x) 't 'nil) ''t
                          `((integerp . (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp
                                                            :formals '(x)
                                                            :thm 'test)
                                          ,(make-type-tuple :type 'integerp :neighbour-type
                                                            'maybe-integerp
                                                            :formals '(x)
                                                            :thm 'test1)))
                             (rationalp . nil)
                             (maybe-integerp . nil))
                          state
                          :which :super)

(super/subtype-judgements '(if (maybe-integerp x) 't 'nil) '(if x 't 'nil)
                          `((integerp . nil)
                            (rationalp . nil)
                            (maybe-integerp . (,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp
                                                                 :formals '(y)
                                                                 :thm 'test2))))
                          state
                          :which :sub)
|#

;; extend-judgements first calculate the subtypes then it calculate the
;; supertypes
(define extend-judgements ((judgements pseudo-termp)
                           (path-cond pseudo-termp)
                           (options type-options-p)
                           state)
  :returns (new-judgements pseudo-termp)
  (super/subtype-judgements
   (super/subtype-judgements judgements path-cond
                             (type-options->supertype (type-options-fix options))
                             state :which :sub)
   path-cond
   (type-options->subtype (type-options-fix options))
   state :which :super))

(defthm correctness-of-extend-judgements
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judgements)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judgements a)
                (ev-smtcp path-cond a))
           (ev-smtcp (extend-judgements judgements path-cond options state) a))
  :hints (("Goal"
           :in-theory (enable extend-judgements))))
