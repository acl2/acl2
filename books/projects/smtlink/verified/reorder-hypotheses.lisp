;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (March 3rd 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "extractor")

(defalist symbol-pseudo-term-list-alist
  :key-type symbolp
  :val-type pseudo-term-listp
  :true-listp t
  :pred symbol-pseudo-term-list-alistp)

(defalist pseudo-term-symbol-list-alist
  :key-type pseudo-termp
  :val-type symbol-listp
  :true-listp t
  :pred pseudo-term-symbol-list-alistp)

(define filter-type-hypo ((hypo-lst pseudo-term-listp)
                          (fixinfo smt-fixtype-info-p))
  :returns (mv (root-hypo pseudo-term-listp)
               (rest-hypo pseudo-term-listp))
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       ((unless (consp hypo-lst)) (mv nil nil))
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((mv tl-root tl-rest) (filter-type-hypo hypo-tl fixinfo))
       ((if (type-decl-p hypo-hd fixinfo))
        (mv (cons hypo-hd tl-root) tl-rest)))
    (mv tl-root (cons hypo-hd tl-rest))))

(defthm correctness-of-filter-type-hypo-1
  (implies (and (pseudo-term-listp hypo-lst)
                (smt-fixtype-info-p fixinfo))
           (b* (((mv & rest-hypo) (filter-type-hypo hypo-lst fixinfo)))
             (implies (ev-smtcp (conjoin hypo-lst) a)
                      (ev-smtcp (conjoin rest-hypo) a))))
  :hints (("Goal"
           :in-theory (enable filter-type-hypo))))

(defthm correctness-of-filter-type-hypo-2
  (implies (and (pseudo-term-listp hypo-lst)
                (smt-fixtype-info-p fixinfo))
           (b* (((mv root-hypo &) (filter-type-hypo hypo-lst fixinfo)))
             (implies (ev-smtcp (conjoin hypo-lst) a)
                      (ev-smtcp (conjoin root-hypo) a))))
  :hints (("Goal"
           :in-theory (enable filter-type-hypo))))

#|
(filter-type-hypo '((equal x2 (binary-+ x0 x1))
                    (equal x1 (rfix y))
                    (equal x0 (ifix x))
                    (integerp x)
                    (rationalp y))
                  `((integerp . ,(make-info-pair :fn-type :recognizer))
                    (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

(define update-alst ((free-vars symbol-listp)
                     (hypo pseudo-termp)
                     (alst symbol-pseudo-term-list-alistp))
  :measure (len free-vars)
  :returns (new-alst symbol-pseudo-term-list-alistp)
  (b* ((free-vars (symbol-list-fix free-vars))
       (hypo (pseudo-term-fix hypo))
       (alst (symbol-pseudo-term-list-alist-fix alst))
       ((unless (consp free-vars)) alst)
       ((cons var-hd var-tl) free-vars)
       (exists? (assoc-equal var-hd alst))
       ((unless exists?)
        (update-alst var-tl hypo (acons var-hd (list hypo) alst)))
       (new-alst (acons var-hd (cons hypo (cdr exists?)) alst)))
    (update-alst var-tl hypo new-alst)))

(define make-var-to-terms ((hypo-lst pseudo-term-listp)
                           (alst symbol-pseudo-term-list-alistp))
  :returns (new-alst symbol-pseudo-term-list-alistp)
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (alst (symbol-pseudo-term-list-alist-fix alst))
       ((unless (consp hypo-lst)) alst)
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((mv okp term) (case-match hypo-hd
                        (('equal & term) (mv t term))
                        (& (mv nil nil))))
       ((unless okp)
        (er hard? 'reorder-hypotheses=>make-var-to-terms
            "INTERNAL: bad equality: ~q0" hypo-hd))
       (free-vars (acl2::simple-term-vars term))
       (new-alst (update-alst free-vars hypo-hd alst)))
    (make-var-to-terms hypo-tl new-alst)))

#|
(make-var-to-terms '((equal x2 (binary-+ x0 x1))
                     (equal x1 (rfix y))
                     (equal x0 (ifix x)))
                   nil)
|#

(define make-term-to-vars ((hypo-lst pseudo-term-listp)
                           (alst pseudo-term-symbol-list-alistp))
  :returns (new-alst pseudo-term-symbol-list-alistp)
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (alst (pseudo-term-symbol-list-alist-fix alst))
       ((unless (consp hypo-lst)) alst)
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((mv okp term) (case-match hypo-hd
                        (('equal & term) (mv t term))
                        (& (mv nil nil))))
       ((unless okp)
        (er hard? 'reorder-hypotheses=>make-term-to-vars
            "INTERNAL: bad equality: ~q0" hypo-hd))
       (free-vars (acl2::simple-term-vars term))
       (exists? (assoc-equal term alst))
       ((if exists?) (make-term-to-vars hypo-tl alst)))
    (make-term-to-vars hypo-tl (acons hypo-hd free-vars alst))))

(defthm correctness-of-make-term-to-vars
  (implies (and (pseudo-term-listp hypo-lst)
                (pseudo-term-symbol-list-alistp alst)
                (alistp a)
                (implies (ev-smtcp (conjoin hypo-lst) a)
                         (ev-smtcp (conjoin (strip-cars alst)) a)))
           (implies (ev-smtcp (conjoin hypo-lst) a)
                    (ev-smtcp (conjoin
                               (strip-cars
                                (make-term-to-vars hypo-lst alst)))
                              a)))
  :hints (("Goal"
           :in-theory (e/d (make-term-to-vars)
                           (pseudo-termp
                            symbol-listp pseudo-term-listp
                            lambda-of-pseudo-lambdap
                            pseudo-term-listp-of-symbol-listp)))))

#|
(make-term-to-vars '((equal x2 (binary-+ x0 x1))
                     (equal x1 (rfix y))
                     (equal x0 (ifix x)))
                   nil)
|#

(define find-resolved-var ((term pseudo-termp)
                           (fixinfo smt-fixtype-info-p))
  :returns (var symbolp)
  (b* ((term (pseudo-term-fix term))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       ((unless (hypo-p term fixinfo))
        (er hard? 'reorder-hypotheses=>find-resolved-var
            "INTERNAL: bad equality: ~q0" term)))
    (cadr term)))

#|
(find-resolved-var '(equal x0 (ifix x))
                   `((integerp . ,(make-info-pair :fn-type :recognizer))
                     (rationalp . ,(make-info-pair :fn-type :recognizer))))
(find-resolved-var '(integerp x)
                   `((integerp . ,(make-info-pair :fn-type :recognizer))
                     (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

(defthm remove-from-symbol-list
  (implies (symbol-listp lst)
           (symbol-listp (remove-equal x lst))))

(defthm positive-len-of-symbol-list
  (implies (and (symbol-listp x) x)
           (> (len x) 0))
  :rule-classes :linear)

(define number-of-unresolved ((term-var-alst pseudo-term-symbol-list-alistp))
  :returns (m natp)
  :measure (len (pseudo-term-symbol-list-alist-fix term-var-alst))
  (b* ((term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       ((unless (consp term-var-alst)) 0)
       ((cons term-var rest-alst) term-var-alst)
       ((cons & vars) term-var))
    (+ (len vars) (number-of-unresolved rest-alst)))
  ///
  (defthm number-of-unresolved-of-cdr
    (implies (pseudo-term-symbol-list-alistp term-var-alst)
             (<= (number-of-unresolved (cdr term-var-alst))
                 (number-of-unresolved term-var-alst))))

  (defthm number-of-unresolved-of-cdr-when-car
    (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                  (consp term-var-alst)
                  (cdr (car term-var-alst)))
             (< (number-of-unresolved (cdr term-var-alst))
                (number-of-unresolved term-var-alst)))
    :hints (("Goal"
             :expand (number-of-unresolved term-var-alst))))

  (defthm number-of-unresolved-of-cons-<=
    (implies (and (pseudo-term-symbol-list-alistp alst1)
                  (pseudo-term-symbol-list-alistp alst2)
                  (pseudo-termp term)
                  (symbol-listp vars1)
                  (symbol-listp vars2)
                  (<= (number-of-unresolved alst1)
                      (number-of-unresolved alst2))
                  (<= (len vars1) (len vars2)))
             (<= (number-of-unresolved (cons (cons term vars1) alst1))
                 (number-of-unresolved (cons (cons term vars2) alst2))))
    :hints (("Goal"
             :in-theory (enable number-of-unresolved))))

  (defthm number-of-unresolved-of-cons-<
    (implies (and (pseudo-term-symbol-list-alistp alst1)
                  (pseudo-term-symbol-list-alistp alst2)
                  (pseudo-termp term)
                  (symbol-listp vars1)
                  (symbol-listp vars2)
                  (< (number-of-unresolved alst1)
                     (number-of-unresolved alst2))
                  (<= (len vars1) (len vars2)))
             (< (number-of-unresolved (cons (cons term vars1) alst1))
                (number-of-unresolved (cons (cons term vars2) alst2))))
    :hints (("Goal"
             :in-theory (enable number-of-unresolved))))

  (defthm number-of-unresolved-of-cons-nil-<=
    (implies (and (pseudo-term-symbol-list-alistp lst1)
                  (pseudo-term-symbol-list-alistp lst2)
                  (pseudo-termp term)
                  (symbol-listp vars2)
                  (not vars2)
                  (<= (number-of-unresolved lst1)
                      (number-of-unresolved lst2)))
             (<= (number-of-unresolved (cons (list term) lst1))
                 (number-of-unresolved (cons (cons term vars2) lst2)))))

  (defthm number-of-unresolved-of-cons-nil-<
    (implies (and (pseudo-term-symbol-list-alistp lst1)
                  (pseudo-term-symbol-list-alistp lst2)
                  (pseudo-termp term)
                  (symbol-listp vars2)
                  (not vars2)
                  (< (number-of-unresolved lst1)
                     (number-of-unresolved lst2)))
             (< (number-of-unresolved (cons (list term) lst1))
                (number-of-unresolved (cons (cons term vars2) lst2)))))

  (defthm number-of-unresolved-of-cons-non-nil-<
    (implies (and (pseudo-term-symbol-list-alistp lst1)
                  (pseudo-term-symbol-list-alistp lst2)
                  (pseudo-termp term)
                  (symbol-listp vars2)
                  (consp vars2)
                  (<= (number-of-unresolved lst1)
                      (number-of-unresolved lst2)))
             (< (number-of-unresolved (cons (list term) lst1))
                (number-of-unresolved (cons (cons term vars2) lst2))))))

(defthm len-<=-of-remove
  (<= (len (remove-equal x lst)) (len lst))
  :rule-classes :linear)

(defthm consp-of-remove
  (implies (remove-equal x lst) (consp lst)))

(define update ((term-var-alst pseudo-term-symbol-list-alistp)
                (resolved-var symbolp)
                (work-lst pseudo-term-listp))
  :returns (mv (new-term-var-alst pseudo-term-symbol-list-alistp)
               (new-work pseudo-term-listp))
  :measure (len (pseudo-term-symbol-list-alist-fix term-var-alst))
  (b* ((term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       (resolved-var (symbol-fix resolved-var))
       (work-lst (pseudo-term-list-fix work-lst))
       ((unless (consp term-var-alst)) (mv nil work-lst))
       ((cons term-vars rest-alst) term-var-alst)
       ((cons term vars) term-vars)
       ((mv rest-term-var-alst rest-work)
        (update rest-alst resolved-var work-lst))
       ((if (null vars))
        (mv (acons term nil rest-term-var-alst)
            rest-work))
       (new-vars (remove-equal resolved-var vars))
       ((unless new-vars)
        (mv (acons term new-vars rest-term-var-alst)
            (cons term rest-work))))
    (mv (acons term new-vars rest-term-var-alst)
        rest-work))
  ///
  (defthm measure-of-update-nil
    (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst)
                  (not (consp term-var-alst)))
             (b* (((mv new-term-var-alst new-work)
                   (update nil resolved-var work-lst)))
               (and (equal (number-of-unresolved new-term-var-alst) 0)
                    (equal (len new-work) (len work-lst))))))

  (defthm measure-of-update-work-lst-increase
    (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst))
             (b* (((mv & new-work)
                   (update term-var-alst resolved-var work-lst)))
               (>= (len new-work) (len work-lst))))
    :rule-classes :linear)

  (defthm measure-of-update-term-var-alst-decrease
    (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst))
             (b* (((mv new-term-var-alst &)
                   (update term-var-alst resolved-var work-lst)))
               (<= (number-of-unresolved new-term-var-alst)
                   (number-of-unresolved term-var-alst))))
    :rule-classes :linear)

  (defthm measure-of-update-term-var-alst-decrease-when-work-lst-increase
    (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst))
             (b* (((mv new-term-var-alst new-work)
                   (update term-var-alst resolved-var work-lst)))
               (implies (> (len new-work) (len work-lst))
                        (< (number-of-unresolved new-term-var-alst)
                           (number-of-unresolved term-var-alst)))))
    :rule-classes :linear)
  )

(defthm correctness-of-update-1
  (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                (pseudo-term-listp work-lst)
                (alistp a))
           (b* (((mv new-term-var-alst &)
                 (update term-var-alst resolved-var work-lst)))
             (implies
              (and (ev-smtcp (conjoin (strip-cars term-var-alst)) a)
                   (ev-smtcp (conjoin work-lst) a))
              (ev-smtcp (conjoin (strip-cars new-term-var-alst)) a))))
  :hints (("Goal"
           :in-theory (enable update)
           :induct (update term-var-alst resolved-var work-lst))))

(defthm correctness-of-update-2
  (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                (pseudo-term-listp work-lst)
                (alistp a))
           (b* (((mv & new-work)
                 (update term-var-alst resolved-var work-lst)))
             (implies
              (and (ev-smtcp (conjoin (strip-cars term-var-alst)) a)
                   (ev-smtcp (conjoin work-lst) a))
              (ev-smtcp (conjoin new-work) a))))
  :hints (("Goal"
           :in-theory (enable update)
           :induct (update term-var-alst resolved-var work-lst))))

#|
(update
 '(((equal x0 (ifix x)) x)
   ((equal x1 (rfix y)) y)
   ((equal x2 (binary-+ x0 x1)) x1 x0))
 'x
 '((rationalp y)))
|#

(define measure-of-order-hypo-lst ((term-var-alst pseudo-term-symbol-list-alistp)
                                   (work-lst pseudo-term-listp))
  :returns (m nat-listp)
  (b* ((work-lst (pseudo-term-list-fix work-lst))
       (term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst)))
    (list (number-of-unresolved term-var-alst) (len work-lst))))

(define order-hypo-lst ((work-lst pseudo-term-listp)
                        (var-term-alst symbol-pseudo-term-list-alistp)
                        (term-var-alst pseudo-term-symbol-list-alistp)
                        (fixinfo smt-fixtype-info-p))
  :returns (sorted pseudo-term-listp)
  :measure (measure-of-order-hypo-lst term-var-alst work-lst)
  :hints (("Goal"
           :in-theory (e/d (measure-of-order-hypo-lst) ())))
  :well-founded-relation l<
  (b* ((work-lst (pseudo-term-list-fix work-lst))
       (var-term-alst (symbol-pseudo-term-list-alist-fix var-term-alst))
       (term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       ((unless (consp work-lst)) nil)
       ((cons work-hd work-tl) work-lst)
       (resolved-var (find-resolved-var work-hd fixinfo))
       ((mv new-term-var-alst new-work-lst)
        (update term-var-alst resolved-var work-tl)))
    (cons work-hd
          (order-hypo-lst new-work-lst var-term-alst
                          new-term-var-alst fixinfo))))

(defthm correctness-of-order-hypo-lst
  (implies (and (pseudo-term-listp work-lst)
                (symbol-pseudo-term-list-alistp var-term-alst)
                (pseudo-term-symbol-list-alistp term-var-alst)
                (smt-fixtype-info-p fixinfo)
                (alistp a))
           (implies (and (ev-smtcp (conjoin work-lst) a)
                         (ev-smtcp (conjoin (strip-cars term-var-alst)) a))
                    (ev-smtcp (conjoin
                               (order-hypo-lst work-lst var-term-alst
                                               term-var-alst fixinfo))
                              a)))
  :hints (("Goal"
           :in-theory (e/d (order-hypo-lst) (pseudo-termp))
           :induct (order-hypo-lst work-lst var-term-alst
                                   term-var-alst fixinfo))))

#|
(order-hypo-lst '((integerp x) (rationalp y))
                '((x (equal x0 (ifix x)))
                  (y (equal x1 (rfix y)))
                  (x0 (equal x2 (binary-+ x0 x1)))
                  (x1 (equal x2 (binary-+ x0 x1))))
                '(((equal x0 (ifix x)) x)
                  ((equal x1 (rfix y)) y)
                  ((equal x2 (binary-+ x0 x1)) x1 x0))
                `((integerp . ,(make-info-pair :fn-type :recognizer))
                  (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

(defthm pseudo-term-list-of-strip-cars-of-pseudo-term-symbol-list-alist
  (implies (pseudo-term-symbol-list-alistp x)
           (pseudo-term-listp (strip-cars x))))

(define reorder-hypotheses ((term pseudo-termp)
                            (hint smtlink-hint-p))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (hint (smtlink-hint-fix hint))
       ((smtlink-hint h) hint)
       ((mv hypo-lst new-term) (extractor term h.types-info))
       ((mv root-hypo rest-hypo) (filter-type-hypo hypo-lst h.types-info))
       (var-term-alst (make-var-to-terms rest-hypo nil))
       (term-var-alst (make-term-to-vars rest-hypo nil))
       (ordered-hypo
        (order-hypo-lst root-hypo var-term-alst term-var-alst h.types-info)))
    `(if ,(conjoin ordered-hypo) ,new-term 't)))

#|
(reorder-hypotheses '(if (if (if (integerp x)
                                 (rationalp y)
                               'nil)
                             (if (equal x2 (binary-+ x0 x1))
                                 (if (equal x0 (ifix x))
                                     (equal x1 (rfix y))
                                   'nil)
                               'nil)
                           'nil)
                         (< x2 '0)
                       't)
                    (change-smtlink-hint
                     (make-smtlink-hint)
                     :types-info
                     `((integerp . ,(make-info-pair :fn-type :recognizer))
                       (rationalp . ,(make-info-pair :fn-type :recognizer)))))
|#

(defthm correctness-of-reorder-hypotheses
  (implies (and (pseudo-termp term)
                (smtlink-hint-p hint)
                (alistp a)
                (ev-smtcp (reorder-hypotheses term hint) a))
           (ev-smtcp term a))
  :hints (("Goal"
           :in-theory (e/d (reorder-hypotheses)
                           (correctness-of-extractor))
           :use ((:instance correctness-of-extractor
                            (fixinfo (smtlink-hint->types-info hint)))))))
