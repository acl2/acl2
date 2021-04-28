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
(include-book "reorder-option")

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defalist symbol-pseudo-term-list-alist
  :key-type symbolp
  :val-type pseudo-term-listp
  :true-listp t
  :pred symbol-pseudo-term-list-alistp)

(defalist pseudo-term-symbol-alist
  :key-type pseudo-termp
  :val-type symbolp
  :true-listp t
  :pred pseudo-term-symbol-alistp)

(defalist pseudo-term-symbol-list-alist
  :key-type pseudo-termp
  :val-type symbol-listp
  :true-listp t
  :pred pseudo-term-symbol-list-alistp)

(define filter-type-hypo ((hypo-lst pseudo-term-listp)
                          (type-info symbol-symbol-alistp))
  :returns (mv (root-hypo pseudo-term-listp)
               (rest-hypo pseudo-term-listp))
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (type-info (symbol-symbol-alist-fix type-info))
       ((unless (consp hypo-lst)) (mv nil nil))
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((mv tl-root tl-rest) (filter-type-hypo hypo-tl type-info))
       ((if (type-decl-p hypo-hd type-info))
        (mv (cons hypo-hd tl-root) tl-rest)))
    (mv tl-root (cons hypo-hd tl-rest))))

(defthm correctness-of-filter-type-hypo-1
  (implies (and (pseudo-term-listp hypo-lst)
                (symbol-symbol-alistp type-info))
           (b* (((mv & rest-hypo) (filter-type-hypo hypo-lst type-info)))
             (implies (ev-smtcp (conjoin hypo-lst) a)
                      (ev-smtcp (conjoin rest-hypo) a))))
  :hints (("Goal"
           :in-theory (enable filter-type-hypo))))

(defthm correctness-of-filter-type-hypo-2
  (implies (and (pseudo-term-listp hypo-lst)
                (symbol-symbol-alistp type-info))
           (b* (((mv root-hypo &) (filter-type-hypo hypo-lst type-info)))
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

(define make-term-to-vars ((hypo-lst pseudo-term-listp))
  :returns (new-alst pseudo-term-symbol-list-alistp)
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       ((unless (consp hypo-lst)) nil)
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((mv okp term) (case-match hypo-hd
                        (('equal & term) (mv t term))
                        (& (mv nil nil))))
       ((unless okp)
        (er hard? 'reorder-hypotheses=>make-term-to-vars
            "INTERNAL: bad equality: ~q0" hypo-hd))
       (free-vars (acl2::simple-term-vars term)))
    (acons hypo-hd free-vars (make-term-to-vars hypo-tl)))
  ///
  (defthm subsetp-equal-of-make-term-to-vars
    (implies (pseudo-term-listp hypo-lst)
             (subsetp-equal (strip-cars (make-term-to-vars hypo-lst))
                            hypo-lst))))

(defthm correctness-of-make-term-to-vars
  (implies (and (pseudo-term-listp hypo-lst)
                (alistp a))
           (implies (ev-smtcp (conjoin hypo-lst) a)
                    (ev-smtcp (conjoin
                               (strip-cars
                                (make-term-to-vars hypo-lst)))
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
                     (equal x0 (ifix x))))
|#

(define find-resolved-var ((term pseudo-termp)
                           (type-info symbol-symbol-alistp))
  :returns (var symbolp)
  :guard-hints (("Goal" :in-theory (enable pseudo-termp)))
  (b* ((term (pseudo-term-fix term))
       (type-info (symbol-symbol-alist-fix type-info))
       ((unless (hypo-p term type-info))
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

(defthm assoc-equal-of-pseudo-term-symbol-list-alist
  (implies (and (pseudo-term-symbol-list-alistp alst)
                (cdr (assoc-equal term alst)))
           (and (assoc-equal term alst)
                (consp (strip-cars alst)))))

(defthm symbol-list-of-remove-equal
  (implies (symbol-listp lst)
           (symbol-listp (remove-equal x lst))))

(defthm implies-of-assoc-equal-of-pseudo-term-symbol-list-alist
  (implies (and (pseudo-term-symbol-list-alistp alst)
                (assoc-equal x alst))
           (symbol-listp (cdr (assoc-equal x alst)))))

(defthm implies-of-assoc-equal-of-symbol-pseudo-term-list-alist
  (implies (and (symbol-pseudo-term-list-alistp alst)
                (assoc-equal x alst))
           (pseudo-term-listp (cdr (assoc-equal x alst)))))

(defthm remove-equal-decreases
  (implies (remove-equal x lst)
           (<= (len (remove-equal x lst)) (len lst)))
  :rule-classes :linear)

(defthm assoc-equal-and-subsetp-equal
  (implies (and (assoc-equal x alst)
                (subsetp-equal (strip-cars alst) lst))
           (member-equal x lst)))

;; The total-terms should contain all keys from term-var-alst.
;; If not, term-var-alst will fail to count the resolved terms
;; that are not in total-terms.
(define number-of-unresolved ((term-var-alst pseudo-term-symbol-list-alistp)
                              (total-terms pseudo-term-listp))
  :returns (m natp)
  :measure (len (pseudo-term-list-fix total-terms))
  (b* ((term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       (total-terms (pseudo-term-list-fix total-terms))
       ((unless (consp total-terms)) 0)
       ((cons term-hd term-tl) total-terms)
       (exists? (assoc-equal term-hd term-var-alst))
       ((unless exists?) (number-of-unresolved term-var-alst term-tl))
       (vars (cdr exists?))
       ((unless vars) (number-of-unresolved term-var-alst term-tl)))
    (1+ (number-of-unresolved term-var-alst term-tl)))
  ///
  (defthm lemma-1
    (implies (and (pseudo-termp x)
                  (pseudo-term-listp klst)
                  (pseudo-term-symbol-list-alistp alst)
                  (not (member-equal x klst)))
             (equal (number-of-unresolved (cons (list x) alst) klst)
                    (number-of-unresolved alst klst)))
    :hints (("Goal"
             :in-theory (enable number-of-unresolved))))

  (defthm lemma-2
    (implies (and (pseudo-termp key)
                  (pseudo-term-listp klst)
                  (pseudo-term-symbol-list-alistp alst)
                  (member-equal key klst)
                  (cdr (assoc-equal key alst)))
             (< (number-of-unresolved (cons (list key) alst) klst)
                (number-of-unresolved alst klst)))
    :hints (("Goal"
             :in-theory (enable number-of-unresolved))))

  (defthm lemma-3
    (implies (and (pseudo-termp key)
                  (pseudo-term-listp klst)
                  (pseudo-term-symbol-list-alistp alst)
                  (symbol-listp vars)
                  (member-equal key klst)
                  (cdr (assoc-equal key alst)))
             (<= (number-of-unresolved (cons (cons key vars) alst) klst)
                 (number-of-unresolved alst klst)))
    :hints (("Goal"
             :in-theory (e/d (number-of-unresolved) (symbol-listp)))))

  (defthm assoc-equal-of-subsetp-equal
    (implies (and (pseudo-termp term)
                  (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp total-terms)
                  (cdr (assoc-equal term term-var-alst))
                  (subsetp-equal (strip-cars term-var-alst) total-terms))
             (member-equal term total-terms)))

  (defthm number-of-unresolved-decreases-term-var-alst-1
    (implies (and (pseudo-termp term)
                  (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp total-terms)
                  (symbolp resolved-var)
                  (cdr (assoc-equal term term-var-alst))
                  (subsetp-equal (strip-cars term-var-alst) total-terms))
             (< (number-of-unresolved (cons (list term) term-var-alst) total-terms)
                (number-of-unresolved term-var-alst total-terms)))
    :hints (("Goal"
             :in-theory (enable number-of-unresolved)))
    :rule-classes :linear)

  (defthm number-of-unresolved-decreases-term-var-alst-2
    (implies (and (pseudo-termp term)
                  (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp total-terms)
                  (symbolp resolved-var)
                  (cdr (assoc-equal term term-var-alst))
                  (subsetp-equal (strip-cars term-var-alst) total-terms))
             (<=
              (number-of-unresolved
               (cons (cons term
                           (remove-equal resolved-var
                                         (cdr (assoc-equal term term-var-alst))))
                     term-var-alst)
               total-terms)
              (number-of-unresolved term-var-alst total-terms)))
    :rule-classes :linear)
  )


(define update ((term-lst pseudo-term-listp)
                (term-var-alst pseudo-term-symbol-list-alistp)
                (work-lst pseudo-term-listp)
                (resolved-var symbolp))
  :returns (mv (new-term-var-alst pseudo-term-symbol-list-alistp)
               (new-work pseudo-term-listp))
  :measure (len (pseudo-term-list-fix term-lst))
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       (work-lst (pseudo-term-list-fix work-lst))
       (resolved-var (symbol-fix resolved-var))
       ((unless (consp term-lst)) (mv term-var-alst work-lst))
       ((cons term-hd term-tl) term-lst)
       (exist? (assoc-equal term-hd term-var-alst))
       ((unless exist?) (update term-tl term-var-alst work-lst resolved-var))
       (vars (cdr exist?))
       ((unless vars) (update term-tl term-var-alst work-lst resolved-var))
       (new-vars (remove-equal resolved-var vars))
       ((unless new-vars)
        (update term-tl (acons term-hd nil term-var-alst)
                (cons term-hd work-lst) resolved-var)))
    (update term-tl (acons term-hd new-vars term-var-alst)
            work-lst resolved-var))
  ///
  (defthm subsetp-equal-of-term-var-alst-of-update
    (implies (and (pseudo-term-listp term-lst)
                  (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst)
                  (pseudo-term-listp total-terms)
                  (symbolp resolved-var)
                  (subsetp-equal (strip-cars term-var-alst) total-terms))
             (b* (((mv new-term-var-alst &)
                   (update term-lst term-var-alst work-lst resolved-var)))
               (subsetp-equal (strip-cars new-term-var-alst) total-terms))))

  (defthm update-term-var-alst-not-increase
    (implies (and (pseudo-term-listp term-lst)
                  (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst)
                  (pseudo-term-listp total-terms)
                  (symbolp resolved-var)
                  (subsetp-equal (strip-cars term-var-alst) total-terms))
             (b* (((mv new-term-var-alst &)
                   (update term-lst term-var-alst work-lst resolved-var)))
               (<= (number-of-unresolved new-term-var-alst total-terms)
                   (number-of-unresolved term-var-alst total-terms))))
    :rule-classes :linear)

  (defthm update-term-var-alst-decrease
    (implies (and (pseudo-term-listp term-lst)
                  (pseudo-term-symbol-list-alistp term-var-alst)
                  (pseudo-term-listp work-lst)
                  (pseudo-term-listp total-terms)
                  (symbolp resolved-var)
                  (subsetp-equal (strip-cars term-var-alst) total-terms))
             (b* (((mv new-term-var-alst new-work)
                   (update term-lst term-var-alst work-lst resolved-var)))
               (implies (> (len new-work) (len work-lst))
                        (< (number-of-unresolved new-term-var-alst total-terms)
                           (number-of-unresolved term-var-alst
                                                 total-terms)))))
    :rule-classes :linear))

(defthm lemma4
  (implies (and (pseudo-term-listp term-lst)
                (pseudo-term-symbol-list-alistp term-var-alst)
                (consp term-lst)
                (cdr (assoc-equal (car term-lst) term-var-alst))
                (alistp a)
                (ev-smtcp (conjoin (strip-cars term-var-alst)) a))
           (ev-smtcp (car term-lst) a)))

(defthm correctness-of-update-1
  (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                (pseudo-term-listp term-lst)
                (pseudo-term-listp work-lst)
                (alistp a))
           (b* (((mv new-term-var-alst &)
                 (update term-lst term-var-alst work-lst resolved-var)))
             (implies
              (and (ev-smtcp (conjoin (strip-cars term-var-alst)) a)
                   (ev-smtcp (conjoin work-lst) a))
              (ev-smtcp (conjoin (strip-cars new-term-var-alst)) a))))
  :hints (("Goal" :in-theory (enable update))))

(defthm correctness-of-update-2
  (implies (and (pseudo-term-symbol-list-alistp term-var-alst)
                (pseudo-term-listp term-lst)
                (pseudo-term-listp work-lst)
                (alistp a))
           (b* (((mv & new-work)
                 (update term-lst term-var-alst work-lst resolved-var)))
             (implies
              (and (ev-smtcp (conjoin (strip-cars term-var-alst)) a)
                   (ev-smtcp (conjoin work-lst) a))
              (ev-smtcp (conjoin new-work) a))))
  :hints (("Goal" :in-theory (enable update))))

#|
(update
 '((equal x0 (ifix x)))
 '(((equal x0 (ifix x)) x)
   ((equal x1 (rfix y)) y)
   ((equal x2 (binary-+ x0 x1)) x1 x0))
 '((rationalp y))
 'x)
|#

(define measure-of-order-hypo-lst ((term-var-alst
                                    pseudo-term-symbol-list-alistp)
                                   (total-terms pseudo-term-listp)
                                   (work-lst pseudo-term-listp))
  :returns (m nat-listp)
  (b* ((term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       (work-lst (pseudo-term-list-fix work-lst)))
    (list (number-of-unresolved term-var-alst total-terms)
          (len work-lst))))

(define order-hypo-lst ((work-lst pseudo-term-listp)
                        (var-term-alst symbol-pseudo-term-list-alistp)
                        (term-var-alst pseudo-term-symbol-list-alistp)
                        (total-terms pseudo-term-listp)
                        (type-info symbol-symbol-alistp))
  :guard (subsetp-equal (strip-cars term-var-alst) total-terms)
  :verify-guards nil
  :returns (sorted pseudo-term-listp)
  :measure (measure-of-order-hypo-lst (pseudo-term-symbol-list-alist-fix term-var-alst)
                                      (pseudo-term-list-fix total-terms)
                                      (pseudo-term-list-fix work-lst))
  :hints (("Goal" :in-theory (e/d (measure-of-order-hypo-lst) ())))
  :well-founded-relation l<
  (b* ((work-lst (pseudo-term-list-fix work-lst))
       (var-term-alst (symbol-pseudo-term-list-alist-fix var-term-alst))
       (term-var-alst (pseudo-term-symbol-list-alist-fix term-var-alst))
       (total-terms (pseudo-term-list-fix total-terms))
       ((unless (mbt (subsetp-equal (strip-cars term-var-alst) total-terms)))
        nil)
       (type-info (symbol-symbol-alist-fix type-info))
       ((unless (consp work-lst)) nil)
       ((cons work-hd work-tl) work-lst)
       (resolved-var (find-resolved-var work-hd type-info))
       (exist? (assoc-equal resolved-var var-term-alst))
       ((unless exist?)
        (cons work-hd
              (order-hypo-lst work-tl var-term-alst term-var-alst
                              total-terms type-info)))
       ((mv new-term-var-alst new-work-lst)
        (update (cdr exist?) term-var-alst work-tl resolved-var)))
    (cons work-hd
          (order-hypo-lst new-work-lst var-term-alst new-term-var-alst
                          total-terms type-info))))

(defthm assoc-equal-of-symbol-pseudo-term-list-alist
  (implies (and (symbol-pseudo-term-list-alistp alst)
                (assoc-equal x alst))
           (consp (assoc-equal x alst))))

(verify-guards order-hypo-lst)

(defthm correctness-of-order-hypo-lst
  (implies (and (pseudo-term-listp work-lst)
                (symbol-pseudo-term-list-alistp var-term-alst)
                (pseudo-term-symbol-list-alistp term-var-alst)
                (symbol-symbol-alistp type-info)
                (alistp a))
           (implies (and (ev-smtcp (conjoin work-lst) a)
                         (ev-smtcp (conjoin (strip-cars term-var-alst)) a))
                    (ev-smtcp (conjoin
                               (order-hypo-lst work-lst var-term-alst
                                               term-var-alst total-terms
                                               type-info))
                              a)))
  :hints (("Goal"
           :in-theory (e/d (order-hypo-lst) (pseudo-termp))
           :induct (order-hypo-lst work-lst var-term-alst
                                   term-var-alst total-terms type-info))))

#|
(order-hypo-lst '((integerp x) (rationalp y))
                '((x (equal x0 (ifix x)))
                  (y (equal x1 (rfix y)))
                  (x0 (equal x2 (binary-+ x0 x1)))
                  (x1 (equal x2 (binary-+ x0 x1))))
                '(((equal x0 (ifix x)) x)
                  ((equal x1 (rfix y)) y)
                  ((equal x2 (binary-+ x0 x1)) x1 x0))
                '((equal x0 (ifix x))
                  (equal x1 (rfix y))
                  (equal x2 (binary-+ x0 x1)))
                `((integerp . ,(make-info-pair :fn-type :recognizer))
                  (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

(defthm pseudo-term-list-of-strip-cars-of-pseudo-term-symbol-list-alist
  (implies (pseudo-term-symbol-list-alistp x)
           (pseudo-term-listp (strip-cars x))))

(define add-hypotheses ((ordered-hypo pseudo-term-listp)
                        (concl pseudo-termp))
  :returns (new-term pseudo-termp)
  (b* ((ordered-hypo (pseudo-term-list-fix ordered-hypo))
       (concl (pseudo-term-fix concl))
       ((unless (consp ordered-hypo)) concl)
       ((cons hypo-hd hypo-tl) ordered-hypo))
    `(if ,hypo-hd ,(add-hypotheses hypo-tl concl) 't)))

(defthm correctness-of-add-hypotheses
  (implies (and (pseudo-term-listp ordered-hypo)
                (pseudo-termp concl)
                (alistp a)
                (ev-smtcp (add-hypotheses ordered-hypo concl) a))
           (ev-smtcp `(if ,(conjoin ordered-hypo) ,concl 't) a))
  :hints (("Goal"
           :induct (add-hypotheses ordered-hypo concl)
           :in-theory (enable add-hypotheses))))

#|
(add-hypotheses '((integerp x)
(equal x0 (ifix x))
(rationalp y)
(equal x1 (rfix y))
(equal x2 (binary-+ x0 x1)))
'(< x2 '0))
|#

(define reorder-hypotheses ((term pseudo-termp)
                            (type-info symbol-symbol-alistp))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (type-info (symbol-symbol-alist-fix type-info))
       ((mv hypo-lst new-term) (extractor term type-info))
       ((mv root-hypo rest-hypo) (filter-type-hypo hypo-lst type-info))
       (var-term-alst (make-var-to-terms rest-hypo nil))
       (term-var-alst (make-term-to-vars rest-hypo))
       (ordered-hypo
        (order-hypo-lst root-hypo var-term-alst term-var-alst rest-hypo
                        type-info)))
    (add-hypotheses ordered-hypo new-term)))

#|
(reorder-hypotheses '(if (if (equal x2 (binary-+ x0 x1))
                             (if (equal x1 (rfix y))
                                 (if (equal x0 (ifix x)) 't 'nil)
                                 'nil)
                             'nil)
                         (if (if (integerp x) (rationalp y) 'nil)
                             (< x2 '0)
                             't)
                         't)
                    (change-smtlink-hint
                     (make-smtlink-hint)
                     :types-info
                     `((integerp . ,(make-info-pair :fn-type :recognizer))
                       (rationalp . ,(make-info-pair :fn-type :recognizer)))))
|#

(defthm correctness-of-reorder-hypotheses
  (implies (and (pseudo-termp term)
                (symbol-symbol-alistp type-info)
                (alistp a)
                (ev-smtcp (reorder-hypotheses term type-info) a))
           (ev-smtcp term a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (reorder-hypotheses)
                           (correctness-of-extractor
                            correctness-of-add-hypotheses))
           :use ((:instance correctness-of-extractor)
                 (:instance correctness-of-add-hypotheses
                            (ordered-hypo
                             (order-hypo-lst
                              (mv-nth 0
                                      (filter-type-hypo
                                       (mv-nth 0 (extractor term type-info))
                                       type-info))
                              (make-var-to-terms
                               (mv-nth 1
                                       (filter-type-hypo
                                        (mv-nth 0 (extractor term type-info))
                                        type-info))
                               nil)
                              (make-term-to-vars
                               (mv-nth 1
                                       (filter-type-hypo
                                        (mv-nth 0 (extractor term type-info))
                                        type-info)))
                              (mv-nth 1
                                      (filter-type-hypo
                                       (mv-nth 0 (extractor term type-info))
                                        type-info))
                              type-info))
                            (concl (mv-nth 1 (extractor term type-info))))))))

(define reorder-hypotheses-cp ((cl pseudo-term-listp)
                               (hints t))
  :returns (new-cl pseudo-term-list-listp
                   :hints (("Goal" :in-theory (enable pseudo-termp))))
  (b* ((cl (pseudo-term-list-fix cl))
       ((unless (smtlink-hint-p hints)) (list cl))
       (goal (disjoin cl))
       (next-cp (cdr (assoc-equal 'reorder *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint `(:clause-processor (,next-cp clause ',hints state)))
       (options (construct-reorder-option hints))
       (new-goal (reorder-hypotheses goal options)))
    (list `((hint-please ',the-hint) ,new-goal))))

(defthm correctness-of-reorder-hypotheses-cp
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (reorder-hypotheses-cp cl hint))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (reorder-hypotheses-cp)
                           (correctness-of-reorder-hypotheses))
           :use ((:instance correctness-of-reorder-hypotheses
                            (term (disjoin cl))
                            (type-info (construct-reorder-option hint))))))
  :rule-classes :clause-processor)
