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

(include-book "extractor")

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

#|
(filter-type-hypo '((equal x2 (binary-+ x0 x1))
                    (equal x1 (rfix y))
                    (equal x0 (ifix x))
                    (integerp x)
                    (rationalp y))
                  `((integerp . ,(make-info-pair :fn-type :recognizer))
                    (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

(defalist pseudo-term-symbol-list-alist
  :key-type pseudo-termp
  :val-type symbol-listp
  :true-listp t
  :pred pseudo-term-symbol-list-alistp)

(defthm symbol-list-of-simple-term-vars
  (symbol-listp (acl2::simple-term-vars term)))

(acl2::make-flag flag-merge-sort-lexorder
                 acl2::merge-sort-lexorder
                 :flag-mapping ((pseudo-termp     . term)
                                (pseudo-term-listp . lst))
                 :defthm-macro-name defthm-flag-pseudo-termp
                 :flag-var flag)

(defthm symbol-list-of-merge-lexorder
  (implies (and (symbol-listp l1)
                (symbol-listp l2)
                (symbol-listp acc))
           (symbol-listp (acl2::merge-lexorder l1 l2 acc))))

(defthm symbol-list-of-evens
  (implies (symbol-listp l) (symbol-listp (evens l)))
  :hints (("Goal" :induct (evens l))))

(defthm symbol-list-of-merge-sort-lexorder
  (implies (symbol-listp x)
           (symbol-listp (acl2::merge-sort-lexorder x))))

(define make-nodes ((hypo-lst pseudo-term-listp)
                    (acc pseudo-term-symbol-list-alistp))
  :returns (branches pseudo-term-symbol-list-alistp)
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (acc (pseudo-term-symbol-list-alist-fix acc))
       ((unless (consp hypo-lst)) acc)
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((mv okp term) (case-match hypo-hd
                        (('equal & term) (mv t term))
                        (& (mv nil nil))))
       ((unless okp)
        (er hard? 'reorder-hypotheses=>make-nodes "bad equality: ~q0" hypo-hd))
       (free-vars (acl2::merge-sort-lexorder (acl2::simple-term-vars term)))
       (exist? (assoc-equal term acc))
       ((if exist?) (make-nodes hypo-tl acc)))
    (make-nodes hypo-tl (acons hypo-hd free-vars acc))))

#|
(make-nodes '((equal x2 (binary-+ x0 x1))
              (equal x1 (rfix y))
              (equal x0 (ifix x))
              (equal x3 (ifix x)))
            nil)
|#

(define update-roots ((node-alist pseudo-term-symbol-list-alistp)
                      (roots symbol-listp)
                      (sorted pseudo-term-listp))
  :returns (mv (new-roots symbol-listp)
               (new-sorted pseudo-term-listp))
  :measure (len (pseudo-term-symbol-list-alist-fix node-alist))
  (b* ((node-alist (pseudo-term-symbol-list-alist-fix node-alist))
       (roots (symbol-list-fix roots))
       (sorted (pseudo-term-list-fix sorted))
       ((unless (consp node-alist)) (mv roots sorted))
       ((cons node-hd node-tl) node-alist)
       ((cons equality var-lst) node-hd)
       ((if (or (member-equal equality sorted)
                (not (subsetp-equal var-lst roots))))
        (update-roots node-tl roots sorted))
       ((mv okp new-var)
        (case-match equality
          (('equal new-var &) (mv t new-var))
          (& (mv nil nil))))
       ((unless (and okp (symbolp new-var)))
        (prog2$ (er hard? 'reorder-hypotheses=>update-roots
                    "bad equality: ~q0" equality)
                (mv roots sorted))))
    (update-roots node-tl (cons new-var roots) (cons equality sorted)))
  ///
  (more-returns
   (new-sorted (implies (pseudo-term-listp sorted)
                        (>= (len new-sorted)
                            (len sorted)))
               :name update-roots-nondecrease-len-of-sorted)
   (new-sorted (implies (and (pseudo-term-listp sorted)
                             (not (equal new-sorted sorted)))
                        (> (len new-sorted)
                           (len sorted)))
               :name update-roots-increase-len-of-sorted)))

#|
(update-roots '(((equal x2 (binary-+ x0 x1)) x0 x1)
                ((equal x3 (ifix x)) x)
                ((equal x0 (ifix x)) x)
                ((equal x1 (rfix y)) y))
              '(x y)
              nil)

(update-roots '(((equal x2 (binary-+ x0 x1)) x0 x1)
                ((equal x3 (ifix x)) x)
                ((equal x0 (ifix x)) x)
                ((equal x1 (rfix y)) y))
              '(x1 x0 x3 x y)
              '((equal x1 (rfix y))
                (equal x0 (ifix x))
                (equal x3 (ifix x))))
|#

(define measure-of-order-equality-hypo
  ((node-alist pseudo-term-symbol-list-alistp)
   (sorted pseudo-term-listp))
  :returns (m natp)
  (if (< (len (pseudo-term-list-fix sorted))
         (len (pseudo-term-symbol-list-alist-fix node-alist)))
      (- (len (pseudo-term-symbol-list-alist-fix node-alist))
         (len (pseudo-term-list-fix sorted)))
    0))

(define order-equality-hypo ((node-alist pseudo-term-symbol-list-alistp)
                             (roots symbol-listp)
                             (sorted pseudo-term-listp))
  :returns (mv (new-roots symbol-listp)
               (new-sorted pseudo-term-listp))
  :measure (measure-of-order-equality-hypo node-alist sorted)
  :hints (("Goal"
           :in-theory (e/d (measure-of-order-equality-hypo)
                           (update-roots-increase-len-of-sorted))
           :use ((:instance update-roots-increase-len-of-sorted
                            (node-alist (pseudo-term-symbol-list-alist-fix node-alist))
                            (roots (symbol-list-fix roots))
                            (sorted (pseudo-term-list-fix sorted))))))
  (b* ((node-alist (pseudo-term-symbol-list-alist-fix node-alist))
       (roots (symbol-list-fix roots))
       (sorted (pseudo-term-list-fix sorted))
       ((if (>= (len sorted) (len node-alist))) (mv roots sorted))
       ((mv new-roots new-sorted) (update-roots node-alist roots sorted))
       ((if (equal new-sorted sorted)) (mv new-roots new-sorted)))
    (order-equality-hypo node-alist new-roots new-sorted)))

(define initialize-roots ((type-hypo pseudo-term-listp))
  :returns (roots symbol-listp)
  (b* ((type-hypo (pseudo-term-list-fix type-hypo))
       ((unless (consp type-hypo)) nil)
       ((cons hypo-hd hypo-tl) type-hypo)
       ((mv okp var) (case-match hypo-hd
                       ((& var) (mv t var))
                       (& (mv nil nil))))
       ((unless (and okp (symbolp var)))
        (prog2$ (er hard? 'reorder-hypotheses=>initialize-roots
                    "bad type hypotheses: ~q0" hypo-hd)
                nil)))
    (cons var (initialize-roots hypo-tl))))

(defthm pseudo-term-list-of-rev
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (acl2::rev x)))
  :hints (("Goal"
           :in-theory (enable acl2::rev)
           :induct (acl2::rev x))))

(defthm pseudo-term-list-of-reverse
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (reverse x))))

(define order-hypo-lst ((hypo-lst pseudo-term-listp)
                        (fixinfo smt-fixtype-info-p))
  :returns (new-hypo-lst pseudo-term-listp
                         :hints (("Goal" :in-theory (disable reverse))))
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       ((mv root-hypo rest-hypo) (filter-type-hypo hypo-lst fixinfo))
       (node-alist (make-nodes rest-hypo nil))
       (roots (initialize-roots root-hypo))
       ((mv & ordered-rest)
        (order-equality-hypo node-alist roots nil))
       ((if (< (len ordered-rest) (len node-alist)))
        (prog2$ (er hard? 'reorder-hypotheses=>order-hypo-lst
                    "Can't order hypotheses: ~q0" rest-hypo)
                hypo-lst)))
    (append root-hypo (reverse ordered-rest))))

#|
(order-hypo-lst '((equal x2 (binary-+ x0 x1))
                  (equal x4 (unary-- x1))
                  (equal x3 (binary-* x0 x2))
                  (equal x1 (rfix y))
                  (equal x0 (ifix x))
                  (rationalp y)
                  (integerp x))
                `((integerp . ,(make-info-pair :fn-type :recognizer))
                  (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

stop

(defthm correctness-of-order-hypo-lst
  (implies (and (pseudo-term-listp hypo-lst)
                (smt-fixtype-info-p fixinfo)
                (alistp a))
           (equal (ev-smtcp-lst (order-hypo-lst hypo-lst fixinfo) a)
                  (ev-smtcp-lst hypo-lst a)))
  :hints (("Goal"
           :in-theory (enable order-hypo-lst))))

(defthm correctness-of-order-hypo-lst-corollary
  (implies (and (pseudo-term-listp hypo-lst)
                (alistp a))
           (equal (ev-smtcp (conjoin (order-hypo-lst hypo-lst)) a)
                  (ev-smtcp (conjoin hypo-lst) a)))
  :hints (("Goal"
           :in-theory (enable order-hypo-lst))))

(define reorder-hypotheses ((term pseudo-termp)
                            (hint smtlink-hint-p))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (hint (smtlink-hint-fix hint))
       ((smtlink-hint h) hint)
       ((mv hypo-lst new-term) (extractor term h.types-info))
       (ordered-hypo (order-hypo-lst hypo-lst h.types-info)))
    `(if ,(conjoin ordered-hypo) ,new-term 't)))

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
