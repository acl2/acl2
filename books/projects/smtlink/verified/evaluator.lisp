;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)

(include-book "hint-please")

;; -----------------------------------------------------------------
;;       Define evaluators

(acl2::defevaluator-fast ev-smtcp ev-smtcp-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z)
                          (binary-+ x y)
                          (integerp x)
                          (rationalp x)
                          (symbolp x)
                          (booleanp x))
                         :namedp t)

(acl2::def-ev-theoremp ev-smtcp)
(acl2::def-meta-extract ev-smtcp ev-smtcp-lst)
(acl2::def-unify ev-smtcp ev-smtcp-alist)

(defthm ev-smtcp-of-disjoin
  (iff (ev-smtcp (disjoin clause) a)
       (acl2::or-list (ev-smtcp-lst clause a)))
  :hints(("Goal" :in-theory (enable acl2::or-list len)
          :induct (len clause))))

(defthm ev-smtcp-alist-of-pairlis$
  (equal (ev-smtcp-alist (pairlis$ x y) a)
         (pairlis$ x (ev-smtcp-lst y a))))

(defthm ev-smtcp-of-implies1
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (consp (disjoin cl))
                (equal (car (disjoin cl)) 'implies)
                (consp (cdr (disjoin cl)))
                (consp (cddr (disjoin cl)))
                (not (cdddr (disjoin cl)))
                (ev-smtcp (caddr (disjoin cl)) a))
           (acl2::or-list (ev-smtcp-lst cl a)))
  :hints (("Goal" :in-theory (enable disjoin))))

(defthm ev-smtcp-of-implies2
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (consp (disjoin cl))
                (equal (car (disjoin cl)) 'implies)
                (consp (cdr (disjoin cl)))
                (consp (cddr (disjoin cl)))
                (not (cdddr (disjoin cl)))
                (not (ev-smtcp (cadr (disjoin cl)) a)))
           (acl2::or-list (ev-smtcp-lst cl a)))
  :hints (("Goal" :in-theory (enable disjoin))))

;; Function for removing hint-please from the clause.
(define remove-hint-please ((cl pseudo-term-listp))
  :returns (cl-removed pseudo-term-list-listp
                       :hints (("Goal"
                                :in-theory (enable pseudo-term-listp
                                                   pseudo-term-list-fix))))
  (b* ((cl (pseudo-term-list-fix cl))
       ((unless (consp cl)) (list cl)))
    (case-match cl
      ((('hint-please &) . term) (list term))
      (& (list cl)))))

(local (in-theory (enable remove-hint-please)))

(defthm correctness-of-remove-hint-please
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-smtcp
                 (conjoin-clauses (remove-hint-please cl))
                 b))
           (ev-smtcp (disjoin cl) b))
  :hints (("Goal"
           :in-theory (enable hint-please remove-hint-please)))
  :rule-classes :clause-processor)
