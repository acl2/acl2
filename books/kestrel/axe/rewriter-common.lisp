; Functions common to the various rewriters
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "axe-trees")
(include-book "bounded-darg-listp")
(include-book "stored-rules")
(include-book "unify-term-and-dag-fast")
(include-book "alist-suitable-for-hypsp")
(include-book "dags") ;drop
(include-book "refined-assumption-alists")
(local (include-book "unify-term-and-dag-fast-correct"))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable quotep)))

;make tail recursive?
(defun make-equalities-from-dotted-pairs (pairs)
  (declare (xargs :guard (and (true-listp pairs)
                              (all-consp pairs))))
  (if (endp pairs)
      nil
    (let ((pair (first pairs)))
      (cons `(equal ,(car pair) ,(cdr pair))
            (make-equalities-from-dotted-pairs (cdr pairs))))))

;; this one takes a context
(defun lookup-eq-safe2 (key alist ctx)
  (declare (xargs :guard (if (symbolp key)
                             (alistp alist)
                           (symbol-alistp alist))
                  :guard-hints (("Goal" :in-theory (enable alistp assoc-eq)))))
  (let ((result (assoc-eq key alist)))
    (if result (cdr result)
      (er hard? 'lookup-eq-safe2
          "There is no binding for key ~x0 in the alist ~x1 (context: ~x2).~%"
          key alist ctx))))

;;;
;;; cons-if-not-equal-car
;;;

(defund cons-if-not-equal-car (item lst)
  (declare (xargs :guard t))
  (if (or (atom lst)
          (not (equal item (car lst))))
      (cons item lst)
    lst))

(defthm true-listp-of-cons-if-not-equal-car
  (equal (true-listp (cons-if-not-equal-car item lst))
         (true-listp lst))
  :hints (("Goal" :in-theory (enable cons-if-not-equal-car))))

(defthm axe-tree-listp-of-cons-if-not-equal-car
  (equal (axe-tree-listp (cons-if-not-equal-car item lst))
         (and (axe-treep item)
              (axe-tree-listp lst)))
  :hints (("Goal" :in-theory (enable CONS-IF-NOT-EQUAL-CAR))))

(defthm all-consp-of-cons-if-not-equal-car
  (equal (all-consp (cons-if-not-equal-car a x))
         (and (consp a)
              (all-consp x)))
  :hints (("Goal" :in-theory (enable cons-if-not-equal-car))))

(defthm alist-suitable-for-hypsp-of-unify-terms-and-dag-items-fast-when-stored-axe-rulep
  (implies (and (stored-axe-rulep stored-rule)
                (not (equal :fail (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule) args-to-match dag-array dag-len))))
           (alist-suitable-for-hypsp (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule) args-to-match dag-array dag-len)
                                     (stored-rule-hyps stored-rule)))
  :hints (("Goal" :in-theory (enable alist-suitable-for-hypsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm alist-suitable-for-hypsp-of-alist-suitable-for-hypsp-of-car
  (implies (and (alist-suitable-for-hyp-args-and-hypsp alist hyp-args other-hyps)
                (bounded-darg-listp (strip-cdrs alist) dag-len)
                (symbol-alistp alist)
                (axe-rule-hyp-listp other-hyps)
                (axe-tree-listp hyp-args)
                (bounded-darg-list-listp assumption-arg-lists dag-len)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (consp assumption-arg-lists)
                (not (equal :fail (unify-trees-with-dag-nodes hyp-args (car assumption-arg-lists) dag-array alist))))
           (alist-suitable-for-hypsp (unify-trees-with-dag-nodes hyp-args (car assumption-arg-lists) dag-array alist)
                                     other-hyps))
  :hints (("Goal" :in-theory (enable alist-suitable-for-hyp-args-and-hypsp
                                     alist-suitable-for-hypsp))))
