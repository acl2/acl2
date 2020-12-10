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

(include-book "all-consp")
(include-book "axe-trees")
(include-book "all-dargp-less-than")
(include-book "dags") ;drop
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable quotep)))

;; Check whether ALIST is an alist that binds exactly the symbols in
;; EXPECTED-SYMBOLS, in that order, to either quoted constants or nodenums less
;; than DAG-LEN.
(defund axe-bind-free-result-okayp (alist expected-symbols dag-len)
  (declare (xargs :guard (and (natp dag-len)
                              (symbol-listp expected-symbols))))
  (if (atom alist)
      (and (null alist)
           (null expected-symbols))
    (let ((entry (first alist)))
      (and (consp entry)
           (consp expected-symbols)
           (eq (car entry) (first expected-symbols))
           (let ((val (cdr entry)))
             (and (or (myquotep val)
                      (and (natp val)
                           (< val dag-len)))
                  (axe-bind-free-result-okayp (rest alist) (rest expected-symbols) dag-len)))))))

(defthmd axe-bind-free-result-okayp-rewrite
  (equal (axe-bind-free-result-okayp alist expected-symbols dag-len)
         (and (alistp alist)
              (equal expected-symbols (strip-cars alist))
              (all-dargp-less-than (strip-cdrs alist) dag-len)))
  :hints (("Goal" :in-theory (e/d (strip-cdrs default-cdr default-car axe-bind-free-result-okayp dargp-less-than)
                                  (myquotep natp)))))

(defthm axe-bind-free-result-okayp-forward-to-alistp
  (implies (axe-bind-free-result-okayp alist expected-symbols dag-len)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-result-okayp))))

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

(defthm all-axe-treep-of-cons-if-not-equal-car
  (equal (all-axe-treep (cons-if-not-equal-car item lst))
         (and (axe-treep item)
              (all-axe-treep lst)))
  :hints (("Goal" :in-theory (enable CONS-IF-NOT-EQUAL-CAR))))

(defthm all-consp-of-cons-if-not-equal-car
  (equal (all-consp (cons-if-not-equal-car a x))
         (and (consp a)
              (all-consp x)))
  :hints (("Goal" :in-theory (enable cons-if-not-equal-car))))
