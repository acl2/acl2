; An evaluator that knows about equal, eql, eq, etc.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")

;; An evaluator that knows about various equality tests (as well as IF and NOT).
(defevaluator+ equality-eval if equal eql eq not)

(defund all-eval-to-true-with-equality-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (equality-eval (first terms) a)
         (all-eval-to-true-with-equality-eval (rest terms) a))))

(defthm all-eval-to-true-with-equality-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-true-with-equality-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-equality-eval))))

(defthm all-eval-to-true-with-equality-eval-of-cons
  (equal (all-eval-to-true-with-equality-eval (cons term terms) a)
         (and (equality-eval term a)
              (all-eval-to-true-with-equality-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-equality-eval))))

(defthm equality-eval-when-all-eval-to-true-with-equality-eval-and-member-equal
  (implies (and (all-eval-to-true-with-equality-eval terms a)
                (member-equal term terms))
           (equality-eval term a))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-equality-eval))))

(defund all-eval-to-false-with-equality-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (not (equality-eval (first terms) a))
         (all-eval-to-false-with-equality-eval (rest terms) a))))

(defthm all-eval-to-false-with-equality-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-false-with-equality-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-equality-eval))))

(defthm all-eval-to-false-with-equality-eval-of-cons
  (equal (all-eval-to-false-with-equality-eval (cons term terms) a)
         (and (not (equality-eval term a))
              (all-eval-to-false-with-equality-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-equality-eval))))

(defthm not-equality-eval-when-all-eval-to-false-with-equality-eval-and-member-equal
  (implies (and (all-eval-to-false-with-equality-eval terms a)
                (member-equal term terms))
           (not (equality-eval term a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-equality-eval))))
