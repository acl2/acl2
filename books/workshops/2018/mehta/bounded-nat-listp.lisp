; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun bounded-nat-listp (l b)
  (declare (xargs :guard (natp b)))
  (if (atom l)
      (equal l nil)
      (and (natp (car l))
           (< (car l) b)
           (bounded-nat-listp (cdr l) b))))

(defthm bounded-nat-listp-correctness-1
  (implies (bounded-nat-listp l b)
           (nat-listp l))
  :rule-classes (:rewrite :forward-chaining))

(defthm bounded-nat-listp-correctness-2
  (implies (true-listp x)
           (equal (bounded-nat-listp (binary-append x y)
                                     b)
                  (and (bounded-nat-listp x b)
                       (bounded-nat-listp y b)))))

(defthm bounded-nat-listp-correctness-3
  (implies (and (bounded-nat-listp l (+ b 1))
                (natp b)
                (not (bounded-nat-listp l b)))
           (member-equal b l))
  :rule-classes :forward-chaining)

(defthm bounded-nat-listp-correctness-4
  (implies (bounded-nat-listp l b)
           (not (member-equal b l)))
  :rule-classes :forward-chaining)

(defthmd bounded-nat-listp-correctness-5
  (implies (and (<= x y) (bounded-nat-listp l x))
           (bounded-nat-listp l y)))

(defthm bounded-nat-listp-correctness-6
  (implies (and (bounded-nat-listp ac b) (natp val) (< val b))
           (bounded-nat-listp (make-list-ac n val ac) b)))

(defund lower-bounded-integer-listp (l b)
  (declare (xargs :guard (integerp b)))
  (if (atom l)
      (equal l nil)
      (and (integerp (car l))
           (>= (car l) b)
           (lower-bounded-integer-listp (cdr l)
                                        b))))

(defthm lower-bounded-integer-listp-correctness-2
  (implies (true-listp x)
           (equal (lower-bounded-integer-listp (binary-append x y)
                                     b)
                  (and (lower-bounded-integer-listp x b)
                       (lower-bounded-integer-listp y b))))
  :hints (("Goal" :in-theory (enable lower-bounded-integer-listp))))

(defthmd lower-bounded-integer-listp-correctness-5
  (implies (and (<= y x) (lower-bounded-integer-listp l x))
           (lower-bounded-integer-listp l y))
  :hints (("Goal" :in-theory (enable lower-bounded-integer-listp))))
