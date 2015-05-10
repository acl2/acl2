; Copyright (C) 2015, ForrestHunt, Inc.
; Written by J Moore, May, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(verify-termination term-order1
                    (declare
                     (xargs :guard
                            (and (pseudo-termp term1)
                                 (pseudo-termp term2)
                                 (alistp invisible-fns-table)
                                 (symbol-list-listp invisible-fns-table)))))

(verify-termination term-order
                    (declare (xargs :guard (and (pseudo-termp term1)
                                                (pseudo-termp term2)))))

(defun steps-to-nil (x)
  (declare (xargs :measure (if x (+ 1 (len x)) 0)))
  (if (null x)
      0 (+ 1 (steps-to-nil (cdr x)))))

(verify-termination merge-term-order
                    (declare (xargs :measure (+ (steps-to-nil l1)
                                                (steps-to-nil l2))
                                    :guard (and (pseudo-term-listp l1)
                                                (pseudo-term-listp l2)))))

(defthm steps-to-nil-evens
  (implies (cdr x)
           (< (steps-to-nil (evens x))
              (steps-to-nil x)))
  :rule-classes :linear)

(defthm steps-to-nil-cdr-weak
  (<= (steps-to-nil (cdr x))
      (steps-to-nil x))
  :rule-classes :linear)

(defthm steps-to-nil-cdr
  (implies x
           (< (steps-to-nil (cdr x))
              (steps-to-nil x)))
  :rule-classes :linear)

(defthm steps-to-nil-odds
  (implies (cdr x)
           (< (steps-to-nil (odds x))
              (steps-to-nil x)))
  :hints (("goal" :in-theory (disable steps-to-nil-evens)
           :use ((:instance steps-to-nil-evens (x (cdr x))))))
  :rule-classes :linear)

(verify-termination merge-sort-term-order
                    (declare (xargs :measure (steps-to-nil l)
                                    :guard (pseudo-term-listp l)
                                    :verify-guards nil)))

(defthm pseudo-term-listp-merge-term-order
  (implies (and (pseudo-term-listp l1)
                (pseudo-term-listp l2))
           (pseudo-term-listp (merge-term-order l1 l2))))

(defthm pseudo-term-listp-evens
  (implies (pseudo-term-listp l)
           (pseudo-term-listp (evens l))))

(defthm pseudo-term-listp-merge-sort-term-order
  (implies (pseudo-term-listp l)
           (pseudo-term-listp (merge-sort-term-order l))))

(verify-guards merge-sort-term-order)
