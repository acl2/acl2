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

; The function steps-to-nil is no longer used in this book, because
; merge-term-order and merge-sort-term-order now have endp tests that allow the
; use of acl2-count for termination.  But we might as well leave this
; definition; it's kind of nice.
(defun steps-to-nil (x)
  (declare (xargs :measure (if x (+ 1 (len x)) 0)))
  (if (null x)
      0 (+ 1 (steps-to-nil (cdr x)))))

(verify-termination merge-term-order
  (declare (xargs
            :guard (and (pseudo-term-listp l1)
                        (pseudo-term-listp l2))))
  #+acl2-devel ; else not redundant with :? measure
  (declare (xargs
            :measure (+ (acl2-count l1)
                        (acl2-count l2)))))

(defthm acl2-count-evens
  (implies (consp (cdr x))
           (< (acl2-count (evens x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-cdr-weak
  (<= (acl2-count (cdr x))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-cdr
  (implies (consp x)
           (< (acl2-count (cdr x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-odds
  (implies (cdr x)
           (< (acl2-count (odds x))
              (acl2-count x)))
  :hints (("goal" :in-theory (disable acl2-count-evens)
           :use ((:instance acl2-count-evens (x (cdr x))))))
  :rule-classes :linear)

(verify-termination merge-sort-term-order
  (declare (xargs :guard (pseudo-term-listp l)
                  :verify-guards nil))
  #+acl2-devel ; else not redundant with :? measure
  (declare (xargs :measure (acl2-count l))))

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
