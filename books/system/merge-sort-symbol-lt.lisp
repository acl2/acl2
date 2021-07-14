; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(verify-termination merge-symbol<
  #+acl2-devel ; otherwise fails to be redundant with :? measure
  (declare (xargs :measure (+ (len l1) (len l2)))))

(defthm acl2-count-evens
  (implies (consp (cdr x))
           (< (acl2-count (evens x))
              (acl2-count x)))
  :rule-classes :linear)

(verify-termination merge-sort-symbol<
  (declare (xargs :verify-guards nil)))

(defthm symbol-listp-evens
  (implies (symbol-listp x)
           (symbol-listp (evens x)))
  :hints (("Goal" :induct (evens x))))

(defthm symbol-listp-merge-symbol<
  (implies (and (symbol-listp l1)
                (symbol-listp l2)
                (symbol-listp acc))
           (symbol-listp (merge-symbol< l1 l2 acc))))

(defthm symbol-listp-merge-sort-symbol<
  (implies (symbol-listp x)
           (symbol-listp (merge-sort-symbol< x))))

(verify-guards merge-sort-symbol<)
