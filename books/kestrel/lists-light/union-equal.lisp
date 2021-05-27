; A lightweight book about the built-in function union-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable union-equal))

(defthm union-equal-of-nil-arg1
  (equal (union-equal nil x)
         x)
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm union-equal-of-nil-arg2
  (equal (union-equal x nil)
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm true-listp-of-union-equal
  (equal (true-listp (union-equal x y))
         (true-listp y))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm true-listp-of-union-equal-type
  (implies (true-listp y)
           (true-listp (union-equal x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm union-equal-iff
  (iff (union-equal x y)
       (or (consp x) y))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm union-equal-of-cons
  (equal (union-equal (cons a x) y)
         (if (member-equal a y)
             (union-equal x y)
           (cons a (union-equal x y))))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm member-equal-of-union-equal
  (iff (member-equal a (union-equal x y))
       (or (member-equal a x)
           (member-equal a y)))
  :hints (("Goal" :in-theory (enable union-equal add-to-set-equal))))

(defthm union-equal-associative
  (equal (union-equal (union-equal x y) z)
         (union-equal x (union-equal y z)))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm union-equal-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (equal (union-equal x y)
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm union-equal-when-not-consp-arg2-cheap
  (implies (not (consp y))
           (equal (union-equal x y)
                  ;; note that this can be simplified further:
                  (append x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable union-equal))))
