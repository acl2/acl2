; A lightweight book about the built-in function union-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
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
