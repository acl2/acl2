; A lightweight book about the built-in function intersection-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "remove1-equal"))

(in-theory (disable intersection-equal))

(defthm intersection-equal-of-cons
  (equal (intersection-equal (cons a x) y)
         (if (member-equal a y)
             (cons a (intersection-equal x y))
           (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-of-append
  (equal (intersection-equal (append x y) z)
         (append (intersection-equal x z)
                 (intersection-equal y z)))
  :hints (("Goal" :in-theory (enable intersection-equal append))))

(defthm member-equal-of-intersection-equal-iff
  (iff (member-equal a (intersection-equal x y))
       (and (member-equal a x)
            (member-equal a y)))
  :hints (("Goal" :in-theory (enable member-equal intersection-equal))))

(defthm intersection-equal-of-union-equal
  (equal (intersection-equal (union-equal x y) z)
         (union-equal (intersection-equal x z)
                      (intersection-equal y z)))
  :hints (("Goal" :in-theory (enable intersection-equal union-equal))))

(defthm intersection-equal-of-nil-arg1
  (equal (intersection-equal nil x)
         nil)
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-of-nil-arg2
  (equal (intersection-equal x nil)
         nil)
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (equal (intersection-equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-when-not-consp-arg2-cheap
  (implies (not (consp y))
           (equal (intersection-equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthmd intersection-equal-when-member-equal-of-car
  (implies (and (member-equal (car x) y)
                (consp x))
           (intersection-equal x y))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-when-member-equal-of-car-cheap
  (implies (and (member-equal (car x) y)
                (consp x))
           (intersection-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0 1)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-of-cons-arg2-iff
  (iff (intersection-equal x (cons a y))
       (or (member-equal a x)
           (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-when-intersection-equal-of-cdr-arg1-cheap
  (implies (intersection-equal (cdr x) y)
           (intersection-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthmd intersection-equal-when-subsetp-equal-iff
  (implies (subsetp-equal y x)
           (iff (intersection-equal x y)
                (consp y))))

(defthm intersection-equal-of-remove1-equal-arg1-irrel-arg1
  (implies (not (member-equal a y))
           (equal (intersection-equal (remove1-equal a x) y)
                  (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal remove-equal))))

(defthm intersection-equal-of-remove1-equal-arg1-irrel-arg2
  (implies (not (member-equal a x))
           (equal (intersection-equal x (remove1-equal a y))
                  (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal remove-equal))))

;enable?
(defthmd intersection-equal-commutative-iff
  (iff (intersection-equal x y)
       (intersection-equal y x))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-when-member-equal-and-member-equal
  (implies (and (member-equal a x)
                (member-equal a y))
           (intersection-equal x y))
  :hints (("Goal" :in-theory (enable intersection-equal))))
