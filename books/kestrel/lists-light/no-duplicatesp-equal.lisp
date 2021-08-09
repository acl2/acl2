; A lightweight book about the built-in function no-duplicatesp-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "member-equal"))
(local (include-book "intersection-equal"))

(in-theory (disable no-duplicatesp-equal))

(defthm no-duplicatesp-equal-when-not-consp-cheap
  (implies (not (consp x))
           (no-duplicatesp-equal x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-cdr
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (cdr x)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-member-equal
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (member-equal a x)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal member-equal))))

(defthm no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr
  (implies (and (no-duplicatesp-equal (cdr x))
                (not (member-equal (car x) (cdr x))))
           (no-duplicatesp-equal x))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal member-equal)
           :induct (no-duplicatesp-equal x))))

(defthm not-member-equal-of-cdr-of-member-equal
  (implies (no-duplicatesp-equal x)
           (not (member-equal a (cdr (member-equal a x)))))
  :hints (("Goal" :in-theory (enable no-duplicatesp member-equal))))

;; The double-rewrite is to match STD.
(defthm no-duplicatesp-equal-of-cons
  (equal (no-duplicatesp-equal (cons a x))
         (and (not (member-equal a (double-rewrite x)))
              (no-duplicatesp-equal x)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

;; Avoids splitting into cases
(defthm no-duplicatesp-equal-of-cons-no-split
  (implies (not (member-equal a x))
           (equal (no-duplicatesp-equal (cons a x))
                  (no-duplicatesp-equal x))))

(defthm no-duplicatesp-equal-of-append
  (equal (no-duplicatesp-equal (append x y))
         (and (no-duplicatesp-equal x)
              (no-duplicatesp-equal y)
              (not (intersection-equal x y))))
  :hints (("Goal" :in-theory (enable append no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-union-equal
  (implies (and (no-duplicatesp-equal x)
                (no-duplicatesp-equal y))
           (no-duplicatesp-equal (union-equal x y)))
  :hints (("Goal" :in-theory (enable union-equal no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-set-difference-equal
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-true-list-fix
  (equal (no-duplicatesp-equal (true-list-fix x))
         (no-duplicatesp-equal x))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

(local
 (defthm not-no-duplicatesp-equal-of-revappend-helper
   (implies (not (no-duplicatesp-equal y))
            (not (no-duplicatesp-equal (revappend x y))))
   :hints (("Goal" :in-theory (enable no-duplicatesp-equal revappend)))))

(local
 (defthm not-no-duplicatesp-equal-of-revappend-helper2
   (implies (and (member-equal a x)
                 (member-equal a y))
            (not (no-duplicatesp-equal (revappend x y))))
   :hints (("Goal" :in-theory (enable no-duplicatesp-equal revappend)))))

(defthm no-duplicatesp-equal-of-revappend
  (equal (no-duplicatesp-equal (revappend x y))
         (and (no-duplicatesp-equal x)
              (no-duplicatesp-equal y)
              (not (intersection-equal x y))))
  :hints (("Goal" :in-theory (e/d (no-duplicatesp-equal revappend)
                                  (intersection-equal)))))

(defthm no-duplicatesp-equal-of-reverse
  (equal (no-duplicatesp-equal (reverse x))
         (no-duplicatesp-equal x))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))
