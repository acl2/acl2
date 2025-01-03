; Rules about list operations that treat lists like sets
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "intersection-equal"))
(local (include-book "set-difference-equal"))
(local (include-book "subsetp-equal"))
(local (include-book "member-equal"))

(defthm not-intersection-equal-of-set-difference-equal-arg1
  (not (intersection-equal (set-difference-equal x y) y))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm not-intersection-equal-of-set-difference-equal-arg2
  (not (intersection-equal y (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal-commutative-iff
                                     set-difference-equal))))

;; see intersection-equal-of-union-equal
;; (defthm intersection-equal-of-union-equal-arg1-iff
;;   (iff (intersection-equal (union-equal y z) x)
;;        (or (intersection-equal y x)
;;            (intersection-equal z x)))
;;   :hints (("Goal" :in-theory (enable union-equal))))

(defthm intersection-equal-of-union-equal-arg2-iff
  (iff (intersection-equal x (union-equal y z))
       (or (intersection-equal x y)
           (intersection-equal x z)))
  :hints (("Goal" :in-theory (enable union-equal intersection-equal))))

(defthm set-difference-equal-of-intersection-equal-and-intersection-equal-swapped
  (equal (set-difference-equal (intersection-equal x y)
                               (intersection-equal y x))
         nil))

(defthm set-difference-equal-of-set-difference-equal-when-subsetp-equal
  (implies (subsetp-equal z y)
           (equal (set-difference-equal (set-difference-equal x y) z)
                  (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

;rename
(defthm set-difference-equal-helper
  (equal (set-difference-equal (set-difference-equal x y)
                               (intersection-equal y z))
         (set-difference-equal x y)))

;; todo: add -arg1 to name
(defthm intersection-equal-of-set-difference-equal-when-subsetp-equal
  (implies (subsetp-equal x z)
           (equal (intersection-equal x (set-difference-equal y z))
                  nil))
  :hints (("Goal" :in-theory (enable intersection-equal set-difference-equal subsetp-equal))))

(defthmd intersection-equal-of-set-difference-equal-when-subsetp-equal-arg2
  (implies (subsetp-equal z y)
           (equal (intersection-equal (set-difference-equal x y) z)
                  nil))
  :hints (("Goal" :in-theory (enable intersection-equal set-difference-equal))))

(defthm subsetp-equal-of-append-of-intersection-equal-and-set-difference-equal-swapped
  (subsetp-equal x
                 (append (intersection-equal y x)
                         (set-difference-equal x y)))
  :hints (("Goal" :in-theory (e/d (subsetp-equal intersection-equal set-difference-equal)
                                  (;; for speed:
                                   remove-equal)))))

(defthm subsetp-equal-of-append-of-set-difference-equal-same-when-subsetp-equal
  (implies (subsetp-equal z x)
           (subsetp-equal z (append y (set-difference-equal x y))))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm set-difference-equal-of-union-equal-arg1
  (equal (set-difference-equal (union-equal x y) z)
         (union-equal (set-difference-equal x z)
                      (set-difference-equal y z)))
  :hints (("Goal" :in-theory (enable set-difference-equal union-equal))))

(defthm not-intersection-equal-when-not-intersection-equal-and-both-subsetp-equal
  (implies (and (not (intersection-equal c d))
                (subsetp-equal a c)
                (subsetp-equal b d))
           (not (intersection-equal a b)))
  :hints (("Goal" :in-theory (enable intersection-equal subsetp-equal))))

;; enabling this caused problems in ../axe
(defthmd intersection-equal-of-set-difference-equal-arg2
  (equal (intersection-equal x (set-difference-equal y z))
         (set-difference-equal (intersection-equal x y) z))
  :hints (("Goal" :in-theory (enable intersection-equal
                                     set-difference-equal))))

;move or gen to a subsetp fact, or gen the second x to z
(defthm intersection-equal-of-intersection-equal-and-intersection-equal-swapped
  (equal (intersection-equal (intersection-equal x y)
                             (intersection-equal y x))
         (intersection-equal x y))
  :hints (("Goal" ;:induct (intersection-equal y x)
           :in-theory (enable intersection-equal))))
