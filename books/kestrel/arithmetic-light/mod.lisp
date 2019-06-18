; A lightweight book about the built-in function mod.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable mod))

;drop?
(defthm acl2-numberp-of-mod
  (acl2-numberp (mod x y)))

(defthm integerp-of-mod
  (implies (and (integerp x)
                (integerp y))
           (integerp (mod x y)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm integerp-of-mod-type
  (implies (and (integerp x)
                (integerp y))
           (integerp (mod x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable mod))))

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

;gen?
(defthm nonneg-of-mod-type
  (implies (and (<= 0 x)
                (rationalp x)
                (<= 0 y)
                (rationalp y))
           (<= 0 (mod x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :cases ((equal 0 y))
           :in-theory (enable mod))))

(defthm nonneg-of-mod-type-2
  (implies (and ;(<= 0 x)
                (rationalp x)
                (< 0 y)
                (rationalp y))
           (<= 0 (mod x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :cases ((equal 0 y))
           :in-theory (enable mod))))

(defthm mod-of-0
  (equal (mod x 0)
         (fix x))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-0-arg1
  (equal (mod 0 y)
         0)
  :hints (("Goal" :in-theory (enable mod))))

;; (mod x 1) returns the fractional part of x, which for an integer is 0.
(defthm mod-of-1-when-integerp
  (implies (integerp x)
           (equal (mod x 1)
                  0)))

(defthm mod-of-1-arg1
  (implies (and (integerp j)
                (<= 0 j) ;gen
                )
           (equal (mod 1 j)
                  ;;(if (<= 0 j)
                  (if (equal 1 j)
                      0
                    1)
                  ;;-1)
                  ))
  :hints (("Goal" :in-theory (enable mod))))

(defthm rationalp-of-mod
  (implies (rationalp x)
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription))

(defthm mod-of-mod-same-arg2
  (implies (and (rationalp x)
                (rationalp y))
           (equal (mod (mod x y) y)
                  (mod x y)))
  :hints (("Goal" :cases ((rationalp i)))))

(defthm mod-when-<
  (implies (and (< i j)
                (<= 0 i)
                (rationalp i)
                (natp j) ;(<= 0 j)
                )
           (equal (mod i j)
                  i))
  :hints (("Goal" :cases ((rationalp i)))))

(defthmd equal-of-0-and-mod
  (implies (and (rationalp i)
                (rationalp j))
           (equal (equal 0 (mod i j))
                  (if (equal 0 j)
                      (equal 0 i)
                    (integerp (/ i j))))))

;; (defthm integerp-of-/-becomes-equal-of-0-and-mod
;;   (implies (and (rationalp i)
;;                 (rationalp j)
;;                 (not (equal 0 j)))
;;            (equal (integerp (/ i j))
;;                   (equal 0 (mod i j)))))

;todo: add alt conjunct
(defthmd integerp-of-*-of-/-becomes-equal-of-0-and-mod
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (integerp (* (/ j) i)) ;should match things like (* 1/32 x)
                  (equal 0 (mod i j))))
  :hints (("Goal" :use (:instance equal-of-0-and-mod)
           :in-theory (disable equal-of-0-and-mod))))

(theory-invariant (incompatible (:rewrite integerp-of-*-of-/-becomes-equal-of-0-and-mod)
                                (:rewrite equal-of-0-and-mod)))

(defthm mod-bound-linear-arg1
  (implies (and (rationalp i)
                (<= 0 i)
                (rationalp j)
                (<= 0 j))
           (<= (mod i j) i))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal j 0))
           :in-theory (enable mod))))

(defthm mod-bound-linear-arg2
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (< (mod i j) j))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal j 0))
           :in-theory (enable mod))))

(defthm equal-of-mod-same-arg1
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (equal (equal i (mod i j))
                  (and (<= 0 i)
                       (< i j)))))

(defthm mod-of-2-when-even-cheap
  (implies (and (integerp (* 1/2 x))
                (rationalp x))
           (equal (mod x 2)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable equal-of-0-and-mod))))

(defthm mod-of-*-lemma
  (implies (and (integerp x)
                (posp y))
           (equal (mod (* x y) y)
                  0)))

(defthm mod-of-*-lemma-alt
  (implies (and (integerp x)
                (posp y))
           (equal (mod (* y x) y)
                  0)))
