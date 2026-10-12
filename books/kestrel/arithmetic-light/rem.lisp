; A lightweight book about the built-in function rem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "truncate"))
(local (include-book "mod"))
(local (include-book "floor"))
(local (include-book "times"))
(local (include-book "times-and-divide"))
(local (include-book "plus-and-minus"))
(local (include-book "plus"))
(local (include-book "minus"))
(local (include-book "divide"))

(in-theory (disable rem))

;; Note: ACL2's built-in :type-prescription rule for REM tells us that it is an
;; acl2-number.

(defthm integerp-of-rem
  (implies (integerp y)
           (equal (integerp (rem x y))
                  (integerp (fix x))))
  :hints (("Goal" :in-theory (enable rem))))

(defthm integerp-of-rem-type
  (implies (and (integerp x)
                (integerp y))
           (integerp (rem x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rem))))

;gen?
;; (defthm nonneg-of-rem-type
;;   (implies (and (<= 0 x)
;;                 (rationalp x)
;;                 (<= 0 y)
;;                 (rationalp y))
;;            (<= 0 (rem x y)))
;;   :rule-classes :type-prescription
;;   :hints (("Goal" :cases ((equal 0 y))
;;                   :in-theory (enable rem ;*-of-truncate-upper-bound
;;                                      ))))

;; To support ACL2(r), we might have to assume (rationalp y) here.
(defthm rationalp-of-rem
  (implies (rationalp x)
           (rationalp (rem x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :cases ((rationalp y)
                          (complex-rationalp y))
           :in-theory (enable rem
                              truncate-when-rationalp-and-complex-rationalp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rem-of-0-arg2
  (equal (rem x 0)
         (fix x))
  :hints (("Goal" :in-theory (enable rem))))

(defthm rem-of-0-arg1
  (equal (rem 0 y)
         0)
  :hints (("Goal" :in-theory (enable rem))))

(defthmd rem-becomes-mod
  (implies (and (rationalp x)
                (rationalp y))
           (equal (rem x y)
                  (if (or (and (<= 0 x) (<= 0 y))
                          (and (< x 0) (< y 0)))
                      (mod x y)
                    (if (equal 0 (mod x y))
                        0
                      (+ (- y) (mod x y))))))
  :hints (("Goal" :in-theory (enable rem mod truncate-becomes-floor-gen)
           :cases ((equal 0 y)))))

(defthm rem-x-y-=-x-better
  (implies (and (rationalp x)
                (rationalp y))
           (equal (equal (rem x y) x)
                  (if (equal 0 y)
                      (acl2-numberp x)
                    (< (abs x) (abs y)))))
  :hints (("Goal" :cases ((< 0 x))
           :in-theory (enable rem
                              truncate-becomes-floor-gen
                              equal-of-floor))))

(defthm rem-when-integerp-of-quotient
  (implies (integerp (* x (/ y)))
           (equal (rem x y)
                  (if (or (not (acl2-numberp x))
                          (and (acl2-numberp y)
                               (not (equal 0 y))))
                      0
                    x)))
  :hints (("Goal" :cases ((acl2-numberp x))
           :in-theory (enable rem
                              truncate-when-integerp-of-quotient))))

;; (defthmd equal-of-0-and-rem
;;   (implies (and (rationalp x)
;;                 (rationalp y))
;;            (equal (equal 0 (rem x y))
;;                   (if (equal 0 y)
;;                       (equal 0 x)
;;                     (integerp (/ x y))))))
