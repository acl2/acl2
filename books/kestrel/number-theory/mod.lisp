; Rules about mod when the modulus is prime
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; Note that books/kestrel/arithmetic-light/mod.lisp also deals with mod but
;; not with primality.

(defthm equal-of-0-and-mod-of-*-when-primep
  (implies (and (rtl::primep p)
                (integerp x)
                (integerp y))
           (equal (equal 0 (mod (* x y) p))
                  (or (equal 0 (mod x p))
                      (equal 0 (mod y p)))))
  :hints (("Goal" :use (:instance rtl::euclid
                                  (a x)
                                  (b y)
                                  (p p))
           :in-theory (enable rtl::divides
                              acl2::integerp-of-*-of-/-becomes-equal-of-0-and-mod))))

;; Another way to phrase equal-of-0-and-mod-of-*-when-primep
(defthm <-of-0-and-mod-of-*-when-primep
  (implies (and (rtl::primep p)
                (integerp x)
                (integerp y))
           (equal (< 0 (mod (* x y) p))
                  (and (< 0 (mod x p))
                       (< 0 (mod y p)))))
  :hints (("Goal" :use (:instance equal-of-0-and-mod-of-*-when-primep)
           :in-theory (disable equal-of-0-and-mod-of-*-when-primep))))


(defthm equal-of-0-and-mod-of-expt-when-primep
  (implies (and (rtl::primep n)
                (natp i)
                (integerp a))
           (equal (equal 0 (acl2::mod (expt a i) n))
                  (and (not (equal i 0)) ;odd case where we get 1
                       (equal 0 (mod a n)))))
  :hints (("Goal" :in-theory (enable expt))))

;; Another way to phrase equal-of-0-and-mod-of-expt-when-primep
(defthm <-of-0-and-mod-of-expt-when-primep
  (implies (and (rtl::primep n)
                (natp i)
                (integerp a))
           (equal (< 0 (acl2::mod (expt a i) n))
                  (or (equal i 0) ;odd case where we get 1
                      (< 0 (mod a n)))))
  :hints (("Goal" :in-theory (enable expt))))
