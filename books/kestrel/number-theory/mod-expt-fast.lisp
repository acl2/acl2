; Rules about mod-expt-fast when the modulus is prime
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; Note that books/kestrel/arithmetic-light/mod-and-expt.lisp also deals with
;; mod-and-expt but not with primality.

;move
(defthm mod-of-expt-when-equal-of-mod-subst-constant
  (implies (and (equal k (mod r n))
                (syntaxp (and (quotep k)
                              (not (quotep r))))
                (integerp i)
                (<= 0 i)
                (integerp r)
                (natp n))
           (equal (mod (expt r i) n)
                  (mod (expt k i) n)))
  :hints (("Goal" :in-theory (enable expt))))

;move?
(defthm equal-of-0-and-mod-of-*
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

;move?
;; Another way to phrase equal-of-0-and-mod-of-*-when-primep
(defthm <-of-0-and-mod-of-*-when-primep
  (implies (and (rtl::primep p)
                (integerp x)
                (integerp y))
           (equal (< 0 (mod (* x y) p))
                  (and (< 0 (mod x p))
                       (< 0 (mod y p)))))
  :hints (("Goal" :use (:instance equal-of-0-and-mod-of-*)
           :in-theory (disable equal-of-0-and-mod-of-*))))

(defthm <-of-0-and-mod-of-expt
  (implies (and (rtl::primep n)
                (natp i)
                (integerp a))
           (equal (< 0 (acl2::mod (expt a i) n))
                  (or (equal i 0) ;odd case where we get 1
                      (< 0 (mod a n)))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm <-of-0-and-mod-expt-fast-when-primep
  (implies (and (rtl::primep n)
                (natp i)
                (integerp a))
           (equal (< 0 (acl2::mod-expt-fast a i n))
                  (or (equal 0 i) ;odd case where we get 1
                      (< 0 (mod a n)))))
  :hints (("Goal" :cases ((equal 0 (mod a n))
                          (< 0 (mod a n))))))
