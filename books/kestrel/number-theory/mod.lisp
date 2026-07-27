; Rules about mod when the modulus is prime
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "projects/numbers/euclid" :dir :system) ;for dm::primep
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; Note that books/kestrel/arithmetic-light/mod.lisp also deals with mod but
;; not with primality.

(defthm equal-of-0-and-mod-of-*-when-primep
  (implies (and (dm::primep p)
                (integerp x)
                (integerp y))
           (equal (equal 0 (mod (* x y) p))
                  (or (equal 0 (mod x p))
                      (equal 0 (mod y p)))))
  :hints (("Goal" :use (:instance dm::euclid
                                  (a x)
                                  (b y)
                                  (p p))
           :in-theory (enable dm::divides
                              acl2::integerp-of-*-of-/-becomes-equal-of-0-and-mod))))

;; Another way to phrase equal-of-0-and-mod-of-*-when-primep
(defthm <-of-0-and-mod-of-*-when-primep
  (implies (and (dm::primep p)
                (integerp x)
                (integerp y))
           (equal (< 0 (mod (* x y) p))
                  (and (< 0 (mod x p))
                       (< 0 (mod y p)))))
  :hints (("Goal" :use (:instance equal-of-0-and-mod-of-*-when-primep)
           :in-theory (disable equal-of-0-and-mod-of-*-when-primep))))


(defthm equal-of-0-and-mod-of-expt-when-primep
  (implies (and (dm::primep n)
                (natp i)
                (integerp a))
           (equal (equal 0 (acl2::mod (expt a i) n))
                  (and (not (equal i 0)) ;odd case where we get 1
                       (equal 0 (mod a n)))))
  :hints (("Goal" :in-theory (enable expt))))

;; Another way to phrase equal-of-0-and-mod-of-expt-when-primep
(defthm <-of-0-and-mod-of-expt-when-primep
  (implies (and (dm::primep n)
                (natp i)
                (integerp a))
           (equal (< 0 (acl2::mod (expt a i) n))
                  (or (equal i 0) ;odd case where we get 1
                      (< 0 (mod a n)))))
  :hints (("Goal" :in-theory (enable expt))))

;; If a prime is a multiple of another prime, they are equal.
;; Disabled to avoid bringing consideration of primep into unrelated proofs.
(defthmd equal-of-0-and-mod-when-primep-and-primep
  (implies (and (dm::primep p1)
                (dm::primep p2))
           (equal (equal 0 (mod p1 p2))
                  (equal p1 p2)))
  :hints (("Goal"
           :use ((:instance dm::primep-no-divisor (dm::p p1) (dm::d p2)))
           :in-theory (enable dm::divides equal-of-0-and-mod))))
