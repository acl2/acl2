; A book about floor, mod, and expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

;; TODO: Combine this with the similar book in arithmetic-light

(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/nonnegative-integer-quotient" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
;(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system)) ;for floor-of-floor

(defthm floor-of-shifting-lemma2-helper
  (implies (and (equal 0 (mod y x)) ;y is a mult of x (todo: consider not using mod to express this)
                (rationalp z)
                (posp x) ;(rationalp x)
                (posp y) ;(rationalp y)
                )
           (equal (floor (* x (floor z x))
                         y)
                  (floor z y)))
  :hints (("Goal" :use ((:instance FLOOR-of-FLOOR
                                  (i (* x (floor z x)))
                                  (j1 x)
                                  (j2 (/ y x)))
                        (:instance FLOOR-of-FLOOR
                                  (i z)
                                  (j1 x)
                                  (j2 (/ y x))))
           :in-theory (disable FLOOR-of-FLOOR))))

(defthm floor-of-shifting-lemma2
  (implies (and (<= low n)
                (natp n)
                (natp low)
                (rationalp x))
           (equal (floor (* (expt 2 low) (floor x (expt 2 low)))
                         (expt 2 n))
                  (floor x (expt 2 n))))
  :hints (("Goal" :in-theory (enable equal-of-0-and-mod)))
;  :hints (("Goal" :in-theory (enable FLOOR-EQUAL-SPLIT)))
  )

;; (defthm equal-of-*-of-/
;;   (implies (and (not (equal y 0))
;;                 (rationalp y)
;;                 (acl2-numberp x)
;;                 (acl2-numberp z))
;;            (equal (equal x (* (/ y) z))
;;                   (equal (* x y) z))))


;; (defthm floor-of-2-cases
;;   (implies (integerp i)
;;            (equal (floor i 2)
;;                   (if (equal 0 (mod i 2))
;;                       (/ i 2)
;;                     (+ 1/2 (/ i 2)))))
;;   :hints (("Goal" :in-theory (enable mod)
;;            :use (:instance floor-unique
;;                            (j 2)
;;                            (n (if (equal 0 (mod i 2))
;;                                   (/ i 2)
;;                                 (+ 1/2 (/ i 2))))))))

;;drop?
(defthmd mod-of-floor-and-expt-of-one-less
  (implies (and (equal (mod i (expt 2 n)) 0)
                (integerp i)
                (natp n))
           (equal (mod (floor i 2) (expt 2 (+ -1 n)))
                  0))
  :hints (("Goal" :in-theory (enable mod-of-floor-of-2-and-expt-of-one-less-alt))))
