; Rules about bitwise operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvand")
(include-book "bvxor")
(include-book "bvnot")
(include-book "bvor")
(include-book "bitxor")
(include-book "bvcat")
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))

;; (thm
;;  (implies (integerp x)
;;           (equal (INTEGERP (+ 1/2 (* 1/2 x)))
;;                  (not (evenp x))))
;;  :hints (("Goal" :in-theory (enable evenp))))

;see also one in thms.lisp

;; De Morgan
(defthmd bvnot-of-bvand
  (implies (natp n)
           (equal (bvnot n (bvand n x y))
                  (bvor n (bvnot n x) (bvnot n y))))
  :hints (("Goal" :in-theory (enable bvnot bvand bvor lognot-of-logand))))

;; De Morgan
(defthmd bvnot-of-bvor
  (implies (natp n)
           (equal (bvnot n (bvor n x y))
                  (bvand n (bvnot n x) (bvnot n y))))
  :hints (("Goal" :in-theory (enable bvnot bvand bvor lognot-of-logand))))

(local
 (defun floor2-floor2-sub1-induct (x y n)
  (if (zp n)
      (list x y n)
    (floor2-floor2-sub1-induct (floor x 2) (floor y 2) (+ -1 n)))))

(local
 (defthm evenp-when-equal-of-mod-of-expt-and-0
  (implies (and (equal (mod x (expt 2 n)) 0) ;n is a free var
                (posp n)
                (integerp x))
           (evenp x))
  :hints (("Goal" :in-theory (enable evenp-becomes-equal-of-0-and-mod)))))

(local
 (defthm evenp-when-equal-of-mod-of-2-and-0-cheap
  (implies (and (equal (mod x 2) 0)
                (integerp x))
           (evenp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable evenp-becomes-equal-of-0-and-mod)))))

(local
 (defthm mod-of-2-and-expt-of-2
  (implies (natp n)
           (equal (mod 2 (expt 2 n))
                  (if (< n 2)
                      0
                    2)))))

(local
 (defthm mod-of-1-and-expt-of-2
  (implies (natp n) ;gen?
           (equal (mod 1 (expt 2 n))
                  (if (< n 1)
                      0
                    1)))
  :hints (("Goal" :cases ((< n 0))))))

(local
 (defthm mod-of-floor-of-2-and-expt2-of-one-less
  (implies (and (equal (mod x (expt 2 n)) 0)
                (integerp x)
                (posp n))
           (equal (mod (floor x 2) (expt 2 (+ -1 n)))
                  0))
  :hints (("Goal" :in-theory (enable mod-expt-split)))))

(local
 (defthmd bvxor-of-bvand-same-arg2-helper
   (implies (and (unsigned-byte-p n x)
                 (natp n))
            (equal (bvxor n y (bvand n x y))
                   (bvand n y (bvnot n x))))
   :hints (("Goal" :in-theory (enable bvxor bvand bvnot logxor lognot-of-logand
                                      logand-of-bvchop)))))

;; Removes a mention of y
(defthm bvxor-of-bvand-same-arg2
  (equal (bvxor n y (bvand n x y))
         (bvand n y (bvnot n x)))
  :hints (("Goal" :cases ((natp n))
           :use (:instance bvxor-of-bvand-same-arg2-helper (x (bvchop n x))))))

(defthmd bvxor-of-+-of-1-split
  (implies (natp n)
           (equal (bvxor (+ 1 n) x y)
                  (bvcat 1 (acl2::bitxor (acl2::getbit n x) (acl2::getbit n y))
                         n (bvxor n x y)))))
