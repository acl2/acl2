; Supporting material for SHA-3 spec
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;reduce?:
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/lists-light/group" :dir :system)
(include-book "kestrel/lists-light/ungroup" :dir :system)
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;(local (include-book "kestrel/typed-lists-light/all-integerp-of-repeat" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
;(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system)) ;for MOD-OF-*-SUBST-CONSTANT-ARG2

;(local (in-theory (disable acl2::group-becomes-group2)))
;(local (in-theory (disable true-listp))) ;prevent inductions
;(local (in-theory (disable acl2::mod-sum-cases))) ;avoid case splits
;(local (in-theory (disable acl2::update-nth-of-update-nth-becomes-update-subrange)))
;(local (in-theory (disable len-of-group)))

(defthm integerp-of-+-of---and--
  (equal (integerp (+ (- x) (- y)))
         (integerp (+ x y)))
  :hints (("Goal" :use (:instance integerp-of-- (x (+ x y)))
           :in-theory (disable integerp-of--))))

;move
(defthm true-list-listp-rewrite
  (equal (true-list-listp x)
         (and (all-true-listp x)
              (true-listp x))))

;move
(defthm ungroup-of-group
  (implies (and (posp n)
                (force (equal 0 (mod (len x) n)))
                (true-listp x))
           (equal (ungroup n (group n x))
                  x))
  :hints (("Goal" :in-theory (enable group ungroup equal-of-append))))

;move
(defthm len-of-group-2
  (implies (and (posp n)
                (force (equal 0 (mod (len x) n))))
           (equal (len (group n x))
                  (/ (len x) n)))
  :hints (("Goal" :in-theory (enable group
                                     CEILING-IN-TERMS-OF-FLOOR
                                     FLOOR-WHEN-MULTIPLE
                                     EQUAL-OF-0-AND-MOD))))

(defthm mod-when-odd
  (implies (and (not (integerp (* 1/2 x)))
                (integerp x))
           (equal (mod x 2)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

;; an odd plus an odd is an even
(defthm evenp-of-+-when-odd-and-odd
  (implies (and (integerp x)
                (integerp y)
                (not (evenp x))
                (not (evenp y)))
           (evenp (+ x y)))
  :hints (("Goal" :in-theory (enable mod-sum-cases)
           :use (:instance equal-of-0-and-mod (x (+ x y)) (y 2)))))

(defthmd even-becomes-equal-of-0-and-mod
  (implies (integerp x)
           (equal (INTEGERP (* 1/2 X))
                  (equal 0 (mod x 2))))
  :hints (("Goal" :in-theory (enable equal-of-0-and-mod))))

;; an odd times an odd is an odd
(defthm oddp-of-*-when-odd-and-odd
  (implies (and (integerp x)
                (integerp y)
                (not (evenp x))
                (not (evenp y)))
           (not (evenp (* x y))))
  :hints (("Goal" :in-theory (enable even-becomes-equal-of-0-and-mod))))

;; (defthm all-integerp-of-repeat
;;   (equal (all-integerp (repeat n x))
;;          (or (zp n)
;;              (integerp x)))
;;   :hints (("Goal" :in-theory (enable all-integerp repeat))))

;; (defthm all-unsigned-byte-p-of-repeat
;;   (equal (all-unsigned-byte-p size (repeat n x))
;;          (or (zp n)
;;              (unsigned-byte-p size x)))
;;   :hints (("Goal" :in-theory (enable all-unsigned-byte-p repeat))))
