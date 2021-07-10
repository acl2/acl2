; Prime fields library: Subtraction
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "add")
(include-book "neg")
(local (include-book "../arithmetic-light/mod"))

;; Compute the difference of x and y modulo the prime.  We'll usually leave sub
;; enabled, so our normal form has no calls of sub, just add and neg.
(defun sub (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p))))
  (add x (neg y p) p))

(defthm natp-of-sub
  (natp (sub x y p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep sub))))

(defthm fep-of-sub
  (implies (posp p)
           (fep (sub x y p) p))
  :hints (("Goal" :in-theory (enable sub fep))))

(defthm sub-of-0
  (implies (and (fep x p)
                (integerp p))
           (equal (sub x 0 p)
                  x))
  :hints (("Goal" :in-theory (enable sub))))

(defthm sub-same
  (implies (and (fep x p)
                (integerp p))
           (equal (sub x x p)
                  0))
  :hints (("Goal" :in-theory (enable sub neg add))))

(defthm sub-same-2
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (sub x (sub x y p) p)
                  y))
  :hints (("Goal" :in-theory (enable sub neg add acl2::mod-sum-cases))))

(defthm equal-of-0-and-sub
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal 0 (sub x y p))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable sub add neg acl2::mod-sum-cases))))

(defthm equal-of-sub-and-sub-cancel-1
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (integerp p))
           (equal (equal (sub x y p) (sub x z p))
                  (equal y z)))
  :hints (("Goal" :in-theory (enable sub add neg))))

(defthm equal-of-sub-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (fep x p)
                (fep k1 p)
                (fep k2 p)
                (integerp p))
           (equal (equal k1 (sub k2 x p))
                  (equal x (sub k2 k1 p))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sub add neg acl2::mod-sum-cases))))

;; Can be useful when p is not a constant
(defthm sub-when-constants
  (implies (and (syntaxp (and (quotep y) ;; checked first since more likely to fail
                              (quotep x)))
                (posp p)
                (integerp x)
                (integerp y))
           (equal (sub x y p)
                  (mod (- x y) p)))
  :hints (("Goal" :in-theory (enable sub add neg acl2::mod-sum-cases))))

(defthm mod-of-sub
  (equal (mod (sub x y p) p)
         (sub x y p))
  :hints (("Goal" :in-theory (enable sub add neg))))

;move?
(defthm neg-of-add
  (equal (neg (add x y p) p)
         (add (neg x p)
              (neg y p)
              p))
  :hints (("Goal" :in-theory (enable neg add sub acl2::mod-sum-cases))))

;; -(x-y) becomes y-x
;; But note that we'll often leave sub enabled
(defthm neg-of-sub
  (equal (neg (sub x y p) p)
         (sub y x p))
  :hints (("Goal" :in-theory (enable sub ;neg
                                     ))))
