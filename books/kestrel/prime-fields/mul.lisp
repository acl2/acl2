; Prime fields library: Multiplication
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/utilities/pos-fix" :dir :system)
(include-book "../utilities/smaller-termp")
(include-book "fep")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/times"))

;; Compute the product of x and y modulo the prime.
(defund mul (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p))))
  (mbe :exec (mod (* x y) p)
       :logic (mod (* (ifix x) (ifix y)) (pos-fix p))))

(defthm natp-of-mul
  (natp (mul x y p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep mul))))

(defthm fep-of-mul
  (implies (posp p)
           (fep (mul x y p) p))
  :hints (("Goal" :in-theory (enable mul fep))))

(defthm mul-of-1-arg1
  (implies (and (fep x p)
                (integerp p))
           (equal (mul 1 x p)
                  x))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-1-arg1-gen
  (equal (mul 1 x p)
         (mod (ifix x) (pos-fix p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-1-arg2
  (implies (and (fep x p)
                (integerp p))
           (equal (mul x 1 p)
                  x))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg1
  (equal (mul 0 y p)
         0)
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg2
  (equal (mul x 0 p)
         0)
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg3
  (equal (mul x y 0)
         0)
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-not-integerp-arg1-cheap
  (implies (not (integerp x))
           (equal (mul x y p)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-not-integerp-arg2-cheap
  (implies (not (integerp y))
           (equal (mul x y p)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable mul))))

(defun strip-inv (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
           (eq 'inv (ffn-symb x)))
      (cadr x)
    x))

;; compare terms ignoring calls to inv
(defun smaller-mul-termp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (smaller-termp (strip-inv x)
                 (strip-inv y)))

(defthm mul-commutative
  (implies (syntaxp (smaller-mul-termp y x))
           (equal (mul x y p)
                  (mul y x p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-commutative-2
  (implies (syntaxp (smaller-mul-termp y x))
           (equal (mul x (mul y z p) p)
                  (mul y (mul x z p) p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-associative
  (equal (mul (mul x y p) z p)
         (mul x (mul y z p) p))
  :hints (("Goal" :in-theory (enable mul))))


(defthm mul-of-mod-arg1
  (equal (mul (mod x p) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-mod-arg2
  (equal (mul x (mod y p) p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm <-of-mul
  (implies (and (< 0 p)
                (integerp p))
           (< (mul x y p) p))
  :hints (("Goal" :in-theory (enable mul))))
