; Prime fields library: Multiplication
;
; Copyright (C) 2019-2024 Kestrel Institute
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
(local (include-book "../arithmetic-light/mod-and-expt"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../number-theory/divides")) ; reduce? for dm::euclid

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

(defthm mul-of-+-same-arg1-arg1
  (equal (mul (+ p x) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-+-same-arg1-arg2
  (equal (mul (+ x p) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-+-same-arg2-arg2
  (equal (mul x (+ y p) p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of--1-and--1
  (implies (posp p)
           (equal (mul -1 -1 p)
                  (if (equal p 1)
                      0 ; unusual case
                    1)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-ifix-arg1
  (equal (mul (ifix x) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-ifix-arg2
  (equal (mul x (ifix y) p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-equal-of-mod-subst-arg1
  (implies (and (syntaxp (not (quotep x)))
                (equal (mod x p) k)
                (syntaxp (quotep k)))
           (equal (mul x y p)
                  (mul k y p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-equal-of-mod-subst-arg2
  (implies (and (syntaxp (not (quotep y)))
                (equal (mod y p) k)
                (syntaxp (quotep k)))
           (equal (mul x y p)
                  (mul x k p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-expt-subst-constant-arg2
  (implies (and (syntaxp (not (quotep y)))
                (equal (mod y p) k)
                (syntaxp (quotep k))
                (integerp y)
                (natp i))
           (equal (mul x (expt y i) p)
                  (mul x (expt k i) p)))
  :hints (("Goal" :in-theory (enable mul acl2::pos-fix))))

(defthm equal-of-0-and-mul
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (equal 0 (mul x y p))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal"
           :use ((:instance dm::euclid
                            (p p)
                            (a x)
                            (b y)))
           :in-theory (enable mul divides acl2::equal-of-0-and-mod))))

(defthm equal-of-0-and-mul-gen
  (implies (primep p)
           (equal (equal 0 (mul x y p))
                  (or (equal (mod (ifix x) p) 0)
                      (equal (mod (ifix y) p) 0))))
  :hints (("Goal" :use (:instance equal-of-0-and-mul
                                  (x (mod (ifix x) p))
                                  (y (mod (ifix y) p)))
           :in-theory (disable equal-of-0-and-mul))))

;; If the resulting constant (* x y) is too large, a rule below will
;; reduce it.
(defthm mul-of-mul-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (integerp p))
           (equal (mul x (mul y z p) p)
                  (mul
                   (* x y) ;we don't call mul here in case the p argument is not known (todo: do something similar for the add rule)
                   z p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthmd mul-of-mul-combine-constants-alt
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep p)))
           (equal (mul x (mul y z p) p)
                  (mul (mul x y p) z p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-constant-reduce-arg1
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (<= p x) ;x is too big (prevents loops)
                ;; (integerp x)
                ;; (integerp y)
                ;; (natp p)
                )
           (equal (mul x y p)
                  (mul (mod x p) y p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-same-arg1
  (implies (and (integerp y)
                (posp p))
           (equal (mul p y p)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mod-of-mul
  (equal (mod (mul x y p) p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

;rename
(defthm mul-bound
  (implies (posp p)
           (< (mul x y p) p))
  :hints (("Goal" :in-theory (enable mul))))
