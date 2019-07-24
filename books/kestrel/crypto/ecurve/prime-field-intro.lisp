; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "../../prime-fields/prime-fields")
(include-book "odd-prime-fields")
(local (include-book "../../arithmetic-light/times"))
(local (include-book "../../arithmetic-light/expt"))
(local (include-book "../../arithmetic-light/mod"))
(local (include-book "../../prime-fields/prime-fields-rules"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime Field Operation Rewriting
; -------------------------------

; This book contains theorems to rewrite operations from the odd prime field
; development in odd-prime-field.lisp to operations from our general prime
; field development.  The latter development may eventually replace the former
; development, thus obviating the need for this book, but for the time being
; some supporting proofs in this elliptic curve library still depend on the
; odd-prime-field.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm mod-of-/p-becomes-inv
  (implies (integerp x)
           (equal (mod (/p x) (prime))
                  (pfield::inv x (prime))))
  :hints (("Goal" :in-theory (enable /p pfield::inv pfield::pow-rewrite
                                     pfield::minus1))))

(defthm mod-of-+-becomes-add
  (equal (mod (+ x y) p)
         (pfield::add x y p))
  :hints (("Goal" :in-theory (enable pfield::add))))

(defthm add-of---arg1
  (implies (and (rationalp x)
                (rationalp y)
                (posp p))
           (equal (pfield::add (- x) y p)
                  (pfield::add (pfield::neg x p) y p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub)
                           (mod-of-+-becomes-add)))))

(defthm add-of---arg2
  (implies (and (rationalp x)
                (rationalp y)
                (posp p))
           (equal (pfield::add y (- x) p)
                  (pfield::add y (pfield::neg x p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub)
                           (mod-of-+-becomes-add)))))

(defthm add-of-+-arg1
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (posp p))
           (equal (pfield::add (+ x1 x2) y p)
                  (pfield::add (pfield::add x1 x2 p) y p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub)
                           (mod-of-+-becomes-add)))))

(defthm add-of-+-arg2
  (implies (and (rationalp x)
                (rationalp y1)
                (rationalp y2)
                (posp p))
           (equal (pfield::add x (+ y1 y2) p)
                  (pfield::add x (pfield::add y1 y2 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub)
                           (mod-of-+-becomes-add)))))

(defthm add-of-*-arg1
  (implies (and (rationalp y)
                (rationalp x1)
                (rationalp x2)
                (posp p))
           (equal (pfield::add (* x1 x2) y p)
                  (pfield::add (pfield::mul x1 x2 p) y p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-+-becomes-add)))))

(defthm add-of-*-arg2
  (implies (and (rationalp y)
                (rationalp x1)
                (rationalp x2)
                (posp p))
           (equal (pfield::add y (* x1 x2) p)
                  (pfield::add y (pfield::mul x1 x2 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-+-becomes-add)))))

(defthm mul-of-*-arg1
  (implies (and (integerp y)
                (integerp x1)
                (integerp x2)
                (posp p))
           (equal (pfield::mul (* x1 x2) y p)
                  (pfield::mul (pfield::mul x1 x2 p) y p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-+-becomes-add)))))

(defthm mul-of-*-arg2
  (implies (and (integerp y)
                (integerp x1)
                (integerp x2)
                (posp p))
           (equal (pfield::mul y (* x1 x2) p)
                  (pfield::mul y (pfield::mul x1 x2 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-+-becomes-add)))))

(defthm mul-of-/p-arg1
  (implies (and (integerp y)
                (integerp x)
                (posp p))
           (equal (pfield::mul (/p x) y (prime))
                  (pfield::mul (pfield::inv x (prime)) y (prime))))
  :hints (("Goal" :do-not '(preprocess)
           :use (:instance mod-of-/p-becomes-inv)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-/p-becomes-inv
                            mod-of-+-becomes-add)))))

(defthm mul-of-/p-arg2
  (implies (and (integerp y)
                (integerp x)
                (posp p))
           (equal (pfield::mul y (/p x) (prime))
                  (pfield::mul y (pfield::inv x (prime)) (prime))))
  :hints (("Goal" :do-not '(preprocess)
           :use (:instance mod-of-/p-becomes-inv)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-/p-becomes-inv
                            mod-of-+-becomes-add)))))

(defthm inv-of-+
  (implies (and (integerp y)
                (integerp x)
                (integerp p)
                (<= 2 p))
           (equal (pfield::inv (+ x y) p)
                  (pfield::inv (pfield::add x y p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul
                                        pfield::inv
                                        pfield::pow-rewrite
                                        pfield::minus1)
                           (mod-of-+-becomes-add)))))

(defthm inv-of-*
  (implies (and (integerp y)
                (integerp x)
                (integerp p)
                (<= 2 p))
           (equal (pfield::inv (* x y) p)
                  (pfield::inv (pfield::mul x y p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add
                                        pfield::sub
                                        pfield::mul
                                        pfield::inv
                                        pfield::pow-rewrite
                                        pfield::minus1)
                           (mod-of-+-becomes-add)))))

(defthm inv-of--
  (implies (and (integerp y)
                (integerp x)
                (integerp p)
                (<= 2 p))
           (equal (pfield::inv (- x y) p)
                  (pfield::inv (pfield::sub x y p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul
                                        pfield::inv
                                        pfield::pow-rewrite
                                        pfield::minus1)
                           (mod-of-+-becomes-add
                            acl2::mod-sum-cases)))))

(defthm inv-of-unary--
  (implies (and (integerp y)
                (integerp x)
                (integerp p)
                (<= 2 p))
           (equal (pfield::inv (- x) p)
                  (pfield::inv (pfield::neg x p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul
                                        pfield::inv
                                        pfield::pow-rewrite
                                        pfield::minus1)
                           (mod-of-+-becomes-add
                            acl2::mod-of-minus-arg1
                            acl2::mod-sum-cases)))))

(defthm mod-of-*-becomes-mul
  (equal (mod (* x y) p)
         (pfield::mul x y p))
  :hints (("Goal" :in-theory (enable pfield::mul))))

(defthm sub-of-p
  (implies (and (integerp x)
                (posp p))
           (equal (pfield::sub p x p)
                  (pfield::neg x p)))
  :hints (("Goal" :in-theory (e/d (pfield::add pfield::sub pfield::neg)
                                  (mod-of-+-becomes-add)))))

(defthm mul-of-mod
  (implies (and (integerp x)
                (integerp y)
                (integerp p))
           (equal (pfield::mul (mod x p) y p)
                  (pfield::mul x y p)))
  :hints (("Goal" :in-theory (e/d (pfield::mul)
                                  (mod-of-*-becomes-mul)))))

(defthm mul-of-mod-arg2
  (implies (and (integerp x)
                (integerp y)
                (integerp p))
           (equal (pfield::mul y (mod x p) p)
                  (pfield::mul y x p)))
  :hints (("Goal" :in-theory (e/d (pfield::mul)
                                  (mod-of-*-becomes-mul)))))

(defthm mul-of-+-arg1
  (implies (and (integerp y)
                (integerp x1)
                (integerp x2)
                (posp p))
           (equal (pfield::mul (+ x1 x2) y p)
                  (pfield::mul (pfield::add x1 x2 p) y p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-*-becomes-mul mod-of-+-becomes-add)))))

(defthm mul-of-+-arg2
  (implies (and (integerp y)
                (integerp x1)
                (integerp x2)
                (posp p))
           (equal (pfield::mul y (+ x1 x2) p)
                  (pfield::mul y (pfield::add x1 x2 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-*-becomes-mul mod-of-+-becomes-add)))))

(defthm mul-of---arg1
  (implies (and (integerp y)
                (integerp x1)
                (posp p))
           (equal (pfield::mul (- x1) y p)
                  (pfield::mul (pfield::neg x1 p) y p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-*-becomes-mul mod-of-+-becomes-add)))))

(defthm mul-of---arg2
  (implies (and (integerp y)
                (integerp x1)
                (posp p))
           (equal (pfield::mul y (- x1) p)
                  (pfield::mul y (pfield::neg x1 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::add pfield::sub pfield::mul)
                           (mod-of-*-becomes-mul mod-of-+-becomes-add)))))

(defthm neg-intro
  (implies (and (natp x)
                (< x p)
                (posp p))
           (equal (+ p (- x))
                  (if (equal x 0)
                      p
                    (pfield::neg x p))))
  :hints (("Goal" :in-theory (enable pfield::neg pfield::sub mod))))

(defthm mod-of--
  (implies (and (natp x)
                (< x p)
                (posp p))
           (equal (mod (- x) p)
                  (pfield::neg x p)))
  :hints (("Goal" :in-theory (e/d (pfield::neg pfield::sub mod)
                                  (neg-intro)))))

(defthm neg-of-*
  (implies (and (rationalp x1)
                (rationalp x2)
                (posp p))
           (equal (pfield::neg (* x1 x2) p)
                  (pfield::neg (pfield::mul x1 x2 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (pfield::neg pfield::mul pfield::sub pfield::mul)
                           (mod-of-*-becomes-mul)))))
