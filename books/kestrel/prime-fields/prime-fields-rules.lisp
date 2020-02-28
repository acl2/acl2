; Prime fields library: additional rules
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "prime-fields")
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))

(local (in-theory (disable acl2::mod-sum-cases))) ;for speed

(in-theory (disable mod)) ;since mod is introduced by some rules below

;distributivity
;move
(defthm mul-of-add-arg2
  (implies (and (integerp x)
                (integerp y1)
                (integerp y2)
                (posp p))
           (equal (mul x (add y1 y2 p) p)
                  (add (mul x y1 p)
                             (mul x y2 p)
                             p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add mul))))

(defthm mul-of-add-arg1
  (implies (and (integerp x)
                (integerp y1)
                (integerp y2)
                (posp p))
           (equal (mul (add y1 y2 p) x p)
                  (add (mul y1 x p)
                             (mul y2 x p)
                             p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add mul))))

;move
(defthm equal-of-add-and-add-cancel-1-gen
  (implies (and (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (posp p))
           (equal (equal (add x y p) (add x z p))
                  (equal (mod y p) (mod z p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add sub))))

(defthm mod-of-add
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (equal (mod (add x y p) p)
                  (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm mod-of-neg
  (implies (and (integerp x)
                (posp p))
           (equal (mod (neg x p) p)
                  (neg x p)))
  :hints (("Goal" :in-theory (enable neg sub))))

(defthm neg-of-*
  (implies (and (rationalp x1)
                (rationalp x2)
                (posp p))
           (equal (neg (* x1 x2) p)
                  (neg (mul x1 x2 p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul))))

(defthm fep-holds
  (implies (and (natp x)
                (< x p))
           (fep x p))
  :hints (("Goal" :in-theory (enable fep))))

;move
(defthm mul-of-neg-arg1
  (implies (and (integerp y)
                (integerp x)
                (posp p))
           (equal (mul (neg x p) y p)
                  (neg (mul x y p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul
                              acl2::equal-of-0-and-mod
                              acl2::integerp-of-*-three))))

(defthm mul-of-neg-arg2
  (implies (and (integerp y)
                (integerp x)
                (posp p))
           (equal (mul y (neg x p) p)
                  (neg (mul y x p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul
                              acl2::equal-of-0-and-mod
                              acl2::integerp-of-*-three))))

(defthm neg-of-add
  (implies (and (integerp y)
                (integerp x)
                (posp p))
           (equal (neg (add x y p) p)
                  (add (neg x p)
                             (neg y p)
                             p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul acl2::mod-sum-cases))))

;move
;gen
(defthm mod-of-expt-of-mod
  (implies (and (integerp x)
                (natp n)
                (posp p))
           (equal (mod (expt (mod x p) n) p)
                  (mod (expt x n) p)))
  :hints (("Goal" :in-theory (enable expt acl2::mod-of-*-subst))))

(defthm mod-of-expt-of-+-of-mod-arg2
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (posp p))
           (equal (mod (expt (+ x (mod y p)) n) p)
                  (mod (expt (+ x y) n) p)))
  :hints (("Goal" :use ((:instance mod-of-expt-of-mod (x (+ x y)))
                        (:instance mod-of-expt-of-mod (x (+ x (mod y p)))))
           :in-theory (disable mod-of-expt-of-mod))))

(defthm mod-of-expt-of-+-of-mod-arg1
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (posp p))
           (equal (mod (expt (+ (mod y p) x) n) p)
                  (mod (expt (+ y x) n) p)))
  :hints (("Goal" :use ((:instance mod-of-expt-of-mod (x (+ x y)))
                        (:instance mod-of-expt-of-mod (x (+ x (mod y p)))))
           :in-theory (disable mod-of-expt-of-mod))))

(defthm mod-of-expt-of-+-of---same
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (posp p))
           (equal (mod (expt (+ (- p) x) n) p)
                  (mod (expt x n) p)))
  :hints (("Goal" :use ((:instance mod-of-expt-of-mod (x x))
                        (:instance mod-of-expt-of-mod (x (+ (- p) x))))
           :in-theory (disable mod-of-expt-of-mod))))

(defthm add-of-0-arg1-gen
  (implies (integerp p)
           (equal (add 0 x p)
                  (mod x p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg2-gen
  (implies (integerp p)
           (equal (add x 0 p)
                  (mod x p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-mul-and-mul-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp x)
                (integerp y)
                (integerp k1)
                (integerp k2)
                (posp p))
           (equal (add (mul k1 x p) (mul k2 x p) p)
                  (mul (+ k1 k2) x p)))
  :hints (("Goal" :in-theory (e/d (add mul)
                                  (acl2::mod-sum-cases)))))

(defthm add-of-mul-and-mul-combine-constants-2
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp x)
                (integerp y)
                (integerp k1)
                (integerp k2)
                (posp p))
           (equal (add (mul k1 x p) (add (mul k2 x p) y p) p)
                  (add (mul (+ k1 k2) x p) y p)))
  :hints (("Goal" :use (:instance add-of-mul-and-mul-combine-constants)
           :in-theory (disable add-of-mul-and-mul-combine-constants))))

(defthm neg-of-neg-gen
  (implies (and (integerp x)
                (posp p))
           (equal (neg (neg x p) p)
                  (mod x p)))
  :hints (("Goal" :in-theory (enable neg sub add))))

(defthm mod-of-mul
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (equal (mod (mul x y p) p)
                  (mul x y p)))
  :hints (("Goal" :in-theory (enable mul))))

(local
 (defthmd *-of-2
   (equal (* 2 x)
          (+ x x))))

;; (-x)+(-x) becomes -2x
(defthm add-of-neg-and-neg-same
  (implies (and (integerp x)
                (posp p))
           (equal (add (neg x p) (neg x p) p)
                  (neg (mul 2 x p) p)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable neg sub add mul
                                     acl2::mod-sum-cases
                                     *-of-2))))

(defthm add-of-add-same
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (equal (add x (add x y p) p)
                  (add (mul 2 x p) y p)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable neg sub add mul *-of-2))))

(defthm add-of-add-of-mul-same
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (posp p))
           (equal (add x (add (mul k x p) y p) p)
                  (add (mul (+ 1 k) x p) y p)))
  :hints (("Goal" :in-theory (enable neg sub add mul *-of-2))))

(defthm add-of-mul-and-add-same
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (posp p))
           (equal (add (mul k x p) (add x y p) p)
                  (add (mul (+ 1 k) x p) y p)))
  :hints (("Goal" :in-theory (enable neg sub add mul *-of-2))))

(defthm add-of-add-of-mul-same-negated
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (posp p))
           (equal (add (neg x p) (add (neg (mul k x p) p) y p) p)
                  (add (neg (mul (+ 1 k) x p) p) y p)))
  :hints (("Goal" :in-theory (enable neg sub add mul
                                     *-of-2
                                     acl2::mod-sum-cases))))

(defthm add-of-neg-of-mul-and-add-of-neg-of-mul-same
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp x)
                (integerp y)
                (integerp k1)
                (integerp k2)
                (posp p))
           (equal (add (neg (mul k1 x p) p) (add (neg (mul k2 x p) p) y p) p)
                  (add (neg (mul (+ k1 k2) x p) p) y p)))
  :hints (("Goal" :in-theory (enable neg sub add mul
                                     *-of-2
                                     acl2::mod-sum-cases))))

;may be too strong
(defthm equal-of-neg
  (implies (and (integerp x)
                (natp y)
                (< y p)
                (posp p))
           (equal (equal (neg x p) y)
                  (equal 0 (add x y p))))
  :hints (("Goal" :in-theory (enable neg sub add acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-of-neg
  (implies (and (natp x)
                (< x p)
                (natp y)
                (< y p)
                (posp p))
           (equal (equal 0 (add (neg x p) y p))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable neg sub add acl2::mod-sum-cases))))

(defthm add-bound
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (< (add x y p) p))
  :hints (("Goal" :in-theory (enable add))))

(defthm mul-bound
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (< (mul x y p) p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm sub-bound
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (< (sub x y p) p))
  :hints (("Goal" :in-theory (enable sub))))

(defthm add-of-add-neg-of-mul-same
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (posp p))
           (equal (add x (add (neg (mul k x p) p) y p) p)
                  (add (neg (mul (+ -1 k) x p) p) y p)))
  :hints (("Goal" :in-theory (enable neg sub add mul
                                     *-of-2
                                     acl2::mod-sum-cases))))

(defthm add-of-neg-same-arg2-gen
  (implies (and (integerp x)
                (posp p))
           (equal (add x (neg x p)
                       p)
                  0))
  :hints (("Goal" :in-theory (enable add sub neg))))

;todo: use a :meta rule
(defthm move-neg-rule-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp v)
                (integerp w)
                (posp p))
           (equal (equal (add x (add y (add (neg z p) w p) p) p)
                         v)
                  (and (fep v p)
                       (equal (add x (add y w p) p)
                              (add v z p)))))
  :hints (("Goal" :in-theory (e/d (neg sub add acl2::mod-sum-cases)
                                  (acl2::mod-when-multiple ;for speed
                                   )))))

(defthm sub-rewrite
  (implies (and (rationalp x)
                (rationalp y)
                (posp p))
           (equal (sub x y p)
                  (add x (neg y p) p)))
  :hints (("Goal" :in-theory (enable sub add neg acl2::mod-sum-cases))))

(defthm not-equal-of-add-and-0-same
  (implies (and (integerp x1)
                (<= 0 x1)
                (< x1 p)
                (not (equal x1 0))
                (integerp p)
                (< 2 p)
                (rtl::primep p))
           (not (equal (add x1 x1 p) 0)))
  :hints (("Goal" :in-theory (enable add-same fep))))

(defthm not-equal-of-inv-and-0
  (implies (and (fep a p)
                (not (equal 0 a))
                (rtl::primep p))
           (not (equal 0 (inv a p))))
  :hints (("Goal" :use (:instance inv-correct
                                  (a (mod a p))
                                  (p p))
           :in-theory (e/d (fep inv)
                           (inv-correct)))))

;; Turns 1/a=b into 1=a*b.
(defthm equal-of-inv
  (implies (and (not (equal 0 a))
                (fep a p)
                (rtl::primep p))
           (equal (equal (inv a p) b)
                  (and (equal 1 (mul a b p))
                       (fep b p))))
  :hints (("Goal" :use (:instance mul-of-inv-mul-of-inv
                                  (a a)
                                  (x b)
                                  (p p))
           :in-theory (disable mul-of-inv-mul-of-inv))))

(defthm inv-of-inv
  (implies (and (not (equal 0 a))
                (fep a p)
                (rtl::primep p))
           (equal (inv (inv a p) p)
                  a)))

(defthm mul-of-0
  (equal (mul 0 y p)
         0)
  :hints (("Goal" :in-theory (enable mul))))

;; a cancellation rule
(defthm equal-of-mul-and-mul-same
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (primep p))
           (equal (equal (mul x y p) (mul x z p))
                  (if (equal 0 x)
                      t
                    (equal y z))))
  :hints (("Goal" :use ((:instance mul-of-inv-mul-of-inv (a x) (x y))
                        (:instance mul-of-inv-mul-of-inv (a x) (x z)))
           :in-theory (disable mul-of-inv-mul-of-inv))))

;; Similar to turining (- (* 3 x)) into (* -3 x).
(defthm neg-of-mul-when-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep p)))
                (integerp y)
                (integerp k)
                (posp p))
           (equal (neg (mul k y p) p)
                  (mul (neg k p) y p)))
  :hints (("Goal" :in-theory (e/d (mul neg sub)
                                  (sub-rewrite)))))

;; Solve for z in something like x=yz when x and y are constants.
(defthm equal-of-mul-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (fep y p)
                (fep z p)
                (rtl::primep p))
           (equal (equal x (mul y z p))
                  (and (fep x p)
                       (if (equal 0 y)
                           (equal x 0)
                         (equal (div x y p) z)))))
  :hints (("Goal" :in-theory (enable div))))

(defthm div-of-0-arg1
  (implies (and (integerp p)
                (integerp y))
           (equal (div 0 y p)
                  0))
  :hints (("Goal" :in-theory (enable div))))

(defthm neg-of-0
  (implies (integerp p)
           (equal (neg 0 p)
                  0))
  :hints (("Goal" :in-theory (enable neg sub))))

(defthm mul-of-mod-arg1
  (implies (and (posp p)
                (integerp x)
                (integerp y))
           (equal (mul (mod x p) y p)
                  (mul x y p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-mod-arg2
  (implies (and (posp p)
                (integerp x)
                (integerp y))
           (equal (mul x (mod y p) p)
                  (mul x y p)))
  :hints (("Goal" :in-theory (enable mul))))

;; x=y/z becomes xz=y.
(defthmd equal-of-div
  (implies (and (syntaxp (not (equal z ''0))) ;prevent loops
                (fep z p)
                (fep y p)
                (rtl::primep p))
           (equal (equal x (div y z p))
                  (if (equal 0 z)
                      ;; odd case:
                      (equal x (div y 0 p))
                    (and (fep x p)
                         (equal (mul x z p)
                                (mod y p))))))
  :hints (("Goal"
           :use (:instance mul-of-inv-mul-of-inv (a z) (x y) (p p))
           :in-theory (e/d (div) (mul-of-inv-mul-of-inv)))))
