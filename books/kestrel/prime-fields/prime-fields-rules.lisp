; Prime fields library: additional rules
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "prime-fields")
(local (include-book "support"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/plus-and-minus"))

(local (in-theory (disable acl2::mod-sum-cases))) ;for speed

(in-theory (disable mod)) ;since mod is introduced by some rules below

(defthm add-of-sub-arg1
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (integerp p))
           (equal (add (sub x y p) z p)
                  (add x (add z (neg y p) p) p)))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthm add-of-sub-arg2
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (integerp p))
           (equal (add z (sub x y p) p)
                  (add x (add z (neg y p) p) p)))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthmd equal-of-0-and-add
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal 0 (add y x p))
                  (equal x (sub 0 y p))))
  :hints (("Goal" :in-theory (enable neg add sub acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-safe
  (implies (and (syntaxp (quotep y))
                (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal 0 (add y x p))
                  (equal x (sub 0 y p))))
  :hints (("Goal" :in-theory (enable equal-of-0-and-add))))

(defthm equal-of-add-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (fep x p)
                (fep k1 p)
                (integerp p))
           (equal (equal k1 (add k2 x p))
                  (equal x (sub k1 k2 p))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sub add neg acl2::mod-sum-cases))))

;;less aggressive than the general rule
(defthm add-associative-when-constant
  (implies (syntaxp (quotep x))
           (equal (add (add x y p) z p)
                  (add x (add y z p) p)))
  :hints (("Goal" :in-theory (enable add))))

;; (defthm pow-of-+-of-1
;;   (implies (and (fep a)
;;                 (natp b))
;;            (equal (pow a (+ 1 b))
;;                   (mul a (pow a b))))
;;   :hints (("Goal" :in-theory (enable pow))))

;move?
(defthm divides-of-prime-means-0
  (implies (and (fep x p)
                (posp p))
           (equal (rtl::divides p x)
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable ;rtl::divides
                              fep))))

;move?
(defthm equal-of-0-and-mul
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (equal 0 (mul x y p))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal"
           :use (;primep-of-prime
                 (:instance rtl::euclid
                            (p p)
                            (a x)
                            (b y)))
           :in-theory (enable mul rtl::divides acl2::equal-of-0-and-mod))))

;; Cherry-pick Fermat's Little Theorem
(encapsulate ()
  (local (include-book "../../projects/quadratic-reciprocity/fermat"))
  (local (include-book "../../arithmetic-3/top"))

  (defthm my-fermat-little
    (implies (and (fep a p)
                  (not (equal 0 a))
                  (primep p))
             (equal (pow a (minus1 p) p)
                    1))
    :hints (("Goal" :use ((:instance rtl::fermat
                                     (m a)
                                     (p p)))
             :cases ((equal 0 a))
             :in-theory (e/d (pow-rewrite fep minus1)
                             (expt (:e expt)))))))

(defthm inv-correct
  (implies (and (fep a p)
                (not (equal 0 a))
                (primep p))
           (equal (mul a (inv a p) p)
                  1))
  :hints (("Goal" :in-theory (e/d (inv minus1) (pow-of-+ my-fermat-little))
           :expand (pow a (+ -1 p) p)
           :use (:instance my-fermat-little))))

(defthm inv-correct-alt
  (implies (and (fep a p)
                (not (equal 0 a))
                (primep p))
           (equal (mul (inv a p) a p)
                  1))
  :hints (("Goal" :use ((:instance inv-correct)
                        (:instance mul-commutative
                                   (x a)
                                   (y (inv a p))))
           :in-theory (disable inv-correct))))

;; 2 is in the field iff the prime is bigger than 2.
(defthm fep-of-2
  (equal (fep 2 p)
         (< 2 p))
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-of-prime-minus-1
  (implies (posp p)
           (fep (+ -1 p) p))
  :hints (("Goal" :in-theory (enable fep))))

(defthm mul-of-minus1-becomes-neg
  (implies (fep x p)
           (equal (mul (minus1 p) x p)
                  (neg x p)))
  :hints (("Goal" :in-theory (enable mul neg sub minus1 fep acl2::mod-sum-cases))))



(local
 (defthm +-same
   (equal (+ x x)
          (* 2 x))))

;; x+x becomes 2*x
(defthmd add-same
  (implies (and (fep x p)
                (integerp p))
           (equal (add x x p)
                  (mul 2 x p)))
  :hints (("Goal" :in-theory (enable mul add))))

(defthmd mul-of-2
  (implies (and (fep x p)
                (integerp p))
           (equal (mul 2 x p)
                  (add x x p)))
  :hints (("Goal" :in-theory (enable mul add))))

(theory-invariant (incompatible (:rewrite mul-of-2) (:rewrite add-same)))

(defthm mul-of-mul-of-inv
  (implies (and (fep a p)
                (fep x p)
                (primep p))
           (equal (mul a (mul (inv a p) x p) p)
                  (if (equal 0 a)
                      0
                    x)))
  :hints (("Goal" :use (:instance mul-associative (x a) (y (inv a p)) (z x))
           :in-theory (disable mul-associative
                               MUL-COMMUTATIVE
                               MUL-COMMUTATIVE-2))))

;todo: swap mul args if one is the inv of the other... as a tiebreaker
(defthm mul-of-inv-mul-of-inv
  (implies (and (fep a p)
                (not (equal 0 a))
                (fep x p)
                (primep p))
           (equal (mul (inv a p) (mul a x p) p)
                  x))
  :hints (("Goal" :use (:instance mul-associative (y a) (x (inv a p)) (z x))
           :in-theory (disable mul-associative))))

(defthm add-of-neg-same-arg2
  (equal (add x (neg x p) p)
         0)
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthm add-of-neg-same-arg1
  (equal (add (neg x p) x p)
         0)
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthm add-of-add-of-neg-same
  (implies (posp p)
           (equal (add x (add (neg x p) y p) p)
                  (mod (ifix y) p)))
  :hints (("Goal" :in-theory (enable add sub neg acl2::mod-sum-cases))))

(defthm add-of-neg-and-add-same
  (implies (posp p)
           (equal (add (neg x p) (add x y p) p)
                  (mod (ifix y) p)))
  :hints (("Goal" :in-theory (enable neg add acl2::mod-sum-cases))))

;; If the resulting constant (* x y) is too large, the next rule below will
;; reduce it.
(defthm mul-combine-constants
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

(defthmd mul-combine-constants-alt
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (integerp p))
           (equal (mul x (mul y z p) p)
                  (mul (mul x y p) z p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-constant-reduce-arg1
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (<= p x) ;x is too big
                (integerp x)
                (integerp y)
                (natp p))
           (equal (mul x y p)
                  (mul (mod x p) y p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-same-arg1
  (implies (and (integerp y)
                (posp p))
           (equal (mul p y p)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

;distributivity
(defthm mul-of-add-arg2
  (implies (posp p)
           (equal (mul x (add y1 y2 p) p)
                  (add (mul x y1 p)
                             (mul x y2 p)
                             p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add mul))))

(defthm mul-of-add-arg1
  (implies (posp p)
           (equal (mul (add y1 y2 p) x p)
                  (add (mul y1 x p)
                       (mul y2 x p)
                       p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add mul))))

(defthm mod-of-add
  (equal (mod (add x y p) p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

(defthmd neg-of-*
  (implies (and (integerp x1)
                (integerp x2)
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
  (implies (posp p)
           (equal (mul (neg x p) y p)
                  (neg (mul x y p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul
                              acl2::equal-of-0-and-mod
                              acl2::integerp-of-*-three))))

(defthm mul-of-neg-arg2
  (implies (posp p)
           (equal (mul y (neg x p) p)
                  (neg (mul y x p) p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul
                              acl2::equal-of-0-and-mod
                              acl2::integerp-of-*-three))))

(defthm neg-of-add
  (implies (posp p)
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
  :hints (("Goal" :in-theory (enable expt acl2::mod-of-*-subst-arg2))))

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
                (natp n)
                (posp p))
           (equal (mod (expt (+ (- p) x) n) p)
                  (mod (expt x n) p)))
  :hints (("Goal" :use ((:instance mod-of-expt-of-mod (x x))
                        (:instance mod-of-expt-of-mod (x (+ (- p) x))))
           :in-theory (disable mod-of-expt-of-mod))))

(defthm add-of-mul-and-mul-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp x)
                (integerp k1)
                (integerp k2)
                (posp p))
           (equal (add (mul k1 x p) (mul k2 x p) p)
                  (mul (+ k1 k2) x p)))
  :hints (("Goal" :in-theory (enable add mul))))

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

(defthm mod-of-mul
  (equal (mod (mul x y p) p)
         (mul x y p))
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
  :hints (("Goal" :in-theory (e/d (neg add mul
                                       acl2::mod-sum-cases
                                       *-of-2)
                                  (+-same)))))

(defthm add-of-add-same
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (equal (add x (add x y p) p)
                  (add (mul 2 x p) y p)))
  :hints (("Goal" :in-theory (e/d (neg sub add mul *-of-2)
                                  (+-same)))))

(defthm add-of-add-of-mul-same
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (posp p))
           (equal (add x (add (mul k x p) y p) p)
                  (add (mul (+ 1 k) x p) y p)))
  :hints (("Goal" :in-theory (e/d (neg sub add mul)
                                  (+-same)))))

;; k*x + x + y becomes (k+1)*x + y
;; We could restrict this to when k is a constant
(defthm add-of-mul-and-add-same
  (equal (add (mul k x p) (add x y p) p)
         (add (mul (+ 1 (ifix k)) x p) y p))
  :hints (("Goal" :in-theory (enable neg sub add mul))))

;; TODO: When k is a constant, perhaps we should pull the negation in (but how
;; should we normalize constants?)
(defthm add-of-add-of-mul-same-negated
  (equal (add (neg x p) (add (neg (mul k x p) p) y p) p)
         (add (neg (mul (+ 1 (ifix k)) x p) p) y p))
  :hints (("Goal" :in-theory (enable neg sub add mul
                                     acl2::mod-sum-cases))))

(defthm add-of-neg-of-mul-and-add-of-neg-of-mul-same
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp k1)
                (integerp k2)
                (posp p))
           (equal (add (neg (mul k1 x p) p) (add (neg (mul k2 x p) p) y p) p)
                  (add (neg (mul (+ k1 k2) x p) p) y p)))
  :hints (("Goal" :in-theory (enable neg sub add mul
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

(defthm equal-of-0-and-add-of-neg-arg1
  (implies (and (fep x p)
                (fep y p)
                (posp p))
           (equal (equal 0 (add (neg x p) y p))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable neg sub add acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-of-neg-arg1-gen
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (equal (equal 0 (add (neg x p) y p))
                  ;; Usually the mods will get dropped:
                  (equal (mod x p) (mod y p))))
  :hints (("Goal" :in-theory (enable neg sub add acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-of-neg-arg2
  (implies (and (fep x p)
                (fep y p)
                (posp p))
           (equal (equal 0 (add x (neg y p) p))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable add neg sub acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-of-neg-arg2-gen
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (equal (equal 0 (add x (neg y p) p))
                  ;; Usually the mods will get dropped:
                  (equal (mod x p) (mod y p))))
  :hints (("Goal" :in-theory (enable add neg sub acl2::mod-sum-cases))))

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
                                     acl2::mod-sum-cases))))

(defthm add-of-neg-same-arg2-gen
  (implies (and (integerp x)
                (posp p))
           (equal (add x (neg x p)
                       p)
                  0))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthmd equal-of-<-and-fep
  (implies (natp x)
           (equal (equal (< x p) (fep x p))
                  t))
  :hints (("Goal" :in-theory (enable fep))))

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
  :hints (("Goal" :in-theory (enable mul neg sub))))

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
  (equal (div 0 y p)
         0)
  :hints (("Goal" :in-theory (enable div))))

(defthm mul-of-mod-arg1
  (equal (mul (mod x p) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-mod-arg2
  (equal (mul x (mod y p) p)
         (mul x y p))
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

;gen?
(defthm mul-of--1-becomes-neg
  (implies (and (integerp x)
                (posp p))
           (equal (mul -1 x p)
                  (neg x p)))
  :hints (("Goal" :in-theory (enable mul neg sub))))

;; p-1 represents -1.
(defthm mul-of--1-becomes-neg-alt
  (Implies (and (posp p)
                (integerp x))
           (equal (mul (+ -1 p) x p)
                  (neg x p)))
  :hints (("Goal" :in-theory (enable mul neg sub ACL2::MOD-SUM-CASES))))



;; x=x*y becomes 1=y.  A cancellation rule.
(defthm equal-of-mul-same-arg1
  (implies (and (fep x p)
                (fep y p)
                (rtl::primep p))
           (equal (equal x (mul x y p))
                  (if (equal 0 x)
                      t
                    (equal 1 y))))
  :hints (("Goal" :cases ((equal x 0))
           :use (:instance equal-of-mul-and-mul-same
                                  (x (inv x p))
                                  (y x)
                                  (z (mul x y p))
                                  (p p)
                                  )
           :in-theory (disable equal-of-mul-and-mul-same))))

;; x=y*x becomes 1=y.  A cancellation rule.
(defthm equal-of-mul-same-arg2
  (implies (and (fep x p)
                (fep y p)
                (rtl::primep p))
           (equal (equal x (mul y x p))
                  (if (equal 0 x)
                      t
                    (equal 1 y))))
  :hints (("Goal" :use (:instance equal-of-mul-same-arg1)
           :in-theory (disable equal-of-mul-same-arg1))))

;; Kept disabled
(defthmd equal-of-mul-cancel
  (implies (and (fep y p)
                (fep z p)
                (rtl::primep p))
           (equal (equal x (mul y z p))
                  (and (fep x p)
                       (if (equal 0 z)
                           (equal x 0)
                         (equal (div x z p) y)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable div))))

(defthm equal-of-neg-and-neg
  (implies (and (fep x1 p)
                (fep x2 p)
                (integerp p))
           (equal (equal (neg x1 p) (neg x2 p))
                  (equal x1 x2)))
  :hints (("Goal" :in-theory (enable neg))))

(defthm equal-of-neg-and-neg-strong
  (equal (equal (neg x1 p) (neg x2 p))
         (equal (mod (ifix x1) (pos-fix p))
                (mod (ifix x2) (pos-fix p))))
  :hints (("Goal" :in-theory (enable neg sub))))

;; Since some of the string rules introduce mod
(defthm mod-when-fep
  (implies (fep x p)
           (equal (mod x p)
                  x))
  :hints (("Goal" :cases ((rationalp p))
           :in-theory (enable fep))))

(defthm mul-of-1-arg1-gen
  (equal (mul 1 x p)
         (mod (ifix x) (pos-fix p)))
  :hints (("Goal" :in-theory (enable mul))))

;; (* -1 y) becomes (neg y)
(defthm mul-becomes-neg
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (equal x (+ -1 p))
                (posp p))
           (equal (mul x y p)
                  (neg y p)))
  :hints (("Goal" :in-theory (enable mul neg sub acl2::mod-sum-cases))))

(defthmd integerp-when-fep
  (implies (fep x p)
           (integerp x)))

;; Changes inner + to add
(defthmd add-of-+-arg2
  (implies (and (integerp y1)
                (integerp y2))
           (equal (add x (+ y1 y2) p)
                  (add x (add y1 y2 p) p)))
  :hints (("Goal" :in-theory (enable add))))

;; Changes inner + to add
(defthmd add-of-+-arg1
  (implies (and (integerp y1)
                (integerp y2))
           (equal (add (+ y1 y2) x p)
                  (add (add y1 y2 p) x p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-same-arg1-arg3
  (implies (posp p)
           (equal (add p x p)
                  (mod (ifix x) p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-same-arg2-arg3
  (implies (posp p)
           (equal (add x p p)
                  (mod (ifix x) p)))
  :hints (("Goal" :in-theory (enable add))))

;move
(defthm pow-of-mod-arg1
  (equal (pow (mod x p) n p)
         (pow x n p))
  :hints (("Goal" :in-theory (enable pow))))

;move
(local
 (defthm mod-of-*-of-mod-arg3
   (implies (and (integerp x)
                 (integerp y)
                 (integerp z)
                 (integerp p))
            (equal (mod (* x y (mod z p)) p)
                   (mod (* x y z) p)))
   :hints (("Goal" :use (:instance acl2::mod-of-*-of-mod
                                   (z p)
                                   (x (* x y))
                                   (y z))
            :in-theory (disable acl2::mod-of-*-of-mod)))))

(defthmd pow-of-*-arg1
  (implies (and (posp p)
                (integerp x)
                (integerp y))
           (equal (pow (* x y) n p)
                  (if (not (posp n))
                      1
                    (mod (* (pow x n p)
                            (pow y n p))
                         p))))
  :hints (("Goal" :in-theory (enable pow mul))))

(defthm pow-of-0-arg1
  (equal (pow 0 n p)
         (if (posp n)
             0
           1 ; 0^0 = 1
           ))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-when-not-integerp-arg1-cheap
  (implies (not (integerp x))
           (equal (pow x n p)
                  (pow 0 n p)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-when-not-integerp-arg2-cheap
  (implies (not (integerp n))
           (equal (pow x n p)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pow))))

(defthmd pow-of-mul-arg1
  (implies (posp p)
           (equal (pow (mul x y p) n p)
                  (if (not (posp n))
                      1
                    (mul (pow x n p)
                         (pow y n p)
                         p))))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable mul
                              pow-of-*-arg1))))

;move
(defthm minus1-linear
  (= (minus1 p) (+ -1 p))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable minus1))))

;; todo: consider enabling
(defthmd inv-of-mul
  (implies (and (integerp p)
                (< 1 p))
           (equal (inv (mul x y p) p)
                  (mul (inv x p) (inv y p) p)))
  :hints (("Goal" :in-theory (enable inv POW-OF-MUL-ARG1))))

(defthm equal-of-0-and-add-of-neg
  (implies (and (fep x p)
                (fep y p)
                (posp p))
           (equal (equal 0 (add (neg x p) y p))
                  (equal x y))))

;; Not sure which form is better
(defthmd add-of-neg-and-neg
  (implies (posp p)
           (equal (add (neg x p) (neg y p) p)
                  (neg (add x y p) p))))

;; In case we only want to move constants to the front
(defthm add-commutative-when-constant
  (implies (syntaxp (and (quotep k)
                         ;; avoid loops:
                         (not (quotep x))))
           (equal (add x k p)
                  (add k x p))))

;; In case we only want to move constants to the front
(defthm add-commutative-2-when-constant
  (implies (syntaxp (and (quotep k)
                         ;; avoid loops:
                         (not (quotep x))))
           (equal (add x (add k y p) p)
                  (add k (add x y p) p))))
