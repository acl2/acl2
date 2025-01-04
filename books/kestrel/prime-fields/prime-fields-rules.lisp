; Prime fields library: additional rules
;
; Copyright (C) 2019-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "prime-fields")
(include-book "../arithmetic-light/ifix") ; since some rules introduce ifix
(local (include-book "support"))
(local (include-book "../number-theory/divides"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/plus-and-minus"))

(local (in-theory (disable acl2::mod-sum-cases))) ;for speed

(in-theory (disable mod)) ;since mod is introduced by some rules below

(defthm add-of-sub-arg1
  (equal (add (sub x y p) z p)
         (add x (add z (neg y p) p) p))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthm add-of-sub-arg2
  (equal (add z (sub x y p) p)
         (add x (add z (neg y p) p) p))
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

(defthm equal-of-add-combine-constants-alt
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (fep x p)
                (fep k1 p)
                (integerp p))
           (equal (equal (add k2 x p) k1)
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

;move or drop?
(defthm divides-of-prime-means-0
  (implies (and (fep x p)
                (integerp p))
           (equal (divides p x)
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable ;divides
                              fep))))

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

;distributivity
(defthm mul-of-add-arg2
  (implies (posp p)
           (equal (mul x (add y1 y2 p) p)
                  (add (mul x y1 p)
                             (mul x y2 p)
                             p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add mul))))

;distributivity
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

(defthm mul-of-neg-arg1
  (equal (mul (neg x p) y p)
         (neg (mul x y p) p))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul
                              acl2::equal-of-0-and-mod
                              acl2::integerp-of-*-three))))

(defthm mul-of-neg-arg2
  (equal (mul y (neg x p) p)
         (neg (mul y x p) p))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable neg add sub mul
                              acl2::equal-of-0-and-mod
                              acl2::integerp-of-*-three))))

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
                (integerp p))
           (equal (equal (neg x p) y)
                  (equal 0 (add x y p))))
  :hints (("Goal" :in-theory (enable neg sub add acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-of-neg-arg1
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
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
                (integerp p))
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
  (implies (posp p)
           (< (add x y p) p))
  :hints (("Goal" :in-theory (enable add))))

(defthm sub-bound
  (implies (posp p)
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
                (< 2 p)
                (primep p))
           (not (equal (add x1 x1 p) 0)))
  :hints (("Goal" :in-theory (enable add-same fep))))

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
  (implies (syntaxp (and (quotep k)
                         (quotep p)))
           (equal (neg (mul k y p) p)
                  (mul (neg k p) y p)))
  :hints (("Goal" :in-theory (enable mul neg sub))))

;; Solve for z in something like x=yz when x and y are constants.
(defthm equal-of-mul-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (fep y p)
                (fep z p)
                (primep p))
           (equal (equal x (mul y z p))
                  (and (fep x p)
                       (if (equal 0 y)
                           (equal x 0)
                         (equal (div x y p) z)))))
  :hints (("Goal" :in-theory (enable div))))

(defthm equal-of-mul-constants-alt
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (fep y p)
                (fep z p)
                (primep p))
           (equal (equal (mul y z p) x)
                  (and (fep x p)
                       (if (equal 0 y)
                           (equal x 0)
                         (equal (div x y p) z)))))
  :hints (("Goal" :in-theory (enable div))))

;; x=y/z becomes xz=y.
(defthmd equal-of-div
  (implies (and (syntaxp (not (equal z ''0))) ;prevent loops
                (fep z p)
                (fep y p)
                (primep p))
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

(defthmd equal-of-div-alt
  (implies (and (not (equal 0 z)) ;exclude odd case
                (fep z p)
                (fep y p)
                (primep p))
           (equal (equal x (div y z p))
                  (and (fep x p)
                       (equal (mul x z p)
                              (mod y p)))))
  :hints (("Goal" :in-theory (enable equal-of-div))))

(defthmd equal-of-0-and-div
  (implies (and (syntaxp (not (equal z ''0))) ;prevent loops
                (fep z p)
                (fep y p)
                (primep p))
           (equal (equal 0 (div y z p))
                  (if (equal 0 z)
                      ;; odd case (usually t unless p=2):
                      (equal 0 (div y 0 p))
                    (equal 0 (mod y p)))))
  :hints (("Goal" :in-theory (enable equal-of-div)))
  )

(defthm div-of-0-arg2
  (implies (and (primep p)
                (integerp x))
           (equal (div x 0 p)
                  0))
  :hints (("Goal" :in-theory (enable div))))

;; for all primes other than 2
(defthmd equal-of-0-and-div-special
  (implies (and (fep z p)
                (fep y p)
                (primep p)
                (< 2 p))
           (equal (equal 0 (div y z p))
                  (or (equal 0 z)
                      (equal 0 y))))
  :hints (("Goal" :in-theory (enable equal-of-div))))

;gen?
;; In this version, the constant is actually -1.
(defthm mul-of--1-becomes-neg
  (implies (posp p)
           (equal (mul -1 x p)
                  (neg x p)))
  :hints (("Goal" :in-theory (enable mul neg sub))))

;; (* -1 y) becomes (neg y)
;; In this version, the constant is p-1.
(defthm mul-of--1-becomes-neg-alt
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (equal x (+ -1 p))
                (posp p))
           (equal (mul x y p)
                  (neg y p)))
  :hints (("Goal" :in-theory (enable mul neg sub acl2::mod-sum-cases))))

;; p-1 represents -1.
;subsumed by mul-of-+-same-arg2
(defthmd mul-of--1-becomes-neg-alt-other
  (implies (posp p)
           (equal (mul (+ -1 p) x p)
                  (neg x p)))
  :hints (("Goal" :in-theory (enable mul neg sub ACL2::MOD-SUM-CASES))))



;; x=x*y becomes 1=y.  A cancellation rule.
(defthm equal-of-mul-same-arg1
  (implies (and (fep x p)
                (fep y p)
                (primep p))
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
                (primep p))
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
                (primep p))
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

;; Not sure which form is better
(defthmd add-of-neg-and-neg
  (equal (add (neg x p) (neg y p) p)
         (neg (add x y p) p)))

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

;; Commutes the neg forward, which we may occasionally want
; warning: can loop if there are multiple negs
(defthmd add-of-neg-commute
  (equal (add x (neg y p) p)
         (add (neg y p) x p)))

;; Commutes the neg forward, which we may occasionally want
; warning: can loop if there are multiple negs
(defthmd add-of-neg-commute-2
  (equal (add x (add (neg y p) z p) p)
         (add (neg y p) (add x z p) p)))

(defthm equal-of-add-same-arg2
  (implies (and (posp p)
                (natp x)
                (integerp y))
           (equal (equal x (add y x p))
                  (and (fep x p)
                       (equal 0 (mod y p)))))
  :hints (("Goal" :in-theory (enable add acl2::mod-sum-cases))))

(defthm neg-of-2
  (implies (integerp x)
           (equal (neg x 2)
                  (mod x 2)))
  :hints (("Goal" :in-theory (enable neg))))

;can loop with other rules?
(defthmd mul-of-constant-normalize-to-fep
  (implies (and (syntaxp (and (quotep x)
                              (quotep p)))
                (not (fep x p)) ; gets computed
                ;; these two hyps ensure that the mod will return a fep:
                (integerp x) ; may be needed to prevent loops
                (posp p) ; may be needed to prevent loops
                )
           (equal (mul x y p)
                  ;; the (mod x p) gets computed:
                  (mul (mod x p) y p))))

;; or just distribute
(defthm mul-of-add-of-mul-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (posp p))
           (equal (mul k1 (add (mul k2 x p) y p) p)
                  (add (mul (mul k1 k2 p) x p)
                       (mul k1 y p)
                       p))))

(defthm equal-of-0-and-add-of-add-of-add-of-neg-lemma
  (implies (and (fep w p)
                (integerp p))
           (equal (equal 0 (add x (add y (add z (neg w p) p) p) p))
                  (equal w (add x (add y z p) p)))))

(defthm equal-of-0-and-add-of-add-of-add-of-neg-lemma-alt
  (implies (and (fep w p)
                (integerp p))
           (equal (equal 0 (add x (add y (add (neg w p) z p) p) p))
                  (equal w (add x (add y z p) p)))))

(defthm equal-of-0-and-add-of-add-of-neg-lemma
  (implies (and (fep w p)
                (integerp p))
           (equal (equal 0 (add x (add (neg w p) y p) p))
                  (equal w (add x y p)))))

(defthm equal-of-constant-and-add-of-neg-arg1
  (implies (and (syntaxp (quotep k))
                ;(fep k p)
                (fep x p)
                (integerp y) ;(fep y p)
                (posp p))
           (equal (equal k (add (neg x p) y p))
                  (and (fep k p)
                       (equal x (add (- k) y p)))))
  :hints (("Goal" :in-theory (enable add neg acl2::mod-sum-cases))))

(defthm equal-of-constant-and-add-of-neg-arg2
  (implies (and (syntaxp (quotep k))
                (fep k p)
                (fep x p)
                (fep y p)
                (posp p))
           (equal (equal k (add y (neg x p) p))
                  (equal x (add (- k) y p))))
  :hints (("Goal" :in-theory (enable add neg acl2::mod-sum-cases))))

(defthm equal-of-add-of-neg
  (implies (posp p)
           (equal (equal x (add y (neg z p) p))
                  (and (fep x p)
                       (equal (add x z p) (mod (ifix y) p)))))
  :hints (("Goal" :in-theory (enable add neg acl2::mod-sum-cases))))

;;  This version has no mod or ifix in the RHS
(defthm equal-of-add-of-neg-simple
  (implies (and (fep y p)
                (integerp p))
           (equal (equal x (add y (neg z p) p))
                  (and (fep x p)
                       (equal (add x z p) y))))
  :hints (("Goal" :in-theory (enable add neg acl2::mod-sum-cases))))

;; For when the constant is negative.  Not sure which normal form is better.
(defthmd mul-when-constant-becomes-neg-of-mul
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (natp p))
           (equal (mul k x p)
                  (neg (mul (neg k p) x p) p)
                  ))
  :hints (("Goal" :in-theory (enable mul neg sub))))

;rename
;;todo: use an axe-bind-free rule?
(defthm move-negation-1
  (implies (and (fep lhs p) ;gen?
                (integerp x2)
                (integerp x3)
                (integerp y)
                (posp p))
           (equal (equal lhs (add x1 (add x2 (add (neg y p) x3 p) p) p))
                  (equal (add lhs y p) (add x1 (add x2 x3 p) p))))
  :hints (("Goal" :use (:instance equal-of-add-of-neg
                                  (x lhs)
                                  (z y)
                                  (y (add x1 (add x2 x3 p) p)))
           :in-theory (disable equal-of-add-of-neg))))

(defthmd add-of---arg1-fixed
  (implies (and (syntaxp (not (quotep x))) ;defeat acl2 matching (- x) with a constant
                (integerp x)
                (integerp y))
           (equal (add (- x) y p)
                  (add (neg x p) y p)))
  :hints (("Goal" :in-theory (enable neg add))))

(defthmd add-of---arg2-fixed
  (implies (and (syntaxp (not (quotep y))) ;defeat acl2 matching (- y) with a constant
                (integerp x)
                (integerp y))
           (equal (add x (- y) p)
                  (add x (neg y p) p)))
  :hints (("Goal" :in-theory (enable neg add))))

(defthm add-subst-constant-arg1
  (implies (and (syntaxp (not (quotep x))) ;prevent loops
                (equal (mod x p) free)
                (syntaxp (quotep free)) ; put in only constants
                )
           (equal (add x y p)
                  (add free y p))))

(defthm add-subst-constant-arg2
  (implies (and (syntaxp (not (quotep y))) ;prevent loops
                (equal (mod y p) free)
                (syntaxp (quotep free)) ; put in only constants
                )
           (equal (add x y p)
                  (add x free p))))

;gen the -1
(defthm add-of-+-of--1
  (equal (add x (+ -1 p) p)
         (add x -1 p))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-+-of-p-arg2
  (equal (add x (+ y p) p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of---of-p-arg2
  (implies (posp p)
           (equal (add x (- p) p)
                  (mod (ifix x) p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of---same-arg2
  (equal (add k (- k) p)
         0)
  :hints (("Goal" :in-theory (enable add))))

(defthm mul-of-+-same-arg2
  (equal (mul (+ x p) y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul))))

;distributivity
;but often sub will be enabled
(defthm mul-of-sub-arg1
  (implies (posp p)
           (equal (mul (sub y1 y2 p) x p)
                  (sub (mul y1 x p)
                       (mul y2 x p)
                       p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable sub))))

;distributivity
;but often sub will be enabled
(defthm mul-of-sub-arg2
  (implies (posp p)
           (equal (mul x (sub y1 y2 p) p)
                  (sub (mul x y1 p)
                       (mul x y2 p)
                       p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable sub))))

(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "kestrel/number-theory/primes" :dir :system))

(defthm pow-of-neg
  (implies (and (posp p)
                (natp n))
           (equal (pow (neg x p) n p)
                  (if (evenp n)
                      (pow x n p)
                    (neg (pow x n p) p))))
  :hints (("Goal" :in-theory (e/d (pow) (PFIELD::EQUAL-OF-NEG)))))

(defthm inv-of-neg
  (implies (primep p)
           (equal (inv (neg x p) p)
                  (neg (inv x p) p)))
  :hints (("Goal" :in-theory (enable inv pfield::minus1))))

;; x * (y / x) becomes y
(defthm mul-of-div-same-arg2
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (mul x (div y x p) p)
                  (if (equal x 0)
                      0
                    y)))
  :hints (("Goal" :in-theory (enable div))))

;; x / (x / y) becomes y
(defthm div-of-div-same-arg1
  (implies (and (fep x p)
                (fep y p)
                (primep p)
                (< 2 p) ;gen?
                )
           (equal (div x (div x y p) p)
                  (if (equal x 0)
                      0
                    y)))
  :hints (("Goal" :in-theory (enable div pfield::inv-of-mul))))

;; (x * y) / y  becomes x
(defthm div-of-mul-same-arg1-arg2
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (div (mul x y p) y p)
                  (if (equal y 0)
                      0
                    x)))
  :hints (("Goal" :in-theory (enable div))))

;; (y * x) / y becomes x
(defthm div-of-mul-same-arg1-arg1
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (div (mul y x p) y p)
                  (if (equal y 0)
                      0
                    x)))
  :hints (("Goal" :in-theory (enable div))))

;somewhat specialized
;; It may be better to lift the neg out of the div
(defthmd div-of-neg-arg1-move-to-arg2
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (div (neg x p) y p)
                  (div x (neg y p) p)))
  :hints (("Goal" :in-theory (enable div))))

(defthm add-of-mul-of-constant-same-arg1
  (implies (and (syntaxp (quotep k))
                (integerp k))
           (equal (add (mul k x p) x p)
                  (mul (+ 1 k) x p)))
  :hints (("Goal" :in-theory (enable mul add acl2::pos-fix))))

(defthm add-of-mul-of-constant-same-arg2
  (implies (and (syntaxp (quotep k))
                (integerp k))
           (equal (add x (mul k x p) p)
                  (mul (+ 1 k) x p)))
  :hints (("Goal" :in-theory (enable mul add acl2::pos-fix))))
