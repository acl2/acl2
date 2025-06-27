; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "support")
(include-book "projects/poseidon/rate-2-alpha-17" :dir :system) ;spec, reduce?


(acl2::defopeners poseidon::absorb)
(acl2::defopeners poseidon::squeeze)
(acl2::defopeners acl2::all-len-equal-p)
(acl2::defopeners pfield::fe-list-listp)
(acl2::defopeners acl2::nat-list-fix$inline)
(acl2::defopeners poseidon::full-rounds)
(acl2::defopeners poseidon::partial-rounds)
(acl2::defopeners poseidon::add-round-constants)
(acl2::defopeners poseidon::mix-layer)
(acl2::defopeners acl2::nat-list-fix$inline)
(acl2::defopeners poseidon::dot-product)
(acl2::defopeners poseidon::sub-words-full)
(acl2::defopeners pow :disable t)
(acl2::defopeners acl2::chars=>nats)
(acl2::defopeners acl2::lendian=>nat)

(acl2::def-constant-opener pfield::fe-list-listp)
(acl2::def-constant-opener pfield::fe-listp)

(defthmd not-<-of-add-and-0
  (not (< (add x y p) 0)))

(defthm integerp-when-fep-special
  (implies (fep x 8444461749428370424248824938781546531375899335154063827935233455917409239041)
           (integerp x)))

(defthm not-<-of-0-when-fep-special
  (implies (fep x 8444461749428370424248824938781546531375899335154063827935233455917409239041)
           (not (< x 0))))

(defthmd mul-of-same-becomes-pow
  (implies (posp p)
           (equal (mul x x p)
                  (pow x 2 p)))
  :hints (("Goal" :expand (pow x 2 p)
           :in-theory (enable pow))))

;; (defthm pow-of-+-gen
;;   (implies (and (fep a p)
;;                 (integerp b)
;;                 ;(<= b c)
;;                 (natp c)
;;                 (< 1 p)
;;                 (integerp p))
;;            (equal (pow a (+ b c) p)
;;                   (mul (pow a b p)
;;                        (pow a c p)
;;                        p)))
;;   :hints (("Goal" :in-theory (enable pow))))

;move
(defthm equal-of-inv-and-0
  (implies (and (fep x p)
                (primep p))
           (equal (equal (inv x p) 0)
                  (equal 0 x))))

(defthm equal-of-1-and-div
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (equal 1 (div x y p))
                  (if (equal 0 y)
                      nil
                    (equal x y))))
  :hints (("Goal" :in-theory (enable div
                                     pfield::equal-of-mul-cancel))))

(defthm div-of-mul-arg1-arg2
  (implies (and (fep x p)
                (fep y p)
                (primep p))
           (equal (div (mul x y p) z p)
                  (mul x (div y z p) p)))
  :hints (("Goal" :in-theory (enable div))))

(defthm pow-of-+-of--
  (implies (and (fep x p)
;                (not (equal x 0))
                (integerp b)
                (<= b c)
                (natp c)
                (natp b)
;                (< 1 p)
                (primep p)
                (integerp p))
           (equal (pow x (+ (- b) c) p)
                  (if (equal 0 x)
                      (if (posp (+ (- b) c))
                          0
                        1)
                  (div (pow x c p)
                       (pow x b p)
                       p))))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-pow-arg1
  (implies (and (fep x p)
                (primep p)
                (natp n1)
                (natp n2))
           (equal (pow (pow x n1 p) n2 p)
                  (pow x (* n1 n2) p)))
  :hints (("subgoal *1/4" :expand (pow x n1 p))
          ("Goal" ;:expand (pow x (* n1 n2) p)
           :in-theory (e/d ((:i pow)
                            pfield::pow-of-mul-arg1
                            ) ((:d pow)
                            pfield::pow-unroll ;todo
                            )))))

(defthmd mul-of-pow-same-arg2
  (implies (natp n)
           (equal (mul x (pow x n p) p)
                  (pow x (+ 1 n) p)))
  :hints (("Goal" :in-theory (enable pow))))

(defthmd mul-of-pow-same-arg1
  (implies (natp n)
           (equal (mul (pow x n p) x p)
                  (pow x (+ 1 n) p)))
  :hints (("Goal" :in-theory (enable pow))))

;; rules to boil away the type assumption after solving:
(defthm pfield::fe-listp-of-append-with-key
  (equal (fe-listp (acl2::append-with-key key x y)
                   p)
         (and (fe-listp (true-list-fix x)
                        p)
              (fe-listp y p)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))


(defthm mul-of-add-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep p)))
                (posp p))
           (equal (mul k1 (add k2 x p) p)
                  (add (mul k1 k2 p)
                       (mul k1 x p)
                       p))))

;; hack: need more general way to sort addends -- new syntaxp function?
(defthm add-combine-constant-factors-3
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (posp p))
           (equal (add (mul k1 x p) (add y (add z (mul k2 x p) p) p) p)
                  (add (mul (add k1 k2 p) x p)
                       (add y z p)
                       p))))

(defthm add-combine-constant-factors-3-extra
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (posp p))
           (equal (add (mul k1 x p) (add y (add z (add (mul k2 x p) w p) p) p) p)
                  (add (mul (add k1 k2 p) x p)
                       (add y
                            (add z w p)
                            p)
                       p))))

;; hack: need more general way to sort addends -- new syntaxp function?
(defthm add-combine-constant-factors-2
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (posp p))
           (equal (add (mul k1 x p) (add y (mul k2 x p) p) p)
                  (add (mul (add k1 k2 p) x p)
                       y
                       p))))

(defthm add-combine-constant-factors-2-extra
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (posp p))
           (equal (add (mul k1 x p) (add y (add (mul k2 x p) w p) p) p)
                  (add (mul (add k1 k2 p) x p)
                       (add y
                            w
                            p)
                       p))))

(defthm mul-of-constant-and-add
  (implies (and (syntaxp (quotep k))
                (posp p))
           (equal (mul k (add x y p) p)
                  (add (mul k x p)
                       (mul k y p)
                       p)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add mul))))

;; restricted case where we want to multiply constants through adds
(defthm helper0
  (implies (posp p)
           (equal (add (mul k1 (add (mul k11 x p) y p) p)
                       (mul k2 (add (mul k21 x p) z p) p)
                       p)
                  (add (mul (add (mul k1 k11 p) (mul k2 k21 p) p) x p)
                       (add (mul k1 y p)
                            (mul k2 z p)
                            p)
                       p))))

(defthm helper0-extra
  (implies (posp p)
           (equal (add (mul k1 (add (mul k11 x p) y p) p)
                       (add (mul k2 (add (mul k21 x p) z p) p)
                            extra
                            p)
                       p)
                  (add (mul (add (mul k1 k11 p) (mul k2 k21 p) p) x p)
                       (add (mul k1 y p)
                            (add (mul k2 z p)
                                 extra
                                 p)
                            p)
                       p))))
