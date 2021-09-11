; Another book about the built-in function mod.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: This book could use some cleaning up.

(include-book "mod")
(local (include-book "divides"))
(local (include-book "times"))
(local (include-book "floor"))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;to prove mod-expt-mod, mod-bound, etc.
(local (include-book "expt"))
(local (include-book "expt2"))
(local (include-book "times-and-divides"))
(local (include-book "times"))
(local (include-book "plus-and-minus"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;fixme SEE this-needs-to-be-added-to-quotient-remainder-lemmas

;;              (defthm mod-hack
;;                (implies (and (integerp x)
;; ;                (integerp (/ n 2))
;;                              (integerp y))
;;                         (equal (MOD (* X (MOD Y 2147483648)) 2)
;;                                (MOD (* X Y) 2))))

;(local (in-theory (disable MOD-X-I*J-OF-POSITIVES))) ;looped

(local (in-theory (disable equal-of-*-2-of-floor-of-2-same)))

;rename
(defthm mod-expt-mod
  (implies (posp n)
           (equal (mod (mod a (expt 2 n)) 2)
                  (mod a 2)))
  :hints (("Goal" :cases ((not (acl2-numberp a))
                          (rationalp a))
           :in-theory (disable ;DIVISIBILITY-IN-TERMS-OF-FLOOR
                       mod-cancel))))

;gross proof? use a bound lemma?
(defthm integerp-of-*-of-/-and-mod
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (integerp (* (/ y) (mod x y)))
                  (equal 0 (mod x y)))))

(defthm mod-non-negative-constant
  (implies (and (syntaxp (quotep y))
                (< 0 y)
                (rationalp y)
                (rationalp x))
           (not (< (mod x y) 0)))
  :hints (("Goal" :in-theory (enable floor)
           :cases ((rationalp x)))))

(defthm mod-non-negative-constant-gen
  (implies (and (syntaxp (and (quotep y) (quotep k)))
                (<= k 0)
                (< 0 y)
                (rationalp y)
                (rationalp x))
           (not (< (mod x y) k)))
  :hints (("Goal" :in-theory (enable floor)
           :cases ((rationalp x)))))

(defthm mod-non-negative-constant-pos-rewrite
  (implies (and (syntaxp (quotep y))
                (< 0 y)
                (rationalp y)
                (rationalp x))
           (equal (< 0 (mod x y))
                  (not (equal 0 (mod x y))))))

(local (include-book "floor")) ;move?!



(local (in-theory (disable mod-minus)))

(defthm mod-of-mod-of-expt-of-2-and-2
  (implies (and ;(natp size)
                (integerp x)
                )
           (equal (mod (mod x (expt 2 size)) 2)
                  (if (zp size)
                      0
                    (mod x 2)))))

;just a special case..
(defthm mod-of-mod-2-expt-2
  (implies (and (rationalp x)
                (posp n))
           (equal (mod (mod x 2) (expt 2 n))
                  (mod x 2))))

(defthmd <-of-mod
  (implies (and (<= y k)
                ;(rationalp k)
                (rationalp x) ;why?
 ;               (<= 0 x)
;                (posp y)
                (< 0 y)
                (rationalp y)
                )
           (< (mod x y) k)))

(defthm mod-of-*-of-same-2
  (implies (integerp (* y z))
           (equal (mod (* y x z) x)
                  0))
  :hints (("Goal" :cases ((equal x 0)))))

(defthm mod-of-mod-when-mult-cheap
  (implies (and (integerp (* y1 (/ y2)))
                (rationalp y1)
                (rationalp y2)
                (not (equal 0 y2)))
           (equal (mod (mod x y1) y2)
                  (mod x y2)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil)))
  :hints (("Goal" :use (:instance mod-of-mod-when-mult)
           :in-theory (disable mod-of-mod-when-mult))))

(defthm +-of-mod-and-*-of-floor-same
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (+ (mod x y) (* y (floor x y)))
                  x)))

(defthmd mod-of-+-when-mult-arg1
  (implies (and (integerp (/ x1 y))
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (mod (+ x1 x2) y)
                  (if (equal y 0)
                      (+ x1 x2)
                    (mod x2 y)))))

(defthmd mod-of-+-when-mult-arg1-alt
  (implies (and (equal 0 (mod x1 y))
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (mod (+ x1 x2) y)
                  (if (equal y 0)
                      (+ x1 x2)
                    (mod x2 y)))))

(defthm mod-of-+-when-mult-arg1-alt-cheap
  (implies (and (equal 0 (mod x1 y))
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (mod (+ x1 x2) y)
                  (if (equal y 0)
                      (+ x1 x2)
                    (mod x2 y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil))))

(defthm floor-when-mod-0-cheap
  (implies (and (equal 0 (mod x y))
                (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (floor x y)
                  (/ x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm equal-of-0-and-mod-of--
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal y 0)))
           (equal (equal 0 (mod (- x) y))
                  (equal 0 (mod x y))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-+-subst-constant-arg1
 (implies (and (equal (mod x p) free)
               (syntaxp (and (quotep free)
                             (not (quotep x))))
               (integerp y)
               (integerp x)
               ;; (rationalp free)
               (integerp p)
               (< 0 p))
          (equal (mod (+ x y) p)
                 (mod (+ free y) p))))

(defthm mod-of-+-subst-constant-arg2
  (implies (and (equal (mod x p) free)
                (syntaxp (and (quotep free)
                              (not (quotep x))))
                (integerp y)
                (integerp x)
                ;; (rationalp free)
                (integerp p)
                (< 0 p))
           (equal (mod (+ y x) p)
                  (mod (+ y free) p))))

;if two close numbers have the same remainder, they are equal
(defthm same-remainder-when-close-helper
  (implies (and (rationalp i)
                (rationalp k)
                (<= 0 diff)
                (integerp diff) ;gen?
                (equal (mod i k) (mod (+ i diff) k))
                (< diff k))
           (equal diff 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (mod FLOOR-OF-SUM) (FLOOR-TYPE-3)))))

;rename?
(defthmd mod-recollapse-lemma2
  (equal (+ x (- (* z (floor x z))))
         (mod x z))
  :hints (("Goal" :in-theory (enable mod))))

;rename?
(defthmd mod-recollapse-lemma
  (equal (+ y x (- (* z (floor (+ y x) z))))
         (mod (+ y x) z))
  :hints (("Goal" :in-theory (enable mod))))

(theory-invariant (incompatible (:definition mod) (:rewrite mod-recollapse-lemma)))
(theory-invariant (incompatible (:definition mod) (:rewrite mod-recollapse-lemma2)))

;; lemma:
;; if i and j are within k of each other, then (i ~ j mod k) iff i=j

(defthmd same-remainder-when-close-helper2
  (IMPLIES (AND (integerp I)
                (integerp J)
                (rationalp K)
                (< I J)
                (< (+ (- I) J) K))
           (NOT (EQUAL (MOD I K) (MOD J K))))
  :hints (("Goal" :use (:instance same-remainder-when-close-helper (diff (- j i))))))

;wlog we let i be the smaller one
(defthm same-remainder-when-close-helper3
  (implies (and (<= i j)
                (< (- j i) k)
                (integerp i)
                (integerp j)
                (rationalp k))
           (equal (equal (mod i k) (mod j k))
                  (equal i j)))
  :hints (("Goal" :use (:instance same-remainder-when-close-helper2))))

(defthm same-remainder-when-close
  (implies (and (< (abs (- i j)) k)
                (integerp i)
                (integerp j)
                (rationalp k))
           (equal (equal (mod i k) (mod j k))
                  (equal i j)))
  :hints (("Goal" :use ((:instance same-remainder-when-close-helper3)
                        (:instance same-remainder-when-close-helper3 (i j) (j i)))
           :in-theory (disable same-remainder-when-close-helper3))))

(local (in-theory (enable mod-=-0))) ;todo

;rename?
(defthm same-remainder-when-close-lemma
  (implies (and (<= i j)
                (< (- j i) k)
                (equal 0 (mod i k))
                (natp i)
                (integerp j)
                (integerp k))
           (equal (* k (floor j k)) i))
  :hints (("Goal" :use (:instance same-remainder-when-close (j (* k (floor j k))))
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable same-remainder-when-close))))
