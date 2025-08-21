; A lightweight book about the built-in function mod.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; For mod-sum-cases, see the copyright on the RTL library.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Theorem rationalp-of-mod below may not hold in ACL2(r), so for now we
;; disable certification of this book in ACL2(r):
; cert_param: (non-acl2r)

(local (include-book "times"))
(local (include-book "minus"))
(local (include-book "plus"))
(local (include-book "floor"))

(in-theory (disable mod))

;; Note: ACL2's built-in :type-prescription rule for MOD tells us that it is an
;; acl2-number.

(defthm integerp-of-mod
  (implies (integerp y)
           (equal (integerp (mod x y))
                  (integerp (fix x))))
  :hints (("Goal" ;:cases (integerp x)
           :in-theory (enable mod))))

(defthm integerp-of-mod-type
  (implies (and (integerp x)
                (integerp y))
           (integerp (mod x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable mod))))

;gen?
(defthm nonneg-of-mod-type
  (implies (and (<= 0 x)
                (rationalp x)
                (<= 0 y)
                (rationalp y))
           (<= 0 (mod x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :cases ((equal 0 y))
           :in-theory (enable mod *-of-floor-upper-bound))))

(defthm nonneg-of-mod-type-2
  (implies (and ;(<= 0 x)
                (rationalp x)
                (< 0 y)
                (rationalp y))
           (<= 0 (mod x y)))
  :rule-classes :type-prescription
  :hints (("Goal" :cases ((equal 0 y))
           :in-theory (enable mod *-of-floor-upper-bound))))

(defthm mod-of-0-arg1
  (equal (mod 0 y)
         0)
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-0-arg2
  (equal (mod x 0)
         (fix x))
  :hints (("Goal" :in-theory (enable mod))))

;; (mod x 1) returns the fractional part of x, which for an integer is 0.
(defthm mod-of-1-when-integerp
  (implies (integerp x)
           (equal (mod x 1)
                  0))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-1-arg1
  (implies (and (integerp y)
                (<= 0 y) ;gen
                )
           (equal (mod 1 y)
                  ;;(if (<= 0 y)
                  (if (equal 1 y)
                      0
                    1)
                  ;;-1)
                  ))
  :hints (("Goal" :in-theory (enable mod))))

;; To support ACL2(r), we might have to assume (rationalp y) here.
(defthm rationalp-of-mod
  (implies (rationalp x)
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :cases ((rationalp y)
                          (complex-rationalp y))
           :in-theory (enable mod
                              floor-when-rationalp-and-complex-rationalp))))

(defthm mod-when-not-acl2-numberp-arg1
  (implies (not (acl2-numberp x))
           (equal (mod x y)
                  0))
  :hints (("Goal" :in-theory (enable mod floor))))

(defthm mod-when-not-acl2-numberp-arg2
  (implies (not (acl2-numberp y))
           (equal (mod x y)
                  (if (acl2-numberp x)
                      x
                    0)))
  :hints (("Goal" :in-theory (enable mod floor))))

;; generalizing this is hard since even if x is not rational, the quotient may be.
(defthm mod-when-not-rationalp-arg1-and-rationalp-arg2
  (implies (and (not (rationalp x))
                (rationalp y))
           (equal (mod x y)
                  (fix x)))
  :hints (("Goal" :in-theory (enable mod))))

;; generalizing this is hard since even if x is not rational, the quotient may be.
(defthm mod-when-rationalp-arg1-and-not-rationalp-arg2
  (implies (and (rationalp x)
                (not (rationalp y)))
           (equal (mod x y)
                  x))
  :hints (("Goal" :in-theory (enable mod floor))))

(defthm +-of-mod-and-*-of-floor-same
  (implies (acl2-numberp x)
           (equal (+ (mod x y) (* y (floor x y)))
                  x))
  :hints (("Goal" :in-theory (enable mod))))

;; Trying to avoid name clash
(defthm floor-mod-elim-rule
  (implies (acl2-numberp x)
           (equal (+ (mod x y) (* y (floor x y)))
                  x))
  :rule-classes :elim
  :hints (("Goal" :in-theory (enable mod))))

(local (include-book "../../arithmetic-3/floor-mod/floor-mod")) ;todo
(local (in-theory (disable INTEGERP-MINUS-X))) ;slow
;(local (include-book "plus-and-times"))

(defthm mod-of-mod-same-arg2
  (implies (and (rationalp x)
                (rationalp y))
           (equal (mod (mod x y) y)
                  (mod x y)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-when-<
  (implies (and (< x y)
                (<= 0 x)
                (rationalp x))
           (equal (mod x y)
                  x))
  :hints (("Goal" :in-theory (enable mod)
           :cases ((rationalp y)))))

(defthmd equal-of-0-and-mod
  (implies (and (rationalp x)
                (rationalp y))
           (equal (equal 0 (mod x y))
                  (if (equal 0 y)
                      (equal 0 x)
                    (integerp (/ x y))))))

;; (defthm integerp-of-/-becomes-equal-of-0-and-mod
;;   (implies (and (rationalp x)
;;                 (rationalp y)
;;                 (not (equal 0 y)))
;;            (equal (integerp (/ x y))
;;                   (equal 0 (mod x y)))))

;todo: add alt conjunct
(defthmd integerp-of-*-of-/-becomes-equal-of-0-and-mod
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (integerp (* (/ y) x)) ;should match things like (* 1/32 x)
                  (equal 0 (mod x y))))
  :hints (("Goal" :use equal-of-0-and-mod
           :in-theory (disable equal-of-0-and-mod))))

(theory-invariant (incompatible (:rewrite integerp-of-*-of-/-becomes-equal-of-0-and-mod)
                                (:rewrite equal-of-0-and-mod)))

(defthm mod-bound-linear-arg1
  (implies (and (rationalp x)
                (<= 0 x)
                (rationalp y)
                (<= 0 y))
           (<= (mod x y) x))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal y 0))
           :in-theory (enable mod))))

;this allows y to be negative (conclusion will be false)
(defthm <-of-mod-same-arg2
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< (mod x y) y)
                  (if (equal 0 y)
                      (< x 0)
                    (<= 0 y)))))

(defthm mod-bound-linear-arg2
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y))
           (< (mod x y) y))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal y 0))
           :in-theory (enable mod))))

(defthm equal-of-mod-same-arg1
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y))
           (equal (equal x (mod x y))
                  (and (<= 0 x)
                       (< x y)))))

(defthm mod-of-2-when-even-cheap
  (implies (and (integerp (* 1/2 x))
                ;; (rationalp x)
                )
           (equal (mod x 2)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable equal-of-0-and-mod))))

;rename?
(defthm mod-of-*-lemma
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (* x y) y)
                  0)))

;rename?
(defthm mod-of-*-lemma-alt
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (* y x) y)
                  0)))

(defthm mod-of-+-of-*-same-arg1-arg1
  (implies (and (rationalp x1)
                (integerp x2)
                (integerp y))
           (equal (mod (+ (* y x2) x1) y)
                  (mod x1 y)))
  :hints (("Goal" :cases ((posp y)))))

(defthm mod-of-+-of-*-same-arg1-arg2
  (implies (and (rationalp x1)
                (integerp x2)
                (integerp y))
           (equal (mod (+ (* x2 y) x1) y)
                  (mod x1 y)))
  :hints (("Goal" :cases ((posp y)))))

(defthm mod-of-+-of-*-same-arg2-arg2
  (implies (and (rationalp x1)
                (integerp x2)
                (integerp y))
           (equal (mod (+ x1 (* x2 y)) y)
                  (mod x1 y)))
  :hints (("Goal" :cases ((posp y)))))

(defthm mod-of-+-of-*-same-arg2-arg1
  (implies (and (rationalp x1)
                (integerp x2)
                (integerp y))
           (equal (mod (+ x1 (* y x2)) y)
                  (mod x1 y)))
  :hints (("Goal" :cases ((posp y)))))

(defthm mod-of-+-of-*-same-arg3-arg1
  (implies (and (posp y)
                (rationalp x)
                (rationalp x2)
                (integerp z))
           (equal (mod (+ x x2 (* y z)) y)
                  (mod (+ x x2) y))))

(defthm mod-of-+-of-*-same-arg3-arg2
  (implies (and (posp y)
                (rationalp x)
                (rationalp x2)
                (integerp z))
           (equal (mod (+ x x2 (* z y)) y)
                  (mod (+ x x2) y))))

(defthm integerp-of-mod-of-1
  (equal (integerp (mod x 1))
         (integerp (fix x)))
  :hints (("Goal" :in-theory (enable mod))))

;quite aggressive
(defthmd mod-cancel
  (implies (syntaxp (not (equal ''1 y)))
           (equal (mod x y)
                  (if (equal 0 (fix y))
                      (fix x)
                    (* y (mod (/ x y) 1)))))
  :hints (("Goal" :in-theory (e/d (mod floor-normalize-denominator)
                                  (floor-of-*-of-/-and-1)))))

;from rtl:
(defthmd mod-sum-cases
  (implies (and (<= 0 y)
                (rationalp x)
                (rationalp y)
                (rationalp k))
           (equal (mod (+ k x) y)
                  (if (< (+ (mod k y)
                            (mod x y))
                         y)
                      (+ (mod k y)
                         (mod x y))
                    (+ (mod k y)
                       (mod x y)
                       (* -1 y)))))
  :hints (("Goal" :in-theory (enable mod))))

;may be expensive..
;could specialize to when y1 and y2 are obviously powers of 2
(defthmd mod-of-mod-when-mult
  (implies (and (integerp (* y1 (/ y2)))
                (rationalp y1)
                (rationalp y2))
           (equal (mod (mod x y1) y2)
                  (if (equal 0 y2)
                      (mod x y1) ;rare case
                    (mod x y2))))
  :hints (("Goal" :in-theory (e/d (mod unicity-of-0)
                                  (|(* y x)| ; for speed
                                   integerp-of-*))
           :use ((:instance integerp-of-* (x (* y1 (/ y2)))
                            (y (floor x y1)))
                 (:instance floor-of-+-when-mult-arg1
                            (i1 (* y1 (floor i y1)))
                            (i2 x)
                            (j y2)
                            (i (* y1 (/ y2) (floor x y1))))))))

;gen
(defthm mod-of-*-of-mod
  (implies (and (integerp x)
                (integerp x1)
                (integerp z)
                )
           (equal (mod (* x (mod x1 z)) z)
                  (mod (* x x1) z))))

;gen
(defthm mod-of-*-of-mod-2
  (implies (and (integerp x)
                (integerp x1)
                (integerp z)
                )
           (equal (mod (* (mod x1 z) x) z)
                  (mod (* x1 x) z))))

;rename
(defthm mod-mult-lemma
  (implies (and (integerp x)
                (integerp w)
                (integerp y))
           (equal (mod (+ (* y x) w) y)
                  (mod w y))))

(defthm mod-same
  (equal (mod x x)
         0)
  :hints (("Goal" :in-theory (enable mod))))

;; TODO: Improve the form of the RHS?
(defthm mod-of-minus-arg1
  (equal (mod (- x) y)
         (if (rationalp y)
             (if (and (rationalp x)
                      (not (equal y 0)))
                 ;; usual case:
                 (if (equal 0 (mod x y))
                     0
                   (- y (mod x y)))
               (- x))
           (if (acl2-numberp y)
               ;; y is complex:
               (if (integerp (* x (/ y))) ;; (equal 0 (mod x y))
                   0
                 (if (rationalp (* x (/ y)))
                     (- y (mod x y))
                   (- x)))
             (- x))))
  :hints (("Goal"
           :in-theory (e/d (mod floor-when-integerp-of-quotient floor-of---special-case)
                           (prefer-positive-addends-equal))
           :cases ((not (acl2-numberp y))
                   (rationalp y)
                   (not (acl2-numberp x))))))

(defthm mod-of-minus-arg2
  (implies (and ;; (rationalp x)
                (rationalp y))
           (equal (mod x (- y))
                  (- (mod (- x) y))))
  :hints (("Goal" :cases ((equal '0 y)))))

(defthm mod-when-integerp-of-quotient
  (implies (integerp (* x (/ y)))
           (equal (mod x y)
                  (if (or (not (acl2-numberp x))
                          (and (acl2-numberp y)
                               (not (equal 0 y))))
                      0
                    x)))
  :hints (("Goal" :cases ((acl2-numberp x))
           :in-theory (enable mod
                              floor-when-integerp-of-quotient))))

;; (defthmd mod-when-multiple
;;   (implies (and (integerp (* x (/ y)))
;;                 ;; (rationalp x)
;;                 (acl2-numberp y)
;;                 (not (equal 0 y)))
;;            (equal (mod x y)
;;                   0))
;;   :hints (("Goal" :in-theory (enable mod
;;                                      floor-when-multiple))))

(defthm mod-of-+-of-mod-arg1
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (< 0 y))
           (equal (mod (+ (mod x1 y) x2) y)
                  (mod (+ x1 x2) y)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-+-of-mod-arg2
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (< 0 y))
           (equal (mod (+ x1 (mod x2 y)) y)
                  (mod (+ x1 x2) y)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm equal-of-mod-of-+-and-mod-of-+-cancel
  (implies (and (rationalp x)
                (rationalp x1)
                (rationalp x2)
                (integerp y)
                (< 0 y))
           (equal (equal (mod (+ x x1) y)
                         (mod (+ x x2) y))
                  (equal (mod x1 y) (mod x2 y))))
  :hints (("Goal" :in-theory (enable mod-sum-cases))))

(defthm equal-of-mod-of-+-and-mod-cancel
  (implies (and (rationalp x)
                (rationalp x1)
                (integerp y)
                (< 0 y))
           (equal (equal (mod x y)
                         (mod (+ x x1) y))
                  (equal 0 (mod x1 y))))
  :hints (("Goal" :in-theory (enable mod-sum-cases))))

(defthm equal-of-mod-of-+-cancel
  (implies (and (rationalp x)
                (rationalp x1)
                (integerp y)
                (< 0 y))
           (equal (equal x (mod (+ x x1) y))
                  (and (< x y)
                       (<= 0 x)
                       (equal 0 (mod x1 y)))))
  :hints (("Goal" :in-theory (enable mod-sum-cases))))

;enable?
(defthmd mod-of-*-subst-arg2
  (implies (and (equal (mod x1 p)
                       (mod free p))
                (syntaxp (not (term-order x1 free)))
                (integerp x)
                (integerp free)
                (integerp p))
           (equal (mod (* x x1) p)
                  (mod (* x free) p)))
  :hints (("Goal" :use ((:instance mod-of-*-of-mod
                                  (z p))
                        (:instance mod-of-*-of-mod
                                  (z p)
                                  (x1 free)))
           :in-theory (disable mod-of-*-of-mod))))

;enable?
(defthmd mod-of-*-subst-arg1
  (implies (and (equal (mod x1 p)
                       (mod free p))
                (syntaxp (not (term-order x1 free)))
                (integerp x)
                (integerp free)
                (integerp p))
           (equal (mod (* x1 x) p)
                  (mod (* free x) p)))
  :hints (("Goal" :use mod-of-*-subst-arg2
           :in-theory (disable mod-of-*-subst-arg2))))

(defthm mod-of-+-of---same
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y))
           (equal (mod (+ (- y) x) y)
                  (mod x y))))

(defthm mod-of-+-of---of-mod-same-arg1
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (< 0 y)
                )
           (equal (mod (+ (- (mod x1 y)) x2) y)
                  (mod (+ (- x1) x2) y))))

(defthm mod-of-+-of---of-mod-same-arg2
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (< 0 y)
                )
           (equal (mod (+ x2 (- (mod x1 y))) y)
                  (mod (+ x2 (- x1)) y))))

(defthm mod-of-+-same-arg1
  (implies (and (rationalp x)
                (rationalp y))
           (equal (mod (+ y x) y)
                  (if (equal 0 y)
                      (fix x)
                    (mod x y))))
  :hints (("Goal" :in-theory (enable mod-sum-cases))))

(defthm mod-of-+-same-arg2
  (implies (and (rationalp x)
                (rationalp y))
           (equal (mod (+ x y) y)
                  (if (equal 0 y)
                      (fix x)
                    (mod x y)))))

(defthm multiple-when-mod-0-cheap
  (implies (and (equal 0 (mod n m))
                (rationalp m)
                (rationalp n))
           (integerp (* (/ m) n)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil))))

(defthm equal-of-0-and-mod-of-1
  (implies (rationalp x)
           (equal (equal 0 (mod x 1))
                  (integerp x))))

(defthm mod-bound-linear-arg2-strong
  (implies (and (integerp x)
                (integerp y)
                (< 0 y))
           (<= (mod x y) (+ -1 y)))
  :rule-classes :linear
  :hints (("Goal" :use mod-bound-linear-arg2)))


;gen?
(defthm <-of-mod-same2
  (implies (and (< 0 y)
                (rationalp y)
                (rationalp x))
           (not (< y (mod x y)))))

;gen?
(defthm equal-of-mod-same
  (implies (and (rationalp y)
                (rationalp x))
           (equal (equal y (mod x y))
                  (if (equal 0 y)
                      (equal 0 x)
                    nil))))

;two ways of saying that i is odd
(defthm equal-of-+-1-and-*-2-of-floor-of-2
  (implies (integerp i)
           (equal (equal i (+ 1 (* 2 (floor i 2))))
                  (equal 1 (mod i 2))))
  :hints (("Goal" :in-theory (enable mod))))

(defthmd *-of-2-and-floor-of-2
  (implies (integerp i)
           (equal (* 2 (floor i 2))
                  (if (equal 1 (mod i 2))
                      (+ -1 i)
                    i)))
  :hints (("Goal" :in-theory (enable))))

;two ways of saying that i is even
(defthmd equal-of-*-2-of-floor-of-2-same
  (equal (equal (* 2 (floor i 2)) i)
         (and (acl2-numberp i)
              (equal 0 (mod i 2))))
  :hints (("Goal" :in-theory (enable mod))))

(theory-invariant (incompatible (:definition mod) (:rewrite equal-of-*-2-of-floor-of-2-same)))

(defthmd floor-when-mod-0
  (implies (and (equal 0 (mod x y))
                (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (floor x y)
                  (/ x y)))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-*-subst-constant-arg1
  (implies (and (equal (mod x p) free)
                (syntaxp (and (quotep free)
                              (not (quotep x))))
                (integerp y)
                ;; (rationalp free)
                (integerp p))
           (equal (mod (* x y) p)
                  (mod (* free y) p))))

(defthm mod-of-*-subst-constant-arg2
  (implies (and (equal (mod x p) free)
                (syntaxp (and (quotep free)
                              (not (quotep x))))
                (integerp y)
                ;; (rationalp free)
                (integerp p))
           (equal (mod (* y x) p)
                  (mod (* y free) p))))

;; since (mod x p) is less than p
(defthm integerp-of-*-of-/-and-mod-same
  (implies (natp p)
           (equal (integerp (* (/ p) (mod x p)))
                  (or (equal 0 (mod x p))
                      (equal p 0)))))

(defthmd mod-when-not-rationalp-of-quotient
  (implies (not (rationalp (* (/ p) x)))
           (equal (mod x p)
                  (fix x)))
  :hints (("Goal" :in-theory (enable mod floor))))



(defthmd mod-when-equal-of-mod-and-0-free
  (implies (and (equal 0 (mod x y2)) ;y2 is a free var
                (equal 0 (mod y2 y))
                (rationalp y2))
           (equal (mod x y)
                  0))
  :hints (("Goal"
           :use (:instance integerp-of-*
                           (x (* x (/ y2)))
                           (y (* (/ y) y2)))
           :in-theory (e/d (equal-of-0-and-mod)
                           (integerp-of-*)))))

(defthm mod-when-equal-of-mod-and-0-free-cheap
  (implies (and (syntaxp (quotep y))
                (equal 0 (mod x y2)) ;y2 is a free var
                (syntaxp (quotep y2))
                (equal 0 (mod y2 y)) ;gets computed
                (rationalp y2))
           (equal (mod x y)
                  0))
  :hints (("Goal" :in-theory (enable mod-when-equal-of-mod-and-0-free))))

;gen
(defthmd mod-of-mod-when-multiple
  (implies (and (equal 0 (mod y1 y2))
                ;; (rationalp y2)
                (< 0 y2)
                (rationalp y1)
                (not (equal 0 y1)))
           (equal (mod (mod x y1) y2)
                  (mod x y2)))
  :hints (("Goal" :in-theory (enable equal-of-0-and-mod
                                     mod-sum-cases ; why?
                                     ))))

(defthm mod-of-mod-when-multiple-safe
  (implies (and (syntaxp (and (quotep y1)
                              (quotep y2)))
                (equal 0 (mod y1 y2)) ;gets computed
                ;; (rationalp y2)
                (< 0 y2)
                (rationalp y1)
                (not (equal 0 y1)))
           (equal (mod (mod x y1) y2)
                  (mod x y2)))
  :hints (("Goal" :use mod-of-mod-when-multiple)))

(defthm unsigned-byte-p-of-mod-when-<=-of-expt
  (implies (and (<= y (expt 2 size))
                (integerp x)
                (posp y)
                (integerp size))
           (unsigned-byte-p size (mod x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-mod
  (implies (and (unsigned-byte-p size y)
                (< 0 y)
                (integerp x))
           (unsigned-byte-p size (mod x y)))
  :hints (("Goal"
           :in-theory (enable unsigned-byte-p))))

;rename?
(defthm unsigned-byte-p-of-mod2
  (implies (and (unsigned-byte-p size y)
                (unsigned-byte-p size x))
           (unsigned-byte-p size (mod x y)))
  :hints (("Goal" :cases ((equal 0 y))
           :in-theory (enable unsigned-byte-p))))

(defthm mod-of-+-of---when-equal-of-mod-arg1
  (implies (and (syntaxp (not (quotep x1))) ; prevent ACL2 from matching (- x1) with a constant
                (equal (mod x1 y) k)
                (syntaxp (quotep k))
                (rationalp x1)
                (rationalp x2)
                (posp y))
           (equal (mod (+ (- x1) x2) y)
                  (mod (+ (- k) x2) y))))

(defthm mod-of-+-of---when-equal-of-mod-arg2
  (implies (and (syntaxp (not (quotep x1))) ; prevent ACL2 from matching (- x1) with a constant
                (equal (mod x1 y) k)
                (syntaxp (quotep k))
                (rationalp x1)
                (rationalp x2)
                (posp y))
           (equal (mod (+ x2 (- x1)) y)
                  (mod (+ x2 (- k)) y))))

(defthm equal-of-mod-of-+-when-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep y)))
                (rationalp x)
                (rationalp k1) ; gets computed
                (rationalp k2) ; gets computed
                (rationalp y) ; gets computed
                (< 0 y) ; gets computed
                )
           (equal (equal k1 (mod (+ k2 x) y))
                  (and (< k1 y) ; usually true, gets computed
                       (<= 0 k1) ; usually true, gets computed
                       (equal (mod (- k1 k2) y) ; gets computed
                              (mod x y)))))
  :hints (("Goal" :in-theory (enable mod-sum-cases))))

;; when x is negative, but not too negative, modding by y just adds y
(defthm mod-when-<-of-0
  (implies (and (< x 0)
                (< (- y) x)
                (integerp x)
                (integerp y))
           (equal (mod x y)
                  (+ x y)))
  :hints (("Goal" :use (:instance mod-when-<
                                  (x (+ x y))
                                  (y y))
           :in-theory (disable mod-when-<))))

(defthm mod-of-*-and-*-cancel-arg2-arg2
  (equal (mod (* x z) (* y z))
         (if (equal (fix z) 0)
             0
           (* z (mod x y))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-of-+-subst-constant
  (implies (and (syntaxp (not (quotep x1)))
                (equal k (mod x1 y))
                (syntaxp (quotep k))
                (rationalp x1)
                (rationalp x2))
           (equal (mod (+ x1 x2) y)
                  (mod (+ k x2) y))))

(defthmd mod-of-+-when-multiple-arg1
  (implies (and (equal 0 (mod x1 y))
                (rationalp x1)
                (rationalp x2))
           (equal (mod (+ x1 x2) y)
                  (mod x2 y))))

;; Disabled in case we want to keep negative constants like -1 (vs some huge
;; positive number), but see mod-of-+-reduce-positive-constant.
(defthmd mod-of-+-reduce-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep y)
                              (not (and (<= 0 (unquote k))
                                        (< (unquote k) (unquote y))))))
                (rationalp y)
                (< 0 y)
                (rationalp x)
                (rationalp k))
           (equal (mod (+ k x) y)
                  ;; the (mod k y) should get computed:
                  (mod (+ (mod k y) x) y))))

(defthm mod-of-+-reduce-positive-constant
  (implies (and (syntaxp (and (quotep k)
                              (< 0 (unquote k))
                              (quotep y)
                              (not (< (unquote k) (unquote y)))))
                (rationalp y)
                (< 0 y)
                (rationalp x)
                (rationalp k))
           (equal (mod (+ k x) y)
                  ;; the (mod k y) should get computed:
                  (mod (+ (mod k y) x) y))))

(defthm mod-of-*-of-/-arg2-arg2
  (implies (and (rationalp y2)
                (not (equal 0 y2)))
           (equal (mod x (* y1 (/ y2)))
                  (/ (mod (* y2 x) y1)
                     y2)))
  :hints (("Goal" :in-theory (enable mod-cancel))))

(defthm mod-of-*-of-mod-arg3
   (implies (and (integerp x)
                 (integerp y)
                 (integerp z)
                 (integerp p))
            (equal (mod (* x y (mod z p)) p)
                   (mod (* x y z) p)))
   :hints (("Goal" :use (:instance mod-of-*-of-mod
                                   (z p)
                                   (x (* x y))
                                   (x1 z))
            :in-theory (disable mod-of-*-of-mod))))

;; Disabled by default for speed
(defthmd equal-when-equal-of-floors-and-equal-of-mods
  (implies (and (equal (floor i1 j) (floor i2 j)) ; j is a free var
                (equal (mod i1 j) (mod i2 j))
                (acl2-numberp i1)
                (acl2-numberp i2))
           (equal (equal i1 i2)
                  t))
  :hints (("Goal" :in-theory (enable mod))))

;; Enable?
(defthmd floor-of-when-mod-known
  (implies (and (equal k (mod i j)) ; k is a free var
                (syntaxp (quotep k))
                (natp k)
                (< k j)
                (integerp j)
                (< 0 j)
                (integerp i))
           (equal (floor i j)
                  (/ (- i k) j))))

(defthm mod-of-+-same-three
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (<= 0 z))
           (equal (mod (+ x y z) z)
                  (mod (+ x y) z)))
  :hints (("Goal" :in-theory (e/d (mod-sum-cases)
                                  ;; these looped:
                                  (prefer-positive-addends-equal
                                   simplify-sums-equal)))))

(defthm <-of-mod-and-0
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< (mod x y) 0)
                  (if (equal 0 y)
                      (< (fix x) 0)
                    (if (< y 0)
                        (not (integerp (/ x y)))
                      nil)))))

;todo: gen to reduce the constant even if not down to 0
(defthm mod-of-+-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep j)))
                (equal 0 (mod k j))
                (rationalp j)
                (rationalp k)
                (not (equal 0 j))
                (integerp x))
           (equal (mod (+ k x) j)
                  (mod x j))))
