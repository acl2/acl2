; BV Library: theorems about logtail
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logtail-def")
(include-book "kestrel/arithmetic-light/power-of-2p-def" :dir :system)
(include-book "kestrel/arithmetic-light/lg-def" :dir :system)
(local (include-book "../library-wrappers/ihs-logops-lemmas"))
(local (include-book "../utilities/equal-of-booleans"))
(local (include-book "unsigned-byte-p"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/times-and-divide"))
(local (include-book "../arithmetic-light/divide"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/floor-and-expt"))
(local (include-book "../arithmetic-light/lg"))

(in-theory (disable logtail))

(defthm logtail-of-0-arg1
  (equal (logtail 0 x)
         (ifix x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-of-0-arg2
  (equal (logtail pos 0)
         0)
   :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-when-not-integerp-arg2
  (implies (not (integerp i))
           (equal (logtail pos i)
                  0))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-becomes-0
  (implies (unsigned-byte-p n x)
           (equal (logtail n x)
                  0))
  :hints (("Goal" :in-theory (enable logtail unsigned-byte-p))))

(defthm logtail-when-not-posp-arg1
  (implies (not (posp size))
           (equal (logtail size x)
                  (ifix x)))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-shift
  (implies (and (integerp x)
                (natp n))
           (equal (logtail n (* x (expt 2 n)))
                  x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-shift-alt
  (implies (and (integerp x)
                (natp n))
           (equal (logtail n (* (expt 2 n) x))
                  (ifix x)))
  :hints (("Goal" :use logtail-shift
           :in-theory (disable logtail-shift))))

(defthm logtail-of-sum
  (implies (and (integerp (/ a (expt 2 m)))
                (integerp a)
                (integerp b))
           (equal (logtail m (+ a b))
                  (+ (logtail m a)
                     (logtail m b))))
  :hints (("Goal" :in-theory (enable logtail
                                     floor-when-multiple))))

(defthm logtail-of-sum2
  (implies (and (integerp (/ b (expt 2 m)))
                (integerp a)
                (integerp b))
           (equal (logtail m (+ a b))
                  (+ (logtail m a) (logtail m b))))
  :hints (("Goal" :use (:instance logtail-of-sum (a b) (b a))
           :in-theory (disable logtail-of-sum))))

;; (defthm logtail-of-logtail-worse
;;   (implies (and (natp i)
;;                 (integerp x)
;;                 (natp j))
;;            (equal (logtail j (logtail i x))
;;                   (logtail (+ i j) x)))
;;   :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm floor-of-logtail-and-expt
  (implies (and (natp n)
                (natp m)
                (integerp x)
                )
           (equal (floor (logtail m x) (expt 2 n))
                  (floor x (expt 2 (+ m n)))))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm logtail-of-minus-one
  (implies (natp n)
           (equal (logtail n -1)
                  -1))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-of-times-2
  (implies (and (syntaxp (not (quotep x))) ; prevent ACL2 from unifying (* 2 x) with a constant
                (natp n)
                (integerp x))
           (equal (logtail n (* 2 x))
                  (if (equal 0 n)
                      (* 2 x)
                    (logtail (+ -1 n) x))))
  :hints (("Goal" :in-theory (enable logtail))))

;; (defthm natp-of-logtail
;;   (implies (NATP X)
;;            (NATP (LOGTAIL HIGH X))))

(defthm logtail-of-logtail
  (equal (logtail pos1 (logtail pos i))
         (logtail (+ (nfix pos) (nfix pos1)) i))
  :hints (("Goal" :use logtail-logtail
           :in-theory (disable logtail-logtail))))

(defthm logtail-of-minus-expt
  (implies (natp size)
           (equal (logtail size (- (expt 2 size)))
                  -1))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-non-neg
  (implies (<= 0 x)
           (not (< (logtail n x) 0)))
  :hints (("Goal"
           :use (:instance LOGTAIL-LESSP (pos n) (i x) (j 0))
           :in-theory (e/d (expt-of-+)
                           (LOGTAIL-LESSP)))))

(defthm logtail-shift-gen
  (implies (and (<= n size)
                (integerp size)
                (natp n)
                (integerp x))
           (equal (logtail size (* x (expt 2 n)))
                  (logtail (- size n) x)))
  :hints (("Goal" :in-theory (e/d (logtail expt-of-+
                                           floor-normalize-denominator)
                                  (floor-of-*-of-/-and-1)))))

(defthm logtail-shift-gen-alt
  (implies (and (<= n size)
                (integerp size)
                (natp n)
                (integerp x))
           (equal (logtail size (* (expt 2 n) x))
                  (logtail (- size n) x)))
  :hints (("Goal" :use logtail-shift-gen
           :in-theory (disable logtail-shift-gen))))

(defthm logtail-of-expt
  (implies (and
            (natp n)
            (integerp size))
           (equal (logtail n (expt 2 size))
                  (if (<= n size)
                      (expt 2 (- size n))
                    0)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+
                                     floor-when-multiple))))

(defthm logtail-monotone
  (implies (and (<= x y) ;expensive?
                (integerp y)
                (integerp x))
           ;rephrase?
           (<= (logtail n x)
               (logtail n y)))
  :hints (("Goal" :in-theory (e/d (logtail) (logtail-lessp)))))

;better than LOGTAIL-UNSIGNED-BYTE-P and UNSIGNED-BYTE-P-OF-LOGTAIL (from
;centaur/bitops/ihsext-basics.lisp)
(defthm unsigned-byte-p-of-logtail-strong
  (equal (unsigned-byte-p n (logtail pos i))
         (and (natp n)
              (unsigned-byte-p (+ n (nfix pos)) (ifix i))))
  :hints (("Goal" :cases ((integerp x)))))

(defthm logtail-shift-gen2
  (implies (and (<= size n) ;this case
                (natp size)
                (integerp n)
                (integerp x))
           (equal (logtail size (* x (expt 2 n)))
                  (* (expt 2 (- n size)) x)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm logtail-shift-gen2-alt
  (implies (and (<= size n) ;this case
                (natp size)
                (integerp n)
                (integerp x))
           (equal (logtail size (* (expt 2 n) x))
                  (* (expt 2 (- n size)) x)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm <-of-logtail-same
  (implies (and (natp x)
                (posp n))
           (equal (< (logtail n x) x)
                  (not (equal x 0))))
  :hints (("Goal" :in-theory (e/d (expt logtail <-of-floor-arg1)
                                  (expt-hack)))))

(defthm <=-of-logtail-same
  (implies (natp x)
           (<= (logtail n x) x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <=-of-logtail-same-linear
  (implies (natp x)
           (<= (logtail n x) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable logtail <-of-floor-arg1))))

;can loop with REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER
(defthmd equal-of-logtail-and-0
  (implies (and (integerp x)
                (natp n))
           (equal (equal (logtail n x) 0)
                  (unsigned-byte-p n x)))
  :hints (("Goal" :cases ((unsigned-byte-p n x))
           :in-theory (enable LOGTAIL))))

;improve the rewrite version?
(defthm logtail-non-positive
  (implies (<= x 0)
           (<= (logtail n x) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logtail))))

(defthm equal-of-logtail-self
  (implies (natp i) ;gen?
           (equal (equal (logtail pos i) i)
                  (or (equal 0 i)
                      (zp pos))))
  :hints (("Goal" :in-theory (enable logtail zip zp))))

(defthm logtail-of-1
  (equal (logtail size 1)
         (if (zp size)
             1
           0))
  :hints (("Goal" :in-theory (enable logtail zp))))

;move
(defthm logtail-non-negative-linear
  (implies (<= 0 x)
           (<= 0 (logtail n x)))
  :rule-classes :linear)

(defthmd equal-of-logtail
  (implies (and (natp pos)
                (integerp i))
           (equal (equal k (logtail pos i))
                  (and (integerp k)
                       (<= (* k (expt 2 pos)) i)
                       (< i (+ (expt 2 pos) (* k (expt 2 pos)))))))
  :hints (("Goal" :in-theory (enable logtail equal-of-floor))))

(defthm equal-of-logtail-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep pos)))
                (natp pos)
                (integerp i))
           (equal (equal k (logtail pos i))
                  (and (integerp k)
                       (<= (* k (expt 2 pos)) i)
                       (< i (+ (expt 2 pos) (* k (expt 2 pos)))))))
  :hints (("Goal" :in-theory (enable logtail equal-of-floor))))

;; ;sort of strength reduction
;; ;gen
;; ;can loop?
;; (defthmd floor-by-4
;;   (implies (integerp x)
;;            (equal (floor x 4)
;;                   (logtail 2 x)))
;;   :hints (("Goal" :in-theory (enable logtail))))
;; (theory-invariant (incompatible (:rewrite FLOOR-BY-4) (:DEFINITION LOGTAIL)))

(defthm logtail-of-1-and-+-of-1-and-*-of-2
  (implies (integerp x)
           (equal (logtail 1 (+ 1 (* 2 x)))
                  x))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <-of-logtail-arg1
  (implies (and (integerp i)
                (natp pos)
                (integerp j) ; needed?
                )
           (equal (< (logtail pos i) j)
                  (< i (* j (expt 2 pos)))))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <-of-logtail-arg2
  (implies (and (integerp i)
                (natp pos)
                (integerp j) ; needed?
                )
           (equal (< j (logtail pos i))
                  (<= (* (+ 1 j) (expt 2 pos)) i)))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <=-of-*-of-expt-and-logtail
  (implies (and (integerp i)
                (natp pos))
           (<= (* (expt 2 pos) (logtail pos i)) i))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <=-of-*-of-expt-and-logtail-linear
  (implies (and (integerp i)
                (natp pos))
           (<= (* (expt 2 pos) (logtail pos i)) i))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable logtail))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Disabled since logtail is more complex than floor
;drop since we have the general one
(defthmd floor-of-2-becomes-logtail-of-1
  (implies (integerp x)
           (equal (floor x 2)
                  (logtail 1 x)))
  :hints (("Goal" :in-theory (enable logtail ifix))))

(theory-invariant (incompatible (:rewrite floor-of-2) (:definition logtail)))

;Disabled since logtail is more complex than floor
(defthmd floor-of-expt-becomes-logtail
  (implies (and (integerp x)
                (natp n))
           (equal (floor x (expt 2 n))
                  (logtail n x)))
  :hints (("Goal" :in-theory (enable logtail ifix))))

(theory-invariant (incompatible (:rewrite floor-of-expt-becomes-logtail) (:definition logtail)))

(defthmd floor-of-power-of-2-becomes-logtail
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp x))
           (equal (floor x k)
                  (logtail (lg k) x)))
  :hints (("Goal" :in-theory (enable logtail ifix))))

(theory-invariant (incompatible (:rewrite floor-of-power-of-2-becomes-logtail) (:definition logtail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm logtail-of-floor-of-expt
  (implies (and (integerp x)
                (natp pos)
                (natp n))
           (equal (logtail pos (floor x (expt 2 n)))
                  (logtail (+ pos n) x)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

;rename
(defthm logtail-hack77
  (implies (posp size)
           (equal (logtail (+ -1 size) (- (expt 2 size)))
                  -2))
  :hints (("Goal" :in-theory (enable logtail
                                     floor-when-integerp-of-quotient
                                     *-of-expt-and-expt-of-1minus
                                     expt-of-+))))

(defthm logtail-of-one-less-when-signed-byte-p
  (implies (signed-byte-p size x)
           (equal (logtail (+ -1 size) x)
                  (if (< x 0)
                      -1
                    0)))
  :hints (("Goal" :in-theory (enable logtail signed-byte-p))))

(defthmd signed-byte-p-in-terms-of-logtail-when-negative
  (implies (< x 0)
           (equal (signed-byte-p size x)
                  (and (integerp x)
                       (posp size)
                       (equal (logtail (+ -1 size) x)
                              -1))))
  :hints (("Goal" :in-theory (enable logtail))))

;; the logtail is either all ones or all zeros depending on the sign
(defthmd signed-byte-p-in-terms-of-logtail
  (equal (signed-byte-p size x)
         (and (integerp x)
              (posp size)
              (equal (logtail (+ -1 size) x)
                     (if (< x 0) -1 0))))
  :hints (("Goal" :in-theory (enable logtail))))
