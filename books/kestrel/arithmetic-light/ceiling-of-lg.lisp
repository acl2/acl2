; Base-2 logarithm (rounded up)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The function CEILING-OF-LG computes the ceiling of the base-2 logarithm of
;; its argument.

(include-book "ceiling-of-lg-def")
(include-book "power-of-2p-def")
(local (include-book "integer-length"))
(local (include-book "expt"))
(local (include-book "times"))
(local (include-book "mod"))

;; See also integer-length.lisp and lg.lisp.

(defthm integerp-of-ceiling-of-lg
  (integerp (ceiling-of-lg x)))

(defthm natp-of-ceiling-of-lg
  (natp (ceiling-of-lg x)))

(defthm <-of-ceiling-of-lg-arg1-when-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (posp x))
           (equal (< (ceiling-of-lg x) k)
                  (if (<= k 0)
                      nil
                    (<= x (expt 2 (+ -1 k)))
                    )))
  :hints (("Goal" :use (:instance <-of-integer-length-arg1 (x (+ -1 x)) (n k))
           :in-theory (e/d (ceiling-of-lg) (<-of-integer-length-arg1)))))

(defthm <-of-ceiling-of-lg-arg2-when-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (posp x))
           (equal (< k (ceiling-of-lg x))
                  (if (< k 0)
                      t
                    (< (expt 2 k) x))))
  :hints (("Goal" :use (:instance <-of-integer-length-arg2 (x (+ -1 x)) (n k))
           :in-theory (e/d (ceiling-of-lg) (<-of-integer-length-arg2)))))

(defthm equal-of-ceiling-of-lg-and-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (posp x))
           (equal (equal (ceiling-of-lg x) k)
                  (if (< k 0)
                      nil
                    (and (< (expt 2 (+ -1 k)) x)
                         (<= x (expt 2 k))))))
  :hints (("Goal" :use (<-of-ceiling-of-lg-arg1-when-constant
                        <-of-ceiling-of-lg-arg2-when-constant)
           :in-theory (disable <-of-ceiling-of-lg-arg1-when-constant
                               <-of-ceiling-of-lg-arg2-when-constant))))

;; for non-positive constants
;rename
(defthm <-of-ceiling-of-lg-and-constant
  (implies (and (syntaxp (quotep k))
                (<= k 0))
           (not (< (ceiling-of-lg x) k))))

(defthm equal-of-0-and-ceiling-of-lg
  (implies (natp x)
           (equal (equal 0 (ceiling-of-lg x))
                  (< x 2)))
  :hints (("Goal" :cases ((not (natp x))
                          (equal 0 x))
           :in-theory (enable ceiling-of-lg))))

(defthm unsigned-byte-p-of-ceiling-of-lg-when-<
  (implies (and (< i j)
                (natp i)
                (integerp j))
           (unsigned-byte-p (ceiling-of-lg j) i))
  :hints (("Goal" :in-theory (enable ceiling-of-lg))))

(defthm ceiling-of-lg-of-expt2
  (implies (natp n)
           (equal (ceiling-of-lg (expt 2 n))
                  n))
  :hints (("Goal" :in-theory (enable ceiling-of-lg))))

(defthm ceiling-of-lg-of-*-of-2
  (implies (natp n)
           (equal (ceiling-of-lg (* 2 n))
                  (if (equal n 0)
                      0
                    (+ 1 (ceiling-of-lg n)))))
  :hints (("Goal" :in-theory (e/d (ceiling-of-lg integer-length-of-+-of--1) (expt)))))

(defthm ceiling-of-lg-of-*-of-expt-arg2
  (implies (and (natp n)
                (natp i))
           (equal (ceiling-of-lg (* n (expt 2 i)))
                  (if (equal n 0)
                      0
                    (+ i (ceiling-of-lg n)))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm ceiling-of-lg-of-*-of-1/2
  (implies (and (evenp n)
                (posp n))
           (equal (ceiling-of-lg (* 1/2 n))
                  (+ -1 (ceiling-of-lg n))))
  :hints (("Goal"
           :in-theory (enable integer-length-of-+-of--1 ceiling-of-lg expt-of-+))))

;move
(local
 (defthm integerp-of-*-of-/-when-equal-of-0-and-mod
   (implies (and  (equal 0 (mod x y))
                  (integerp x)
                  (posp y))
            (integerp (* x (/ y))))))

(defthm ceiling-of-lg-of-*-of-expt-of--
  (implies (and (<= 0 i)                     ; gen?
                (equal 0 (mod x (expt 2 i))) ; or else x/2^i is not an integer
                (< 0 x)
                (integerp x)
                (integerp i))
           (equal (ceiling-of-lg (* x (expt 2 (- i))))
                  (- (ceiling-of-lg x) i)))
  :hints (("Goal" :in-theory (enable ceiling-of-lg integer-length-of-+-of--1 expt-of-+))))

(defthm ceiling-of-lg-of-*-of-expt-when-negative
  (implies (and (<= i 0) ; gen?
                (equal 0 (mod x (expt 2 (- i)))) ; or else x*2^i is not an integer
                (< 0 x)
                (integerp x)
                (integerp i))
           (equal (ceiling-of-lg (* x (expt 2 i)))
                  (+ (ceiling-of-lg x) i)))
  :hints (("Goal" :use (:instance ceiling-of-lg-of-*-of-expt-of-- (i (- i)))
                  :in-theory (disable ceiling-of-lg-of-*-of-expt-of--))))

(defthm <-of-expt-2-of-ceiling-of-lg-same
  (implies (posp x)
           (equal (< x (expt 2 (ceiling-of-lg x)))
                  (not (power-of-2p x))))
  :hints (("Goal" :in-theory (enable ceiling-of-lg power-of-2p))))

(defthm <=-of-expt-of-celing-of-lg-same
  (implies (integerp x)
           (<= x (expt 2 (ceiling-of-lg x))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ceiling-of-lg expt))))

(defthm <-of-expt-of-ceiling-of-lg-when-<
  (implies (and (< x y)
                (integerp x)
                (integerp y))
           (< x (expt 2 (ceiling-of-lg y))))
  :hints (("Goal" :in-theory (enable ceiling-of-lg expt))))

;; monotonicity
(defthm <=-of-ceiling-of-lg-and-ceiling-of-lg
  (implies (and (<= x y)
                (natp x) ; gen?
                (integerp y))
           (<= (ceiling-of-lg x) (ceiling-of-lg y)))
  :hints (("Goal" :in-theory (enable ceiling-of-lg)
           :cases ((equal 0 x)))))

(defthm <=-of-ceiling-of-lg-and-ceiling-of-lg-linear
  (implies (and (<= x y)
                (natp x) ; gen?
                (integerp y))
           (<= (ceiling-of-lg x) (ceiling-of-lg y)))
  :rule-classes :linear)

(defthm expt-of-ceiling-of-lg-when-power-of-2p
  (implies (power-of-2p x)
           (equal (expt 2 (ceiling-of-lg x))
                  x))
  :hints (("Goal" :in-theory (enable power-of-2p
                              ceiling-of-lg))))

;; if x is a power of 2 we need the 1 extra bit
(defthm unsigned-byte-p-of-+-of-1-and-ceiling-of-lg-same
  (implies (natp x)
           (unsigned-byte-p (+ 1 (ceiling-of-lg x)) x))
  :hints (("Goal" :in-theory (enable ceiling-of-lg
                                     expt-of-+))))

(defthm unsigned-byte-p-of-ceiling-of-lg-same
  (implies (natp x)
           (equal (unsigned-byte-p (ceiling-of-lg x) x)
                  (not (power-of-2p x))))
  :hints (("Goal" :in-theory (enable power-of-2p))))

(defthmd ceiling-of-lg-of-+-of--1
  (implies (posp x) ; gen?
           (equal (ceiling-of-lg (+ -1 x))
                  (if (power-of-2p (+ -1 x))
                      (+ -1 (ceiling-of-lg x))
                    (ceiling-of-lg x))))
  :hints (("Goal"
           :use ((:instance integer-length-of-+-of--1-alt (i x))
                 (:instance integer-length-of-+-of--1-alt (i (+ -1 x))))
           :in-theory (enable ceiling-of-lg))))
