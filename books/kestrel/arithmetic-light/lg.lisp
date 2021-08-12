; Base-2 integer logarithm
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;TODO: Which do we prefer, lg or integer-length?  i think i like lg best,
;but my current rules may target integer-length?

(include-book "power-of-2p")
(local (include-book "expt2"))
(local (include-book "plus"))
(local (include-book "floor"))
(local (include-book "integer-length"))

;for integer-length proofs
(defun double-floor-by-2-induct (i j)
  (if (zip i)
      0
      (if (= i -1)
          0
          (if (zip j)
              0
              (if (= j -1)
                  0
                  (+ 1 (double-floor-by-2-induct (floor i 2) (floor j 2))))))))

(defthm integer-length-monotonic
  (implies (and (<= x y)
                (natp x)
                (integerp y))
           (<= (integer-length x) (integer-length y)))
  :hints (("Goal"
           :induct (double-floor-by-2-induct x y)
           :in-theory (enable integer-length))))

(defthm integer-length-of-times-2
  (implies (posp n)
           (equal (integer-length (* 2 n))
                  (+ 1 (integer-length n))))
  :hints (("Goal" :in-theory (enable integer-length))))

(in-theory (disable integer-length))

(defthm integer-length-of-floor-by-2
  (implies (posp i)
           (equal (integer-length (floor i 2))
                  (+ -1 (integer-length i))))
  :hints (("Goal" :in-theory (enable integer-length))))

;enable?
(defthmd floor-when-multiple
  (implies (integerp (/ i j))
           (equal (floor i j)
                  (/ i j)))
  :hints (("Goal" :in-theory (enable floor numerator))))

;dup?
(defthm floor-by-2-bound-even-linear
  (implies (and (<= k x)
                (syntaxp (quotep k))
                (natp x) ;gen?
                (natp k)  ;gets computed
                (evenp k) ;gets computed
                )
           (<= (/ k 2) (floor x 2)))
  :rule-classes ((:linear :trigger-terms ((floor x 2))))
  :hints (("Goal" :cases ((equal x k))
           :in-theory (e/d (evenp) (floor-weak-monotone))
           :use (:instance floor-weak-monotone (i1 k) (i2 x) (j 2)))))


;gen?
(defthm <-of-1-and-floor-of-2
  (implies (rationalp x) ;(natp x)
           (equal (< 1 (floor x 2))
                  (<= 4 x))))

(defthm equal-of-0-and-integer-length
  (implies (natp i)
           (equal (equal 0 (integer-length i))
                  (equal i 0)))
  :hints (("Goal" :expand ((integer-length i))
           :in-theory (disable integer-length-of-floor-by-2))))

(defthm equal-of-1-and-integer-length
  (implies (natp i)
           (equal (equal (integer-length i) 1)
                  (equal i 1)))
  :hints (("Goal" :expand ((integer-length i))
           :in-theory (disable integer-length-of-floor-by-2))))

(defthm <-of-1-and-integer-length
  (implies (and (integerp k)
                (< 1 k))
           (< 1 (integer-length k)))
  :hints (("Goal" :in-theory (enable integer-length))))

;; The function LG computes the floor of the base-2 logarithm of its argument.

;; TODO: Rename lg to floor-of-lg ?

;; TODO: what should lg of 0 be?
;; TODO: Add a guard that x is positive?

;; See also ceiling-of-lg.lisp.

(include-book "kestrel/arithmetic-light/integer-length" :dir :system) ;move

(defund lg (x)
  (declare (type integer x))
  (+ -1 (integer-length x)))

(defthm lg-of-expt
  (implies (natp n)
           (equal (lg (expt 2 n))
                  n))
  :hints (("Goal" :in-theory (enable lg))))

(defthmd lg-of-both-sides
  (implies (equal x y)
           (equal (lg x) (lg y))))

(defthm equal-of-expt-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (quotep size)) ;avoid loops if (:e expt) is disabled
                              ))
                (natp size))
           (equal (equal (expt 2 size) k)
                  (and (equal k (expt 2 (lg k))) ;k must be a power of 2
                       (equal size (lg k)))))
  :hints (("Goal" :use ((:instance lg-of-both-sides (x (expt 2 size)) (y k))))))

;todo: lg of mask?

(defthm equal-of-0-and-lg
  (implies (natp k)
           (equal (equal 0 (lg k))
                  (equal 1 k)))
  :hints (("Goal" :in-theory (enable lg integer-length))))

(defthm natp-of-lg
  (implies (natp x)
           (equal (natp (lg x))
                  (posp x)))
  :hints (("Goal" :in-theory (enable lg))))

;todo: prove something about integer-length first?
(defthm posp-of-lg
  (implies (natp x)
           (equal (posp (lg x))
                  (< 1 x)))
  :hints (("Goal" :cases ((< 1 X))
           :in-theory (enable lg integer-length))))

(defthm natp-of-lg-type
  (implies (posp x)
           (natp (lg x)))
  :rule-classes :type-prescription)

(defthm expt-of-lg
  (implies (power-of-2p x)
           (equal (expt 2 (lg x))
                  x))
  :hints (("Goal" :in-theory (enable power-of-2p lg))))

(defthm <-of-expt-2-of-lg-same
  (implies (posp n)
           (equal (< (expt 2 (lg n)) n)
                  (not (power-of-2p n))))
  :hints (("Goal" :in-theory (enable lg))))

(defthm <-of-expt-2-of-lg-same-linear
  (implies (and (not (power-of-2p n))
                (posp n))
           (< (expt 2 (lg n)) n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable lg))))

(defthm <-of-lg-and-0
  (implies (integerp i)
           (equal (< (lg i) 0)
                  (or (equal i 0)
                      (equal i -1))))
  :hints (("Goal" :in-theory (enable lg))))

(defthm lg-of-*-of-1/2
  (implies (and (evenp x)
                (integerp x))
           (equal (lg (* 1/2 x))
                  (if (equal 0 x)
                      -1
                    (+ -1 (lg x)))))
  :hints (("Goal" :in-theory (enable lg))))

(defthmd <-of-lg-when-unsigned-byte-p
  (implies (unsigned-byte-p n x)
           (< (lg x) n))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable lg))))

(defthm <-of-lg-when-unsigned-byte-p-cheap
  (implies (unsigned-byte-p n x)
           (< (lg x) n))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable lg))))
