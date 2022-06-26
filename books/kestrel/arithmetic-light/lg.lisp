; Base-2 integer logarithm
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;TODO: Which do we prefer, lg or integer-length?  i think i like lg best,
;but my current rules may target integer-length?

(include-book "power-of-2p")
(include-book "integer-length")
(local (include-book "expt2"))
(local (include-book "plus"))
(local (include-book "floor"))

;; The function LG computes the floor of the base-2 logarithm of its argument.

;; TODO: Rename lg to floor-of-lg ?

;; TODO: what should lg of 0 be?
;; TODO: Extend to non-integers?

;; See also ceiling-of-lg.lisp.

;; Returns the floor of the base 2 logarithm of x.  Not meaningful for 0.
(defund lg (x)
  (declare (xargs :guard (posp x)
                  :split-types t)
           (type integer x))
  (+ -1 (integer-length x)))

(defthm lg-of-expt
  (implies (natp x)
           (equal (lg (expt 2 x))
                  x))
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

(defthm expt-of-lg-when-power-of-2p
  (implies (power-of-2p x)
           (equal (expt 2 (lg x))
                  x))
  :hints (("Goal" :in-theory (enable power-of-2p lg))))

;; These next two help show that LG is correct:

(defthm <=-of-expt-2-of-lg-linear
  (implies (posp x)
           (<= (expt 2 (lg x)) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable lg))))

(defthm <=-of-expt-2-of-+-of-1-and-lg-linear
  (implies (posp x)
           (< x (expt 2 (+ 1 (lg x)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable lg))))

(defthm <-of-expt-2-of-lg-same
  (implies (posp x)
           (equal (< (expt 2 (lg x)) x)
                  (not (power-of-2p x))))
  :hints (("Goal" :in-theory (enable lg))))

(defthm <-of-expt-2-of-lg-same-linear
  (implies (and (not (power-of-2p x))
                (posp x))
           (< (expt 2 (lg x)) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable lg))))

(defthm <-of-lg-and-0
  (implies (integerp x)
           (equal (< (lg x) 0)
                  (or (equal x 0)
                      (equal x -1))))
  :hints (("Goal" :in-theory (enable lg))))

(defthm lg-of-*-of-1/2
  (implies (and (evenp x)
                (rationalp x))
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
