; Base-2 integer logarithm
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also log2.lisp and ceiling-of-lg.lisp.

;; TODO: Deprecate this book in favor of log2.lisp.

;TODO: Which do we prefer, lg or log2, or integer-length?  Some rules about
;integer-length could be adapted to target lg or log2.

(include-book "lg-def")
(include-book "power-of-2p")
(local (include-book "integer-length"))
(local (include-book "expt2"))
(local (include-book "plus"))
(local (include-book "floor"))

(defthm lg-of-expt
  (implies (natp x)
           (equal (lg (expt 2 x))
                  x))
  :hints (("Goal" :in-theory (enable lg))))

;; (defthmd lg-of-both-sides
;;   (implies (equal x y)
;;            (equal (lg x) (lg y))))

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
  :hints (("Goal"; :cases ((< 1 X))
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
