; Base-2 logarithm (rounded up)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The function CEILING-OF-LG computes the ceiling of the base-2 logarithm of
;; its argument.

(local (include-book "integer-length"))
(local (include-book "expt"))
(local (include-book "times"))

;; See also lg.lisp.

(defund ceiling-of-lg (x)
  (declare (type integer x))
  (integer-length (+ -1 x)))

(defthm integerp-of-ceiling-of-lg
  (integerp (ceiling-of-lg x)))

(defthm natp-of-ceiling-of-lg
  (natp (ceiling-of-lg x)))

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
