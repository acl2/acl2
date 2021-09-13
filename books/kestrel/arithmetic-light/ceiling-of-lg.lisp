; Base-2 logarithm (rounded up)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The function CEILING-OF-LG computes the ceiling of the base-2 logarithm of
;; its argument.

(local (include-book "integer-length"))

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
