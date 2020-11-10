; More rules about arithmetic
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Arithmetic rules with more dependencies than the basic rules.

(include-book "arith")
(include-book "kestrel/utilities/polarity" :dir :system)

;Strengthen (< x (+ 1 y)) to (<= x y) when we know the values are integers.
(defthm <-of-+-of-1-when-integers-strengthen-with-polarity
  (implies (and (syntaxp (want-to-strengthen (< x (+ 1 y))))
                (integerp x)
                (integerp y))
           (equal (< x (+ 1 y))
                  (<= x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 0))))

;better than INTEGER-TIGHTEN-BOUND
(defthm >-constant-when-integer-strengthen
  (implies (and (syntaxp (quotep k))
                (syntaxp (want-to-strengthen (< k x)))
                (integerp k)
                (integerp x)) ;could be slow?
           (equal (< k x)
                  (<= (+ 1 k) x) ;k+1 gets computed
                  )))

(defthm <-of-constant-when-integer-strengthen
  (implies (and (syntaxp (quotep k))
                (syntaxp (want-to-strengthen (< x k)))
                (not (equal x free))
                (syntaxp (quotep free))
                (equal free (+ -1 k))
                (integerp k)
                (integerp x)) ;could be slow?
           (equal (< x k)
                  (< x (+ -1 k)) ;k-1 gets computed
                  )))
