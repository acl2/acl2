; Rules about len-mult-of-8p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book includes rules about len-mult-of-8p that use polarities.

(include-book "len-mult-of-8p")
(include-book "kestrel/utilities/polarity" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
;(local (include-book "kestrel/bv/arith" :dir :system)) ;todo: reduce, for integerp-squeeze

;dup
(local
 (DEFTHM INTEGERP-SQUEEZE
   (IMPLIES (AND (< 0 X) (< X 1))
            (NOT (INTEGERP X)))))

(defthm mult-of-8-when-positive
  (implies (and (syntaxp (want-to-strengthen (< x 8)))
                (integerp (* 1/8 x)))
           (equal (< x 8)
                  (<= x 0)))
  :hints (("Goal"
           :use (:instance integerp-squeeze
                           (x (* 1/8 x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0))))

;todo: improve polarities to handle backchaining...
(defthm mult-of-8-when-positive-gen-polarity
  (implies (and (syntaxp (want-to-strengthen (< x 8))) ;todo: why not k instead of 8?
                (syntaxp (quotep k))
                (posp k)
                (<= k 8)
                (integerp (* 1/8 x)))
           (equal (< x k)
                  (<= x 0)))
  :hints (("Goal"
           :use (:instance integerp-squeeze
                           (x (* 1/8 x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil nil nil nil 0))))

(defthm mult-of-8-when-positive-gen-alt
  (implies (and (syntaxp (want-to-weaken (< k x)))
                (syntaxp (quotep k))
                (posp k)
                (< k 8)
                (integerp (* 1/8 x)))
           (equal (< k x)
                  (< 0 x)))
  :hints (("Goal"
           :use (:instance integerp-squeeze
                           (x (* 1/8 x))))))
