; Fixing Function for Integer Ranges
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-range-fix ((lower integerp)
                           (upper integerp)
                           (x (integer-range-p lower upper x)))
  :returns (fixed-x (integer-range-p lower upper fixed-x)
                    :hyp (and (integerp lower)
                              (integerp upper)
                              (< lower upper)))
  :parents (kestrel-utilities integer-range-p)
  :short "Fixing function for @(tsee integer-range-p)."
  :long
  "<p>
   Since the set denoted by @(tsee integer-range-p)
   is empty for some values of @('lower') and @('upper'),
   this fixing function cannot always return a value satisfying the predicate.
   Even though @(tsee integer-range-p)
   does not fix its @('lower') and @('upper') arguments to @(tsee integerp),
   this fixing function does,
   i.e. it treats @('lower') and @('upper') as integers.
   Thus, the set (range) denoted by @(tsee integer-range-p) is empty iff
   @('lower') is not below @('upper').
   If the range is empty, this fixing function returns 0.
   If the range is not empty but @('x') is below @('lower'),
   we return @('lower'), i.e. the closest value to @('x') in range.
   If the range is not empty and @('x') is not below @('upper'),
   we return one below @('upper'), i.e. the closest value to @('x') in range.
   </p>
   <p>
   Since @(tsee integer-range-p) is enabled by default,
   this fixing function is also enabled by default.
   When these functions are enabled, they are meant as abbreviations,
   and theorems triggered by them may not fire during proofs.
   </p>"
  (mbe :logic (b* ((lower (ifix lower))
                   (upper (ifix upper))
                   (x (ifix x)))
                (if (< lower upper)
                    (cond ((< x lower) lower)
                          ((>= x upper) (1- upper))
                          (t x))
                  0))
       :exec x)
  :enabled t
  :hooks (:fix)
  ///

  (defrule integer-range-fix-when-integer-range-p
    (implies (and (integer-range-p (ifix lower) (ifix upper) x)
                  (< (ifix lower) (ifix upper)))
             (equal (integer-range-fix lower upper x)
                    x))))
