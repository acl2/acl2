; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(local (include-book "projects/quadratic-reciprocity/eisenstein" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Primes
; ------

; Our elliptic curve library depends on
; (part of) the quadratic reciprocity library in the community books,
; which, in particular, includes a predicate for prime numbers.

; This book is a wrapper of that library for our elliptic curve library.
; We add a theorem and disable ODDP.
; This is in fact more general than our elliptic curve library,
; and it could be turned into a more general wrapper,
; or the theorem could be added to the quadratic reciprocity library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable oddp))

(defthm odd-when-primep-and-not-2
  (implies (and (rtl::primep p)
                (< 2 p))
           (oddp p)))
