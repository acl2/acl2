; Tests of the floating point formalization
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ieee-floats-as-bvs")
(include-book "std/testing/assert-equal" :dir :system)

;; Exhaustive tests of a very small floating-point format with just 4 bits (1
;; sign bit, 2 exponent bits and 1 trailing significand bit).  See the table "4
;; bits and fewer" in https://en.wikipedia.org/wiki/Minifloat.
(assert-equal (decode-bv-float 4 2 0) :float-positive-zero)
(assert-equal (decode-bv-float 4 2 1) 1/2)
(assert-equal (decode-bv-float 4 2 2) 1)
(assert-equal (decode-bv-float 4 2 3) 3/2)
(assert-equal (decode-bv-float 4 2 4) 2)
(assert-equal (decode-bv-float 4 2 5) 3)
(assert-equal (decode-bv-float 4 2 6) :float-positive-infinity)
(assert-equal (decode-bv-float 4 2 7) :float-nan)
(assert-equal (decode-bv-float 4 2 8) :float-negative-zero)
(assert-equal (decode-bv-float 4 2 9) -1/2)
(assert-equal (decode-bv-float 4 2 10) -1)
(assert-equal (decode-bv-float 4 2 11) -3/2)
(assert-equal (decode-bv-float 4 2 12) -2)
(assert-equal (decode-bv-float 4 2 13) -3)
(assert-equal (decode-bv-float 4 2 14) :float-negative-infinity)
(assert-equal (decode-bv-float 4 2 15) :float-nan)
