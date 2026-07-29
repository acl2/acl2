; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "primitives-evaluation")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro iv (n) `(expr-value-base (base-value-int (int-value ,n))))
(defmacro fv (r) `(expr-value-base (base-value-float (float-value-ratio ,r))))
(defmacro bv (b) `(expr-value-base (base-value-bool ,b)))
(defmacro f-n0 () '(expr-value-base (base-value-float (float-value-neg0))))
(defmacro f-pinf () '(expr-value-base (base-value-float (float-value-posinf))))
(defmacro f-ninf () '(expr-value-base (base-value-float (float-value-neginf))))
(defmacro f-nan () '(expr-value-base (base-value-float (float-value-nan))))

(defconst *int-max* 9223372036854775807)  ; Haskell 64-bit Int maxBound, 2^63 - 1
(defconst *int-min* -9223372036854775808) ; Haskell 64-bit Int minBound, -2^63

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-int-add (iv 2) (iv 3)) (iv 5))
(acl2::assert-equal (prim-int-add (iv -2) (iv 3)) (iv 1))
(acl2::assert-event (reserrp (prim-int-add (bv t) (iv 1))))
; mismatch: Haskell's 64-bit Int overflows, wrapping to minBound
(acl2::assert-equal (prim-int-add (iv *int-max*) (iv 1)) (iv (1+ *int-max*)))
; mismatch: Haskell underflows, wrapping to maxBound
(acl2::assert-equal (prim-int-add (iv *int-min*) (iv -1)) (iv (1- *int-min*)))

(acl2::assert-equal (prim-int-sub (iv 5) (iv 3)) (iv 2))
(acl2::assert-equal (prim-int-sub (iv 3) (iv 5)) (iv -2))
; mismatch: Haskell underflows, wrapping to maxBound
(acl2::assert-equal (prim-int-sub (iv *int-min*) (iv 1)) (iv (1- *int-min*)))
; mismatch: Haskell overflows, wrapping to minBound
(acl2::assert-equal (prim-int-sub (iv *int-max*) (iv -1)) (iv (1+ *int-max*)))

(acl2::assert-equal (prim-int-mul (iv 2) (iv 3)) (iv 6))
(acl2::assert-equal (prim-int-mul (iv -2) (iv 3)) (iv -6))
(acl2::assert-equal (prim-int-mul (iv 0) (iv 5)) (iv 0))
; mismatch: Haskell overflows, wrapping to -2
(acl2::assert-equal (prim-int-mul (iv *int-max*) (iv 2)) (iv (* 2 *int-max*)))

(acl2::assert-equal (prim-int-div (iv 6) (iv 3)) (iv 2))
(acl2::assert-equal (prim-int-div (iv 7) (iv 2)) (iv 3))
(acl2::assert-equal (prim-int-div (iv -7) (iv 2)) (iv -4))
(acl2::assert-equal (prim-int-div (iv 7) (iv -3)) (iv -3))
(acl2::assert-event (reserrp (prim-int-div (iv 5) (iv 0))))
; mismatch: Haskell raises arithmetic overflow (minBound div -1 is not a 64-bit Int)
(acl2::assert-equal (prim-int-div (iv *int-min*) (iv -1)) (iv (- *int-min*)))

(acl2::assert-equal (prim-int-expt (iv 2) (iv 10)) (iv 1024))
(acl2::assert-equal (prim-int-expt (iv -2) (iv 3)) (iv -8))
(acl2::assert-equal (prim-int-expt (iv 5) (iv 0)) (iv 1))
(acl2::assert-equal (prim-int-expt (iv 0) (iv 0)) (iv 1))
(acl2::assert-event (reserrp (prim-int-expt (iv 2) (iv -1))))
(acl2::assert-event (reserrp (prim-int-expt (bv t) (iv 1))))
; mismatch: Haskell's 64-bit Int overflows, wrapping to 0
(acl2::assert-equal (prim-int-expt (iv 2) (iv 64)) (iv (expt 2 64)))

(acl2::assert-equal (prim-int-mod (iv 7) (iv 3)) (iv 1))
(acl2::assert-equal (prim-int-mod (iv -7) (iv 3)) (iv 2))
(acl2::assert-equal (prim-int-mod (iv 7) (iv -3)) (iv -2))
(acl2::assert-equal (prim-int-mod (iv *int-min*) (iv -1)) (iv 0))
(acl2::assert-event (reserrp (prim-int-mod (iv 5) (iv 0))))

(acl2::assert-equal (prim-int-max (iv 2) (iv 3)) (iv 3))
(acl2::assert-equal (prim-int-max (iv 3) (iv 2)) (iv 3))
(acl2::assert-equal (prim-int-max (iv 5) (iv 5)) (iv 5))
(acl2::assert-equal (prim-int-max (iv -1) (iv -5)) (iv -1))
(acl2::assert-equal (prim-int-max (iv *int-min*) (iv *int-max*)) (iv *int-max*))

(acl2::assert-equal (prim-int-min (iv 2) (iv 3)) (iv 2))
(acl2::assert-equal (prim-int-min (iv 3) (iv 2)) (iv 2))
(acl2::assert-equal (prim-int-min (iv -1) (iv -5)) (iv -5))
(acl2::assert-equal (prim-int-min (iv *int-min*) (iv *int-max*)) (iv *int-min*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-int-bit-and (iv 6) (iv 3)) (iv 2))
(acl2::assert-equal (prim-int-bit-and (iv -1) (iv 5)) (iv 5))
(acl2::assert-equal (prim-int-bit-and (iv 0) (iv 7)) (iv 0))

(acl2::assert-equal (prim-int-bit-or (iv 6) (iv 3)) (iv 7))
(acl2::assert-equal (prim-int-bit-or (iv 0) (iv 0)) (iv 0))
(acl2::assert-equal (prim-int-bit-or (iv -1) (iv 0)) (iv -1))

(acl2::assert-equal (prim-int-bit-xor (iv 6) (iv 3)) (iv 5))
(acl2::assert-equal (prim-int-bit-xor (iv 5) (iv 5)) (iv 0))
(acl2::assert-equal (prim-int-bit-xor (iv -1) (iv 0)) (iv -1))

(acl2::assert-equal (prim-int-bit-not (iv 0)) (iv -1))
(acl2::assert-equal (prim-int-bit-not (iv 5)) (iv -6))
(acl2::assert-equal (prim-int-bit-not (iv -1)) (iv 0))
(acl2::assert-equal (prim-int-bit-not (iv *int-max*)) (iv *int-min*))
(acl2::assert-equal (prim-int-bit-not (iv *int-min*)) (iv *int-max*))

(acl2::assert-equal (prim-int-shl (iv 1) (iv 4)) (iv 16))
(acl2::assert-equal (prim-int-shl (iv 3) (iv 0)) (iv 3))
(acl2::assert-equal (prim-int-shl (iv -1) (iv 2)) (iv -4))
(acl2::assert-event (reserrp (prim-int-shl (iv 5) (iv -1))))
; mismatch: Haskell's 64-bit shiftL sets the sign bit, giving minBound
(acl2::assert-equal (prim-int-shl (iv 1) (iv 63)) (iv (1+ *int-max*)))
; mismatch: Haskell drops bits shifted past bit 63, giving 0
(acl2::assert-equal (prim-int-shl (iv 1) (iv 64)) (iv (expt 2 64)))
; mismatch: Haskell shift >= word width gives 0
(acl2::assert-equal (prim-int-shl (iv 1) (iv 100)) (iv (expt 2 100)))
; mismatch: Haskell overflows, giving -2
(acl2::assert-equal (prim-int-shl (iv *int-max*) (iv 1)) (iv (* 2 *int-max*)))

(acl2::assert-equal (prim-int-shr (iv 16) (iv 2)) (iv 4))
(acl2::assert-equal (prim-int-shr (iv 5) (iv 0)) (iv 5))
(acl2::assert-equal (prim-int-shr (iv -8) (iv 1)) (iv -4))
(acl2::assert-equal (prim-int-shr (iv -1) (iv 1)) (iv -1))
(acl2::assert-equal (prim-int-shr (iv 5) (iv 100)) (iv 0))
(acl2::assert-equal (prim-int-shr (iv -1) (iv 100)) (iv -1))
(acl2::assert-event (reserrp (prim-int-shr (iv 5) (iv -1))))

(acl2::assert-equal (prim-int-popc (iv 0)) (iv 0))
(acl2::assert-equal (prim-int-popc (iv 5)) (iv 2))
(acl2::assert-equal (prim-int-popc (iv 7)) (iv 3))
(acl2::assert-equal (prim-int-popc (iv *int-max*)) (iv 63))
; mismatch: Haskell counts the 64-bit two's-complement bits, giving 64
(acl2::assert-event (reserrp (prim-int-popc (iv -1))))
; mismatch: Haskell gives 61
(acl2::assert-event (reserrp (prim-int-popc (iv -8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-int-eq (iv 2) (iv 2)) (bv t))
(acl2::assert-equal (prim-int-eq (iv 2) (iv 3)) (bv nil))
(acl2::assert-equal (prim-int-eq (iv *int-min*) (iv *int-min*)) (bv t))

(acl2::assert-equal (prim-int-neq (iv 2) (iv 3)) (bv t))
(acl2::assert-equal (prim-int-neq (iv 2) (iv 2)) (bv nil))

(acl2::assert-equal (prim-int-lt (iv 2) (iv 3)) (bv t))
(acl2::assert-equal (prim-int-lt (iv 3) (iv 2)) (bv nil))
(acl2::assert-equal (prim-int-lt (iv 2) (iv 2)) (bv nil))
(acl2::assert-equal (prim-int-lt (iv *int-min*) (iv *int-max*)) (bv t))

(acl2::assert-equal (prim-int-gt (iv 3) (iv 2)) (bv t))
(acl2::assert-equal (prim-int-gt (iv 2) (iv 3)) (bv nil))
(acl2::assert-equal (prim-int-gt (iv *int-max*) (iv *int-min*)) (bv t))

(acl2::assert-equal (prim-int-leq (iv 2) (iv 2)) (bv t))
(acl2::assert-equal (prim-int-leq (iv 2) (iv 3)) (bv t))
(acl2::assert-equal (prim-int-leq (iv 3) (iv 2)) (bv nil))

(acl2::assert-equal (prim-int-geq (iv 2) (iv 2)) (bv t))
(acl2::assert-equal (prim-int-geq (iv 3) (iv 2)) (bv t))
(acl2::assert-equal (prim-int-geq (iv 2) (iv 3)) (bv nil))

(acl2::assert-equal (prim-int-to-float (iv 5)) (fv 5))
(acl2::assert-equal (prim-int-to-float (iv -3)) (fv -3))
(acl2::assert-equal (prim-int-to-float (iv 0)) (fv 0))
; mismatch: single-precision Float rounds (24-bit mantissa) to 1073741824
(acl2::assert-equal (prim-int-to-float (iv 1073741825)) (fv 1073741825))
; mismatch: Haskell rounds to 9.223372e18
(acl2::assert-equal (prim-int-to-float (iv *int-max*)) (fv *int-max*))

(acl2::assert-equal (prim-int-to-bool (iv 0)) (bv nil))
(acl2::assert-equal (prim-int-to-bool (iv 5)) (bv t))
(acl2::assert-equal (prim-int-to-bool (iv -3)) (bv t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-bool-not (bv t)) (bv nil))
(acl2::assert-equal (prim-bool-not (bv nil)) (bv t))

(acl2::assert-equal (prim-bool-and (bv t) (bv t)) (bv t))
(acl2::assert-equal (prim-bool-and (bv t) (bv nil)) (bv nil))
(acl2::assert-equal (prim-bool-and (bv nil) (bv nil)) (bv nil))

(acl2::assert-equal (prim-bool-or (bv t) (bv nil)) (bv t))
(acl2::assert-equal (prim-bool-or (bv nil) (bv nil)) (bv nil))
(acl2::assert-equal (prim-bool-or (bv t) (bv t)) (bv t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-bool-eq (bv t) (bv t)) (bv t))
(acl2::assert-equal (prim-bool-eq (bv nil) (bv nil)) (bv t))
(acl2::assert-equal (prim-bool-eq (bv t) (bv nil)) (bv nil))

(acl2::assert-equal (prim-bool-neq (bv t) (bv nil)) (bv t))
(acl2::assert-equal (prim-bool-neq (bv t) (bv t)) (bv nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-bool-to-int (bv t)) (iv 1))
(acl2::assert-equal (prim-bool-to-int (bv nil)) (iv 0))

(acl2::assert-equal (prim-bool-to-float (bv t)) (fv 1))
(acl2::assert-equal (prim-bool-to-float (bv nil)) (fv 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-float-add (fv 2) (fv 3)) (fv 5))
(acl2::assert-equal (prim-float-add (fv 1/2) (fv 1/2)) (fv 1))
(acl2::assert-equal (prim-float-add (f-nan) (fv 1)) (f-nan))
(acl2::assert-equal (prim-float-add (f-pinf) (f-ninf)) (f-nan))
(acl2::assert-equal (prim-float-add (f-pinf) (fv 5)) (f-pinf))
(acl2::assert-equal (prim-float-add (f-ninf) (fv 5)) (f-ninf))
(acl2::assert-equal (prim-float-add (f-n0) (f-n0)) (f-n0))
(acl2::assert-equal (prim-float-add (f-n0) (fv 0)) (fv 0))
(acl2::assert-equal (prim-float-add (fv 5) (fv -5)) (fv 0))
; mismatch: single-precision Float rounds (24-bit mantissa) to 1073741824
(acl2::assert-equal (prim-float-add (fv 1073741824) (fv 1)) (fv 1073741825))

(acl2::assert-equal (prim-float-sub (fv 5) (fv 3)) (fv 2))
(acl2::assert-equal (prim-float-sub (f-nan) (fv 1)) (f-nan))
(acl2::assert-equal (prim-float-sub (f-pinf) (f-pinf)) (f-nan))
(acl2::assert-equal (prim-float-sub (f-ninf) (f-ninf)) (f-nan))
(acl2::assert-equal (prim-float-sub (f-pinf) (f-ninf)) (f-pinf))
(acl2::assert-equal (prim-float-sub (fv 1) (f-ninf)) (f-pinf))
(acl2::assert-equal (prim-float-sub (f-ninf) (fv 1)) (f-ninf))
(acl2::assert-equal (prim-float-sub (fv 1) (f-pinf)) (f-ninf))
(acl2::assert-equal (prim-float-sub (f-n0) (fv 0)) (f-n0))
(acl2::assert-equal (prim-float-sub (f-n0) (f-n0)) (fv 0))
(acl2::assert-equal (prim-float-sub (fv 5) (fv 5)) (fv 0))

(acl2::assert-equal (prim-float-mul (fv 2) (fv 3)) (fv 6))
(acl2::assert-equal (prim-float-mul (fv -2) (fv 3)) (fv -6))
(acl2::assert-equal (prim-float-mul (f-nan) (fv 1)) (f-nan))
(acl2::assert-equal (prim-float-mul (fv 0) (f-pinf)) (f-nan))
(acl2::assert-equal (prim-float-mul (f-n0) (f-pinf)) (f-nan))
(acl2::assert-equal (prim-float-mul (f-pinf) (f-pinf)) (f-pinf))
(acl2::assert-equal (prim-float-mul (f-pinf) (f-ninf)) (f-ninf))
(acl2::assert-equal (prim-float-mul (f-ninf) (f-ninf)) (f-pinf))
(acl2::assert-equal (prim-float-mul (f-pinf) (fv -2)) (f-ninf))
(acl2::assert-equal (prim-float-mul (fv 0) (fv -5)) (f-n0))
(acl2::assert-equal (prim-float-mul (f-n0) (fv -5)) (fv 0))
(acl2::assert-equal (prim-float-mul (f-n0) (fv 5)) (f-n0))
; mismatch: Haskell Float overflows to Infinity
(acl2::assert-equal (prim-float-mul (fv (expt 10 38)) (fv (expt 10 38)))
                    (fv (expt 10 76)))

(acl2::assert-equal (prim-float-div (fv 6) (fv 3)) (fv 2))
(acl2::assert-equal (prim-float-div (fv -6) (fv 3)) (fv -2))
(acl2::assert-equal (prim-float-div (f-nan) (fv 1)) (f-nan))
(acl2::assert-equal (prim-float-div (fv 0) (fv 0)) (f-nan))
(acl2::assert-equal (prim-float-div (f-pinf) (f-pinf)) (f-nan))
(acl2::assert-equal (prim-float-div (fv 5) (fv 0)) (f-pinf))
(acl2::assert-equal (prim-float-div (fv 5) (f-n0)) (f-ninf))
(acl2::assert-equal (prim-float-div (fv -5) (fv 0)) (f-ninf))
(acl2::assert-equal (prim-float-div (fv -5) (f-n0)) (f-pinf))
(acl2::assert-equal (prim-float-div (f-pinf) (fv -2)) (f-ninf))
(acl2::assert-equal (prim-float-div (fv 5) (f-pinf)) (fv 0))
(acl2::assert-equal (prim-float-div (fv 5) (f-ninf)) (f-n0))
(acl2::assert-equal (prim-float-div (fv 0) (fv -5)) (f-n0))
(acl2::assert-equal (prim-float-div (f-n0) (fv 5)) (f-n0))

(acl2::assert-equal (prim-float-expt (fv 2) (fv 3)) (fv 8))
(acl2::assert-equal (prim-float-expt (fv 2) (fv -1)) (fv 1/2))
(acl2::assert-equal (prim-float-expt (fv -2) (fv 3)) (fv -8))
(acl2::assert-equal (prim-float-expt (fv -2) (fv -3)) (fv -1/8))
(acl2::assert-equal (prim-float-expt (fv 5) (fv 0)) (fv 1))
(acl2::assert-equal (prim-float-expt (f-nan) (fv 0)) (fv 1))
(acl2::assert-equal (prim-float-expt (f-pinf) (fv 0)) (fv 1))
(acl2::assert-equal (prim-float-expt (fv 1) (f-nan)) (fv 1))
(acl2::assert-equal (prim-float-expt (fv -1) (f-pinf)) (fv 1))
(acl2::assert-equal (prim-float-expt (fv -1) (f-ninf)) (fv 1))
(acl2::assert-equal (prim-float-expt (f-nan) (fv 3)) (f-nan))
(acl2::assert-equal (prim-float-expt (fv 2) (f-nan)) (f-nan))
(acl2::assert-equal (prim-float-expt (fv 2) (f-pinf)) (f-pinf))
(acl2::assert-equal (prim-float-expt (fv 1/2) (f-pinf)) (fv 0))
(acl2::assert-equal (prim-float-expt (fv 2) (f-ninf)) (fv 0))
(acl2::assert-equal (prim-float-expt (fv 1/2) (f-ninf)) (f-pinf))
(acl2::assert-equal (prim-float-expt (fv 0) (fv 3)) (fv 0))
(acl2::assert-equal (prim-float-expt (fv 0) (fv -3)) (f-pinf))
(acl2::assert-equal (prim-float-expt (f-n0) (fv 3)) (f-n0))
(acl2::assert-equal (prim-float-expt (f-n0) (fv 2)) (fv 0))
(acl2::assert-equal (prim-float-expt (f-n0) (fv -3)) (f-ninf))
(acl2::assert-equal (prim-float-expt (f-n0) (fv -2)) (f-pinf))
(acl2::assert-equal (prim-float-expt (f-pinf) (fv 3)) (f-pinf))
(acl2::assert-equal (prim-float-expt (f-pinf) (fv -3)) (fv 0))
(acl2::assert-equal (prim-float-expt (f-ninf) (fv 3)) (f-ninf))
(acl2::assert-equal (prim-float-expt (f-ninf) (fv 2)) (f-pinf))
(acl2::assert-equal (prim-float-expt (f-ninf) (fv -3)) (f-n0))
(acl2::assert-equal (prim-float-expt (f-ninf) (fv -2)) (fv 0))
; mismatch: Haskell computes 2**0.5 = 1.4142135; we require an integer exponent
(acl2::assert-event (reserrp (prim-float-expt (fv 2) (fv 1/2))))
; mismatch: Haskell computes 9**0.5 = 3.0
(acl2::assert-event (reserrp (prim-float-expt (fv 9) (fv 1/2))))
; mismatch: Haskell Float overflows to Infinity
(acl2::assert-equal (prim-float-expt (fv (expt 10 38)) (fv 2))
                    (fv (expt 10 76)))

; mismatch: Haskell computes sqrt 4 = 2.0
(acl2::assert-event (reserrp (prim-float-sqrt (fv 4))))
; mismatch: Haskell computes sqrt 2 = 1.4142135
(acl2::assert-event (reserrp (prim-float-sqrt (fv 2))))
; mismatch: Haskell computes sqrt 0 = 0.0
(acl2::assert-event (reserrp (prim-float-sqrt (fv 0))))
; mismatch: Haskell computes sqrt -1 = NaN
(acl2::assert-event (reserrp (prim-float-sqrt (fv -1))))
; mismatch: Haskell computes sqrt Infinity = Infinity
(acl2::assert-event (reserrp (prim-float-sqrt (f-pinf))))
; mismatch: Haskell computes sqrt NaN = NaN
(acl2::assert-event (reserrp (prim-float-sqrt (f-nan))))

(acl2::assert-equal (prim-float-max (fv 2) (fv 3)) (fv 3))
(acl2::assert-equal (prim-float-max (fv 3) (fv 2)) (fv 3))
(acl2::assert-equal (prim-float-max (f-pinf) (fv 5)) (f-pinf))
(acl2::assert-equal (prim-float-max (f-ninf) (fv 5)) (fv 5))
(acl2::assert-equal (prim-float-max (f-nan) (fv 1)) (f-nan))
(acl2::assert-equal (prim-float-max (fv 1) (f-nan)) (fv 1))
(acl2::assert-equal (prim-float-max (f-n0) (fv 0)) (fv 0))
(acl2::assert-equal (prim-float-max (fv 0) (f-n0)) (f-n0))

(acl2::assert-equal (prim-float-min (fv 2) (fv 3)) (fv 2))
(acl2::assert-equal (prim-float-min (fv 3) (fv 2)) (fv 2))
(acl2::assert-equal (prim-float-min (f-pinf) (fv 5)) (fv 5))
(acl2::assert-equal (prim-float-min (f-ninf) (fv 5)) (f-ninf))
(acl2::assert-equal (prim-float-min (f-nan) (fv 1)) (fv 1))
(acl2::assert-equal (prim-float-min (fv 1) (f-nan)) (f-nan))
(acl2::assert-equal (prim-float-min (f-n0) (fv 0)) (f-n0))
(acl2::assert-equal (prim-float-min (fv 0) (f-n0)) (fv 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal (prim-float-eq (fv 2) (fv 2)) (bv t))
(acl2::assert-equal (prim-float-eq (fv 2) (fv 3)) (bv nil))
(acl2::assert-equal (prim-float-eq (f-n0) (fv 0)) (bv t))
(acl2::assert-equal (prim-float-eq (f-nan) (f-nan)) (bv nil))
(acl2::assert-equal (prim-float-eq (f-nan) (fv 1)) (bv nil))
(acl2::assert-equal (prim-float-eq (f-pinf) (f-pinf)) (bv t))
(acl2::assert-equal (prim-float-eq (f-pinf) (fv 5)) (bv nil))

(acl2::assert-equal (prim-float-neq (fv 2) (fv 3)) (bv t))
(acl2::assert-equal (prim-float-neq (fv 2) (fv 2)) (bv nil))
(acl2::assert-equal (prim-float-neq (f-nan) (f-nan)) (bv t))
(acl2::assert-equal (prim-float-neq (f-n0) (fv 0)) (bv nil))

(acl2::assert-equal (prim-float-lt (fv 2) (fv 3)) (bv t))
(acl2::assert-equal (prim-float-lt (fv 3) (fv 2)) (bv nil))
(acl2::assert-equal (prim-float-lt (fv 2) (fv 2)) (bv nil))
(acl2::assert-equal (prim-float-lt (f-n0) (fv 0)) (bv nil))
(acl2::assert-equal (prim-float-lt (f-ninf) (fv 5)) (bv t))
(acl2::assert-equal (prim-float-lt (fv 5) (f-pinf)) (bv t))
(acl2::assert-equal (prim-float-lt (f-nan) (fv 1)) (bv nil))

(acl2::assert-equal (prim-float-gt (fv 3) (fv 2)) (bv t))
(acl2::assert-equal (prim-float-gt (fv 2) (fv 3)) (bv nil))
(acl2::assert-equal (prim-float-gt (f-pinf) (fv 5)) (bv t))
(acl2::assert-equal (prim-float-gt (f-nan) (fv 1)) (bv nil))

(acl2::assert-equal (prim-float-leq (fv 2) (fv 2)) (bv t))
(acl2::assert-equal (prim-float-leq (fv 2) (fv 3)) (bv t))
(acl2::assert-equal (prim-float-leq (fv 3) (fv 2)) (bv nil))
(acl2::assert-equal (prim-float-leq (f-n0) (fv 0)) (bv t))
(acl2::assert-equal (prim-float-leq (f-ninf) (f-ninf)) (bv t))
(acl2::assert-equal (prim-float-leq (f-nan) (fv 1)) (bv nil))

(acl2::assert-equal (prim-float-geq (fv 2) (fv 2)) (bv t))
(acl2::assert-equal (prim-float-geq (fv 3) (fv 2)) (bv t))
(acl2::assert-equal (prim-float-geq (fv 2) (fv 3)) (bv nil))
(acl2::assert-equal (prim-float-geq (f-pinf) (f-pinf)) (bv t))
(acl2::assert-equal (prim-float-geq (f-nan) (fv 1)) (bv nil))

(acl2::assert-equal (prim-float-truncate (fv 5/2)) (iv 2))
(acl2::assert-equal (prim-float-truncate (fv -5/2)) (iv -2))
(acl2::assert-equal (prim-float-truncate (fv 4)) (iv 4))
(acl2::assert-equal (prim-float-truncate (f-n0)) (iv 0))
(acl2::assert-event (reserrp (prim-float-truncate (f-pinf))))
(acl2::assert-event (reserrp (prim-float-truncate (f-nan))))
; mismatch: Haskell truncate saturates the 64-bit Int to maxBound
(acl2::assert-equal (prim-float-truncate (fv (expt 10 30))) (iv (expt 10 30)))

(acl2::assert-equal (prim-float-round (fv 5/2)) (iv 2))
(acl2::assert-equal (prim-float-round (fv 7/2)) (iv 4))
(acl2::assert-equal (prim-float-round (fv 1/2)) (iv 0))
(acl2::assert-equal (prim-float-round (fv 3/2)) (iv 2))
(acl2::assert-equal (prim-float-round (fv -5/2)) (iv -2))
(acl2::assert-equal (prim-float-round (f-n0)) (iv 0))
(acl2::assert-event (reserrp (prim-float-round (f-pinf))))
(acl2::assert-event (reserrp (prim-float-round (f-nan))))
; mismatch: Haskell round saturates the 64-bit Int to maxBound
(acl2::assert-equal (prim-float-round (fv (expt 10 30))) (iv (expt 10 30)))

(acl2::assert-equal (prim-float-ceiling (fv 5/2)) (iv 3))
(acl2::assert-equal (prim-float-ceiling (fv -5/2)) (iv -2))
(acl2::assert-equal (prim-float-ceiling (fv 4)) (iv 4))
(acl2::assert-equal (prim-float-ceiling (f-n0)) (iv 0))
(acl2::assert-event (reserrp (prim-float-ceiling (f-pinf))))
(acl2::assert-event (reserrp (prim-float-ceiling (f-nan))))

(acl2::assert-equal (prim-float-floor (fv 5/2)) (iv 2))
(acl2::assert-equal (prim-float-floor (fv -5/2)) (iv -3))
(acl2::assert-equal (prim-float-floor (fv 4)) (iv 4))
(acl2::assert-equal (prim-float-floor (f-n0)) (iv 0))
(acl2::assert-event (reserrp (prim-float-floor (f-ninf))))
(acl2::assert-event (reserrp (prim-float-floor (f-nan))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unary (curried) application of primitive operation values:
; applying a binary operation to its first argument yields the next stage,
; whose application to the second argument yields the result.

(acl2::assert-equal
 (eval-primop-fun (primop-value-int-binary (int-binary-primop-add)) (iv 2))
 (expr-value-primop (make-primop-value-int-binary-x
                     :op (int-binary-primop-add)
                     :xval (iv 2))))

(acl2::assert-equal
 (eval-primop-fun (make-primop-value-int-binary-x :op (int-binary-primop-add)
                                                  :xval (iv 2))
                  (iv 3))
 (iv 5))

(acl2::assert-equal
 (eval-primop-fun-chain (primop-value-int-binary (int-binary-primop-add))
                        (list (iv 2) (iv 3)))
 (iv 5))

(acl2::assert-equal
 (eval-primop-fun-chain (primop-value-int-rel (int-rel-primop-lt))
                        (list (iv 2) (iv 3)))
 (bv t))

(acl2::assert-equal
 (eval-primop-fun-chain (primop-value-float-binary (float-binary-primop-add))
                        (list (fv 1/2) (fv 1/4)))
 (fv 3/4))

(acl2::assert-equal
 (eval-primop-fun-chain (primop-value-bool-binary (bool-binary-primop-and))
                        (list (bv t) (bv nil)))
 (bv nil))
