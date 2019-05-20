; Representation of Natural Numbers as Digits in Base 2^N for Specific Ns
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pow2-1")
(include-book "pow2-2")
(include-book "pow2-3")
(include-book "pow2-4")
(include-book "pow2-8")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The files included by this file use DEFTHM-DAB-RETURN-TYPES
; to generate return type theorems for
; the conversions from natural numbers to digits in base 2^N
; for several common values of N.
; If theorems for a certain value of N
; are needed but are not among the ones already defined here,
; new files can be easily added for such theorems,
; and included in this file so they will all appear in the manual.
