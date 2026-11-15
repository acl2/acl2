; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "normalization-test")
(include-book "../data/v18.0.0/normalization-test")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run all of the normalization conformance test of Unicode 18.0.0
; (NormalizationTest.txt), as described in the book normalization-test.
; If an assertion fails, evaluate its call
; to see the lines or the code points that fail.

; Requirement 1: no line fails.

(assert-event
 (equal (normalization-test-failures *normalization-test-v18.0.0*
                                     (version-v18.0.0))
        nil))

; Requirement 2: no code point that Part 1 does not list fails.

(assert-event
 (equal (normalization-test-unlisted-failures *normalization-test-v18.0.0*
                                              (version-v18.0.0))
        nil))

; The number of lines, so that an empty test does not pass unnoticed.

(assert-event
 (< 19000 (normalization-test-line-count *normalization-test-v18.0.0*)))
