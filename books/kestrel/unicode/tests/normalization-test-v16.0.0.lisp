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
(include-book "../data/v16.0.0/normalization-test")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run all of the normalization conformance test of Unicode 16.0.0
; (NormalizationTest.txt), as described in the book normalization-test.
; If this fails, evaluate the call of RUN-NORMALIZATION-TEST
; to see the lines and the code points that fail.

(assert-event (normalization-test-p *normalization-test-v16.0.0*))

(assert-event
 (equal (run-normalization-test *normalization-test-v16.0.0*
                                (version-v16.0.0))
        (list nil
              nil
              (normalization-test-count *normalization-test-v16.0.0*))))

(assert-event
 (< 19000 (normalization-test-count *normalization-test-v16.0.0*)))
