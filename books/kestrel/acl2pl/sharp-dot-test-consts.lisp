; ACL2 Programming Language Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Constants for testing #. (sharp-dot) reader syntax in reader-tests.lisp.
; These must be in a separate book because certify-book reads the entire
; book before evaluating its forms, so a defconst and a #. reference to it
; cannot be in the same book.
; https://acl2.org/doc/?topic=ACL2____SHARP-DOT-READER

(in-package "ACL2")

;; A simple constant (name will be upcased to *SHARP-DOT-TEST-CONST*)
(defconst *sharp-dot-test-const* 42)

;; A constant with a lowercase name (preserved by vertical-bar escaping)
(defconst |*lower-case-const*| 99)
