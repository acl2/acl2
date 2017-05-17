; SOFT (Second-Order Functions and Theorems) -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file tests SOFT (Second-Order Functions and Theorems),
; a tool to mimic second-order functions and theorems
; in the first-order logic of ACL2.
; More tests should be added to this file.

; SOFT is documented in documentation.lisp.
; Examples of use of SOFT are in
; workshop-paper-examples.lisp and workshop-talk-examples.lisp.
; Other tests are in tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; GitHub Issue #690 (https://github.com/acl2/acl2/issues/690):

(defunvar ?p (*) => *)

(defun-sk2 exists[?p] (?p) ()
  (exists x (?p x)))

(verify-guards exists[?p])

(defun-inst exists[symbolp]
  (exists[?p] (?p . symbolp)))
