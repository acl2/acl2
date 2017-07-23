; SOFT (Second-Order Functions and Theorems) -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More tests should be added to this file.

; GitHub Issue #690 (https://github.com/acl2/acl2/issues/690):

(defunvar ?p (*) => *)

(defun-sk2 exists[?p] (?p) ()
  (exists x (?p x)))

(verify-guards exists[?p])

(defun-inst exists[symbolp]
  (exists[?p] (?p . symbolp)))
