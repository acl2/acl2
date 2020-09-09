; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "defunvar")
(include-book "defsoft")
(include-book "defun2")
(include-book "defund2")
(include-book "define2")
(include-book "defchoose2")
(include-book "defun-sk2")
(include-book "defund-sk2")
(include-book "define-sk2")
(include-book "defun-inst")
(include-book "defthm-inst")
(include-book "defequal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft-implementation
  :parents (soft)
  :short "Implementation of SOFT."
  :order-subtopics t)
