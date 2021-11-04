; Top file for clause-processors library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; utilities:
(include-book "clause-to-clause-list")

(include-book "do-nothing")
(include-book "do-nothing-to-literals")
(include-book "subst-flag")
(include-book "handle-constant-literals")
(include-book "flatten-literals")
(include-book "simple-subsumption")
(include-book "push-unary-functions")
(include-book "simplify-after-using-conjunction")
(include-book "simplify-assumptions")
