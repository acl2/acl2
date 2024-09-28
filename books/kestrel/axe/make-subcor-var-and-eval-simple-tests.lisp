; A test of make-subcor-var-and-eval-simple
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-subcor-var-and-eval-simple")
(include-book "evaluator-basic")

(make-subcor-var-and-eval-simple basic axe-evaluator-basic)
