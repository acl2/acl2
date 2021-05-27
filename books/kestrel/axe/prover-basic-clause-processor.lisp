; A clause processor that uses prover-basic
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in prover-basic-tests.lisp

(include-book "prover-basic")
(include-book "make-clause-processor-simple")

;; Make a clause-processor that uses the basic prover:
(make-clause-processor-simple basic)
