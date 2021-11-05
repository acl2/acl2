; An Axe Prover for R1CS reasoning
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/make-prover-simple" :dir :system)
(include-book "axe-evaluator-r1cs")
(include-book "axe-syntaxp-evaluator-r1cs")
;; At least for now, the basic version of this is fine:
(include-book "kestrel/axe/axe-bind-free-evaluator-basic" :dir :system)

(make-prover-simple r1cs
                    r1cs
                    r1cs
                    basic)
