; A custom axe-syntaxp-evaluator for R1CS proofs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../axe-syntax-functions-boolean")
(include-book "../axe-syntax-functions-bv")
(include-book "../make-axe-syntaxp-evaluator")
(include-book "axe-syntax-functions-r1cs")

(make-axe-syntaxp-evaluator 'r1cs '(;; These are the additional functions needed for R1CS proofs:
                                    var-less-than-unquoted-keyp
                                    var-not-less-than-unquoted-keyp
                                    ;; same stuff as in the "basic" version:
                                    heavier-dag-term
                                    ;; bv-term-syntaxp
                                    is-a-myif
                                    syntactic-booleanp
                                    syntactic-call-of
                                    ;; syntactic-constantp
                                    syntactic-variablep
                                    is-the-variablep
                                    should-reverse-equality
                                    ;term-should-be-converted-to-bvp ; needed?
                                    bv-array-write-nest-ending-inp-axe
                                    bvcat-nest-with-low-zerosp-axe
                                    bv-array-write-nest-with-val-at-indexp-axe
                                    term-should-be-trimmed-axe-plus-one
                                    term-should-be-trimmed-axe
                                    should-commute-axe-argsp
                                    should-commute-axe-args-increasingp))
