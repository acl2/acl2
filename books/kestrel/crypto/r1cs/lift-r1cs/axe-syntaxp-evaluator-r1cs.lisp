; A basic axe-syntaxp-evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/axe-syntax-functions-bv" :dir :system)
(include-book "kestrel/axe/make-axe-syntaxp-evaluator" :dir :system)
(include-book "../proof-support") ;todo: reduce

(make-axe-syntaxp-evaluator 'r1cs '(var-less-than-unquoted-keyp
                                    var-not-less-than-unquoted-keyp
                                    ;; same stuff as in the "basic" version:
                                    not-quotep ;drop?
                                    heavier-dag-term
                                    bv-term-syntaxp
                                    not-bv-term-syntaxp
                                    is-a-myif
                                    not-is-a-myif ;drop?
                                    known-booleanp
                                    syntactic-call-of
                                    syntactic-constantp
                                    should-reverse-equality
                                    bv-array-write-nest-ending-inp
                                    bvcat-nest-with-low-zeros
                                    bv-array-write-nest-with-val-at-index
                                    term-should-be-trimmed-axe-plus-one
                                    term-should-be-trimmed-axe
                                    should-commute-args-dag
                                    should-commute-args-increasing-dag))
