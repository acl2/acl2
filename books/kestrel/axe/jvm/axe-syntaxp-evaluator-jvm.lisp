; An axe-syntaxp-evaluator that knows about the JVM model
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

(include-book "../make-axe-syntaxp-evaluator")
(include-book "../axe-syntax-functions-boolean")
(include-book "../axe-syntax-functions-bv")
(include-book "axe-syntax-functions-jvm") ; for no-state-to-step-p and perhaps others
(include-book "axe-syntax-functions-jvm2") ; for no-state-to-step-for-loop-lifter-p and perhaps others

(make-axe-syntaxp-evaluator 'jvm '(heavier-dag-term
                                   ;; bv-term-syntaxp
                                   is-a-myif
                                   syntactic-booleanp
                                   syntactic-call-of
                                   ;; syntactic-constantp
                                   should-reverse-equality
                                   bv-array-write-nest-ending-inp-axe
                                   bvcat-nest-with-low-zerosp-axe
                                   term-should-be-converted-to-bvp
                                   no-state-to-step-p ;jvm-specific
                                   bv-array-write-nest-with-val-at-indexp-axe
                                   term-should-be-trimmed-axe-plus-one
                                   term-should-be-trimmed-axe
                                   should-commute-axe-argsp
                                   should-commute-axe-args-increasingp
                                   no-state-to-step-for-loop-lifter-p ;jvm-specific
                                   ))
