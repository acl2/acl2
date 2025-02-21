; An axe-syntaxp evaluator for x86 lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: package

(include-book "../axe-syntax-functions-boolean")
(include-book "../axe-syntax-functions-bv")
(include-book "../make-axe-syntaxp-evaluator")
(include-book "axe-syntax-functions-x86")

;; todo: what order should these be in?
(make-axe-syntaxp-evaluator 'x86 '(lighter-dargp
                                   ;; bv-term-syntaxp
                                   is-a-myif
                                   syntactic-booleanp
                                   syntactic-call-of
                                   ;; syntactic-constantp
                                   ;; syntactic-variablep ; maybe add this
                                   ;; is-the-variablep ; maybe add this
                                   should-reverse-equality
                                   term-should-be-converted-to-bvp
                                   bv-array-write-nest-ending-inp-axe
                                   bvcat-nest-with-low-zerosp-axe
                                   bv-array-write-nest-with-val-at-indexp-axe
                                   term-should-be-trimmed-axe-plus-one
                                   term-should-be-trimmed-axe
                                   should-commute-axe-argsp
                                   should-commute-axe-args-increasingp
                                   x::write-with-addr-and-size-presentp-axe
                                   x::write-nest-with-inner-set-flagp-axe
                                   dargs-equalp
                                   x::addresses-out-of-orderp))
