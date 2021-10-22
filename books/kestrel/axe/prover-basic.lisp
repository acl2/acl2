; A general-purpose Axe Prover
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in prover-basic-tests.lisp

(include-book "make-prover-simple")
(include-book "evaluator-basic")
(include-book "axe-syntaxp-evaluator-basic")
(include-book "axe-bind-free-evaluator-basic")

;; Create a "basic" prover.  Here, "basic" refers to the functions the prover
;; knows how to evaluate (including axe-syntaxp and axe-bind-free functions).
(make-prover-simple basic
                    basic
                    basic
                    basic)
