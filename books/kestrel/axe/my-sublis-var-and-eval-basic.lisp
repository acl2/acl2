; A variant of my-sublis-var-and-eval that uses the basic evaluator.
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

;; This utility applies a subsitution (mapping vars to dargs) to a term, such
;; as the RHS of a rewrite rule.  As it goes, it evaluates ground calls of
;; known functions.

;; Similar to instantiate-hyp-basic.

(include-book "evaluator-basic")
(include-book "make-substitution-code-simple")
(local (include-book "replace-var-rules"))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

;; Make a version of my-sublis-var-and-eval, etc that use the basic evaluator:
(make-substitution-code-simple basic axe-evaluator-basic)
