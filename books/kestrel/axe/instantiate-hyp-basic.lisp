; A variant of instantiate-hyp that uses the basic evaluator.
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

;; Similar to my-sublis-var-and-eval-basic, but this one also returns a free-vars flag.

;; This version uses the basic evaluator.

(include-book "evaluator-basic")
(include-book "make-instantiation-code-simple")

;; Make a version of instantiate-hyp, etc that use the basic evaluator:
(make-instantiation-code-simple basic axe-evaluator-basic)
