; A general-purpose Axe Rewriter
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

;; See tests in rewriter-basic-tests.lisp

(include-book "make-rewriter-simple")
(include-book "evaluator-basic")
(include-book "axe-syntaxp-evaluator-basic")
(include-book "axe-bind-free-evaluator-basic")

;; Create a "basic" rewriter.  Here, "basic" refers to the set of functions to
;; evaluate and to the sets of axe-syntaxp and axe-bind-free functions that the
;; rewriter "knows" about.  To understand what gets generated, see
;; make-rewriter-simple-fn.  The main interface functions are
;; simplify-term-basic, simp-term-basic, and simp-terms-basic.
(make-rewriter-simple basic
                      axe-evaluator-basic
                      basic
                      basic)
