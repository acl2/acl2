; An Axe Rewriter that knows about the JVM
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

;; This book creates a rewriter for use in JVM lifting / symbolic execution.

(include-book "kestrel/axe/make-rewriter-simple" :dir :system)
(include-book "kestrel/axe/evaluator-basic" :dir :system) ;todo: consider an evaluator with some JVM functions built-in
(include-book "axe-syntaxp-evaluator-jvm") ;jvm-specific
(include-book "axe-bind-free-evaluator-jvm") ;jvm-specific

(make-rewriter-simple jvm
                      ;; we could use a different evaluator here that knows about JVM functions:
                      axe-evaluator-basic
                      jvm
                      jvm)
