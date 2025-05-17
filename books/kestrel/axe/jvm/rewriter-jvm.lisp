; An Axe Rewriter that knows about the JVM
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

;; This book creates a rewriter for use in JVM lifting / symbolic execution.

(include-book "../make-rewriter-simple")
(include-book "evaluator-jvm") ;jvm-specific
(include-book "axe-syntaxp-evaluator-jvm") ;jvm-specific
(include-book "axe-bind-free-evaluator-jvm") ;jvm-specific

(make-rewriter-simple jvm
                      axe-evaluator-jvm
                      jvm
                      jvm
                      :smt nil ; do not use SMT (todo: consider using it, but make a variant without it)
                      )
