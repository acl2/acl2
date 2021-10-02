; APT (Automated Program Transformations) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "becomes-theorem-names")
(include-book "defaults-table")
(include-book "deftransformation")
(include-book "defun-variant")
(include-book "def-equality-transformation")
(include-book "drop-corresponding-items")
(include-book "extract-non-local-events")
(include-book "fixup-ignores")
(include-book "function-renamingp")
(include-book "generate-print-events")
(include-book "hints-specifiers")
(include-book "input-processing")
(include-book "input-processing-soft")
(include-book "make-becomes-theorem")
(include-book "maybe-verify-guards2")
(include-book "option-parsing")
(include-book "pattern-matching")
(include-book "pattern-matching-ext")
(include-book "process-keyword-args")
(include-book "print-specifiers")
(include-book "remove-event-types")
(include-book "set-stobjs-in-declares-to-match")
(include-book "transformation-prologue")
(include-book "transformation-table")
(include-book "untranslate-specifiers")
(include-book "verify-guards-for-defun")
(include-book "xdoc-constructors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc utilities
  :parents (apt)
  :short "Utilities shared by the implementations of the APT tools.")
