; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "defaults-table")
(include-book "defun-variant")
(include-book "function-renamingp")
(include-book "input-processing")
(include-book "input-processing-soft")
(include-book "pattern-matching")
(include-book "pattern-matching-ext")
(include-book "print-specifiers")
(include-book "transformation-table")
(include-book "untranslate-specifiers")
(include-book "xdoc-constructors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc utilities
  :parents (apt)
  :short "Utilities shared by the implementations of the APT tools.")
