; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "bound-variable-operations")
(include-book "free-variable-operations")
(include-book "all-variable-operations")
(include-book "fresh-variable-operations")
(include-book "variable-renaming-operations")
(include-book "variable-renaming-alpha-operations")
(include-book "variable-substitution-operations")
(include-book "variable-substitution-alpha-operations")
(include-book "free-variables-under-desugaring")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-variable-operations
  :parents (abstract-syntax)
  :short "Operations on ASTs related to variables."
  :order-subtopics (bound-variable-operations
                    free-variable-operations
                    all-variable-operations
                    fresh-variable-operations
                    variable-renaming-operations
                    variable-renaming-alpha-operations
                    variable-substitution-operations
                    variable-substitution-alpha-operations
                    free-variables-under-desugaring))
