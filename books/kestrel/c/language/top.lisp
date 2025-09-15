; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "implementation-environments/top")
(include-book "grammar")
(include-book "keywords")
(include-book "character-sets")
(include-book "abstract-syntax")
(include-book "abstract-syntax-operations")
(include-book "errors")
(include-book "types")
(include-book "portable-ascii-identifiers")
(include-book "integer-formats")
(include-book "integer-ranges")
(include-book "tag-environments")
(include-book "static-semantics")
(include-book "values")
(include-book "integer-operations")
(include-book "arithmetic-operations")
(include-book "pointer-operations")
(include-book "array-operations")
(include-book "structure-operations")
(include-book "operations")
(include-book "computation-states")
(include-book "dynamic-semantics")
(include-book "execution-without-function-calls")
(include-book "variable-preservation-in-execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ language
  :parents (c)
  :short "A formal model of (a subset of) the C language."
  :order-subtopics t)
