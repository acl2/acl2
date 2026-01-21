; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "abstract-syntax-induction-schemas")
(include-book "static-semantics")
(include-book "dynamic-semantics")
(include-book "static-soundness")
(include-book "errors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ language
  :parents (yul)
  :short "A formalization of the Yul language in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "This formalization covers a generic form of Yul
     that supports the types of the EVM dialect.
     The formalization consists of
     a concrete syntax,
     an abstract syntax,
     a static semantics, and
     a dynamic semantics.
     We plan to make this formalization more generic,
     and in particular to also support types in other Yul dialects."))
  :order-subtopics (concrete-syntax
                    abstract-syntax
                    static-semantics
                    dynamic-semantics
                    static-soundness
                    errors))
