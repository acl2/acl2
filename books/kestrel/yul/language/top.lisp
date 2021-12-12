; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "concrete-syntax")
(include-book "abstract-syntax")
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
    "This formalization covers a generic for of Yul
     that supports the types of the EVM dialect.
     The formalization consists of
     a concrete syntax,
     an abstract syntax,
     a static semantics, and
     a dynamic semantics.
     We plan to make this formalization more generic,
     and in particular to also support types in othe Yul dialects."))
  :order-subtopics t)
