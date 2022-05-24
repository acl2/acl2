; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "keywords")
(include-book "character-sets")
(include-book "bytes")
(include-book "abstract-syntax")
(include-book "abstract-syntax-operations")
(include-book "types")
(include-book "portable-ascii-identifiers")
(include-book "errors")
(include-book "integer-formats")
(include-book "integer-ranges")
(include-book "tag-environments")
(include-book "static-semantics")
(include-book "values")
(include-book "pointer-operations")
(include-book "array-operations")
(include-book "structure-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ language
  :parents (c)
  :short "A formal model of (some aspects of) the C language."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress."))
  :order-subtopics t)
