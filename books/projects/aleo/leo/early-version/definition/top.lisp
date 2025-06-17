; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "static-semantics")
(include-book "dynamic-semantics")
(include-book "compilation")
(include-book "compile-file")
(include-book "format-strings")
(include-book "flattening")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ definition
  :parents (early-version)
  :short "An ACL2 formalization of the Leo language."
  :long
  (xdoc::topstring
   (xdoc::p
    "This formalization defines, with mathematical precision,
     the syntax and semantics of Leo.
     This formalization covers Leo code,
     which is the primary artifact of the language,
     and also related artifacts such as Leo input files,
     which are considered a part of the language at large
     in this formalization.")
   (xdoc::p
    "This ACL2 formalization of Leo is work in progress."))
  :order-subtopics (concrete-syntax
                    abstract-syntax
                    static-semantics
                    dynamic-semantics
                    compilation
                    format-strings
                    flattening))
