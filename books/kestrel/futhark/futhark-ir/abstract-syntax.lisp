; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "abstract-syntax-trees")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (futhark-ir)
  :short "Abstract syntax for the supported Futhark IR subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax is the FTY representation produced by
     @(see syntax-abstraction) after parsing Remora-emitted textual Futhark
     SOACS IR.  It is intentionally narrower than the full ordinary Futhark
     source language and also narrower than the compiler's full internal IR
     datatype hierarchy.")
   (xdoc::p
    "The ASTs keep the information needed by the current front end:
     optional @('name_source') text, declarations, entry attributes, typed
     parameters and patterns, expressions, statements, bodies, and simple
     Futhark IR types.")
   (xdoc::p
    "Names, literal text, and decoded string-literal contents are represented
     as ACL2 strings.  As in Remora, non-ASCII source text is stored in these
     strings as UTF-8 bytes."))
  :order-subtopics (abstract-syntax-trees))
