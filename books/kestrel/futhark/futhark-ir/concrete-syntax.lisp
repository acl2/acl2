; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "grammar")
(include-book "concrete-syntax-trees")
(include-book "lexical-syntax")
(include-book "identifier-syntax")
(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (futhark-ir parsing-and-printing)
  :short "Concrete syntax of the Remora-emitted Futhark subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concrete syntax defines which Unicode code-point sequences form
     supported textual Futhark IR programs, and how those sequences are
     organized into declarations, bodies, expressions, types, names, and
     literals.")
   (xdoc::p
    "This is not the ordinary Futhark source language.  It is the textual
     SOACS IR subset emitted by the current Remora-to-Futhark path.  The
     concrete syntax is formalized by @(see ir-grammar), with an
     executable parser in @(see parser).")
   (xdoc::p
    "The core parser operates on lists of natural numbers that represent
     Unicode code points.  Decoding UTF-8 bytes from ACL2 strings is handled
     by @(see parser-interface), outside the core grammar parser.")
   (xdoc::p
    "A few constraints are enforced outside pure ABNF.  For example,
     keywords require a word boundary, words are later distinguished as names
     or literals, and names reject reserved words.  The token-level
     predicates are split between @(see lexical-syntax) and
     @(see identifier-syntax), and abstraction-time checks are in
     @(see syntax-abstraction)."))
  :order-subtopics (ir-grammar
                    concrete-syntax-trees
                    lexical-syntax
                    identifier-syntax
                    parser))
