; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "codepoint-utilities")
(include-book "futhark-ir/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ futhark
  :parents (acl2::projects acl2::kestrel-books)
  :short "ACL2 libraries for Futhark syntax and related intermediate forms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The current library contains @(see futhark-ir), an ACL2 specification
     of the textual Futhark SOACS IR subset emitted by the Remora compiler.
     SOACS stands for <i>Second Order Array Combinators</i>.")
   (xdoc::p
    "The ordinary Futhark source language is specified by the official "
    (xdoc::ahref
     "https://futhark.readthedocs.io/en/stable/language-reference.html"
     "Futhark language reference")
    ".  A future source-language front end can live alongside
     @(see futhark-ir) under this umbrella."))
  :order-subtopics (codepoint-utilities
                    futhark-ir))
