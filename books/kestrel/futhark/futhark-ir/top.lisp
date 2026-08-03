; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "parsing-and-printing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ futhark-ir
  :parents (futhark)
  :short "An ACL2 front end for the Futhark IR text emitted by Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library formalizes the concrete and abstract syntax needed to
     parse the Futhark SOACS IR text that the current Remora compiler emits
     in @('.fut_soacs') files.")
   (xdoc::p
    "The full ordinary Futhark language is specified by the official "
    (xdoc::ahref
     "https://futhark.readthedocs.io/en/stable/language-reference.html"
     "Futhark language reference")
    ".  The Remora compiler currently prints textual IR via the Futhark
     Haskell library, so this front end intentionally starts with that
     Remora-facing subset.")
   (xdoc::p
    "For background on the Futhark compiler's Haskell IR datatypes, see the
     Hackage documentation for "
    (xdoc::ahref
     "https://hackage-content.haskell.org/package/futhark-0.25.34/docs/Futhark-IR-Syntax.html"
     "Futhark.IR.Syntax")
    ".  This is a convenient released-version reference; Remora's Nix flake
     may pin a different Futhark Git revision, so this ACL2 front end follows
     the textual IR emitted by Remora."))
  :order-subtopics (concrete-syntax
                    abstract-syntax
                    parsing-and-printing))
