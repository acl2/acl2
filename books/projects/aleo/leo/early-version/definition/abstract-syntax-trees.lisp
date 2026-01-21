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

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc abstract-syntax-trees
  :parents (abstract-syntax)
  :short "Abstract syntax trees (ASTs)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The values of the fixtype @(tsee file)
     and of its (recursively) constituent fixtypes,
     which define the abstract syntax of Leo
     are tree-like structures.")
   (xdoc::p
    "These are the Leo ASTs.
     These are abstractions of the Leo "
    (xdoc::seetopic "concrete-syntax-trees" "CSTs")
    ", according to the "
    (xdoc::seetopic "syntax-abstraction" "syntax abstraction mapping")
    ".")))
