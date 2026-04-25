; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-derived-fixtypes")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-environments
  :parents (static-semantics)
  :short "Static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of
     the contextual information needed to
     enforce the static semantics of some AST.
     Our static environments correspond to the combination of
     the sort environment @($\\Theta$),
     the kind environment @($\\Delta$), and
     the type environment @($\\Gamma$)
     in [arxiv], [thesis], and [esop].")
   (xdoc::p
    "This is currently not used in the type checker.
     It is intended for use in the upcoming declarative typing rules.
     We may also use it in the type checker."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senv
  :short "Fixtype of static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of:")
   (xdoc::ul
    (xdoc::li
     "The set of index variables in scope.
      This corresponds to @($\\Theta$),
      but since our index variables include their own sort,
      a set suffices, as opposed to a map from variables to sorts.")
    (xdoc::li
     "A map from the type variables in scope to their kinds.
      This corresponds to @($\\Delta$).")
    (xdoc::li
     "A map from the term variables in scope to their types.
      This corresponds to @($\\Gamma$).")))
  ((index-vars index-param-set)
   (type-vars string-kind-map)
   (term-vars string-type-map))
  :pred senvp)
