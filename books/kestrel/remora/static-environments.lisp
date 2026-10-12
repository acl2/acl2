; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-static-environments")
(include-book "type-static-environments")
(include-book "expression-static-environments")

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
     It is the static counterpart of a "
    (xdoc::seetopic "dynamic-semantics" "dynamic environment")
    ".")
   (xdoc::p
    "There are three kinds of static environments:
     for ispace variables, type variables, and expression variables.
     They correspond to, respectively,
     the sort environment @($\\Theta$),
     the kind environment @($\\Delta$), and
     the type environment @($\\Gamma$)
     in [thesis] [arxiv] [esop].
     The nomenclature in [thesis] [arxiv] [esop]
     refers to what is assigned to the variables:
     sorts to ispace variables,
     kinds to type variables,
     and types to expression variables.
     In our formalization,
     we use a nomenclature that refers to the variables instead:
     an ispace environment contains information about ispace variables;
     a type environment contains information about type variables; and
     an expression environment contains information about expression variables.
     There are two reasons for this terminological difference:")
   (xdoc::ul
    (xdoc::li
     "Our static environments do not quite assign
      sorts to ispace variables and kinds to type variables:
      sorts and kinds are part of our ASTs for ispace and type variables,
      and instead our static environments may assign
      ispaces and types to ispace and type variables,
      to capture definitions from @('let') bindings
      (see the details in the fixtype definitions for environments).")
    (xdoc::li
     "We want a clear correspondence between static and dynamic environments,
      but the latter assign
      ispace values to ispace variables,
      type values to type variables, and
      expression values to expression variables.
      None of these involve the assignment of sorts, kinds, or types."))
   (xdoc::p
    "The only terminological overlap and possible confusion
     between our formalization and [thesis] [arxiv] [esop]
     is then `type environments',
     which assign information to type variables in our formalization,
     while they assign types to (expression) variables
     in [thesis] [arxiv] [esop].
     This is not ideal, but we see no way around it,
     given the motivations above for our nomenclature.
     As a weak form of disambiguation,
     we can say that ours are actually
     `type static environments' and `type dynamic environments',
     while the ones in [thesis] [arxiv] [esop]
     are just `type environments' without qualification.
     However, when clear from context,
     we may just say `type environment'
     to mean either `type static environment' or `type dynamic environment',
     and we use the same abbreviations for
     ispace environments and expression environments as well.")
   (xdoc::p
    "In Remora, variables are in five separate name spaces:
     one for dimension variables,
     one for shape variables,
     one for atom types,
     one for array types,
     and one for expression variables.
     E.g. @('$x'), @('@x'), @('&x'), @('*x'), and @('x')
     are all distinct variables, despite the common @('x') part;
     indeed, they are distinguished by the prefixes.
     The variables in static environments are similarly separated."))
  :order-subtopics (ispace-static-environments
                    type-static-environments
                    expression-static-environments))
