; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "variables-in-computation-states")
(include-book "proof-generation")
(include-book "proof-generation-theorems")
(include-book "add-section-attr-doc")
(include-book "add-section-attr")
(include-book "constant-propagation")
(include-book "copy-fn")
(include-book "rename")
(include-book "simpadd0")
(include-book "simpadd0-doc")
(include-book "specialize")
(include-book "specialize-doc")
(include-book "split-fn")
(include-book "split-fn-doc")
(include-book "split-fn-when")
(include-book "split-fn-when-doc")
(include-book "split-all-gso")
(include-book "split-all-gso-doc")
(include-book "split-gso")
(include-book "split-gso-doc")
(include-book "utilities/top")
(include-book "wrap-fn")
(include-book "wrap-fn-doc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transformation-tools
  :parents (c::c)
  :short "C2C: transformation tools for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide tools to transform C code (C-to-C transformations)
     according to various purposes and criteria.
     The transformations are invoked as event macros,
     which generally have the form")
   (xdoc::codeblock
    "(<xform> :const-old ..."
    "         :const-new ..."
    "         ...)")
   (xdoc::p
    "where @('<xform>') is the name of the transformation,
     @(':const-old') specifies (the name of a constant containing)
     the ``old'' code to apply the transformation to,
     @('const-new') specifies (the name of a constant in which to put)
     the ``new'' code resulting from the transformation,
     and the remaining @('...') indicate additional keyword inputs
     that certain transformations may accept.
     See the user documentation of individual transformations for details.")
   (xdoc::p
    "Typically, the C code to be transformed is ingested
     via the @(tsee c$::input-files) event macro,
     which produces a named constant suitable for
     the @(':const-old') input of transformations.
     Then the user invokes one or more transformations,
     and eventually the final C code is written out
     via the @(tsee c$::output-files) event macro,
     which takes the named constant specified in
     the @(':const-new') input of the last invoked transformation.")
   (xdoc::p
    "The transformations operate on the abstract syntax
     defined in @(see c$::syntax-for-tools),
     specifically on code ensembles.
     The transformations are implemented as
     collections of ACL2 functions that operate on the ASTs,
     following their recursive structure.")
   (xdoc::p
    "For a growing subset of transformations and C constructs,
     we also generate correctness theorems.
     The theorems are specific to the code being transformed,
     according to a verifying compiler approach.")
   (xdoc::p
    "The theorems are generated in a bottom-up fashion,
     until constructs are encountered
     for which proof generation is not supported,
     at which point proof generation stops
     with just the theorems generated so far.
     In some cases, proof generation can proceed
     all the way up to function definitions,
     which currently provide the top-level theorems.")
   (xdoc::p
    "The generated theorems have names obtained by
     combining the aforementioned @('const-new') input
     with an increasing numeric index,
     which is threaded through the transformation functions.
     The generated theorem events are accumulated into a list
     that is threaded through the transformation functions;
     the list is accumulated in reverse order,
     so that each new generated event is @(tsee cons)ed,
     but the list is reversed to the right order
     in the top-level generated event that is submitted to ACL2.")
   (xdoc::p
    "A growing amount of functionality is factored into
     general utilities usable in different transformations.
     In particular, @(see proof-generation) includes utilities
     to generate theorems for various classes of constructs,
     and @(see input-processing) includes utilities
     to process inputs of transformations.")))
