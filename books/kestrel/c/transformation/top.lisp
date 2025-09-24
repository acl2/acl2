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
(include-book "splitgso")
(include-book "splitgso-doc")
(include-book "utilities/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transformation-tools
  :parents (c::c)
  :short "Transformation tools for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide tools to transform C code into (different) C code,
     according to various purposes and criteria.
     The transformations are invoked as event macros,
     normally after using @(tsee c$::input-files) to ingest code,
     and normally using @(tsee c$::output-files) on the transformed code.")
   (xdoc::p
    "These transformation tools operate on the abstract syntax
     defined in @(see c$::syntax-for-tools).
     The transformations are implemented as
     collections of ACL2 functions that operate on the ASTs,
     following their recursive structure.
     For a growing subset of transformations and C constructs,
     we also generate correctness theorems.")))
