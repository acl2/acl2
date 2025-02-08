; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "constant-propagation")
(include-book "copy-fn")
(include-book "deftrans")
(include-book "rename")
(include-book "simpadd0")
(include-book "specialize")
(include-book "split-fn-proofs")
(include-book "splitgso")
(include-book "utilities/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transformation-tools
  :parents (c::c)
  :short "Transformation tools for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide tools to transform C code into (different) C code.
     The transformations may have different purposes.")
   (xdoc::p
    "These transformation tools operate on the abstract syntax
     defined in @(see c$::syntax-for-tools).")))
