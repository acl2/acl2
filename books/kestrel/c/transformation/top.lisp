; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "proof-generation")
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
    "We provide tools to transform C code into (different) C code.
     The transformations may have different purposes.")
   (xdoc::p
    "These transformation tools operate on the abstract syntax
     defined in @(see c$::syntax-for-tools).")))
