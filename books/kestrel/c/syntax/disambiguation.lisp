; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "unambiguity")
(include-book "disambiguator")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ disambiguation
  :parents (syntax-for-tools)
  :short "Disambiguation for our C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our ASTs include ambiguous constructs,
     i.e. constructs that capture syntactically ambiguous constructs.
     See the documentation of the "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " for details.")
   (xdoc::p
    "We provide predicates on the ASTs that characterize
     the absence of ambiguities.")
   (xdoc::p
    "We provide a disambiguator that transforms ASTs
     by resolving the ambiguous constructs in favor of unambiguous ones.
     We prove that the output of the disambiguator, if successful,
     satisfies the unambiguity predicates."))
  :order-subtopics (unambiguity
                    disambiguator))
