; LIft-iso Transformation -- Documentation
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license.  See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file documents lift-iso, a transformation to lift an isomorphism
; to a predicate that is true of some structure where one or more components is subject
; to the original isomorphism

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc lift-iso
  :parents (apt)
  :short "Lift an isomorphism to an isomorphism on a structure containing the original isoporphism predicate."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-section-intro

      (xdoc::p
        "@('lift-iso') takes a predicate and one or more isomorphisms where the domain predicates
         of the isomorphisms are referenced by the predicate, and lifts them to create an isomorphism
         from the predicate to a newly created predicate. It is useful for cases where the predicate
         specifies a structure that includes components for which isomorphisms exist. It is also
         useful for extending an isomorphism to a subdomain. Examples are in lift-iso-tests.lisp.
         @('lift-iso') is used by propagate-iso to lift isomorphisms, and it is more general
         as it also lifts theorems and functions involving the lifted isomorphism and new predicate.")

      (xdoc::evmac-section-form
        (xdoc::codeblock
          " (lift-iso pred isomorphism-name-or-names"
          "                fn-iso-specs"
          "                &key"
          "                :iso-name          ; Name of new isomorphism"
          "                :iso-pred-name     ; Name of new predicate"
          "                )"))

      (xdoc::desc
        "@('isomorphism-name-or-names')"
        (xdoc::p
          "A single name or a list of names of isomorphisms defined using @(tsee defiso)."))

      (xdoc::desc
        "@('iso-name')"
        (xdoc::p
          "The name to be used for the generated isomorphism. If not provided, @('lift-iso') generates
           a name from the provided predicate and the isomorphism names."))

      (xdoc::desc
        "@('iso-pred-name')"
        (xdoc::p
          "The name to be used for the generated predicate. If not providd,e @('lift-iso') generates
           a name from the provided predicate and the isomorphism names."))

      )))
