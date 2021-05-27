; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defunit

  :parents (fty-extensions fty)

  :short (xdoc::topstring
          "Generate a singleton " (xdoc::seetopic "fty::fty" "fixtype") ".")

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Some languages have a unit type,
      which consists of a single value.
      This is useful, for example,
      when some code returns nothing
      (besides presumably having some side effects),
      or as a component of larger types
      (e.g. a disjoint union of a detailed error value for failure
      and of the unit type for success without further information).")

    (xdoc::p
     "This macro introduces a fixtype consisting of a single keyword value.
      Given that ACL2 is an untyped language,
      the ability to customize the exact value of a unit type
      provides more flexibility, e.g. to create "
     (xdoc::seetopic "defflatsum" "flat sums")
     " involving unit types,
      which requires such unit types to be disjoint from
      the other summand types, which are unknown a priori."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defunit type"
     "         :value ...    ; no default"
     "         :pred ...     ; default type-p"
     "         :fix ...      ; default type-fix"
     "         :equiv ...    ; default type-equiv"
     "         :parents ...  ; no default"
     "         :short ...    ; no default"
     "         :long ...     ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('type')"
     (xdoc::p
      "The name of the new fixtype."))

    (xdoc::desc
     "@(':value') &mdash; no default"
     (xdoc::p
      "A keyword to be used as the (only) value of the new fixtype.")
     (xdoc::p
      "This must be provided, there is no default."))

    (xdoc::desc
     (list
      "@(':parents') &mdash; default @('type') followed by @('-p')"
      "@(':short') &mdash; default @('type') followed by @('-fix')"
      "@(':long') &mdash; default @('type') followed by @('-equiv')")
     (xdoc::p
      "The name of the recognizer, fixer, and equivalence
       for the new fixtype."))

    (xdoc::desc
     (list
      "@(':parents') &mdash; no default"
      "@(':short') &mdash; no default"
      "@(':long') &mdash; no default")
     (xdoc::p
      "The parents, short string, and long string
       for the XDOC topic generated for the new fixtype.")
     (xdoc::p
      "If any of these is not supplied, it is omitted from the XDOC topic;
       there are no defaults.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "The following are generated, inclusive of XDOC documentation:")

    (xdoc::ul

     (xdoc::li
      "The recognizer, the fixer, the equivalence, and the fixtype."))

    (xdoc::p
     "See the implementation, which uses a readable backquote notation,
      for details."))))
