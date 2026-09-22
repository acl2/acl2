; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc def-guard-theorem-rewrite

  :parents (std/util guard-theorem)

  :short "Introduce rewrite rules from a function's guard theorem."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This event macro proves a disabled theorem consisting of
      the rewrite-rule implications extracted from
      the guard theorem of a guard-verified function."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(def-guard-theorem-rewrite name"
     "                           fn"
     "                           :simplify ... ; default :limited"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::p
     "The inputs are not evaluated.")

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name of the generated theorem."))

    (xdoc::desc
     "@('fn')"
     (xdoc::p
      "Name of an existing guard-verified function.")
     (xdoc::p
      "If it belongs to a mutually recursive clique,
       the guard theorem covers the entire clique,
       as for a @(':guard-theorem') @(see lemma-instance)."))

    (xdoc::desc
     "@(':simplify') &mdash; default @(':limited')"
     (xdoc::p
      "It must be @(':limited') or @('nil').
       It is passed both to @(tsee guard-theorem) and to the generated hint.
       @(':limited') performs ACL2's theory-independent guard simplification;
       @('nil') requests the unsimplified guard theorem.
       See @(see gthm).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('name')"

     (xdoc::p
      "Guard theorems are conjunctions and disjunctions,
       expressed through @(tsee if) as translated terms.
       This utility uses ACL2's clause conversion to obtain disjunctions.
       Each disjunction becomes an implication
       whose conclusion is its last literal
       and whose hypotheses negate the preceding literals.
       For example, @('(or (not hyp1) (not hyp2) concl)')
       becomes @('(implies (and hyp1 hyp2) concl)').")

     (xdoc::p
      "Each implication is checked using ACL2's rewrite-rule admissibility check.
       If its unaltered conclusion does not yield a valid rewrite rule,
       that implication is omitted.
       For example, a conclusion @('(equal x nil)') would rewrite a variable,
       so it is skipped.
       Conclusions could be ``repaired'' by adding @(tsee iff) wrappers,
       but this utility does not do that,
       partly so that the generated theorem can be proved efficiently
       via a @(':by') hint instead of a @(':use') hint;
       the latter can lead to many case splits,
       with fairly large guard theorems for fairly large functions.
       Because of this filtering of implications,
       the generated theorem may express only part of the original guard theorem.")

     (xdoc::p
      "The retained implications are conjoined in one @(tsee defthmd).
       ACL2 installs their rewrite rules under the supplied theorem name.
       They are disabled initially; use @('(enable name)') to enable them.
       If no implication is retained,
       the event is instead a @(tsee defthm) of @('t')
       with @(':rule-classes nil'),
       and installs no rules.")))))
