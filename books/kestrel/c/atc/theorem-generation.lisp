; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "generation-contexts")
(include-book "types-to-recognizers")

(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/untranslate-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-theorem-generation
  :parents (atc-event-and-code-generation)
  :short "Facilities for generating theorems in ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for the new approach to proof generation
     in which we generate modular, compositional theorems.
     Since these theorems have a fairly regular structure,
     and are generated in many parts of the code
     with only some slight variations (e.g. the hints),
     it makes sense to factor their commonalities, which we do here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-correct-thm ((fn symbolp)
                                       (fn-guard symbolp)
                                       (context atc-contextp)
                                       (expr exprp)
                                       (type typep)
                                       (term pseudo-termp)
                                       (compst-var symbolp)
                                       (hints true-listp)
                                       (thm-index posp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate a correctness theorem for a pure expression execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @('fn') that the expression is part of is passed as input.")
   (xdoc::p
    "As theorem name, we just combine
     @('fn') with @('correct') and with the theorem index.
     The name just needs to be unique locally to the call to ATC,
     so we expect that generally no @('$') signs will need to be added
     by @(tsee fresh-logical-name-with-$s-suffix).")
   (xdoc::p
    "The theorem says that
     @(tsee exec-expr-pure) called on the quoted expression
     is the same as the term;
     it also says that the term has the expression's type.
     The term is untranslated, to make it more readable,
     in particular to eliminate quotes before numbers.
     Term, expression, and type are passed as inputs.
     The theorem is contextualized,
     and further conditioned by the satisfaction of the guard of @('fn')."))
  (b* ((wrld (w state))
       (name (pack fn '-correct- thm-index))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (type-pred (type-to-recognizer type wrld))
       (uterm (untranslate$ term nil state))
       (formula `(and (equal (exec-expr-pure ',expr ,compst-var)
                             ,uterm)
                      (,type-pred ,uterm)))
       (formula (atc-contextualize formula context nil))
       (formula `(implies (and (compustatep ,compst-var)
                               (,fn-guard ,@(formals+ fn wrld)))
                          ,formula))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv event name (1+ thm-index) names-to-avoid)))
