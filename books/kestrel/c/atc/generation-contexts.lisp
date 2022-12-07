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

(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-generation-contexts
  :parents (atc-event-and-code-generation)
  :short "Logical contexts in which ATC generates C expressions and statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "As ATC visits ACL2 terms that represent C expressions and statements,
     and generates from the terms the C expressions and statements,
     along with correctness theorems for them,
     there is a growing logical context consisting of
     conditional tests and of @(tsee let) and @(tsee mv-let) bindings.
     We call these tests and bindings `premises',
     which is not ideal terminology because
     it is essentially synonmous of `hypotheses',
     which in ACL2 refers specifically to terms (conditions) and not bindings.
     So we use `premises' because it is not used as much in ACL2;
     we may find a better term in the future.")
   (xdoc::p
    "We define data types for premises,
     and for contexts that consist of lists of premises.
     We carry and augment contexts as we visit terms;
     we use these contexts in generated theorems."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum atc-premise
  :short "Fixtype of premises."
  :long
  (xdoc::topstring
   (xdoc::p
    "We include bindings of the computation state.
     Each such binding consists of
     a variable for the computation state
     (contained in @('compst-var') in the code generation code),
     and a term that must represent a computation state.
     The meaning is that the variable is bound to the term.")
   (xdoc::p
    "We also include terms that are tests of @(tsee if)s.")
   (xdoc::p
    "We may add more kinds later."))
  (:compustate ((var symbolp)
                (term any)))
  (:test ((get pseudo-term)))
  (:other ())
  :pred atc-premisep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atc-context
  :short "Fixtype of contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "A context is a list of premises, in order."))
  :elt-type atc-premise
  :true-listp t
  :elementp-of-nil nil
  :pred atc-contextp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-contextualize (term (context atc-contextp))
  :returns term1
  :short "Put a term into a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the context elements,
     generating code for them
     and ending with the term given as input."))
  (b* (((when (endp context)) term)
       (premise (car context)))
    (atc-premise-case
     premise
     :compustate `(let ((,premise.var ,premise.term))
                    ,(atc-contextualize term (cdr context)))
     :test `(and ,premise.get
                 ,(atc-contextualize term (cdr context)))
     :other (raise "Internal error: reached :OTHER case of ATC-PREMISE."))))
