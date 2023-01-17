; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/top" :dir :system))

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
  (:test ((term any)))
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

(define atc-contextualize (term (context atc-contextp) (skip-cs booleanp))
  :returns term1
  :short "Put a term into a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the context elements,
     generating code for them
     and ending with the term given as input.")
   (xdoc::p
    "The @('skip-cs') flag controls whether
     we skip over the computation state bindings or not.
     For certain generated lemmas that apply just to ACL2 terms,
     and not to relations between ACL2 terms and C constructs,
     we skip over the bindings of computation states,
     because there are no computation states mentioned in the lemmas.")
   (xdoc::p
    "We wrap tests with @(tsee hide),
     to prevent ACL2 from making use of them,
     in the generated modular theorems,
     to simplify things in ways that interfere with the compositional proofs.
     For instance, when ACL2 has a hypothesis @('(not <term>)') in context,
     it rewrites occurrences of @('<term>') with @('nil'):
     this is generally good for interactive proofs,
     but not if that prevents a previously proved theorem from applying,
     about a subterm that is supposed not to be simplified"))
  (b* (((when (endp context)) term)
       (premise (car context)))
    (atc-premise-case
     premise
     :compustate (if skip-cs
                     (atc-contextualize term (cdr context) skip-cs)
                   `(let ((,premise.var ,premise.term))
                      ,(atc-contextualize term (cdr context) skip-cs)))
     :test `(implies (hide ,premise.term)
                     ,(atc-contextualize term (cdr context) skip-cs)))))
