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
(include-book "kestrel/std/system/formals-plus" :dir :system)
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

(define atc-contextualize ((formula "An untranslated term.")
                           (context atc-contextp)
                           (fn symbolp)
                           (fn-guard symbolp)
                           (compst-var symbolp)
                           (limit-var symbolp)
                           (limit-bound pseudo-termp)
                           (wrld plist-worldp))
  :returns (formula1 "An untranslated term.")
  :short "Put a formula into a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the context elements,
     generating code for them
     and ending with the term given as input.")
   (xdoc::p
    "We also add, around the resulting term from the process described above,
     with additional premises:")
   (xdoc::ul
    (xdoc::li
     "The fact that the guard of the target function @('fn')
      holds on the formals of the function.")
    (xdoc::li
     "The fact that the computation state variable is a computation state.")
    (xdoc::li
     "The fact that the limit variable is an integer.")
    (xdoc::li
     "The fact that the limit variable is greater than or equal to
      a given bound (expressed as a term)."))
   (xdoc::p
    "If @('compst-var') is @('nil'),
     we avoid all the premises and hypotheses that concern computation states.
     Some of the theorems we generate do not involve computation states:
     they apply just to ACL2 terms that represent shallowly embedded C code;
     they do not apply to relations between ACL2 and deeply embedded C code.")
   (xdoc::p
    "If @('limit-var') is @('nil'),
     we avoid the hypotheses that concern limits.
     Some of the theorems we generate (e.g. for pure expressions)
     do not involve execution recursion limits.
     In this case, @('limit-bound') must be @('nil') too.")
   (xdoc::p
    "We wrap tests from the context premises with @(tsee hide),
     to prevent ACL2 from making use of them,
     in the generated modular theorems,
     to simplify things in ways that interfere with the compositional proofs.
     For instance, when ACL2 has a hypothesis @('(not <term>)') in context,
     it rewrites occurrences of @('<term>') with @('nil'):
     this is generally good for interactive proofs,
     but not if that prevents a previously proved theorem from applying,
     about a subterm that is supposed not to be simplified"))
  (b* ((skip-cs (not compst-var))
       (formula (atc-contextualize-aux formula context skip-cs))
       (hyps (append `((,fn-guard ,@(formals+ fn wrld)))
                     (and compst-var
                          `((compustatep ,compst-var)))
                     (and limit-var
                          `((integerp ,limit-var)
                            (>= ,limit-var ,limit-bound)))))
       ((when (and (not limit-var) limit-bound))
        (raise "Internal error: LIMIT-VAR is NIL but LIMIT-BOUND is ~x0."
               limit-bound))
       (formula `(implies (and ,@hyps) ,formula)))
    formula)

  :prepwork
  ((define atc-contextualize-aux ((formula "An untranslated term.")
                                  (context atc-contextp)
                                  (skip-cs booleanp))
     :returns (formula1 "An untranslated term.")
     :parents nil
     (b* (((when (endp context)) formula)
          (premise (car context)))
       (atc-premise-case
        premise
        :compustate
        (if skip-cs
            (atc-contextualize-aux formula (cdr context) skip-cs)
          `(let ((,premise.var ,premise.term))
             ,(atc-contextualize-aux formula (cdr context) skip-cs)))
        :test `(implies
                (hide ,premise.term)
                ,(atc-contextualize-aux formula (cdr context) skip-cs)))))))
