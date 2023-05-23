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

(include-book "test-star")

(include-book "kestrel/std/util/defirrelevant" :dir :system)

(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
    "We also include bindings of variables that hold (ACL2 models of) C values.
     (Note that a computation state is not, and does not model, a C value.
     These also consist of a variable and a term,
     like the computation state bindings.
     However, it is useful to differentiate them in this fixtype,
     so we can support different processing of the different kind of bindings
     (as in @(tsee atc-contextualize)).")
   (xdoc::p
    "We also include terms that are tests of @(tsee if)s.")
   (xdoc::p
    "We may add more kinds later."))
  (:compustate ((var symbolp)
                (term any)))
  (:cvalue ((var symbolp)
            (term any)))
  (:test ((term any)))
  :pred atc-premisep
  :prepwork ((local (in-theory (enable identity)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atc-premise-list
  :short "Fixtype of lists of premises."
  :elt-type atc-premise
  :true-listp t
  :elementp-of-nil nil
  :pred atc-premise-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atc-context
  :short "Fixtype of contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "A context consists a list of premises, in order.
     We wrap the list type into a product type
     because we will extend this fixtype soon."))
  ((premises atc-premise-list))
  :pred atc-contextp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-atc-context
  :short "An irrelevant context."
  :type atc-contextp
  :body (make-atc-context :premises nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-contextualize ((formula "An untranslated term.")
                           (context atc-contextp)
                           (fn? symbolp)
                           (fn-guard? symbolp)
                           (compst-var? symbolp)
                           (limit-var? symbolp)
                           (limit-bound? pseudo-termp)
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
    "If @('fn-guard?') is @('nil'), we omit the guard hypothesis.
     This is used to generate some claims within the ACL2 proof builder.
     In this case, @('fn?') must be @('nil') too.")
   (xdoc::p
    "If @('compst-var?') is @('nil'),
     we avoid all the premises and hypotheses that concern computation states.
     Some of the theorems we generate do not involve computation states:
     they apply just to ACL2 terms that represent shallowly embedded C code;
     they do not apply to relations
     between ACL2 terms and deeply embedded C code.")
   (xdoc::p
    "If @('limit-var?') is @('nil'),
     we avoid the hypotheses that concern limits.
     Some of the theorems we generate (e.g. for pure expressions)
     do not involve execution recursion limits.
     In this case, @('limit-bound?') must be @('nil') too."))
  (b* ((skip-cs (not compst-var?))
       (formula (atc-contextualize-aux formula
                                       (atc-context->premises context)
                                       skip-cs))
       (hyps (append (and compst-var?
                          `((compustatep ,compst-var?)))
                     (and fn-guard?
                          `((,fn-guard? ,@(formals+ fn? wrld))))
                     (and limit-var?
                          `((integerp ,limit-var?)
                            (>= ,limit-var? ,limit-bound?)))))
       ((when (and (not fn-guard?) fn?))
        (raise "Internal error: FN-GUARD? is NIL but FN? is ~x0."
               fn?))
       ((when (and (not limit-var?) limit-bound?))
        (raise "Internal error: LIMIT-VAR? is NIL but LIMIT-BOUND? is ~x0."
               limit-bound?))
       (formula `(implies (and ,@hyps) ,formula)))
    formula)

  :prepwork
  ((define atc-contextualize-aux ((formula "An untranslated term.")
                                  (premises atc-premise-listp)
                                  (skip-cs booleanp))
     :returns (formula1 "An untranslated term.")
     :parents nil
     (b* (((when (endp premises)) formula)
          (premise (car premises)))
       (atc-premise-case
        premise
        :compustate
        (if skip-cs
            (atc-contextualize-aux formula (cdr premises) skip-cs)
          `(let ((,premise.var ,premise.term))
             ,(atc-contextualize-aux formula (cdr premises) skip-cs)))
        :cvalue `(let ((,premise.var ,premise.term))
                   ,(atc-contextualize-aux formula (cdr premises) skip-cs))
        :test `(implies
                (test* ,premise.term)
                ,(atc-contextualize-aux formula (cdr premises) skip-cs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-contextualize-compustate ((compst-var symbolp)
                                      (premises atc-premise-listp))
  :returns (term "An untranslated term.")
  :short "Put a computation state into context."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial computation state is expressed as a variable,
     passed to this ACL2 function as @('compst-var').
     We go through the premises and wrap the computation state variable
     with @(tsee let)s corresponding to binding of
     computation states and C variables.")
   (xdoc::p
    "This is used to calculate an updated (symbolic) computation state
     after the execution of some code, e.g. a list of block items.
     The caller takes the ``difference'' between
     the context before and after that execution,
     and passes it to this function.
     We expect that there should be no test in that difference context:
     we defensively check that, and raise an error if we find one.")
   (xdoc::p
    "Note that this function takes as input a list of premises, not a context.
     This is the ``difference'' betweeen the two contexts mentioned above."))
  (b* (((when (endp premises)) compst-var)
       (premise (car premises)))
    (atc-premise-case
     premise
     :compustate `(let ((,premise.var ,premise.term))
                    ,(atc-contextualize-compustate compst-var (cdr premises)))
     :cvalue `(let ((,premise.var ,premise.term))
                ,(atc-contextualize-compustate compst-var (cdr premises)))
     :test (raise "Internal error: test ~x0 found." premise.term))))
