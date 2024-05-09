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
     and generates the C expressions and statements from the terms,
     along with correctness theorems for them,
     there is a growing logical context consisting of
     conditional tests and of @(tsee let) and @(tsee mv-let) bindings.
     We call these tests and bindings `premises',
     which is not ideal terminology because
     it is essentially synonmous of `hypotheses',
     which in ACL2 refers specifically to terms (conditions) and not bindings.
     So we use `premises' because it is not used as much in ACL2;
     we may find a better nomenclature in the future.")
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
     (stored in @('compst-var') in the code generation code),
     and a term that must represent a computation state.
     The meaning is that the variable is bound to the term.")
   (xdoc::p
    "We also include bindings of single variables
     that hold (ACL2 models of) C values.
     (Note that a computation state is not, and does not model, a C value.)
     These also consist of a variable and a term,
     like the computation state bindings.
     However, it is useful to differentiate them in this fixtype,
     so we can support different processing of the different kind of bindings
     (as in @(tsee atc-contextualize)).")
   (xdoc::p
    "We also include bindings of multiple variables
     that hold (ACL2 models of) C values.
     This is similar to the bindings described in the previous paragraph,
     but involve @(tsee mv-let) instead of @(tsee let).")
   (xdoc::p
    "We also include terms that are tests of @(tsee if)s.")
   (xdoc::p
    "Since the terms used in premises are untranslated,
     we do not have type constraints on them.
     In the future, we could use a type for untranslated terms,
     perhaps a shallow/light recognizer
     analogous to @(tsee pseudo-event-formp).")
   (xdoc::p
    "We may add more kinds later."))
  (:compustate ((var symbol)
                (term any)))
  (:cvalue ((var symbol)
            (term any)))
  (:cvalues ((vars symbol-list)
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
    "A context consists of:")
   (xdoc::ul
    (xdoc::li
     "A preamble consisting of a list of terms.
      Since the terms are untranslated,
      we do not constrain them to be of any specific type,
      analogously to tests in premises
      (see discussion in @(tsee atc-premise)).")
    (xdoc::li
     "A list of premises, in order."))
   (xdoc::p
    "The preamble is fixed, and logically precedes the premises.
     The premises, as explained in @(see atc-generation-contexts), grow."))
  ((preamble true-list)
   (premises atc-premise-list))
  :pred atc-contextp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-atc-context
  :short "An irrelevant context."
  :type atc-contextp
  :body (make-atc-context :preamble nil :premises nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-context-extend ((context atc-contextp) (premises atc-premise-listp))
  :returns (new-context atc-contextp)
  :short "Extend a context with a list of premises."
  (change-atc-context context
                      :premises (append (atc-context->premises context)
                                        premises)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-contextualize ((formula "An untranslated term.")
                           (context atc-contextp)
                           (fn? symbolp)
                           (fn-guard? symbolp)
                           (compst-var? symbolp)
                           (limit-var? symbolp)
                           (limit-bound? pseudo-termp)
                           (preamblep booleanp)
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
     additional premises:")
   (xdoc::ul
    (xdoc::li
     "The fact that the computation state variable is a computation state.")
    (xdoc::li
     "The preamble from the context.")
    (xdoc::li
     "The fact that the guard of the target function @('fn')
      holds on the formals of the function.")
    (xdoc::li
     "The fact that the limit variable is an integer.")
    (xdoc::li
     "The fact that the limit variable is greater than or equal to
      a given bound (expressed as a term)."))
   (xdoc::p
    "If @('preamblep') is @('nil'), we omit the preamble from the context.
     This is used to generate some claims within the ACL2 proof builder.")
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
                     (and preamblep
                          (atc-context->preamble context))
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
        :cvalues `(mv-let ,premise.vars ,premise.term
                    ,(atc-contextualize-aux formula (cdr premises) skip-cs))
        :test `(implies
                (test* ,premise.term)
                ,(atc-contextualize-aux formula (cdr premises) skip-cs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-contextualize-compustate ((compst-var symbolp)
                                      (context-start atc-contextp)
                                      (context-end atc-contextp))
  :returns (term "An untranslated term.")
  :short "Put a computation state into a context
          that is the difference between two contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "When generating modular proofs,
     in certain cases we need to contextualize the computation state
     to the ``difference'' between a starting context and an ending context,
     where the latter is an extension of the former.
     This ACL2 function accomplished this.")
   (xdoc::p
    "The initial computation state is expressed as a variable,
     passed to this ACL2 function as @('compst-var').")
   (xdoc::p
    "We ensure that the starting context is a prefix of the ending context,
     i.e. it has the same preamble and a prefix of the premises.
     This should be always the case when this ACL2 function is called,
     but we defensively check that, stopping with an error if the check fails.")
   (xdoc::p
    "We calculate the premises in the ending context
     that are not in the starting context,
     and we go through them,
     wrapping the computation state variable
     with @(tsee let)s corresponding to binding of
     computation states and C variables.")
   (xdoc::p
    "We skip any test encountered in the list of premises.
     Because of the way this function is used, this is adeguate.
     The context difference may include tests in modular proofs,
     so it would be inappropriate to stop with an error
     upon encountering a test here."))
  (b* (((unless (equal (atc-context->preamble context-start)
                       (atc-context->preamble context-end)))
        (raise "Internal error: different context preambles ~x0 and ~x1."
               (atc-context->preamble context-start)
               (atc-context->preamble context-end)))
       (premises-start (atc-context->premises context-start))
       (premises-end (atc-context->premises context-end))
       ((unless (prefixp premises-start premises-end))
        (raise "Internal error: premises ~x0 not a prefix of premises ~x1."
               premises-start premises-end))
       (premises-diff (nthcdr (len premises-start) premises-end)))
    (atc-contextualize-compustate-aux compst-var premises-diff))

  :prepwork
  ((define atc-contextualize-compustate-aux ((compst-var symbolp)
                                             (premises atc-premise-listp))
     :returns (term "An untranslated term.")
     :parents nil
     (b* (((when (endp premises)) compst-var)
          (premise (car premises)))
       (atc-premise-case
        premise
        :compustate `(let ((,premise.var ,premise.term))
                       ,(atc-contextualize-compustate-aux compst-var
                                                          (cdr premises)))
        :cvalue `(let ((,premise.var ,premise.term))
                   ,(atc-contextualize-compustate-aux compst-var
                                                      (cdr premises)))
        :cvalues `(mv-let ,premise.vars ,premise.term
                    ,(atc-contextualize-compustate-aux compst-var
                                                       (cdr premises)))
        :test (atc-contextualize-compustate-aux compst-var
                                                (cdr premises)))))))
