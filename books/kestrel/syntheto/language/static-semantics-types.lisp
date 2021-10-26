; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax-operations")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "std/util/defval" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap variable-context
  :short "Fixtype of variable contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable context is a finite map from identifiers to types.
     The identifiers are the names of the variables."))
  :key-type identifier
  :val-type type
  :pred variable-contextp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typed-variables-to-variable-context ((tvars typed-variable-listp))
  :returns (var-ctxt variable-contextp)
  :short "Turn a list of typed variables into a variable context."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just reformat the list into a map.
     If there are duplicate variable names,
     the type of the first one in the list prevails;
     however, well-formed lists of typed variables have unique names."))
  (cond ((endp tvars) nil)
        (t (omap::update (typed-variable->name (car tvars))
                         (typed-variable->type (car tvars))
                         (typed-variables-to-variable-context (cdr tvars)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod binding
  :short "Fixtype of bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "We plan to incorporate this into the abstract syntax,
     but for now we define this here because we need this
     to define the static semantics of Syntheto.
     In particular, as we traverse an expression
     to check that it satisfies the constraints of the static semantic,
     we collect the let bindings along the way.
     This fixtype captures one of these let bindings:
     it corresponds to the first two components of
     a binding expression in the abstract syntax."))
  ((variables typed-variable-list)
   (value expression))
  :pred bindingp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum obligation-hyp
  :short "Fixtype of hypotheses for proof obligations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Proof obligations arise from expressions
     that may be contained in larger expressions.
     In that case, the path from the super-expression to the sub-expression
     may include boolean conditions (tests or negated tests)
     as well as bindings:
     these all provide hypotheses in which the proof obligation must be proved.
     That a boolean condition is a hypothesis is obvious.
     But note that also a binding can be regarded as a hypothesis of sorts,
     because it introduces new variables and equates them to expressions:
     both the new variables and the equations can be used
     to prove the obligation.")
   (xdoc::p
    "This fixtype captures these two kinds of hypotheses
     for proof obligations."))
  (:condition ((get expression)))
  (:binding ((get binding)))
  :pred obligation-hypp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist obligation-hyp-list
  :short "Fixtype of lists of hypotheses for proof obligations."
  :elt-type obligation-hyp
  :true-listp t
  :elementp-of-nil nil
  :pred obligation-hyp-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod proof-obligation
  :short "Fixtype of proof obligations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the proof obligations that arise from expressions.")
   (xdoc::p
    "A proof obligation consists of
     a list of typed variables,
     a list of hypotheses,
     and a conclusion.
     One can form a formula from it,
     universally quantified over the variables,
     where each hypothesis becomes
     an implication antecedent (when it is an expression)
     or a let binding (when it is a binding),,
     and where the conclusion becomes the final
     implication consequent or let binding body.
     This formula construction will be defined later."))
  ((variables typed-variable-list)
   (hypotheses obligation-hyp-list)
   (conclusion expression)
   (source-expression expression))
  :pred proof-obligationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist proof-obligation-list
  :short "Fixtype of lists of proof obligations."
  :elt-type proof-obligation
  :true-listp t
  :elementp-of-nil nil
  :pred proof-obligation-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-proof-obligation
  proof-obligation
  :short "Fixtype of optional proof obligations."
  :pred maybe-proof-obligationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod context
  :short "Fixtype of contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "A context consists of the following components:")
   (xdoc::ul
    (xdoc::li
     "A sequence of top-level constructs
      processed so far by the static semantics.
      This starts with the empty sequence,
      and is extended one top-level construct after the other.
      In Syntheto, order matters:
      things are introduced in order, bottom-up;
      there are no forward references allowed,
      unless they are within explicit mutual recursion constructs.")
    (xdoc::li
     "A list of the type names whose definitions are being checked.
      This is non-empty only when checking
      a type definition
      (in which case it contains the name of the type being defined)
      or a type recursion
      (in which case it contains the names of the types being defined).
      This component is necessary to accept recursive type definitions.")
    (xdoc::li
     "A list of the function headers whose definitions are being checked.
      This is non-empty only when checking
      a function definition
      (in which case it contains the header of the function being defined)
      or a function recursion
      (in which case it contains the headers of the functions being defined).
      This component is necessary to accept recursive function definitions.")
    (xdoc::li
     "A variable context for the variables encountered so far and their types,
      when checking an expression.
      This is non-empty only if we are checking an expression.")
    (xdoc::li
     "A list of the typed variables
      at the top level of the expression being checked.
      These variables are used in the generated proof obligations,
      where only the top-level variables count,
      because the non-top-level variables, i.e. the let-bound variables,
      are collected in the obligation hypotheses instead (see next item).
      This list is non-empty only if we are checking an expression.")
    (xdoc::li
     "A list of the obligation hypotheses collected
      at the current position in the Syntheto code.
      See @(tsee obligation-hyp).
      This list is non-empty only if we are checking an expression.")))
  ((tops toplevel-listp)
   (types identifier-listp)
   (functions function-header-listp)
   (variables variable-context)
   (obligation-vars typed-variable-list)
   (obligation-hyps obligation-hyp-listp))
  :pred contextp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-add-variables ((var-ctxt variable-contextp) (ctxt contextp))
  :returns (new-ctxt contextp)
  :short "Add some variables to a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables to be added are supplied as a variable context
     that is used to update the context's variable context.
     The update may override previous pairs:
     this is expected; it happens with let bindings."))
  (b* ((old-var-ctxt (context->variables ctxt))
       (new-var-ctxt (omap::update* (variable-context-fix var-ctxt)
                                    old-var-ctxt)))
    (change-context ctxt :variables new-var-ctxt))
  :hooks (:fix)
  ///

  (defret context->types-of-context-add-variables
    (equal (context->types new-ctxt)
           (context->types ctxt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-add-condition ((cond expressionp) (ctxt contextp))
  :returns (new-ctxt contextp)
  :short "Add a condition obligation hypothesis to a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "The hypothesis is added at the end,
     because its well-formedness may depend on the preceding hypotheses."))
  (change-context ctxt
                  :obligation-hyps (append
                                    (context->obligation-hyps ctxt)
                                    (list (obligation-hyp-condition cond))))
  :hooks (:fix)
  ///

  (defret context->types-of-context-add-condition
    (equal (context->types new-ctxt)
           (context->types ctxt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-add-condition-list ((conds expression-listp) (ctxt contextp))
  :returns (new-ctxt contextp)
  :short "Add a list of condition obligation-hypotheses to a context, in order."
  (b* (((when (endp conds)) (context-fix ctxt))
       (ctxt (context-add-condition (car conds) ctxt)))
    (context-add-condition-list (cdr conds) ctxt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-add-binding ((bind bindingp) (ctxt contextp))
  :returns (new-ctxt contextp)
  :short "Add a binding obligation hypothesis to a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "The hypothesis is added at the end,
     because its well-formedness may depend on the preceding hypotheses."))
  (change-context ctxt
                  :obligation-hyps (append
                                    (context->obligation-hyps ctxt)
                                    (list (obligation-hyp-binding bind))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define context-add-toplevel ((new-top toplevelp) (ctxt contextp))
  :returns (new-ctxt contextp)
  :short "Add a toplevel object to context."
  :enabled t
  (change-context ctxt :tops (append (context->tops ctxt)
                                     (list new-top)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obligation-hyp-to-expr ((hyp obligation-hypp))
  :returns (e expressionp)
  (obligation-hyp-case hyp
     :condition hyp.get
     :binding (b* (((binding b) hyp.get))
                (equate-expressions (typed-variable-list->-expression b.variables)
                                    b.value)))
  :hooks (:fix))

(define obligation-hyps-to-expressions ((l obligation-hyp-listp))
  :returns (exprs expression-listp)
  (if (endp l)
      ()
    (cons (obligation-hyp-to-expr (car l))
          (obligation-hyps-to-expressions (cdr l))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obligation-function-calls ((oblig proof-obligationp))
  :returns (fn-nms string-listp)
  ;; Crude but effective!
  (functions-called oblig))

(define split-obligations-using-functions ((obligs proof-obligation-listp) (fn-names string-listp))
  :returns (mv (before-obligs proof-obligation-listp :hyp :guard)
               (after-obligs proof-obligation-listp :hyp :guard))
  (if (endp obligs)
      (mv () ())
    (b* (((mv r-before-obligs r-after-obligs)
          (split-obligations-using-functions (cdr obligs) fn-names))
         (oblig (car obligs)))
      (if (null (intersection-equal fn-names (obligation-function-calls oblig)))
          (mv (cons oblig r-before-obligs) r-after-obligs)
        (mv r-before-obligs (cons oblig r-after-obligs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-builtin-function-in/out/pre-post ((name identifierp)
                                              (types type-listp))
  :returns (mv err?
               (foundp booleanp)
               (inputs typed-variable-listp)
               (outputs typed-variable-listp)
               (precondition? maybe-expressionp)
               (postcondition? maybe-expressionp))
  :short "Retrieve the inputs, outputs, precondition, and postcondition
          of a built-in function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This ACL2 function implicitly defines the
     inputs, outputs, preconditions, and postoconditions
     of the built-in functions.
     At this time, there is no other explicit representation of them
     in the Syntheto abstract syntax of top-level constructs.")
   (xdoc::p
    "The current built-in functions are polymorphic.
     The @('types') argument of this ACL2 function
     specifies which monomorphic instance is being referenced.")
   (xdoc::p
    "The names of the currently supported built-in functions
     are in @(tsee *builtin-function-names*)."))
  (cond
   ((identifier-equiv name (identifier "empty"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 nil ; inputs
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 nil ; inputs
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "add"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type (type-sequence->element type))
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "xy")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type (type-set->element type))
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "xy")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "append"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type)
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "xy")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "length"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "b")
                                            :type (type-integer)))
                 nil ; precondition
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "b")
                                            :type (type-integer)))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "is_empty"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "b")
                                            :type (type-boolean)))
                 nil ; precondition
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "b")
                                            :type (type-boolean)))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "first"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "y")
                                            :type (type-sequence->element
                                                   type)))
                 (make-expression-unary
                  :operator (unary-op-not)
                  :operand (make-expression-call
                            :function (identifier "is_empty")
                            :types (list type)
                            :arguments
                            (list (make-expression-variable
                                   :name (identifier "x")))))
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "y")
                                            :type (type-set->element
                                                   type)))
                 (make-expression-unary
                  :operator (unary-op-not)
                  :operand (make-expression-call
                            :function (identifier "is_empty")
                            :types (list type)
                            :arguments
                            (list (make-expression-variable
                                   :name (identifier "x")))))
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "last"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "y")
                                            :type (type-sequence->element
                                                   type)))
                 (make-expression-unary
                  :operator (unary-op-not)
                  :operand (make-expression-call
                            :function (identifier "is_empty")
                            :types (list type)
                            :arguments
                            (list (make-expression-variable
                                   :name (identifier "x")))))
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "rest"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "y")
                                            :type type))
                 (make-expression-unary
                  :operator (unary-op-not)
                  :operand (make-expression-call
                            :function (identifier "is_empty")
                            :types (list type)
                            :arguments
                            (list (make-expression-variable
                                   :name (identifier "x")))))
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type type))
                 (list (make-typed-variable :name (identifier "y")
                                            :type type))
                 (make-expression-unary
                  :operator (unary-op-not)
                  :operand (make-expression-call
                            :function (identifier "is_empty")
                            :types (list type)
                            :arguments
                            (list (make-expression-variable
                                   :name (identifier "x")))))
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "member"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type (type-sequence->element type))
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "b")
                                            :type (type-boolean)))
                 nil ; precondition
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type (type-set->element type))
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "b")
                                            :type (type-boolean)))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   ((identifier-equiv name (identifier "remove_first"))
    (b* (((unless (= (len types) 1))
          (mv (list :builtin-wrong-types
                (identifier-fix name)
                (type-list-fix types))
              nil nil nil nil nil))
         (type (car types)))
      (cond ((type-case type :sequence)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type (type-sequence->element type))
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "z")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            ((type-case type :set)
             (mv nil ; err?
                 t
                 (list (make-typed-variable :name (identifier "x")
                                            :type (type-set->element type))
                       (make-typed-variable :name (identifier "y")
                                            :type type))
                 (list (make-typed-variable :name (identifier "z")
                                            :type type))
                 nil ; precondition
                 nil ; postcondition
                 ))
            (t (mv (list :builtin-wrong-type
                     (identifier-fix name)
                     (type-fix type))
                   nil nil nil nil nil)))))
   (t (mv nil nil nil nil nil nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-in/out/pre/post ((name identifierp)
                                      (types type-listp)
                                      (ctxt contextp))
  :returns (mv err?
               (inputs typed-variable-listp)
               (outputs typed-variable-listp)
               (precondition? maybe-expressionp)
               (postcondition? maybe-expressionp))
  :short "Retrieve the inputs, outputs, precondition, and postcondition
          of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call a separate ACL2 function to see whether
     the Syntheto function is a built-in one.
     If that ACL2 function returns an error, we return it here too.
     If that ACL2 functions finds the function among the built-in ones,
     we return the retrieved information.
     Otherwise, we look for the function in the context."))
  (b* (((mv err? foundp inputs outputs precond postcond)
        (get-builtin-function-in/out/pre-post name types))
       ((when err?) (mv err? nil nil nil nil))
       ((when foundp) (mv nil inputs outputs precond postcond))
       ((when (consp types))
        (mv (list :non-null-types-for-non-builtin-function
              (type-list-fix types))
            nil nil nil nil))
       (fundef? (get-function-definition name (context->tops ctxt)))
       ((when fundef?)
        (b* ((header (function-definition->header fundef?))
             (inputs (function-header->inputs header))
             (outputs (function-header->outputs header))
             (precond (function-definition->precondition fundef?))
             (postcond (function-definition->postcondition fundef?)))
          (mv nil inputs outputs precond postcond)))
       (header? (get-function-header-in-list name (context->functions ctxt)))
       ((when header?)
        (b* ((inputs (function-header->inputs header?))
             (outputs (function-header->outputs header?)))
          (mv nil inputs outputs nil nil))))
    (mv (list :function-not-found (identifier-fix name)) nil nil nil nil))
  :hooks (:fix)
  ///
  (more-returns
   (inputs true-listp :rule-classes :type-prescription)
   (outputs true-listp :rule-classes :type-prescription)))
