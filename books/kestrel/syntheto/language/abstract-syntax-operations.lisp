; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-operations
  :parents (language abstract-syntax)
  :short "Operations on the Syntheto abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are operations to query and manipulate the syntax.
     We will add more as needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-op-nonstrictp ((op binary-opp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is non-strict."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Syntheto, some boolean connectives are non-strict,
     in the sense that one operand can assume
     the truth or falsehood of the other operand
     to discharge its type obligations.
     This is because the value of the result may be determined
     just by one operand value in some cases.
     See the static semantics for details."))
  (and (member-eq (binary-op-kind op)
                  '(:and :or :implies :implied))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-op-strictp ((op binary-opp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is strict."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the operators that are not non-strict,
     i.e. that are strict."))
  (not (binary-op-nonstrictp op))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap variable-substitution
  :short "Fixtype of variable substitutions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable substituion is a finite map from identifiers to expressions."))
  :key-type identifier
  :val-type expression
  :pred variable-substitutionp)

(defrule variable-substitutionp-of-from-lists
  (implies (and (identifier-listp keys)
                (expression-listp vals)
                (equal (len keys) (len vals)))
           (variable-substitutionp (omap::from-lists keys vals)))
  :enable (variable-substitutionp omap::from-lists))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-expression-fns
  :short "Mutually recursive functions for expression substitution."

  (define subst-expression ((subst variable-substitutionp)
                            (expr expressionp))
    :returns (new-expr expressionp)
    :parents (abstract-syntax-operations subst-expression-fns)
    :short "Apply a substitution to an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "Literals are unchanged.")
     (xdoc::p
      "If a variable is in the substitution map,
       we replace it with its associated expression.
       Otherwise the variable is unchanged.")
     (xdoc::p
      "Most expressions and related entities (e.g. branches) are transformed by
       recursively applying the substitution to subexpressions.")
     (xdoc::p
      "When we encounter a binding,
       we remove from the substitution map the bound variables
       before applying the (new) substitution to the body."))
    (expression-case
     expr
     :literal (expression-literal expr.get)
     :variable (b* ((pair (omap::in expr.name
                                    (variable-substitution-fix subst))))
                 (if pair
                     (cdr pair)
                   (expression-variable expr.name)))
     :unary (make-expression-unary :operator expr.operator
                                   :operand (subst-expression subst
                                                              expr.operand))
     :binary (make-expression-binary
              :operator expr.operator
              :left-operand (subst-expression subst expr.left-operand)
              :right-operand (subst-expression subst expr.right-operand))
     :if (make-expression-if :test (subst-expression subst expr.test)
                             :then (subst-expression subst expr.then)
                             :else (subst-expression subst expr.else))
     :when (make-expression-if :test (subst-expression subst expr.test)
                               :then (subst-expression subst expr.then)
                               :else (subst-expression subst expr.else))
     :unless (make-expression-if :test (subst-expression subst expr.test)
                                 :then (subst-expression subst expr.then)
                                 :else (subst-expression subst expr.else))
     :cond (make-expression-cond
            :branches (subst-branch-list subst expr.branches))
     :call (make-expression-call
            :function expr.function
            :types expr.types
            :arguments (subst-expression-list subst expr.arguments))
     :multi (make-expression-multi
             :arguments (subst-expression-list subst expr.arguments))
     :component (make-expression-component
                 :multi (subst-expression subst expr.multi)
                 :index expr.index)
     :bind (b* ((new-value (subst-expression subst expr.value))
                (new-subst (omap::delete*
                            (set::mergesort
                             (typed-variable-list->name-list expr.variables))
                            (variable-substitution-fix subst)))
                (new-body (subst-expression new-subst expr.body)))
             (make-expression-bind :variables expr.variables
                                   :value new-value
                                   :body new-body))
     :product-construct (make-expression-product-construct
                         :type expr.type
                         :fields (subst-initializer-list subst expr.fields))
     :product-field (make-expression-product-field
                     :type expr.type
                     :target (subst-expression subst expr.target)
                     :field expr.field)
     :product-update (make-expression-product-update
                      :type expr.type
                      :target (subst-expression subst expr.target)
                      :fields (subst-initializer-list subst expr.fields))
     :sum-construct (make-expression-sum-construct
                     :type expr.type
                     :alternative expr.alternative
                     :fields (subst-initializer-list subst expr.fields))
     :sum-field (make-expression-sum-field
                 :type expr.type
                 :target (subst-expression subst expr.target)
                 :alternative expr.alternative
                 :field expr.field)
     :sum-update (make-expression-sum-update
                  :type expr.type
                  :target (subst-expression subst expr.target)
                  :alternative expr.alternative
                  :fields (subst-initializer-list subst expr.fields))
     :sum-test (make-expression-sum-test
                :type expr.type
                :target (subst-expression subst expr.target)
                :alternative expr.alternative)
     :bad-expression (make-expression-bad-expression :info expr.info))
    :measure (expression-count expr))

  (define subst-expression-list ((subst variable-substitutionp)
                                 (exprs expression-listp))
    :returns (new-exprs expression-listp)
    :parents (abstract-syntax-operations subst-expression-fns)
    :short "Apply a substitution to a list of expressions."
    (cond ((endp exprs) nil)
          (t (cons (subst-expression subst (car exprs))
                   (subst-expression-list subst (cdr exprs)))))
    :measure (expression-list-count exprs))

  (define subst-branch ((subst variable-substitutionp)
                        (branch branchp))
    :returns (new-branch branchp)
    :parents (abstract-syntax-operations subst-expression-fns)
    :short "Apply a substitution to a branch."
    (make-branch :condition (subst-expression subst (branch->condition branch))
                 :action (subst-expression subst (branch->action branch)))
    :measure (branch-count branch))

  (define subst-branch-list ((subst variable-substitutionp)
                             (branches branch-listp))
    :returns (new-branches branch-listp)
    :parents (abstract-syntax-operations subst-expression-fns)
    :short "Apply a substitution to a list of branches."
    (cond ((endp branches) nil)
          (t (cons (subst-branch subst (car branches))
                   (subst-branch-list subst (cdr branches)))))
    :measure (branch-list-count branches))

  (define subst-initializer ((subst variable-substitutionp)
                             (init initializerp))
    :returns (new-init initializerp)
    :short "Apply a substitution to an initializer."
    (make-initializer :field (initializer->field init)
                      :value (subst-expression subst (initializer->value init)))
    :measure (initializer-count init))

  (define subst-initializer-list ((subst variable-substitutionp)
                                  (inits initializer-listp))
    :returns (new-inits initializer-listp)
    :short "Apply a substitution to a list of initializers."
    (cond ((endp inits) nil)
          (t (cons (subst-initializer subst (car inits))
                   (subst-initializer-list subst (cdr inits)))))
    :measure (initializer-list-count inits))

  :verify-guards nil ; done below
  ///
  (verify-guards subst-expression)

  (fty::deffixequiv-mutual subst-expression-fns))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equate-expressions ((left expressionp) (right expressionp))
  :returns (equality expressionp)
  :short "Construct an equality between two expressions."
  (make-expression-binary :operator (binary-op-eq)
                          :left-operand left
                          :right-operand right)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equate-expression-lists ((lefts expression-listp)
                                 (rights expression-listp))
  :guard (= (len lefts) (len rights))
  :returns (equalities expression-listp)
  :short "Construct a list of equalities between two lists of expressions,
          element-wise."
  (cond ((endp lefts) nil)
        (t (cons (equate-expressions (car lefts) (car rights))
                 (equate-expression-lists (cdr lefts) (cdr rights)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define negate-expression ((expr expressionp))
  :returns (negated-expr expressionp)
  :short "Negate an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The argument expression should be boolean-valued
     in order for the resulting expression to make sense.
     We apply the unary boolean negation operator to the expression,
     but we simplify the resulting expression as follows, when possible:")
   (xdoc::ul
    (xdoc::li
     "If the argument expression is a boolean literal, we flip it.")
    (xdoc::li
     "If the argument expression starts with the boolean negation operator,
      we simply remove the operator (double negation cancels).")
    (xdoc::li
     "If the argument expression starts with an equality or ordering operator,
      we change the operator to its negation."))
   (xdoc::p
    "Other simplifications could be done,
     but for now we limit ourselves to the ones above."))
  (expression-case
   expr
   :literal (literal-case
             expr.get
             :boolean (expression-literal
                       (literal-boolean
                        (not expr.get.value)))
             :character (prog2$ (raise "Internal error: ~
                                        applying boolean negation to ~x0."
                                       expr.get)
                                (expression-fix expr))
             :string (prog2$ (raise "Internal error: ~
                                     applying boolean negation to ~x0."
                                    expr.get)
                             (expression-fix expr))
             :integer (prog2$ (raise "Internal error: ~
                                      applying boolean negation to ~x0."
                                     expr.get)
                              (expression-fix expr)))
   :variable (make-expression-unary :operator (unary-op-not)
                                    :operand expr)
   :unary (unary-op-case
           expr.operator
           :not expr.operand
           :minus (prog2$ (raise "Internal error: ~
                                  applying boolean negation to ~x0."
                                 (expression-fix expr))
                          (expression-fix expr)))
   :binary (binary-op-case
            expr.operator
            :eq (make-expression-binary :operator (binary-op-ne)
                                        :left-operand expr.left-operand
                                        :right-operand expr.right-operand)
            :ne (make-expression-binary :operator (binary-op-eq)
                                        :left-operand expr.left-operand
                                        :right-operand expr.right-operand)
            :lt (make-expression-binary :operator (binary-op-ge)
                                        :left-operand expr.left-operand
                                        :right-operand expr.right-operand)
            :le (make-expression-binary :operator (binary-op-gt)
                                        :left-operand expr.left-operand
                                        :right-operand expr.right-operand)
            :gt (make-expression-binary :operator (binary-op-le)
                                        :left-operand expr.left-operand
                                        :right-operand expr.right-operand)
            :ge (make-expression-binary :operator (binary-op-lt)
                                        :left-operand expr.left-operand
                                        :right-operand expr.right-operand)
            :and (make-expression-unary :operator (unary-op-not)
                                        :operand expr)
            :or (make-expression-unary :operator (unary-op-not)
                                       :operand expr)
            :implies (make-expression-unary :operator (unary-op-not)
                                            :operand expr)
            :implied (make-expression-unary :operator (unary-op-not)
                                            :operand expr)
            :iff (make-expression-unary :operator (unary-op-not)
                                        :operand expr)
            :add (prog2$ (raise "Internal error: ~
                                 applying boolean negation to ~x0."
                                (expression-fix expr))
                         (expression-fix expr))
            :sub (prog2$ (raise "Internal error: ~
                                 applying boolean negation to ~x0."
                                (expression-fix expr))
                         (expression-fix expr))
            :mul (prog2$ (raise "Internal error: ~
                                 applying boolean negation to ~x0."
                                (expression-fix expr))
                         (expression-fix expr))
            :div (prog2$ (raise "Internal error: ~
                                 applying boolean negation to ~x0."
                                (expression-fix expr))
                         (expression-fix expr))
            :rem (prog2$ (raise "Internal error: ~
                                 applying boolean negation to ~x0."
                                (expression-fix expr))
                         (expression-fix expr)))
   :if (make-expression-unary :operator (unary-op-not)
                              :operand expr)
   :when (make-expression-unary :operator (unary-op-not)
                                :operand expr)
   :unless (make-expression-unary :operator (unary-op-not)
                                  :operand expr)
   :cond (make-expression-unary :operator (unary-op-not)
                                :operand expr)
   :call (make-expression-unary :operator (unary-op-not)
                                :operand expr)
   :multi (make-expression-unary :operator (unary-op-not)
                                 :operand expr)
   :component (make-expression-unary :operator (unary-op-not)
                                     :operand expr)
   :bind (make-expression-unary :operator (unary-op-not)
                                :operand expr)
   :product-construct (make-expression-unary :operator (unary-op-not)
                                             :operand expr)
   :product-field (make-expression-unary :operator (unary-op-not)
                                         :operand expr)
   :product-update (make-expression-unary :operator (unary-op-not)
                                          :operand expr)
   :sum-construct (make-expression-unary :operator (unary-op-not)
                                         :operand expr)
   :sum-field (make-expression-unary :operator (unary-op-not)
                                     :operand expr)
   :sum-update (make-expression-unary :operator (unary-op-not)
                                      :operand expr)
   :sum-test (make-expression-unary :operator (unary-op-not)
                                    :operand expr)
   :bad-expression (make-expression-unary :operator (unary-op-not)
                                          :operand expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define disjoin-expressions ((exprs expression-listp))
  :returns (disjoined-expression expressionp)
  :short "Disjoin a list of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently Syntheto's boolean disjunction operator is binary.
     Thus, to disjoin a list of expressions, we need to build a nest.
     If there are no expressions, we return the boolean literal for false.
     If there is one expression, we return it.
     If there are two or more expressions, we return a nest."))
  (cond ((endp exprs) (expression-literal (literal-boolean nil)))
        ((endp (cdr exprs)) (expression-fix (car exprs)))
        (t (make-expression-binary
            :operator (binary-op-or)
            :left-operand (car exprs)
            :right-operand (disjoin-expressions (cdr exprs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define conjoin-expressions ((exprs expression-listp))
  :returns (conjoined-expression expressionp)
  :short "Conjoin a list of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently Syntheto's boolean conjunction operator is binary.
     Thus, to conjoin a list of expressions, we need to build a nest.
     If there are no expressions, we return the boolean literal for false.
     If there is one expression, we return it.
     If there are two or more expressions, we return a nest."))
  (cond ((endp exprs) (expression-literal (literal-boolean t)))
        ((endp (cdr exprs)) (expression-fix (car exprs)))
        (t (make-expression-binary
            :operator (binary-op-and)
            :left-operand (car exprs)
            :right-operand (conjoin-expressions (cdr exprs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-type-definition-in-type-definitions
  ((name identifierp) (typedefs type-definition-listp))
  :returns (typedef? maybe-type-definitionp)
  :short "Find the definition of a type with a given name
          in a list of type definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when looking up a type definition in a type recursion.")
   (xdoc::p
    "We return @('nil') if the type definition is not found.")
   (xdoc::p
    "We look up the definitions in order.
     In well-formed lists of type definitions,
     the type names are unique,
     so any order would yield the same result."))
  (b* (((when (endp typedefs)) nil)
       ((when (identifier-equiv name (type-definition->name (car typedefs))))
        (type-definition-fix (car typedefs))))
    (get-type-definition-in-type-definitions name (cdr typedefs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-type-definition ((name identifierp) (tops toplevel-listp))
  :returns (typedef? maybe-type-definitionp)
  :short "Find the definition of a type with a given name
          in a list of top-level constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look both at the type definitions at the top level
     and at the type definitions inside the type recursions.")
   (xdoc::p
    "We return @('nil') if the type definition is not found.")
   (xdoc::p
    "We look up the top-level constructs in order.
     In well-formed lists of top-level constructs,
     the defined type names are unique,
     so any order would yield the same result."))
  (b* (((when (endp tops)) nil)
       (top (car tops)))
    (toplevel-case
     top
     :type (if (identifier-equiv name (type-definition->name top.get))
               top.get
             (get-type-definition name (cdr tops)))
     :types (b* ((definition? (get-type-definition-in-type-definitions
                               name (type-recursion->definitions top.get))))
              (or definition?
                  (get-type-definition name (cdr tops))))
     :function (get-type-definition name (cdr tops))
     :functions (get-type-definition name (cdr tops))
     :specification (get-type-definition name (cdr tops))
     :theorem (get-type-definition name (cdr tops))
     :transform (get-type-definition name (cdr tops))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-defined-type-names-in-type-definitions ((typedefs
                                                     type-definition-listp))
  :returns (names identifier-listp)
  :short "Return the list of the type names defined in
          a list of definitions, in the same order."
  (cond ((endp typedefs) nil)
        (t (cons (type-definition->name (car typedefs))
                 (get-defined-type-names-in-type-definitions (cdr typedefs)))))
  :hooks (:fix)
  ///

  (defrule defined-type-name-in-type-definitions-has-definition
    (implies (member-equal name
                           (get-defined-type-names-in-type-definitions
                            typedefs))
             (type-definitionp
              (get-type-definition-in-type-definitions name typedefs)))
    :enable get-type-definition-in-type-definitions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-defined-type-names ((tops toplevel-listp))
  :returns (names identifier-listp)
  :short "Return the list of the type names defined in
          a list of top-level constructs, in the same order."
  (b* (((when (endp tops)) nil)
       (top (car tops))
       (names (toplevel-case
               top
               :type (list (type-definition->name top.get))
               :types (get-defined-type-names-in-type-definitions
                       (type-recursion->definitions top.get))
               :function nil
               :functions nil
               :specification nil
               :theorem nil
               :transform nil))
       (more-names (get-defined-type-names (cdr tops))))
    (append names more-names))
  :hooks (:fix)
  ///

  (defrule defined-type-name-has-definition
    (implies (member-equal name
                           (get-defined-type-names tops))
             (type-definitionp
              (get-type-definition name tops)))
    :enable get-type-definition))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define direct-supertype ((type typep) (tops toplevel-listp))
  :returns (super? maybe-typep)
  :short "Return the direct supertype of a type, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only a type defined as a subtype has a direct supertype,
     namely the one referenced in the subtype definition.
     All the other types do not."))
  (type-case
   type
   :boolean nil
   :character nil
   :string nil
   :integer nil
   :set nil
   :sequence nil
   :map nil
   :option nil
   :defined (b* ((typedef (get-type-definition type.name tops))
                 ((when (not typedef)) nil)
                 (definer (type-definition->body typedef))
                 ((when (not definer)) nil))
              (type-definer-case
               definer
               :product nil
               :sum nil
               :subset (type-subset->supertype definer.get))))
  :hooks (:fix)
  ///

  (defrule defined-type-when-direct-supertype
    (implies (direct-supertype type tops)
             (type-case type :defined))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-type-subset ((type typep) (tops toplevel-listp))
  :returns (tsub maybe-type-subsetp)
  :short "Return the type subset that defines a type, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like an enriched version of @(tsee direct-supertype):
     instead of returning just the supertype,
     it returns the whole type subset,
     consisting of the supertype, restriction, etc."))
  (type-case
   type
   :boolean nil
   :character nil
   :string nil
   :integer nil
   :set nil
   :sequence nil
   :map nil
   :option nil
   :defined (b* ((typedef (get-type-definition type.name tops))
                 ((when (not typedef)) nil)
                 (definer (type-definition->body typedef))
                 ((when (not definer)) nil))
              (type-definer-case
               definer
               :product nil
               :sum nil
               :subset definer.get)))
  :hooks (:fix)
  ///

  (defrule defined-type-when-get-type-subset
    (implies (get-type-subset type tops)
             (type-case type :defined))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-type-product ((type typep) (tops toplevel-listp))
  :returns (tprod maybe-type-productp)
  :short "Return the type product that defines a type, if any."
  (type-case
   type
   :boolean nil
   :character nil
   :string nil
   :integer nil
   :set nil
   :sequence nil
   :map nil
   :option nil
   :defined (b* ((typedef (get-type-definition type.name tops))
                 ((when (not typedef)) nil)
                 (definer (type-definition->body typedef))
                 ((when (not definer)) nil))
              (type-definer-case
               definer
               :product definer.get
               :sum nil
               :subset nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-type-sum ((type typep) (tops toplevel-listp))
  :returns (tprod maybe-type-sump)
  :short "Return the type sum that defines a type, if any."
  (type-case
   type
   :boolean nil
   :character nil
   :string nil
   :integer nil
   :set nil
   :sequence nil
   :map nil
   :option nil
   :defined (b* ((typedef (get-type-definition type.name tops))
                 ((when (not typedef)) nil)
                 (definer (type-definition->body typedef))
                 ((when (not definer)) nil))
              (type-definer-case
               definer
               :product nil
               :sum definer.get
               :subset nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-definition-in-function-definitions
  ((name identifierp) (fundefs function-definition-listp))
  :returns (fundef? maybe-function-definitionp)
  :short "Find the definition of a function with a given name
          in a list of function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when looking up a function definition
     in a function recursion.")
   (xdoc::p
    "We return @('nil') if the function definition is not found.")
   (xdoc::p
    "We look up the definitions in order.
     In well-formed lists of function definitions,
     the function names are unique,
     so any order would yield the same result."))
  (b* (((when (endp fundefs)) nil)
       ((when (identifier-equiv name
                                (function-header->name
                                 (function-definition->header (car fundefs)))))
        (function-definition-fix (car fundefs))))
    (get-function-definition-in-function-definitions name (cdr fundefs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-definition ((name identifierp)
                                 (tops toplevel-listp))
  :returns (fundef? maybe-function-definitionp)
  :short "Find the definition of a function with a given name
          in a list of top-level constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look both at the function definitions at the top level
     and at the function definitions inside the function recursions.")
   (xdoc::p
    "We return @('nil') if the function definition is not found.")
   (xdoc::p
    "We look up the top-level constructs in order.
     In well-formed lists of top-level constructs,
     the defined function names are unique,
     so any order would yield the same result."))
  (b* (((when (endp tops)) nil)
       (top (car tops)))
    (toplevel-case
     top
     :type (get-function-definition name (cdr tops))
     :types (get-function-definition name (cdr tops))
     :function (if (identifier-equiv name
                                     (function-header->name
                                      (function-definition->header top.get)))
                   top.get
                 (get-function-definition name (cdr tops)))
     :functions (b* ((fundef? (get-function-definition-in-function-definitions
                               name
                               (function-recursion->definitions top.get))))
                  (or fundef?
                      (get-function-definition name (cdr tops))))
     :specification (get-function-definition name (cdr tops))
     :theorem (get-function-definition name (cdr tops))
     ;; Not sure about the transform case
     :transform (get-function-definition name (cdr tops))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-specification ((name identifierp)
                                    (tops toplevel-listp))
  :returns (funspec? maybe-function-specificationp)
  :short "Find the function specification with a given name
          in a list of top-level constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the specification is not found."))
  (b* (((when (endp tops)) nil)
       (top (car tops)))
    (toplevel-case
     top
     :type (get-function-specification name (cdr tops))
     :types (get-function-specification name (cdr tops))
     :function (get-function-specification name (cdr tops))
     :functions (get-function-specification name (cdr tops))
     :specification (if (identifier-equiv
                         name
                         (function-specification->name top.get))
                        top.get
                      (get-function-specification name
                                                  (cdr tops)))
     :theorem (get-function-specification name (cdr tops))
     :transform (get-function-specification name (cdr tops))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-theorem ((name identifierp) (tops toplevel-listp))
  :returns (thm? maybe-theoremp)
  :short "Find the theorem with a given name
          in a list of top-level constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the specification is not found."))
  (b* (((when (endp tops)) nil)
       (top (car tops)))
    (toplevel-case
     top
     :type (get-theorem name (cdr tops))
     :types (get-theorem name (cdr tops))
     :function (get-theorem name (cdr tops))
     :functions (get-theorem name (cdr tops))
     :specification (get-theorem name (cdr tops))
     :theorem (if (identifier-equiv name (theorem->name top.get))
                  top.get
                (get-theorem name (cdr tops)))
     :transform (get-theorem name (cdr tops))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-header-in-list ((name identifierp)
                                     (headers function-header-listp))
  :returns (funhead? maybe-function-headerp)
  :short "Find the function header with a given name
          in a list of function headers."
  (cond ((endp headers) nil)
        (t (if (identifier-equiv name (function-header->name (car headers)))
               (function-header-fix (car headers))
             (get-function-header-in-list name (cdr headers)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-field-type ((name identifierp) (fields field-listp))
  :returns (type? maybe-typep)
  :short "Find the type of the field with a specified name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the type of the first field found with the specified name.
     Well-formed lists of fields have unique names,
     so the first one found is also the only one (if present at all)."))
  (b* (((when (endp fields)) nil)
       (field (car fields))
       ((when (identifier-equiv name (field->name field))) (field->type field)))
    (get-field-type name (cdr fields)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-alternative-product ((name identifierp) (alts alternative-listp))
  :returns (product maybe-type-productp)
  :short "Find the type product of the alternative with a specified name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the type product of the first alternative found
     with the specified name.
     Well-formed lists of alternatives have unique names,
     so the first one found is also the only one (if present at all)."))
  (b* (((when (endp alts)) nil)
       (alt (car alts))
       ((when (identifier-equiv name (alternative->name alt)))
        (alternative->product alt)))
    (get-alternative-product name (cdr alts)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-to-typed-variable ((field fieldp))
  :returns (var typed-variablep)
  :short "Turn a field into a typed variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Sometimes fields are used as variables,
     in particular in invariants of product and sum types.
     Fields and typed variables are isomorphic.
     This function converts the former to the latter."))
  (make-typed-variable :name (field->name field)
                       :type (field->type field))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection field-list-to-typed-variable-list ((x field-listp))
  :result-type typed-variable-listp
  :short "Lift @(tsee field-to-typed-variable) to lists."
  (field-to-typed-variable x)
  ///
  (fty::deffixequiv field-list-to-typed-variable-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typed-variable-list->-expression-variable-list ((l typed-variable-listp))
  :returns (r expression-listp)
  (if (endp l)
      ()
    (cons (make-expression-variable :name (typed-variable->name (car l)))
          (typed-variable-list->-expression-variable-list (cdr l)))))

(define typed-variable-list->-expression ((l typed-variable-listp))
  :returns (r expressionp)
  (let ((exprs (typed-variable-list->-expression-variable-list l)))
    (if (equal (len exprs) 1)
        (car exprs)
      (make-expression-multi :arguments exprs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Avoid doing a (verbose) comprehensive expression recursion for now!
(define functions-called (expr)
  :returns (l string-listp)
  (if (atom expr)
      nil
    (let ((rec-fns (append (functions-called (car expr))
                           (functions-called (cdr expr)))))
      (if (and (expressionp expr)
               (equal (expression-kind expr) ':call))
          (cons (identifier->name (expression-call->function expr))
                rec-fns)
        rec-fns))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Avoid doing a (verbose) comprehensive expression recursion for now!
(define local-variables (expr)
  :returns (vars typed-variable-listp)
  (if (atom expr)
      nil
    (let ((rec-vars (append (local-variables (car expr))
                            (local-variables (cdr expr)))))
      (if (and (expressionp expr)
               (equal (expression-kind expr) ':bind))
          (append (expression-bind->variables expr)
                  rec-vars)
        rec-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-list-names ((ids identifier-listp))
  :returns (l string-listp)
  (if (endp ids)
      ()
    (cons (identifier->name (car ids))
          (identifier-list-names (cdr ids)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initializer-list-from-flds-vals ((field-ids identifier-listp) (new-args expression-listp))
  ;:guard (= (len field-ids) (len new-args))
  :returns (l initializer-listp)
  (if (or (endp field-ids)
          (endp new-args))
      nil
    (cons (make-initializer :field (car field-ids) :value (car new-args))
          (initializer-list-from-flds-vals (cdr field-ids) (cdr new-args)))))
