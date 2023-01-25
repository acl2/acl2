; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")

(include-book "std/util/deflist" :dir :system)

(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-operations
  :parents (abstract-syntax prime-field-constraint-systems)
  :short "Operations on the abstract syntax of PFCSes."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expression-var-list (x)
  :guard (symbol-listp x)
  :returns (exprs expression-listp)
  :short "Lift @(tsee expression-var) to lists."
  (expression-var x)
  ///
  (fty::deffixequiv expression-var-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expression-var-listp (x)
  :guard (expression-listp x)
  :short "Check if all the expressions in a list are variables."
  (expression-case x :var)
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expression-const/var-listp (x)
  :guard (expression-listp x)
  :short "Check if all the expressions in a list are constants or variables."
  (or (expression-case x :const)
      (expression-case x :var))
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-vars ((expr expressionp))
  :returns (vars symbol-listp)
  :short "Variables in an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are returned as a list without repetitions."))
  (expression-case
   expr
   :const nil
   :var (list expr.name)
   :add (union-eq (expression-vars expr.arg1)
                  (expression-vars expr.arg2))
   :mul (union-eq (expression-vars expr.arg1)
                  (expression-vars expr.arg2)))
  :measure (expression-count expr)
  :verify-guards :after-returns
  ///

  (defrule no-duplicatesp-equal-of-expression-vars
    (no-duplicatesp-equal (expression-vars expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-list-vars ((exprs expression-listp))
  :returns (vars symbol-listp)
  :short "Variables in a list of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are returned as a list without repetitions."))
  (cond ((endp exprs) nil)
        (t (union-eq (expression-vars (car exprs))
                     (expression-list-vars (cdr exprs)))))
  :verify-guards :after-returns
  ///

  (defrule no-duplicatesp-equal-of-expression-list-vars
    (no-duplicatesp-equal (expression-list-vars exprs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-vars ((constr constraintp))
  :returns (vars symbol-listp)
  :short "Variables in a constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are returned as a list without repetitions."))
  (constraint-case
   constr
   :equal (union-eq (expression-vars constr.left)
                    (expression-vars constr.right))
   :relation (expression-list-vars constr.args))
  :verify-guards :after-returns
  ///

  (defrule no-duplicatesp-equal-of-constraint-vars
    (no-duplicatesp-equal (constraint-vars expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-list-vars ((constrs constraint-listp))
  :returns (vars symbol-listp)
  :short "Variables in a list of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are returned as a list without repetitions."))
  (cond ((endp constrs) nil)
        (t (union-eq (constraint-vars (car constrs))
                     (constraint-list-vars (cdr constrs)))))
  :verify-guards :after-returns
  ///

  (defrule no-duplicatesp-equal-of-constraint-list-vars
    (no-duplicatesp-equal (constraint-list-vars expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-free-vars ((def definitionp))
  :returns (vars symbol-listp)
  :short "Free variables in a definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the variables in the body minus the parameters.")
   (xdoc::p
    "The variables are returned as a list without repetitions."))
  (set-difference-eq (constraint-list-vars (definition->body def))
                     (definition->para def))
  ///

  (defrule no-duplicatesp-equal-of-definition-free-vars
    (no-duplicatesp-equal (definition-free-vars expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-neg ((expr expressionp))
  :returns (neg-expr expressionp)
  :short "Abbreviation to construct a negation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may be added to the abstract syntax at some point.
     For now it is just an ephemeral abbreviation."))
  (expression-mul (expression-const -1) expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-sub ((expr1 expressionp) (expr2 expressionp))
  :returns (sub-expr expressionp)
  :short "Abbreviation to construct a subtraction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may be added to the abstract syntax at some point.
     For now it is just an ephemeral abbreviation."))
  (expression-add expr1
                  (expression-neg expr2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup-definition ((name symbolp) (defs definition-listp))
  :returns (def? definition-optionp)
  :short "Look up a definition in a list of definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the list has a definition for the given name,
     return that definition.
     Otherwise return @('nil').")
   (xdoc::p
    "We return the first definition found for that name.
     In a well-formed lists of definitions,
     there is at most a definition for each name,
     and thus the first one found (if any) is also the only one."))
  (b* (((when (endp defs)) nil)
       (def (car defs))
       ((when (eq (definition->name def)
                  (symbol-fix name)))
        (definition-fix def)))
    (lookup-definition name (cdr defs)))
  :hooks (:fix))
