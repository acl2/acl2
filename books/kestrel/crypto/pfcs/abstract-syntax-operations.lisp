; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-operations
  :parents (abstract-syntax prime-field-constraint-systems)
  :short "Operations on the abstract syntax of PFCS."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-vars ((expr expressionp))
  :returns (vars symbol-listp)
  :short "Variables in an expression."
  (expression-case
   expr
   :const nil
   :var (list expr.name)
   :add (union-eq (expression-vars expr.arg1)
                  (expression-vars expr.arg2))
   :mul (union-eq (expression-vars expr.arg1)
                  (expression-vars expr.arg2)))
  :measure (expression-count expr)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-list-vars ((exprs expression-listp))
  :returns (vars symbol-listp)
  :short "Variables in a list of expressions."
  (cond ((endp exprs) nil)
        (t (union-eq (expression-vars (car exprs))
                     (expression-list-vars (cdr exprs)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-vars ((constr constraintp))
  :returns (vars symbol-listp)
  :short "Variables in a constraint."
  (constraint-case
   constr
   :equal (union-eq (expression-vars constr.left)
                    (expression-vars constr.right))
   :relation (expression-list-vars constr.args))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-list-vars ((constrs constraint-listp))
  :returns (vars symbol-listp)
  :short "Variables in a list of constraints."
  (cond ((endp constrs) nil)
        (t (union-eq (constraint-vars (car constrs))
                     (constraint-list-vars (cdr constrs)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-free-vars ((def definitionp))
  :returns (vars symbol-listp)
  :short "Free variables in a definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the variables in the body minus the parameters."))
  (set-difference-eq (constraint-list-vars (definition->body def))
                     (definition->para def)))

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

(define lookup-definition ((name symbolp) (sys systemp))
  :returns (def? definition-optionp)
  :short "Look up a definition in a system of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the system has a definition for the given name,
     return that definition.
     Otherwise return @('nil').")
   (xdoc::p
    "We return the first definition found for that name.
     In a well-formed system of constraints,
     there is at most a definition for each name,
     and thus returning the first one found is also the only one."))
  (b* (((when (endp sys)) nil)
       (def (car sys))
       ((when (eq (definition->name def)
                  (symbol-fix name)))
        (definition-fix def)))
    (lookup-definition name (cdr sys)))
  :hooks (:fix))
