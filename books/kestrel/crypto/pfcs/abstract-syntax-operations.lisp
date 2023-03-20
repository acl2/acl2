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

(include-book "kestrel/fty/symbol-set" :dir :system)
(include-book "std/util/deflist" :dir :system)

(set-induction-depth-limit 0)

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
  :returns (vars symbol-setp)
  :short "Set of variables in an expression."
  (expression-case
   expr
   :const nil
   :var (set::insert expr.name nil)
   :add (set::union (expression-vars expr.arg1)
                    (expression-vars expr.arg2))
   :mul (set::union (expression-vars expr.arg1)
                    (expression-vars expr.arg2)))
  :measure (expression-count expr)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expression-list-vars ((exprs expression-listp))
  :returns (vars symbol-setp)
  :short "Set of variables in a list of expressions."
  (cond ((endp exprs) nil)
        (t (set::union (expression-vars (car exprs))
                       (expression-list-vars (cdr exprs)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-vars ((constr constraintp))
  :returns (vars symbol-setp)
  :short "Set of variables in a constraint."
  (constraint-case
   constr
   :equal (set::union (expression-vars constr.left)
                      (expression-vars constr.right))
   :relation (expression-list-vars constr.args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-list-vars ((constrs constraint-listp))
  :returns (vars symbol-setp)
  :short "Set of variables in a list of constraints."
  (cond ((endp constrs) nil)
        (t (set::union (constraint-vars (car constrs))
                       (constraint-list-vars (cdr constrs)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-free-vars ((def definitionp))
  :returns (vars symbol-setp)
  :short "Set of free variables in a definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the variables in the body minus the parameters."))
  (set::difference (constraint-list-vars (definition->body def))
                   (set::mergesort (definition->para def))))

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
