; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ r1cs-subset
  :parents (pfcs)
  :short "R1CS subset of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "PFCSes generalize R1CSes;
     a subset of PFCSes corresponds to R1CSes.
     Here we characterize that subset.")
   (xdoc::p
    "We provide two related characterizations.
     One is that of a PFCS that is an R1CS,
     i.e. it has no definitions and all the constraints are in R1CS form.
     Another is that of a PFCS that has definitions,
     but all its equality constraints are in R1CS form,
     and all its relation applications have constants or variables as arguments.
     The latter kind of PFCS can be regarded as a structured R1CS:
     the constraints are all in R1CS form in the end,
     but they may be organized hierarchically, via defined relations.
     We use the prefix @('sr1cs') for predicates
     that define these structured R1CSes.")
   (xdoc::p
    "Our characterization of
     R1CS monomials, polynomials, and equality constraints
     is a natural one, but not necessarily the only one possible.
     In particular, PFCS expressions are trees,
     and there are many tree shapes that represent linear polynomials,
     besides the left-associated ones that we use here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-monomialp ((expr expressionp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS expression is an R1CS monomial."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an addend of an R1CS polynomial (i.e. linear combination).
     It is either a constant
     or a variable
     or a product of a constant (natural number) by a variable,
     or a product of a negated constant (negative number) by a variable.")
   (xdoc::p
    "Although it could be supported, for simplicity we disallow a product of 
     a constant (natural number) by a negated variable."))
  (or (expression-case expr :const)
      (expression-case expr :var)
      (and (expression-case expr :mul)
           (or (expression-case (expression-mul->arg1 expr) :const)
               (and (expression-case (expression-mul->arg1 expr) :neg)
                    (expression-case (expression-neg->arg
                                      (expression-mul->arg1 expr)) :const)))
           (expression-case (expression-mul->arg2 expr) :var)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-polynomialp ((expr expressionp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS expression is an R1CS polynomial."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a linear combination, i.e. a sum of one or more monomials.")
   (xdoc::p
    "We allow both binary addition and subtraction,
     We pick left-associated additions/subtractions as linear polynomials;
     the base case is that of a single monomial."))
  (or (r1cs-monomialp expr)
      (and (expression-case expr :add)
           (r1cs-polynomialp (expression-add->arg1 expr))
           (r1cs-monomialp (expression-add->arg2 expr)))
      (and (expression-case expr :sub)
           (r1cs-polynomialp (expression-sub->arg1 expr))
           (r1cs-monomialp (expression-sub->arg2 expr))))
  :measure (expression-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-constraintp ((constr constraintp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS constraint is an R1CS constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must be an equality constraint,
     whose left side is the product of two R1CS polynomials
     and whose right side is an R1CS polynomial."))
  (and (constraint-case constr :equal)
       (b* ((left (constraint-equal->left constr))
            (right (constraint-equal->right constr)))
         (and (expression-case left :mul)
              (r1cs-polynomialp (expression-mul->arg1 left))
              (r1cs-polynomialp (expression-mul->arg2 left))
              (r1cs-polynomialp right))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist r1cs-constraint-listp (x)
  :guard (constraint-listp x)
  :short "Check if a list of PFCS constraints
          consists of R1CS constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee r1cs-constraintp) to lists."))
  (r1cs-constraintp x)
  ///
  (fty::deffixequiv r1cs-constraint-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-systemp ((sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS is an R1CS."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be no definitions,
     and all the constraints must be in R1CS form."))
  (and (endp (system->definitions sys))
       (r1cs-constraint-listp (system->constraints sys)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sr1cs-constraintp ((constr constraintp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS constraint is a structured R1CS constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the constraint is an equality, it must be in R1CS form.
     If the constraint is a relation application,
     the arguments must be constants or variables:
     this way, the constraints resulting from the body of the relation,
     instantiated from the arguments,
     are in R1CS form if the ones in the body of the relation are."))
  (constraint-case
   constr
   :equal (r1cs-constraintp constr)
   :relation (expression-const/var-listp constr.args))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist sr1cs-constraint-listp (x)
  :guard (constraint-listp x)
  :short "Check if a list of PFCS constraints
          consists of structured R1CS constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sr1cs-constraintp) to lists."))
  (sr1cs-constraintp x)
  ///
  (fty::deffixequiv sr1cs-constraint-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sr1cs-definitionp ((def definitionp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS definition
          consists of strcutred R1CS constraints."
  (sr1cs-constraint-listp (definition->body def))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist sr1cs-definition-listp (x)
  :guard (definition-listp x)
  :short "Check if a list of PFCS definitions
          consist of structured R1CS constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sr1cs-definitionp) to lists."))
  (sr1cs-definitionp x)
  ///
  (fty::deffixequiv sr1cs-definition-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sr1cs-systemp ((sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a PFCS system consits of structured R1CS constraints."
  (b* (((system sys) sys))
    (and (sr1cs-definition-listp sys.definitions)
         (sr1cs-constraint-listp sys.constraints)))
  :hooks (:fix))
