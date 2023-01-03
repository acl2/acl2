; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ r1cs-subset
  :parents (prime-field-constraint-systems)
  :short "R1CS subset of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "PFCSes generalize R1CSes;
     a subset of PFCSes corresponds to R1CSes.
     Here we characterize that subset.")
   (xdoc::p
    "This is not the only possible characterization,
     but it is the one we use for now."))
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
     or a product of a constant by a variable."))
  (or (expression-case expr :const)
      (expression-case expr :var)
      (and (expression-case expr :mul)
           (expression-case (expression-mul->arg1 expr) :const)
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
    "Currently the PFCS abstract syntax only has binary addition.
     We pick left-associated additions as linear polynomials;
     the base case is that of a single monomial."))
  (or (r1cs-monomialp expr)
      (and (expression-case expr :add)
           (r1cs-polynomialp (expression-add->arg1 expr))
           (r1cs-monomialp (expression-add->arg2 expr))))
  :measure (expression-count expr)
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
  (r1cs-constraintp x))
