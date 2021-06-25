; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (prime-field-constraint-systems)
  :short "Abstract syntax of PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "Expressions are built out of
     constants, variables, and field operations.
     A constraint is an equality between expressions.
     Constraints may be (conjunctively) grouped into named relations
     (see @(tsee definition)),
     which may be conjoined with equality constraints.
     A system of constraints is a collection of named relations,
     which are hierarchically organized."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum expression
  :short "Fixtype of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use any integers as constants.
     This way, the definition of expression
     (and of the other syntactic entities)
     does not depend on (the prime number that defines) the prime field.
     Semantically, integers are treated modulo the prime.")
   (xdoc::p
    "We use (any) symbols for variables.")
   (xdoc::p
    "We include just two field operations for now: addition and multiplication.
     These suffice for arithmetic circuits.
     Negation, and therefore subtraction, are easily represented,
     via multiplication by negative one
     (see @(tsee expression-neg) and @(tsee expression-sub)).
     We may add other operations in the future,
     most notably reciprocal, and therefore division.
     We may also add square roots,
     and even support user defined functions.
     Some of these operations will introduce the issue of well-definedness,
     e.g. non-zero divisors."))
  (:const ((value int)))
  (:var ((name symbol)))
  (:add ((arg1 expression) (arg2 expression)))
  (:mul ((arg1 expression) (arg2 expression)))
  :pred expressionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist expression-list
  :short "Fixtype of lists of expressions."
  :elt-type expression
  :true-listp t
  :elementp-of-nil nil
  :pred expression-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum constraint
  :short "Fixtype of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "A constraint is either an equality of expressions,
     or the application of a named relation to argument expressions.
     We use (any) symbols for relation names.")
   (xdoc::p
    "In the future, this may be extended with propositional connectives
     to combine equalities and applications of named relations."))
  (:equal ((left expression)
           (right expression)))
  (:relation ((name symbol)
              (args expression-list)))
  :pred constraintp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist constraint-list
  :short "Fixtype of lists of constraints."
  :elt-type constraint
  :true-listp t
  :elementp-of-nil nil
  :pred constraint-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod definition
  :short "Fixtype of definitions of relations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A relation definition consists of
     the name of the relation (any symbol),
     a list of formal parameters (any symbols),
     and a body consisting of a list of constraints.
     The constraints are taken conjunctively;
     but see the discussion in @(tsee constraint)
     about possible extensions to allow explicit propositional connectives
     (in which case the body of a definition
     would presumably be just a single constraint,
     which may be a conjunction)."))
  ((name symbol)
   (para symbol-list)
   (body constraint-list))
  :tag :definition
  :pred definitionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist system
  :short "Fixtype of systems of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "A system consists of a list of definitions.")
   (xdoc::p
    "For now we define it as a plain list,
     but in the future we may use a product fixtype
     that includes the list of definitions as well as some other information."))
  :elt-type definition
  :true-listp t
  :elementp-of-nil nil
  :pred systemp)
