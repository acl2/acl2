; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-trees
  :parents (abstract-syntax)
  :short "Abstract syntax trees of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Expressions are built out of
     constants, variables, and field operations.
     A basic constraint is an equality between expressions.
     Constraints may be (conjunctively) grouped into named relations
     (see @(tsee definition)),
     which may be conjoined with equality constraints.
     A system of constraints is a collection of named relations,
     which are hierarchically organized,
     and of constraints that may reference the relations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod name
  :short "Fixtype of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "Names are used for variables and relations.")
   (xdoc::p
    "For now we define names as wrappers of (any) strings,
     but in the future we may add more structure."))
  ((string string))
  :pred namep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist name-list
  :short "Fixtype of lists of names."
  :elt-type name
  :true-listp t
  :elementp-of-nil nil
  :pred name-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset name-set
  :short "Fixtype of sets of names."
  :elt-type name
  :elementp-of-nil nil
  :pred name-setp

  ///

  (defrule name-setp-of-mergesort-of-name-list
    (implies (name-listp x)
             (name-setp (set::mergesort x)))
    :induct t
    :enable set::mergesort))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult name-result
  :short "Fixtype of errors and names."
  :ok name
  :pred name-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult name-list-result
  :short "Fixtype of errors and lists of names."
  :ok name-list
  :pred name-list-resultp)

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
    "Two field operations, addition and multiplication,
     suffice for arithmetic circuits.
     We also add negation (unary), and subtraction (binary)
     for convenience.
     We may add other operations in the future,
     most notably reciprocal, and therefore division.
     We may also add square roots,
     and even support user defined functions.
     Some of these operations will introduce the issue of well-definedness,
     e.g. non-zero divisors."))
  (:const ((value int)))
  (:var ((name name)))
  (:neg ((arg expression)))
  (:add ((arg1 expression) (arg2 expression)))
  (:sub ((arg1 expression) (arg2 expression)))
  (:mul ((arg1 expression) (arg2 expression)))
  :pred expressionp
  :prepwork ((local (in-theory (enable ifix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expression-result
  :short "Fixtype of errors and PFCS expressions."
  :ok expression
  :pred expression-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist expression-list
  :short "Fixtype of lists of expressions."
  :elt-type expression
  :true-listp t
  :elementp-of-nil nil
  :pred expression-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expression-list-result
  :short "Fixtype of errors and lists of PFCS expressions."
  :ok expression-list
  :pred expression-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum constraint
  :short "Fixtype of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "A constraint is either an equality of expressions,
     or the application of a named relation to argument expressions.")
   (xdoc::p
    "In the future, this may be extended with propositional connectives
     to combine equalities and applications of named relations."))
  (:equal ((left expression)
           (right expression)))
  (:relation ((name name)
              (args expression-list)))
  :pred constraintp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult constraint-result
  :short "Fixtype of errors and PFCS constraints."
  :ok constraint
  :pred constraint-resultp
  :prepwork ((local (in-theory (enable constraint-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist constraint-list
  :short "Fixtype of lists of constraints."
  :elt-type constraint
  :true-listp t
  :elementp-of-nil nil
  :pred constraint-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult constraint-list-result
  :short "Fixtype of errors and lists of PFCS constraints."
  :ok constraint-list
  :pred constraint-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod definition
  :short "Fixtype of definitions of relations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A relation definition consists of
     the name of the relation,
     a list of formal parameters (any names),
     and a body consisting of a list of constraints.
     The constraints are taken conjunctively;
     but see the discussion in @(tsee constraint)
     about possible extensions to allow explicit propositional connectives
     (in which case the body of a definition
     would presumably be just a single constraint,
     which may be a conjunction)."))
  ((name name)
   (para name-list)
   (body constraint-list))
  :tag :definition
  :pred definitionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult definition-result
  :short "Fixtype of errors and PFCS definitions."
  :ok definition
  :pred definition-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption definition-option
  definition
  :short "Fixtype of optional definitions of relations."
  :pred definition-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist definition-list
  :short "Fixtype of lists of definitions of relations."
  :elt-type definition
  :true-listp t
  :elementp-of-nil nil
  :pred definition-listp
  :prepwork ((local (in-theory (enable nfix))))
  ///

  (defruled rev-of-definition-list-fix
    (equal (rev (definition-list-fix defs))
           (definition-list-fix (rev defs)))
    :enable definition-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult definition-list-result
  :short "Fixtype of errors and lists of PFCS definitions."
  :ok definition-list
  :pred definition-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod system
  :short "Fixtype of systems of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "A system consists of a list of definitions and a list of constraints."))
  ((definitions definition-list)
   (constraints constraint-list))
  :tag :system ; added to get the defresult to certify
  :pred systemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult system-result
  :short "Fixtype of errors and PFCS systems."
  :ok system
  :pred system-resultp)
