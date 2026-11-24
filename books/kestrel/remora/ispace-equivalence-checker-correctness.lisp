; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-checker")
(include-book "ispace-equivalence-rewriting")
(include-book "dimension-polynomials-properties")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/omaps/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We use the rule sets for rewriting modulo ispace equivalence throughout,
; and we keep ground calls of the AST constructors unevaluated,
; so that the rewrite rules apply to them.

(local (in-theory (enable* dim-eq-equiv-rules
                           shape-eq-equiv-rules)))

(local (in-theory (disable (:e dim-const)
                           (:e dim-add)
                           (:e dim-mul)
                           (:e dim-sub)
                           (:e shape-dims)
                           (:e shape-append)
                           (:e shape-splice))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-checker-correctness
  :parents (validator-correctness)
  :short "Correctness of the ispace equivalence checker
          with respect to ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that the "
    (xdoc::seetopic "ispace-equivalence-checker" "ispace equivalence checker")
    " is sound and complete with respect to
     the inference rules in @(see ispace-equivalence):
     the checker succeeds exactly on the equivalent
     dimensions, shapes, and ispaces.")
   (xdoc::p
    "The checker compares normal forms.
     Soundness follows from the fact that
     every dimension, shape, and ispace is equivalent to its normal form:
     if two of them have the same normal form,
     they are equivalent by symmetry and transitivity.
     Completeness is the fact that
     equivalent dimensions, shapes, and ispaces have the same normal form,
     which is proved by induction on proof trees:
     the conclusion of each inference rule
     relates two dimensions, shapes, or ispaces with the same normal form,
     if its premises do.")
   (xdoc::p
    "The normal form of a dimension is calculated via
     the polynomial that the dimension denotes
     (see @(see dimension-polynomials)).
     Completeness for dimensions amounts to the fact that
     the inference rules preserve the polynomials,
     which follows from the fact that the polynomials form
     a commutative ring with identity
     (see @(see dimension-polynomials-properties)).
     For soundness, we introduce
     a simpler translation of polynomials back to dimensions,
     we prove that the operations on polynomials
     correspond to the operations on dimensions modulo equivalence,
     and we prove that the simpler translation
     is equivalent to the one used by the checker.")
   (xdoc::p
    "The normal form of a shape or ispace is calculated in three passes.
     We prove theorems that characterize
     the normal form of each kind of shape and ispace
     in terms of the normal forms of its components,
     without reference to the three passes.
     Soundness and completeness are both proved from these theorems.")
   (xdoc::p
    "The proofs that involve equivalences make use of the ACL2
     equivalence relations,
     congruence rules,
     and rewrite rules
     in @(see ispace-equivalence-rewriting).
     A recurring idiom in these proofs is to instantiate,
     via a @(':use') hint,
     a rewrite rule that is disabled,
     and to let the enabled rewrite rules
     simplify the two sides of the instance,
     so that it becomes the theorem to prove:
     this is used when a rule must be applied from right to left,
     or to subterms that do not occur in the theorem."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coeff-to-plain-dim ((coeff integerp))
  :returns (dim dimp)
  :short "Turn an integer coefficient into a dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "A non-negative coefficient is turned into a constant dimension.
     A negative coefficient is turned into
     the unary subtraction of the constant dimension of its absolute value.")
   (xdoc::p
    "This maps the integers to dimensions homomorphically,
     modulo dimension equivalence:
     see @(see coeff-to-plain-dim-arithmetic)."))
  (b* ((coeff (lifix coeff)))
    (if (>= coeff 0)
        (dim-const coeff)
      (dim- (dim-const (- coeff))))))

;;;;;;;;;;;;;;;;;;;;

(define term-to-plain-dim ((mono dim-listp) (coeff integerp))
  :returns (dim dimp)
  :short "Turn a term of a polynomial into a dimension in plain form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the binary multiplication of
     the dimension for the coefficient
     and the multiplication of the factors of the monomial."))
  (dim* (coeff-to-plain-dim coeff) (dim-mul mono)))

;;;;;;;;;;;;;;;;;;;;

(define poly-to-plain-dim ((poly dim-polyp))
  :returns (dim dimp)
  :short "Turn a polynomial into a dimension in plain form."
  :long
  (xdoc::topstring
   (xdoc::p
    "The zero polynomial is turned into the constant dimension 0.
     Any other polynomial is turned into the binary addition of
     the dimension for its first term
     and the dimension for the rest of the polynomial.")
   (xdoc::p
    "Unlike @(tsee poly-to-dim), which is used by the checker,
     this function does not treat specially
     the unit coefficients, the terms without factors,
     the terms with negative coefficients,
     or the polynomials with a single term.
     Thus, the result is not as readable,
     but it is easier to relate to the operations on polynomials:
     see @(see poly-to-plain-dim-of-operations).
     The two functions return equivalent dimensions:
     see @(see poly-to-dim-and-poly-to-plain-dim)."))
  (b* (((when (omap::emptyp (dim-poly-fix poly))) (dim-const 0))
       ((mv mono coeff) (omap::head poly)))
    (dim+ (term-to-plain-dim mono coeff)
          (poly-to-plain-dim (omap::tail poly))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(std::defprojection poly-list-to-plain-dim-list ((x dim-poly-listp))
  :returns (dims dim-listp)
  :short "Lift @(tsee poly-to-plain-dim) to lists."
  (poly-to-plain-dim x))

;;;;;;;;;;;;;;;;;;;;

; We keep ground calls of these functions unevaluated,
; for the same reason as the ground calls of the AST constructors.

(local (in-theory (disable (:e coeff-to-plain-dim)
                           (:e term-to-plain-dim)
                           (:e poly-to-plain-dim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection coeff-to-plain-dim-arithmetic
  :short "Arithmetic of the dimensions for integer coefficients."
  :long
  (xdoc::topstring
   (xdoc::p
    "The mapping @(tsee coeff-to-plain-dim) is a homomorphism,
     modulo dimension equivalence,
     with respect to addition, negation, and multiplication.
     Since dimension constants are natural numbers,
     and negative integers are mapped to negated constants,
     this is proved by cases on the signs of the integers.")
   (xdoc::p
    "For addition, we first prove theorems about
     the addition of two negated constants,
     and the addition of a constant and a negated constant
     where the larger one is expressed as a sum;
     the second kind of theorems applies to
     an addition of two integers of opposite signs
     by expressing the one with the larger absolute value
     as the sum of the result and of the other one.
     These theorems are proved from
     the inference rule that adds two constants,
     together with the properties of the additive inverse."))

  (defruled coeff-to-plain-dim-of-0
    (equal (coeff-to-plain-dim 0)
           (dim-const 0))
    :enable coeff-to-plain-dim)

  (defruled coeff-to-plain-dim-of-1
    (equal (coeff-to-plain-dim 1)
           (dim-const 1))
    :enable coeff-to-plain-dim)

  (defruled coeff-to-plain-dim-when-natp
    (implies (natp coeff)
             (equal (coeff-to-plain-dim coeff)
                    (dim-const coeff)))
    :enable (coeff-to-plain-dim
             natp))

  (defruled dim-eq-equiv-add-of-neg-const-and-neg-const
    (dim-eq-equiv (dim+ (dim- (dim-const n1)) (dim- (dim-const n2)))
                  (dim- (dim-const (+ (nfix n1) (nfix n2)))))
    :disable dim-eq-equiv-neg-add
    :use (:instance dim-eq-equiv-neg-add
                    (dim1 (dim-const n1))
                    (dim2 (dim-const n2))))

  (defruled dim-eq-equiv-add-of-greater-const-and-neg-const
    (implies (and (natp m)
                  (natp n))
             (dim-eq-equiv (dim+ (dim-const (+ m n)) (dim- (dim-const n)))
                           (dim-const m)))
    :enable (nfix
             natp)
    :disable dim-eq-equiv-add-assoc
    :use (:instance dim-eq-equiv-add-assoc
                    (dim1 (dim-const m))
                    (dim2 (dim-const n))
                    (dim3 (dim- (dim-const n)))))

  (defruled dim-eq-equiv-add-of-const-and-neg-greater-const
    (implies (and (natp m)
                  (natp n))
             (dim-eq-equiv (dim+ (dim-const m) (dim- (dim-const (+ m n))))
                           (dim- (dim-const n))))
    :enable (dim-eq-equiv-add-of-neg-const-and-neg-const
             nfix
             natp)
    :disable dim-eq-equiv-add-inv-2
    :use (:instance dim-eq-equiv-add-inv-2
                    (dim1 (dim-const m))
                    (dim2 (dim- (dim-const n)))))

  (defruled dim-eq-equiv-add-of-coeff-to-plain-dim-and-coeff-to-plain-dim
    (dim-eq-equiv (dim+ (coeff-to-plain-dim coeff1)
                        (coeff-to-plain-dim coeff2))
                  (coeff-to-plain-dim (+ (ifix coeff1) (ifix coeff2))))
    :use (:instance lemma (coeff1 (ifix coeff1)) (coeff2 (ifix coeff2)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (integerp coeff1)
                     (integerp coeff2))
                (dim-eq-equiv (dim+ (coeff-to-plain-dim coeff1)
                                    (coeff-to-plain-dim coeff2))
                              (coeff-to-plain-dim (+ coeff1 coeff2))))
       :enable (coeff-to-plain-dim
                nfix
                natp
                dim-eq-equiv-add-of-neg-const-and-neg-const)
       :use ((:instance dim-eq-equiv-add-of-greater-const-and-neg-const
                        (m (+ coeff1 coeff2))
                        (n (- coeff2)))
             (:instance dim-eq-equiv-add-of-const-and-neg-greater-const
                        (m coeff1)
                        (n (- (+ coeff1 coeff2))))
             (:instance dim-eq-equiv-add-of-greater-const-and-neg-const
                        (m (+ coeff1 coeff2))
                        (n (- coeff1)))
             (:instance dim-eq-equiv-add-of-const-and-neg-greater-const
                        (m coeff2)
                        (n (- (+ coeff1 coeff2))))))))

  (defruled dim-eq-equiv-neg-of-coeff-to-plain-dim
    (dim-eq-equiv (dim- (coeff-to-plain-dim coeff))
                  (coeff-to-plain-dim (- (ifix coeff))))
    :enable (coeff-to-plain-dim
             ifix))

  (defruled dim-eq-equiv-mul-of-coeff-to-plain-dim-and-coeff-to-plain-dim
    (dim-eq-equiv (dim* (coeff-to-plain-dim coeff1)
                        (coeff-to-plain-dim coeff2))
                  (coeff-to-plain-dim (* (ifix coeff1) (ifix coeff2))))
    :use (:instance lemma (coeff1 (ifix coeff1)) (coeff2 (ifix coeff2)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (integerp coeff1)
                     (integerp coeff2))
                (dim-eq-equiv (dim* (coeff-to-plain-dim coeff1)
                                    (coeff-to-plain-dim coeff2))
                              (coeff-to-plain-dim (* coeff1 coeff2))))
       :enable (coeff-to-plain-dim
                nfix)))))

;;;;;;;;;;;;;;;;;;;;

(defsection term-to-plain-dim-arithmetic
  :short "Arithmetic of the dimensions for terms of polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The multiplication of the factors of a monomial
     is equivalent to the multiplication of the same factors
     in a different order.
     Thus, sorting the factors yields an equivalent multiplication,
     and the multiplication of the factors of two monomials
     is equivalent to
     the multiplication of the factors of the product of the monomials.")
   (xdoc::p
    "From that, and from the arithmetic of coefficients
     (see @(see coeff-to-plain-dim-arithmetic)),
     we prove that the dimensions for terms
     are added, when the terms have the same monomial,
     negated, and multiplied
     in the way that the terms are, modulo dimension equivalence.
     We also prove that a term with zero coefficient
     is equivalent to 0."))

  (defruled dim-eq-equiv-dim-mul-of-sort-dims-aux
    (dim-eq-equiv (dim-mul (sort-dims-aux dim dims))
                  (dim-mul (cons dim dims)))
    :use (:instance lemma (dims (dim-list-fix dims)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp dims)
                (dim-eq-equiv (dim-mul (sort-dims-aux dim dims))
                              (dim-mul (cons dim dims))))
       :induct t
       :enable (sort-dims-aux
                dim-eq-equiv-mul-cons))))

  (defruled dim-eq-equiv-dim-mul-of-sort-dims
    (dim-eq-equiv (dim-mul (sort-dims dims))
                  (dim-mul dims))
    :use (:instance lemma (dims (dim-list-fix dims)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp dims)
                (dim-eq-equiv (dim-mul (sort-dims dims))
                              (dim-mul dims)))
       :induct t
       :enable (sort-dims
                dim-eq-equiv-dim-mul-of-sort-dims-aux
                dim-eq-equiv-mul-cons))))

  (defruled dim-eq-equiv-mul-of-dim-mul-and-dim-mul
    (dim-eq-equiv (dim* (dim-mul mono1) (dim-mul mono2))
                  (dim-mul (dim-mono-mul mono1 mono2)))
    :enable (dim-mono-mul
             dim-eq-equiv-dim-mul-of-sort-dims
             dim-eq-equiv-mul-of-append))

  (defruled dim-eq-equiv-add-of-term-to-plain-dim-and-term-to-plain-dim
    (dim-eq-equiv (dim+ (term-to-plain-dim mono coeff1)
                        (term-to-plain-dim mono coeff2))
                  (term-to-plain-dim mono (+ (ifix coeff1) (ifix coeff2))))
    :enable (term-to-plain-dim
             dim-eq-equiv-add-of-coeff-to-plain-dim-and-coeff-to-plain-dim)
    :disable dim-eq-equiv-distrib-right
    :use (:instance dim-eq-equiv-distrib-right
                    (dim1 (coeff-to-plain-dim coeff1))
                    (dim2 (coeff-to-plain-dim coeff2))
                    (dim (dim-mul mono))))

  (defruled dim-eq-equiv-term-to-plain-dim-of-0
    (dim-eq-equiv (term-to-plain-dim mono 0)
                  (dim-const 0))
    :enable (term-to-plain-dim
             coeff-to-plain-dim-of-0))

  (defruled dim-eq-equiv-neg-of-term-to-plain-dim
    (dim-eq-equiv (dim- (term-to-plain-dim mono coeff))
                  (term-to-plain-dim mono (- (ifix coeff))))
    :enable (term-to-plain-dim
             dim-eq-equiv-neg-of-coeff-to-plain-dim)
    :disable dim-eq-equiv-neg-mul-left
    :use (:instance dim-eq-equiv-neg-mul-left
                    (dim1 (coeff-to-plain-dim coeff))
                    (dim2 (dim-mul mono))))

  (defruled dim-eq-equiv-mul-of-term-to-plain-dim-and-term-to-plain-dim
    (dim-eq-equiv (dim* (term-to-plain-dim mono1 coeff1)
                        (term-to-plain-dim mono2 coeff2))
                  (term-to-plain-dim (dim-mono-mul mono1 mono2)
                                     (* (ifix coeff1) (ifix coeff2))))
    :enable (term-to-plain-dim
             dim-eq-equiv-mul-of-coeff-to-plain-dim-and-coeff-to-plain-dim
             dim-eq-equiv-mul-of-dim-mul-and-dim-mul)
    :disable (dim-eq-equiv-mul-assoc
              dim-eq-equiv-mul-comm
              dim-eq-equiv-mul-comm-2)
    :use (:instance dim-eq-equiv-mul-interchange
                    (dim1 (coeff-to-plain-dim coeff1))
                    (dim2 (dim-mul mono1))
                    (dim3 (coeff-to-plain-dim coeff2))
                    (dim4 (dim-mul mono2)))))

;;;;;;;;;;;;;;;;;;;;

(defsection poly-to-plain-dim-of-operations
  :short "Plain dimensions of the results of the operations on polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operations on polynomials correspond to
     the operations on dimensions, modulo dimension equivalence:
     the plain dimension of the result of an operation on polynomials
     is equivalent to the result of the corresponding operation
     on the plain dimensions of the polynomials.")
   (xdoc::p
    "The key property is that
     the plain dimension of the addition of a term to a polynomial
     is equivalent to the addition of
     the plain dimension of the term and
     the plain dimension of the polynomial.
     Its proof has the same structure as the proof of
     how multiplication by a term treats the addition of a term
     (see @(see dim-poly-mul-term-properties)):
     we consider the update of an omap with a new key,
     the deletion of a key from an omap,
     and then an arbitrary update of an omap,
     from which the property follows.")
   (xdoc::p
    "The properties of the other operations
     follow from that one and from each other,
     by induction on the operations."))

  (defruled poly-to-plain-dim-when-emptyp
    (implies (omap::emptyp (dim-poly-fix poly))
             (equal (poly-to-plain-dim poly)
                    (dim-const 0)))
    :enable poly-to-plain-dim)

  (defruled dim-eq-equiv-poly-to-plain-dim-of-update-when-not-assoc
    (implies (and (dim-polyp poly)
                  (dim-listp mono)
                  (integerp coeff)
                  (not (omap::assoc mono poly)))
             (dim-eq-equiv (poly-to-plain-dim (omap::update mono coeff poly))
                           (dim+ (term-to-plain-dim mono coeff)
                                 (poly-to-plain-dim poly))))
    :induct t
    :expand ((poly-to-plain-dim (omap::update mono coeff poly))
             (poly-to-plain-dim poly))
    :enable poly-to-plain-dim-when-emptyp
    :prep-lemmas
    ((defrule lemma
       (implies (and (dim-listp mono)
                     (integerp coeff))
                (equal (poly-to-plain-dim (omap::update mono coeff nil))
                       (dim+ (term-to-plain-dim mono coeff)
                             (dim-const 0))))
       :expand ((poly-to-plain-dim (omap::update mono coeff nil)))
       :enable poly-to-plain-dim-when-emptyp)))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-delete
    (implies (and (dim-polyp poly)
                  (dim-listp mono))
             (dim-eq-equiv (poly-to-plain-dim (omap::delete mono poly))
                           (dim+ (term-to-plain-dim
                                  mono
                                  (- (dim-poly-coeff mono poly)))
                                 (poly-to-plain-dim poly))))
    :induct t
    :enable (poly-to-plain-dim
             omap::delete
             dim-eq-equiv-poly-to-plain-dim-of-update-when-not-assoc
             dim-poly-coeff-when-emptyp
             dim-poly-coeff-when-not-emptyp
             dim-eq-equiv-add-of-term-to-plain-dim-and-term-to-plain-dim
             dim-eq-equiv-term-to-plain-dim-of-0))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-update
    (implies (and (dim-polyp poly)
                  (dim-listp mono)
                  (integerp coeff))
             (dim-eq-equiv (poly-to-plain-dim (omap::update mono coeff poly))
                           (dim+ (term-to-plain-dim
                                  mono
                                  (- coeff (dim-poly-coeff mono poly)))
                                 (poly-to-plain-dim poly))))
    :use (:instance dim-eq-equiv-poly-to-plain-dim-of-update-when-not-assoc
                    (poly (omap::delete mono poly)))
    :enable (dim-eq-equiv-poly-to-plain-dim-of-delete
             dim-eq-equiv-add-of-term-to-plain-dim-and-term-to-plain-dim))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add-term
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-add-term mono coeff poly))
                  (dim+ (term-to-plain-dim mono coeff)
                        (poly-to-plain-dim poly)))
    :use (:instance lemma (coeff (ifix coeff)))
    :prep-lemmas
    ((defruled lemma
       (implies (integerp coeff)
                (dim-eq-equiv
                 (poly-to-plain-dim (dim-poly-add-term mono coeff poly))
                 (dim+ (term-to-plain-dim mono coeff)
                       (poly-to-plain-dim poly))))
       :cases ((equal coeff (- (dim-poly-coeff mono poly))))
       :expand ((:free (coeff) (dim-poly-add-term mono coeff poly)))
       :enable (dim-eq-equiv-poly-to-plain-dim-of-update
                dim-eq-equiv-poly-to-plain-dim-of-delete))))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-const
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-const coeff))
                  (coeff-to-plain-dim coeff))
    :enable (dim-poly-const
             term-to-plain-dim
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add-term))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-factor
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-factor factor))
                  factor)
    :enable (dim-poly-factor
             term-to-plain-dim
             coeff-to-plain-dim-of-1
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add-term))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-add poly1 poly2))
                  (dim+ (poly-to-plain-dim poly1)
                        (poly-to-plain-dim poly2)))
    :induct t
    :expand ((poly-to-plain-dim poly2))
    :enable (dim-poly-add
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add-term))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-neg
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-neg poly))
                  (dim- (poly-to-plain-dim poly)))
    :induct t
    :expand ((poly-to-plain-dim poly))
    :enable (dim-poly-neg
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-update
             dim-poly-coeff-of-dim-poly-neg
             dim-poly-coeff-of-tail-when-head-key
             dim-eq-equiv-neg-of-term-to-plain-dim))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-sub
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-sub poly1 poly2))
                  (dim+ (poly-to-plain-dim poly1)
                        (dim- (poly-to-plain-dim poly2))))
    :enable (dim-poly-sub
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-neg))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-mul-term
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-mul-term mono coeff poly))
                  (dim* (term-to-plain-dim mono coeff)
                        (poly-to-plain-dim poly)))
    :induct t
    :expand ((poly-to-plain-dim poly))
    :enable (dim-poly-mul-term
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add-term
             dim-eq-equiv-mul-of-term-to-plain-dim-and-term-to-plain-dim))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-mul
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-mul poly1 poly2))
                  (dim* (poly-to-plain-dim poly1)
                        (poly-to-plain-dim poly2)))
    :induct t
    :expand ((poly-to-plain-dim poly1))
    :enable (dim-poly-mul
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-mul-term))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-list-sum
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-list-sum polys))
                  (dim-add (poly-list-to-plain-dim-list polys)))
    :induct t
    :enable (dim-poly-list-sum
             poly-list-to-plain-dim-list
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-add
             dim-eq-equiv-add-cons))

  (defruled dim-eq-equiv-poly-to-plain-dim-of-dim-poly-list-product
    (dim-eq-equiv (poly-to-plain-dim (dim-poly-list-product polys))
                  (dim-mul (poly-list-to-plain-dim-list polys)))
    :induct t
    :enable (dim-poly-list-product
             poly-list-to-plain-dim-list
             coeff-to-plain-dim-of-1
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-const
             dim-eq-equiv-poly-to-plain-dim-of-dim-poly-mul
             dim-eq-equiv-mul-cons)
    :disable ((:e dim-poly-const))))

;;;;;;;;;;;;;;;;;;;;

(defsection poly-to-plain-dim-of-dims-to-polys
  :short "Plain dimensions of the polynomials of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The plain dimension of the polynomial that a dimension denotes
     is equivalent to the dimension.
     This is proved by induction on the translation to polynomials,
     via the theorems in @(see poly-to-plain-dim-of-operations).")
   (xdoc::p
    "In each case of the induction,
     the dimension is known by its kind,
     and the plain dimension of its polynomial
     is rewritten to a dimension built from its components.
     For variables, constants, additions, and multiplications,
     that dimension is the constructor applied to the components,
     which is the original dimension.
     For subtractions, which are translated by number of operands,
     that dimension has a different form in each case;
     so we first prove three theorems
     saying that those forms are equivalent to the original dimension.
     The first one is phrased as an equality with @('t'),
     so that the whole equivalence is the left-hand side of the rewrite rule:
     otherwise, the left-hand side would be a ground term,
     which could not bind the variable for the dimension."))

  (defruled dim-eq-equiv-sub-nil-when-sub-and-not-consp
    (implies (and (dim-case dim :sub)
                  (not (consp (dim-sub->dims dim))))
             (equal (dim-eq-equiv (dim-sub nil) dim)
                    t))
    :enable (dim-eq-equiv
             dim-eq-refl)
    :use ((:instance dim-sub-of-fields (x dim))
          (:instance dim-listp-when-not-consp (acl2::x (dim-sub->dims dim))))
    :disable (dim-sub-of-fields
              equal-of-dim-sub
              dim-listp-when-not-consp))

  (defruled dim-eq-equiv-neg-of-car-when-sub-and-not-consp-of-cdr
    (implies (and (dim-case dim :sub)
                  (consp (dim-sub->dims dim))
                  (not (consp (cdr (dim-sub->dims dim)))))
             (dim-eq-equiv (dim- (car (dim-sub->dims dim)))
                           dim))
    :prep-lemmas
    ((defrule lemma
       (implies (and (dim-listp dims)
                     (consp dims)
                     (not (consp (cdr dims))))
                (equal (list (car dims))
                       dims)))))

  (defruled dim-eq-equiv-sub2m-when-sub-and-consp-of-cdr
    (implies (and (dim-case dim :sub)
                  (consp (cdr (dim-sub->dims dim))))
             (dim-eq-equiv (dim+ (car (dim-sub->dims dim))
                                 (dim- (dim-add (cdr (dim-sub->dims dim)))))
                           dim))
    :use (:instance dim-eq-equiv-sub2m
                    (dim (car (dim-sub->dims dim)))
                    (dims (cdr (dim-sub->dims dim))))
    :disable dim-eq-equiv-sub2m)

  (defthm-dims-to-polys-flag
    (defthmd dim-eq-equiv-poly-to-plain-dim-of-dim-to-poly
      (dim-eq-equiv (poly-to-plain-dim (dim-to-poly dim))
                    dim)
      :flag dim-to-poly)
    (defthmd
      dims-eq-equiv-poly-list-to-plain-dim-list-of-dim-list-to-poly-list
      (dims-eq-equiv (poly-list-to-plain-dim-list
                      (dim-list-to-poly-list dims))
                     dims)
      :flag dim-list-to-poly-list)
    :hints
    (("Goal"
      :in-theory
      (enable dim-to-poly
              dim-list-to-poly-list
              coeff-to-plain-dim-when-natp
              dims-eq-equiv-of-nil-when-not-consp
              dim-eq-equiv-poly-to-plain-dim-of-dim-poly-factor
              dim-eq-equiv-poly-to-plain-dim-of-dim-poly-const
              dim-eq-equiv-poly-to-plain-dim-of-dim-poly-list-sum
              dim-eq-equiv-poly-to-plain-dim-of-dim-poly-list-product
              dim-eq-equiv-poly-to-plain-dim-of-dim-poly-neg
              dim-eq-equiv-poly-to-plain-dim-of-dim-poly-sub
              dim-eq-equiv-sub-nil-when-sub-and-not-consp
              dim-eq-equiv-neg-of-car-when-sub-and-not-consp-of-cdr
              dim-eq-equiv-sub2m-when-sub-and-consp-of-cdr)))))

;;;;;;;;;;;;;;;;;;;;

(defsection poly-to-dim-and-poly-to-plain-dim
  :short "Equivalence of the canonical and plain dimensions of polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The dimension in canonical form
     that @(tsee poly-to-dim) turns a polynomial into
     is equivalent to the dimension in plain form
     that @(tsee poly-to-plain-dim) turns the polynomial into.")
   (xdoc::p
    "The function @(tsee poly-to-dim) splits the terms of the polynomial
     into a positive part and a negative part,
     and combines the two parts by cases.
     In all the cases, the result is equivalent to
     the addition of the sum of the positive part
     and of the negation of the sum of the negative part.
     That addition is equivalent to the plain dimension of the polynomial,
     by induction on the terms of the polynomial."))

  (defruled dim-eq-equiv-poly-to-dim-term
    (implies (posp coeff)
             (dim-eq-equiv (poly-to-dim-term mono coeff)
                           (term-to-plain-dim mono coeff)))
    :use (:instance lemma (mono (dim-list-fix mono)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (dim-listp mono)
                     (posp coeff))
                (dim-eq-equiv (poly-to-dim-term mono coeff)
                              (term-to-plain-dim mono coeff)))
       :enable (poly-to-dim-term
                term-to-plain-dim
                coeff-to-plain-dim-when-natp
                dim-eq-equiv-mul-cons))))

  (defruled dim-eq-equiv-poly-to-dim-sum
    (dim-eq-equiv (poly-to-dim-sum terms)
                  (dim-add terms))
    :use (:instance lemma (terms (dim-list-fix terms)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp terms)
                (dim-eq-equiv (poly-to-dim-sum terms)
                              (dim-add terms)))
       :enable poly-to-dim-sum
       :expand ((len terms)
                (len (cdr terms))))))

  (defruled dim-eq-equiv-add-of-poly-to-dim-parts
    (dim-eq-equiv (dim+ (dim-add (mv-nth 0 (poly-to-dim-parts poly)))
                        (dim- (dim-add (mv-nth 1 (poly-to-dim-parts poly)))))
                  (poly-to-plain-dim poly))
    :induct t
    :expand ((poly-to-plain-dim poly))
    :enable (poly-to-dim-parts
             poly-to-plain-dim-when-emptyp
             dim-eq-equiv-poly-to-dim-term
             dim-eq-equiv-add-cons
             dim-eq-equiv-neg-of-term-to-plain-dim
             dim-eq-equiv-term-to-plain-dim-of-0))

  (defruled dim-eq-equiv-poly-to-dim
    (dim-eq-equiv (poly-to-dim poly)
                  (poly-to-plain-dim poly))
    :enable (lemma
             dim-eq-equiv-add-of-poly-to-dim-parts)
    :prep-lemmas
    ((defruled lemma
       (dim-eq-equiv
        (poly-to-dim poly)
        (dim+ (dim-add (mv-nth 0 (poly-to-dim-parts poly)))
              (dim- (dim-add (mv-nth 1 (poly-to-dim-parts poly))))))
       :enable (poly-to-dim
                dim-eq-equiv-poly-to-dim-sum
                dim-eq-equiv-add-when-not-consp)))))

;;;;;;;;;;;;;;;;;;;;

(defsection normalize-dim-soundness
  :short "Dimensions are equivalent to their normal forms."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems in
     @(see poly-to-plain-dim-of-dims-to-polys) and
     @(see poly-to-dim-and-poly-to-plain-dim).
     It is lifted to lists of dimensions."))

  (defruled dim-eq-equiv-normalize-dim
    (dim-eq-equiv (normalize-dim dim)
                  dim)
    :enable (normalize-dim
             dim-eq-equiv-poly-to-dim
             dim-eq-equiv-poly-to-plain-dim-of-dim-to-poly))

  (defruled dims-eq-equiv-normalize-dim-list
    (dims-eq-equiv (normalize-dim-list dims)
                   dims)
    :induct t
    :enable (normalize-dim-list
             dim-eq-equiv-normalize-dim
             dims-eq-equiv-of-nil-when-not-consp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalize-dim-completeness
  :short "Equivalent dimensions have the same normal form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Equivalent dimensions denote the same polynomial,
     and equivalent lists of dimensions denote the same list of polynomials.
     This is proved by induction on the proof validity predicates:
     for each inference rule,
     the theorems in @(see dims-to-polys-properties)
     turn the equality of the polynomials of the conclusion
     into an equality between results of operations on polynomials,
     which is a property of the ring of polynomials
     (see @(see dimension-polynomials-properties)).
     We disable the rules that would turn
     the equalities between the dimensions in the conclusion
     and calls of the dimension constructors
     into conjunctions about the kinds and components of the dimensions,
     so that ACL2 replaces the dimensions with the constructor calls,
     to which the theorems about the translation apply.
     We also keep ground calls of some functions unevaluated,
     so that the theorems about the ring apply to them.")
   (xdoc::p
    "Since the normal form of a dimension
     is calculated from its polynomial,
     equivalent dimensions have the same normal form.
     This is lifted to lists of dimensions,
     again by induction on the proof validity predicates."))

  (local
   (defthm-dim-eq-proof-validp-clique-flag
     (defthmd same-dim-to-poly-when-dim-eq-proof-validp
       (implies (dim-eq-proof-validp proof _dim1 _dim2)
                (equal (dim-to-poly _dim1)
                       (dim-to-poly _dim2)))
       :flag dim-eq-proof-validp)
     (defthmd same-dim-list-to-poly-list-when-dims-eq-proof-validp
       (implies (dims-eq-proof-validp proof _dims1 _dims2)
                (equal (dim-list-to-poly-list _dims1)
                       (dim-list-to-poly-list _dims2)))
       :flag dims-eq-proof-validp)
     :hints
     (("Goal"
       :in-theory
       (acl2::e/d* (dim-equivalence-definition-validp-defs
                    dim-to-poly-of-dim-const
                    dim-to-poly-of-dim-add
                    dim-to-poly-of-dim-mul
                    dim-to-poly-of-dim-sub
                    dim-list-to-poly-list-of-cons
                    consp-of-dim-list-to-poly-list
                    dim-poly-list-sum-of-cons
                    dim-poly-list-product-of-nil
                    dim-poly-list-product-of-cons
                    dim-poly-sub
                    dim-poly-const-of-0
                    commutativity-of-dim-poly-add
                    associativity-of-dim-poly-add
                    dim-poly-add-of-nil-left
                    dim-poly-add-of-nil-right
                    dim-poly-add-of-dim-poly-neg
                    dim-poly-add-of-dim-poly-const-and-dim-poly-const
                    commutativity-of-dim-poly-mul
                    associativity-of-dim-poly-mul
                    dim-poly-mul-of-dim-poly-const-1-left
                    dim-poly-mul-of-dim-poly-const-1-right
                    dim-poly-mul-of-dim-poly-const-and-dim-poly-const
                    dim-poly-mul-of-dim-poly-add-right
                    nfix
                    natp)
                   (equal-of-dim-const
                    equal-of-dim-add
                    equal-of-dim-mul
                    equal-of-dim-sub
                    (:e dim-poly-const)
                    (:e dim-poly-list-product)))))))

  (defruled same-dim-to-poly-when-dim-eq
    (implies (dim-eq dim1 dim2)
             (equal (dim-to-poly dim1)
                    (dim-to-poly dim2)))
    :enable (dim-eq
             same-dim-to-poly-when-dim-eq-proof-validp))

  (defruled same-dim-list-to-poly-list-when-dims-eq
    (implies (dims-eq dims1 dims2)
             (equal (dim-list-to-poly-list dims1)
                    (dim-list-to-poly-list dims2)))
    :enable (dims-eq
             same-dim-list-to-poly-list-when-dims-eq-proof-validp))

  (defruled same-normalize-dim-when-dim-eq
    (implies (dim-eq dim1 dim2)
             (equal (normalize-dim dim1)
                    (normalize-dim dim2)))
    :enable normalize-dim
    :use same-dim-to-poly-when-dim-eq)

  (local
   (defthm-dim-eq-proof-validp-clique-flag
     (defthmd same-normalize-dim-list-when-dims-eq-proof-validp
       (implies (dims-eq-proof-validp proof _dims1 _dims2)
                (equal (normalize-dim-list _dims1)
                       (normalize-dim-list _dims2)))
       :flag dims-eq-proof-validp)
     :skip-others t
     :hints
     (("Goal"
       :in-theory (enable* dim-equivalence-definition-validp-defs
                           normalize-dim-list
                           normalize-dim
                           same-dim-to-poly-when-dim-eq-proof-validp)))))

  (defruled same-normalize-dim-list-when-dims-eq
    (implies (dims-eq dims1 dims2)
             (equal (normalize-dim-list dims1)
                    (normalize-dim-list dims2)))
    :enable (dims-eq
             same-normalize-dim-list-when-dims-eq-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalize-shape/ispace-by-kind
  :short "Normal forms of shapes and ispaces, by kind."
  :long
  (xdoc::topstring
   (xdoc::p
    "The normal form of a shape or ispace is calculated in three passes
     (see @(tsee normalize-shape) and @(tsee normalize-ispace)).
     Here we prove theorems that express, for each kind of shape and ispace,
     its normal form in terms of the normal forms of its components,
     without reference to the three passes.")
   (xdoc::p
    "The normal form of a shape is always a concatenation,
     of shape variables and of singleton shapes with normalized dimensions.
     The normal form of a shape variable
     is the concatenation of just the variable.
     The normal form of a shape built from dimensions
     is the concatenation of the singleton shapes
     of the normalized dimensions.
     The normal form of a concatenation of shapes
     is the concatenation of the lists of shapes
     that the normal forms of the shapes consist of;
     we express this by cases on the list of shapes,
     where the case of a non-empty list refers to
     the normal form of the first shape and
     the normal form of the concatenation of the remaining shapes.
     The normal form of a splice of ispaces
     is expressed in a similar way,
     where the first ispace contributes the shape of its normal form,
     which is always a shape ispace.
     The normal form of a dimension ispace
     is the shape ispace whose shape is
     the concatenation of the singleton shape of the normalized dimension.
     The normal form of a shape ispace
     is the shape ispace of the normal form of the shape.")
   (xdoc::p
    "We start with two theorems about the third pass,
     which flattens concatenations,
     and one about the second pass.
     Then we prove the theorems about normal forms,
     by expanding the definitions of the three passes
     on the kinds of shapes and ispaces at hand."))

  (defruled flatten-append-in-shape-list-of-t-when-consp
    (implies (consp shapes)
             (equal (flatten-append-in-shape-list shapes t)
                    (append (shape-append->shapes
                             (flatten-append-in-shape (car shapes)))
                            (flatten-append-in-shape-list (cdr shapes) t))))
    :expand ((flatten-append-in-shape-list shapes t)))

  (defruled
    flatten-append-in-shape-list-of-shape-dims-list-of-list-to-singletons
    (equal (flatten-append-in-shape-list
            (shape-dims-list (list-to-singletons dims)) t)
           (shape-dims-list (list-to-singletons dims)))
    :induct t
    :enable (list-to-singletons
             flatten-append-in-shape-list-of-t-when-consp)
    :expand ((:free (dims) (flatten-append-in-shape (shape-dims dims)))))

  (defruled ispace-list-case-shape-of-normalize-shapes-single-in-ispace-list
    (ispace-list-case-shape (normalize-shapes-single-in-ispace-list ispaces))
    :induct (len ispaces)
    :enable ((:induction len))
    :expand ((normalize-shapes-single-in-ispace-list ispaces)))

  (defruled normalize-shape-when-var
    (implies (shape-case shape :var)
             (equal (normalize-shape shape)
                    (shape-append
                     (list (shape-var (shape-var->name shape))))))
    :enable normalize-shape
    :expand ((normalize-dims-in-shape shape)
             (normalize-shapes-single-in-shape shape)
             (flatten-append-in-shape shape)))

  (defruled normalize-shape-when-dims
    (implies (shape-case shape :dims)
             (equal (normalize-shape shape)
                    (shape-append
                     (shape-dims-list
                      (list-to-singletons
                       (normalize-dim-list (shape-dims->dims shape)))))))
    :enable normalize-shape
    :expand ((normalize-dims-in-shape shape))
    :prep-lemmas
    ((defrule lemma
       (implies (dim-listp dims)
                (equal (flatten-append-in-shape
                        (normalize-shapes-single-in-shape (shape-dims dims)))
                       (shape-append
                        (shape-dims-list (list-to-singletons dims)))))
       :enable
       flatten-append-in-shape-list-of-shape-dims-list-of-list-to-singletons
       :expand ((normalize-shapes-single-in-shape (shape-dims dims))
                (:free (dims) (flatten-append-in-shape (shape-dims dims)))
                (:free (shapes)
                 (flatten-append-in-shape (shape-append shapes))))
       :prep-lemmas
       ((defrule lemma1
          (implies (and (consp list)
                        (not (consp (cdr list))))
                   (equal (list-to-singletons list)
                          (list (list (car list)))))
          :expand ((list-to-singletons list)
                   (list-to-singletons (cdr list))))
        (defrule lemma2
          (implies (and (dim-listp dims)
                        (consp dims)
                        (not (consp (cdr dims))))
                   (equal (list (car dims))
                          dims)))))))

  (defruled normalize-shape-of-shape-append
    (equal (normalize-shape (shape-append shapes))
           (shape-append
            (flatten-append-in-shape-list
             (normalize-shapes-single-in-shape-list
              (normalize-dims-in-shape-list shapes))
             t)))
    :enable normalize-shape
    :expand ((:free (shapes) (normalize-dims-in-shape (shape-append shapes)))
             (:free (shapes)
              (normalize-shapes-single-in-shape (shape-append shapes)))
             (:free (shapes)
              (flatten-append-in-shape (shape-append shapes)))))

  (defruled normalize-shape-of-shape-append-when-not-consp
    (implies (not (consp shapes))
             (equal (normalize-shape (shape-append shapes))
                    (shape-append nil)))
    :enable normalize-shape-of-shape-append
    :expand ((normalize-dims-in-shape-list shapes)))

  (defruled normalize-shape-of-shape-append-when-consp
    (implies (consp shapes)
             (equal (normalize-shape (shape-append shapes))
                    (shape-append
                     (append (shape-append->shapes
                              (normalize-shape (car shapes)))
                             (shape-append->shapes
                              (normalize-shape
                               (shape-append (cdr shapes))))))))
    :enable (normalize-shape-of-shape-append
             flatten-append-in-shape-list-of-t-when-consp)
    :expand ((normalize-dims-in-shape-list shapes)
             (:free (shape shapes)
              (normalize-shapes-single-in-shape-list (cons shape shapes)))
             (normalize-shape (car shapes))))

  (defruled normalize-shape-of-shape-splice
    (equal (normalize-shape (shape-splice ispaces))
           (shape-append
            (flatten-append-in-shape-list
             (ispace-shape-list->shape
              (normalize-shapes-single-in-ispace-list
               (normalize-dims-in-ispace-list ispaces)))
             t)))
    :enable (normalize-shape
             ispace-list-case-shape-of-normalize-shapes-single-in-ispace-list)
    :expand ((:free (ispaces)
              (normalize-dims-in-shape (shape-splice ispaces)))
             (:free (ispaces)
              (normalize-shapes-single-in-shape (shape-splice ispaces)))
             (:free (ispaces)
              (flatten-append-in-shape (shape-splice ispaces)))))

  (defruled normalize-shape-of-shape-splice-when-not-consp
    (implies (not (consp ispaces))
             (equal (normalize-shape (shape-splice ispaces))
                    (shape-append nil)))
    :enable normalize-shape-of-shape-splice
    :expand ((normalize-dims-in-ispace-list ispaces)))

  (defruled normalize-shape-of-shape-splice-when-consp
    (implies (consp ispaces)
             (equal (normalize-shape (shape-splice ispaces))
                    (shape-append
                     (append (shape-append->shapes
                              (ispace-shape->shape
                               (normalize-ispace (car ispaces))))
                             (shape-append->shapes
                              (normalize-shape
                               (shape-splice (cdr ispaces))))))))
    :enable (normalize-shape-of-shape-splice
             flatten-append-in-shape-list-of-t-when-consp
             normalize-ispace)
    :expand ((normalize-dims-in-ispace-list ispaces)
             (:free (ispace ispaces)
              (normalize-shapes-single-in-ispace-list (cons ispace ispaces)))
             (:free (ispace) (flatten-append-in-ispace ispace))))

  (defruled normalize-ispace-when-dim
    (implies (ispace-case ispace :dim)
             (equal (normalize-ispace ispace)
                    (ispace-shape
                     (shape-append
                      (list (shape-dims
                             (list (normalize-dim
                                    (ispace-dim->dim ispace)))))))))
    :enable normalize-ispace
    :expand ((normalize-dims-in-ispace ispace)
             (:free (dim) (normalize-shapes-single-in-ispace (ispace-dim dim)))
             (:free (shape) (flatten-append-in-ispace (ispace-shape shape)))
             (:free (dims) (flatten-append-in-shape (shape-dims dims)))))

  (defruled normalize-ispace-when-shape
    (implies (ispace-case ispace :shape)
             (equal (normalize-ispace ispace)
                    (ispace-shape
                     (normalize-shape (ispace-shape->shape ispace)))))
    :enable (normalize-ispace
             normalize-shape)
    :expand ((normalize-dims-in-ispace ispace)
             (:free (shape)
              (normalize-shapes-single-in-ispace (ispace-shape shape)))
             (:free (shape) (flatten-append-in-ispace (ispace-shape shape))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalize-shape/ispace-soundness
  :short "Shapes and ispaces are equivalent to their normal forms."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by induction on the structure of shapes and ispaces,
     via the theorems in @(see normalize-shape/ispace-by-kind)
     and the fact that dimensions are equivalent to their normal forms
     (see @(see normalize-dim-soundness)).
     The induction scheme is the one of the first pass,
     which recurs on the components of shapes and ispaces.")
   (xdoc::p
    "The four theorems proved by induction are all about shape equivalence.
     The ones for lists of shapes and ispaces
     are formulated on the concatenation of the shapes
     and on the splice of the ispaces,
     consistently with the theorems
     in @(see normalize-shape/ispace-by-kind);
     in the theorems for shapes,
     these make the cases of concatenations and splices
     follow directly from the induction hypotheses.
     The one for ispaces is formulated
     on the shape of the normal form of the ispace
     and on the splice of just the ispace,
     which is what the case of a non-empty list of ispaces needs:
     an equivalence between ispaces
     would not imply the equivalence between shapes needed there.")
   (xdoc::p
    "The theorem for ispaces, formulated on ispace equivalence,
     is then proved by cases on the kind of the ispace."))

  (defruled shape-eq-equiv-append-of-shape-dims-list-of-list-to-singletons
    (shape-eq-equiv (shape-append (shape-dims-list (list-to-singletons dims)))
                    (shape-dims dims))
    :induct t
    :enable (list-to-singletons
             shape-eq-equiv-dims-cons
             shape-eq-equiv-append-cons
             shape-eq-equiv-dims-when-not-consp))

  (defthm-normalize-dims-in-shapes/ispaces-flag
    (defthmd shape-eq-equiv-normalize-shape
      (shape-eq-equiv (normalize-shape shape)
                      shape)
      :flag normalize-dims-in-shape)
    (defthmd shape-eq-equiv-normalize-shape-of-shape-append
      (shape-eq-equiv (normalize-shape (shape-append shapes))
                      (shape-append shapes))
      :flag normalize-dims-in-shape-list)
    (defthmd shape-eq-equiv-ispace-shape->shape-of-normalize-ispace
      (shape-eq-equiv (ispace-shape->shape (normalize-ispace ispace))
                      (shape-splice (list ispace)))
      :flag normalize-dims-in-ispace)
    (defthmd shape-eq-equiv-normalize-shape-of-shape-splice
      (shape-eq-equiv (normalize-shape (shape-splice ispaces))
                      (shape-splice ispaces))
      :flag normalize-dims-in-ispace-list)
    :hints
    (("Goal"
      :in-theory
      (enable normalize-shape-when-var
              normalize-shape-when-dims
              normalize-shape-of-shape-append-when-not-consp
              normalize-shape-of-shape-append-when-consp
              normalize-shape-of-shape-splice-when-not-consp
              normalize-shape-of-shape-splice-when-consp
              normalize-ispace-when-dim
              normalize-ispace-when-shape
              shape-eq-equiv-append-cons
              shape-eq-equiv-append-of-append
              shape-eq-equiv-append-of-shape-dims-list-of-list-to-singletons
              shape-eq-equiv-splice-cons
              shape-eq-equiv-append-when-not-consp
              shape-eq-equiv-splice-when-not-consp
              dim-eq-equiv-normalize-dim
              dims-eq-equiv-normalize-dim-list))))

  (defruled ispace-eq-equiv-normalize-ispace
    (ispace-eq-equiv (normalize-ispace ispace)
                     ispace)
    :use (:instance ispace-kind-possibilities (x ispace))
    :enable (normalize-ispace-when-dim
             normalize-ispace-when-shape
             shape-eq-equiv-normalize-shape
             dim-eq-equiv-normalize-dim
             ispace-eq-equiv-ispace-dim-shape)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalize-shape/ispace-completeness
  :short "Equivalent shapes and ispaces have the same normal form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by induction on the proof validity predicates,
     via the theorems in @(see normalize-shape/ispace-by-kind)
     and the fact that equivalent dimensions have the same normal form
     (see @(see normalize-dim-completeness)).
     The theorems about normal forms
     turn the equality of the normal forms
     of the conclusion of each inference rule
     into an equality between concatenations of lists,
     which follows from the induction hypotheses
     and from properties of lists.")
   (xdoc::p
    "The lemmas for lists of shapes and ispaces
     are formulated on the concatenation of the shapes
     and on the splice of the ispaces,
     like the theorems in @(see normalize-shape/ispace-soundness).
     As in @(see normalize-dim-completeness),
     we disable the rules that would turn
     the equalities between the shapes and ispaces in the conclusion
     and calls of the constructors
     into conjunctions about kinds and components."))

  (local
   (defthm-shape-eq-proof-validp-clique-flag
     (defthmd same-normalize-shape-when-shape-eq-proof-validp
       (implies (shape-eq-proof-validp proof _shape1 _shape2)
                (equal (normalize-shape _shape1)
                       (normalize-shape _shape2)))
       :flag shape-eq-proof-validp)
     (defthmd
       same-normalize-shape-of-shape-append-when-shapes-eq-proof-validp
       (implies (shapes-eq-proof-validp proof _shapes1 _shapes2)
                (equal (normalize-shape (shape-append _shapes1))
                       (normalize-shape (shape-append _shapes2))))
       :flag shapes-eq-proof-validp)
     (defthmd same-normalize-ispace-when-ispace-eq-proof-validp
       (implies (ispace-eq-proof-validp proof _ispace1 _ispace2)
                (equal (normalize-ispace _ispace1)
                       (normalize-ispace _ispace2)))
       :flag ispace-eq-proof-validp)
     (defthmd
       same-normalize-shape-of-shape-splice-when-ispaces-eq-proof-validp
       (implies (ispaces-eq-proof-validp proof _ispaces1 _ispaces2)
                (equal (normalize-shape (shape-splice _ispaces1))
                       (normalize-shape (shape-splice _ispaces2))))
       :flag ispaces-eq-proof-validp)
     :hints
     (("Goal"
       :in-theory
       (acl2::e/d* (shape/ispace-equivalence-definition-validp-defs
                    normalize-shape-when-dims
                    normalize-shape-of-shape-append-when-not-consp
                    normalize-shape-of-shape-append-when-consp
                    normalize-shape-of-shape-splice-when-not-consp
                    normalize-shape-of-shape-splice-when-consp
                    normalize-ispace-when-dim
                    normalize-ispace-when-shape
                    same-normalize-dim-when-dim-eq
                    same-normalize-dim-list-when-dims-eq
                    normalize-dim-list
                    list-to-singletons)
                   (equal-of-shape-dims
                    equal-of-shape-append
                    equal-of-shape-splice
                    equal-of-ispace-dim
                    equal-of-ispace-shape))))))

  (defruled same-normalize-shape-when-shape-eq
    (implies (shape-eq shape1 shape2)
             (equal (normalize-shape shape1)
                    (normalize-shape shape2)))
    :enable (shape-eq
             same-normalize-shape-when-shape-eq-proof-validp))

  (defruled same-normalize-ispace-when-ispace-eq
    (implies (ispace-eq ispace1 ispace2)
             (equal (normalize-ispace ispace1)
                    (normalize-ispace ispace2)))
    :enable (ispace-eq
             same-normalize-ispace-when-ispace-eq-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-equivalence-checker-soundness
  :short "Soundness of the ispace equivalence checker."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the checker succeeds,
     the dimensions, shapes, or ispaces are equivalent
     according to the inference rules.
     This follows from the fact that
     each of them is equivalent to its normal form
     (see @(see normalize-dim-soundness)
     and @(see normalize-shape/ispace-soundness)),
     given that the two normal forms are equal.")
   (xdoc::p
    "The hypotheses that the ASTs have the right types are needed
     because the equivalence predicates do not fix their arguments,
     while the checker does."))

  (defruled dim-eq-when-dim-equivp
    (implies (and (dimp dim1)
                  (dimp dim2)
                  (dim-equivp dim1 dim2))
             (dim-eq dim1 dim2))
    :enable (dim-equivp
             dim-eq-when-dim-eq-equiv)
    :use ((:instance dim-eq-equiv-normalize-dim (dim dim1))
          (:instance dim-eq-equiv-normalize-dim (dim dim2))))

  (defruled shape-eq-when-shape-equivp
    (implies (and (shapep shape1)
                  (shapep shape2)
                  (shape-equivp shape1 shape2))
             (shape-eq shape1 shape2))
    :enable (shape-equivp
             shape-eq-when-shape-eq-equiv)
    :use ((:instance shape-eq-equiv-normalize-shape (shape shape1))
          (:instance shape-eq-equiv-normalize-shape (shape shape2))))

  (defruled ispace-eq-when-ispace-equivp
    (implies (and (ispacep ispace1)
                  (ispacep ispace2)
                  (ispace-equivp ispace1 ispace2))
             (ispace-eq ispace1 ispace2))
    :enable (ispace-equivp
             ispace-eq-when-ispace-eq-equiv)
    :use ((:instance ispace-eq-equiv-normalize-ispace (ispace ispace1))
          (:instance ispace-eq-equiv-normalize-ispace (ispace ispace2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-equivalence-checker-completeness
  :short "Completeness of the ispace equivalence checker."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two dimensions, shapes, or ispaces are equivalent
     according to the inference rules,
     the checker succeeds on them.
     This is because they have the same normal form
     (see @(see normalize-dim-completeness)
     and @(see normalize-shape/ispace-completeness))."))

  (defruled dim-equivp-when-dim-eq
    (implies (dim-eq dim1 dim2)
             (dim-equivp dim1 dim2))
    :enable (dim-equivp
             same-normalize-dim-when-dim-eq))

  (defruled shape-equivp-when-shape-eq
    (implies (shape-eq shape1 shape2)
             (shape-equivp shape1 shape2))
    :enable (shape-equivp
             same-normalize-shape-when-shape-eq))

  (defruled ispace-equivp-when-ispace-eq
    (implies (ispace-eq ispace1 ispace2)
             (ispace-equivp ispace1 ispace2))
    :enable (ispace-equivp
             same-normalize-ispace-when-ispace-eq)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-equivalence-checker-equivalence
  :short "Equivalence of the ispace equivalence checker
          and ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "These combine
     @(see ispace-equivalence-checker-soundness) and
     @(see ispace-equivalence-checker-completeness).
     The equalities hold because
     both the checker and the equivalence predicates are boolean-valued."))

  (defruled dim-equivp-to-dim-eq
    (implies (and (dimp dim1)
                  (dimp dim2))
             (equal (dim-equivp dim1 dim2)
                    (dim-eq dim1 dim2)))
    :use (dim-eq-when-dim-equivp
          dim-equivp-when-dim-eq))

  (defruled shape-equivp-to-shape-eq
    (implies (and (shapep shape1)
                  (shapep shape2))
             (equal (shape-equivp shape1 shape2)
                    (shape-eq shape1 shape2)))
    :use (shape-eq-when-shape-equivp
          shape-equivp-when-shape-eq))

  (defruled ispace-equivp-to-ispace-eq
    (implies (and (ispacep ispace1)
                  (ispacep ispace2))
             (equal (ispace-equivp ispace1 ispace2)
                    (ispace-eq ispace1 ispace2)))
    :use (ispace-eq-when-ispace-equivp
          ispace-equivp-when-ispace-eq)))
