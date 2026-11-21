; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "dimension-polynomials")

(include-book "std/omaps/extensionality" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/omaps/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dimension-polynomials-properties
  :parents (validator)
  :short "Properties of the polynomials in the dimension variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the canonical representation of polynomials
     described in @(see dimension-polynomials):
     the monomials are sorted lists of factors,
     and there are no zero coefficients.
     We prove that the operations on polynomials
     preserve the canonical representation,
     and that the translation of dimensions into polynomials
     yields polynomials in canonical representation.")
   (xdoc::p
    "We prove that two polynomials in canonical representation are equal
     exactly when they have the same coefficients for all monomials.
     This reduces equalities of polynomials to equalities of integers.")
   (xdoc::p
    "We prove that the polynomials in canonical representation
     form a commutative ring with identity,
     under the operations defined in @(see dimension-polynomials):
     addition is commutative and associative,
     the zero polynomial is its identity,
     and negation yields additive inverses;
     multiplication is commutative and associative,
     the constant polynomial 1 is its identity,
     and it distributes over addition.
     We also prove that the constant polynomials
     are added and multiplied by adding and multiplying their constants.
     These properties are equalities, not just equivalences,
     because the representation is canonical."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection sort-dims-properties
  :short "Properties of the sorting of lists of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee sort-dims) is an insertion sort,
     whose auxiliary function inserts a dimension into a list.
     The key property is that insertions commute:
     the result of inserting two dimensions into a list
     does not depend on the order of the two insertions.
     This holds for all lists, not only for the sorted ones;
     it relies on the fact that @(tsee <<) is a total order.")
   (xdoc::p
    "From that, we prove that sorting absorbs
     the sorting of the list,
     and the sorting and the swapping of two lists that are appended.
     In essence, the result of sorting only depends on
     the elements of the list, with their multiplicities.
     We express these properties as equalities between results of sorting,
     without introducing notions of ordered lists and of permutations."))

  (defruled sort-dims-aux-of-sort-dims-aux
    (equal (sort-dims-aux dim1 (sort-dims-aux dim2 dims))
           (sort-dims-aux dim2 (sort-dims-aux dim1 dims)))
    :induct t
    :enable sort-dims-aux)

  (defruled sort-dims-of-sort-dims-aux
    (equal (sort-dims (sort-dims-aux dim dims))
           (sort-dims-aux dim (sort-dims dims)))
    :induct t
    :enable (sort-dims-aux
             sort-dims
             sort-dims-aux-of-sort-dims-aux))

  (defruled sort-dims-of-sort-dims
    (equal (sort-dims (sort-dims dims))
           (sort-dims dims))
    :induct t
    :enable (sort-dims
             sort-dims-of-sort-dims-aux))

  (defruled sort-dims-of-append-of-sort-dims-aux
    (equal (sort-dims (append (sort-dims-aux dim dims1) dims2))
           (sort-dims-aux dim (sort-dims (append dims1 dims2))))
    :induct t
    :enable (sort-dims-aux
             sort-dims
             append
             sort-dims-aux-of-sort-dims-aux))

  (defruled sort-dims-of-append-of-cons
    (equal (sort-dims (append dims1 (cons dim dims2)))
           (sort-dims-aux dim (sort-dims (append dims1 dims2))))
    :induct t
    :enable (sort-dims
             append
             sort-dims-aux-of-sort-dims-aux))

  (defruled sort-dims-of-append-commutative
    (equal (sort-dims (append dims1 dims2))
           (sort-dims (append dims2 dims1)))
    :induct t
    :enable (sort-dims
             append
             sort-dims-of-append-of-cons))

  (defruled sort-dims-of-append-of-sort-dims-left
    (equal (sort-dims (append (sort-dims dims1) dims2))
           (sort-dims (append dims1 dims2)))
    :induct t
    :enable (sort-dims
             append
             sort-dims-of-append-of-sort-dims-aux))

  (defruled sort-dims-of-append-of-sort-dims-right
    (equal (sort-dims (append dims1 (sort-dims dims2)))
           (sort-dims (append dims1 dims2)))
    :use ((:instance sort-dims-of-append-commutative
                     (dims2 (sort-dims dims2)))
          (:instance sort-dims-of-append-of-sort-dims-left
                     (dims1 dims2)
                     (dims2 dims1))
          (:instance sort-dims-of-append-commutative
                     (dims1 dims2)
                     (dims2 dims1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-mono-sortedp ((mono dim-listp))
  :returns (yes/no booleanp)
  :short "Check if a monomial is sorted."
  :long
  (xdoc::topstring
   (xdoc::p
    "A monomial is represented as the list of its factors,
     which must be sorted according to the total order of ACL2 values
     (see @(see dimension-polynomials)).
     We express this by saying that sorting the list leaves it unchanged."))
  (equal (sort-dims mono)
         (dim-list-fix mono))

  ///

  (defrule dim-mono-sortedp-of-nil
    (dim-mono-sortedp nil))

  (defrule dim-mono-sortedp-of-singleton
    (dim-mono-sortedp (list dim))
    :enable (sort-dims
             sort-dims-aux))

  (defrule dim-mono-sortedp-of-sort-dims
    (dim-mono-sortedp (sort-dims dims))
    :enable sort-dims-of-sort-dims)

  (defruled sort-dims-when-dim-mono-sortedp
    (implies (dim-mono-sortedp mono)
             (equal (sort-dims mono)
                    (dim-list-fix mono)))))

;;;;;;;;;;;;;;;;;;;;

(defsection dim-mono-mul-properties
  :short "Properties of the multiplication of monomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The product of two monomials is sorted.
     Multiplication is commutative and associative,
     for all monomials, not only for the sorted ones.
     The empty monomial is its identity, for the sorted monomials."))

  (defrule dim-mono-sortedp-of-dim-mono-mul
    (dim-mono-sortedp (dim-mono-mul mono1 mono2))
    :enable dim-mono-mul)

  (defruled commutativity-of-dim-mono-mul
    (equal (dim-mono-mul mono1 mono2)
           (dim-mono-mul mono2 mono1))
    :enable dim-mono-mul
    :use (:instance sort-dims-of-append-commutative
                    (dims1 (dim-list-fix mono1))
                    (dims2 (dim-list-fix mono2))))

  (defruled associativity-of-dim-mono-mul
    (equal (dim-mono-mul (dim-mono-mul mono1 mono2) mono3)
           (dim-mono-mul mono1 (dim-mono-mul mono2 mono3)))
    :enable (dim-mono-mul
             sort-dims-of-append-of-sort-dims-left
             sort-dims-of-append-of-sort-dims-right))

  (defruled dim-mono-mul-of-nil-when-dim-mono-sortedp
    (implies (dim-mono-sortedp mono)
             (equal (dim-mono-mul nil mono)
                    (dim-list-fix mono)))
    :enable (dim-mono-mul
             sort-dims-when-dim-mono-sortedp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-coeff-properties
  :short "Properties of the coefficients of monomials in polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every monomial has coefficient 0 in the empty polynomial.
     In a non-empty polynomial,
     the monomial of the first term, i.e. of the head of the omap,
     has the coefficient of that term,
     while every other monomial has the coefficient that it has
     in the rest of the polynomial, i.e. in the tail of the omap.
     The monomial of the first term has coefficient 0 in the rest,
     because the keys of an omap are unique.")
   (xdoc::p
    "We prove how the coefficients change
     when an entry of the polynomial is updated or deleted,
     and thus when a term is added to the polynomial.
     From that, we prove that
     the coefficients of the sum of two polynomials
     are the sums of the coefficients of the two polynomials,
     and that the coefficients of the negation of a polynomial
     are the negations of the coefficients of the polynomial."))

  (defruled dim-poly-coeff-when-emptyp
    (implies (omap::emptyp (dim-poly-fix poly))
             (equal (dim-poly-coeff mono poly)
                    0))
    :enable dim-poly-coeff)

  (defruled dim-poly-coeff-when-not-emptyp
    (implies (not (omap::emptyp (dim-poly-fix poly)))
             (equal (dim-poly-coeff mono poly)
                    (if (equal (dim-list-fix mono)
                               (mv-nth 0 (omap::head poly)))
                        (mv-nth 1 (omap::head poly))
                      (dim-poly-coeff mono (omap::tail poly)))))
    :enable (dim-poly-coeff
             omap::assoc))

  (defruled dim-poly-coeff-of-tail-when-head-key
    (implies (and (dim-polyp poly)
                  (equal (dim-list-fix mono)
                         (mv-nth 0 (omap::head poly))))
             (equal (dim-poly-coeff mono (omap::tail poly))
                    0))
    :enable dim-poly-coeff
    :disable omap::head-key-not-assoc-tail
    :use (:instance omap::head-key-not-assoc-tail (omap::map poly)))

  (defruled dim-poly-coeff-of-update
    (implies (and (dim-polyp poly)
                  (dim-listp mono)
                  (integerp coeff))
             (equal (dim-poly-coeff mono1 (omap::update mono coeff poly))
                    (if (equal (dim-list-fix mono1) mono)
                        coeff
                      (dim-poly-coeff mono1 poly))))
    :enable dim-poly-coeff)

  (defruled dim-poly-coeff-of-delete
    (implies (dim-polyp poly)
             (equal (dim-poly-coeff mono1 (omap::delete mono poly))
                    (if (equal (dim-list-fix mono1) mono)
                        0
                      (dim-poly-coeff mono1 poly))))
    :enable dim-poly-coeff)

  (defruled dim-poly-coeff-of-dim-poly-add-term
    (equal (dim-poly-coeff mono1 (dim-poly-add-term mono coeff poly))
           (if (equal (dim-list-fix mono1)
                      (dim-list-fix mono))
               (+ (ifix coeff)
                  (dim-poly-coeff mono poly))
             (dim-poly-coeff mono1 poly)))
    :enable (dim-poly-add-term
             dim-poly-coeff-of-update
             dim-poly-coeff-of-delete))

  (defruled dim-poly-coeff-of-dim-poly-add
    (equal (dim-poly-coeff mono (dim-poly-add poly1 poly2))
           (+ (dim-poly-coeff mono poly1)
              (dim-poly-coeff mono poly2)))
    :induct t
    :enable (dim-poly-add
             dim-poly-coeff-of-dim-poly-add-term
             dim-poly-coeff-when-emptyp
             dim-poly-coeff-when-not-emptyp
             dim-poly-coeff-of-tail-when-head-key))

  (defruled dim-poly-coeff-of-dim-poly-neg
    (equal (dim-poly-coeff mono (dim-poly-neg poly))
           (- (dim-poly-coeff mono poly)))
    :induct t
    :enable (dim-poly-neg
             dim-poly-coeff-of-update
             dim-poly-coeff-when-emptyp
             dim-poly-coeff-when-not-emptyp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-canonicalp ((poly dim-polyp))
  :returns (yes/no booleanp)
  :short "Check if a polynomial is in canonical representation."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the monomials must be sorted,
     and all the coefficients must be nonzero
     (see @(see dimension-polynomials)).
     The order of the terms is determined by the omap."))
  (b* (((when (omap::emptyp (dim-poly-fix poly))) t)
       ((mv mono coeff) (omap::head poly)))
    (and (dim-mono-sortedp mono)
         (not (equal coeff 0))
         (dim-poly-canonicalp (omap::tail poly))))

  ///

  (defrule dim-poly-canonicalp-of-nil
    (dim-poly-canonicalp nil))

  (defruled dim-poly-canonicalp-of-update
    (implies (and (dim-polyp poly)
                  (dim-poly-canonicalp poly)
                  (dim-listp mono)
                  (dim-mono-sortedp mono)
                  (integerp coeff)
                  (not (equal coeff 0)))
             (dim-poly-canonicalp (omap::update mono coeff poly)))
    :induct (dim-poly-canonicalp poly)
    :expand ((dim-poly-canonicalp (omap::update mono coeff poly))))

  (defruled dim-poly-canonicalp-of-delete
    (implies (and (dim-polyp poly)
                  (dim-poly-canonicalp poly))
             (dim-poly-canonicalp (omap::delete mono poly)))
    :induct t
    :enable (omap::delete
             dim-poly-canonicalp-of-update))

  (defruled not-zero-cdr-assoc-when-dim-poly-canonicalp
    (implies (and (dim-polyp poly)
                  (dim-poly-canonicalp poly)
                  (omap::assoc mono poly))
             (not (equal (cdr (omap::assoc mono poly)) 0)))
    :induct t
    :enable omap::assoc))

;;;;;;;;;;;;;;;;;;;;

(std::deflist dim-poly-list-canonicalp (x)
  :short "Check if all the polynomials in a list
          are in canonical representation."
  :guard (dim-poly-listp x)
  (dim-poly-canonicalp x)
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-extensionality
  :short "Extensionality of polynomials in canonical representation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two polynomials in canonical representation are equal
     exactly when they have the same coefficients for all monomials.
     We express this as a rewrite rule that turns
     the equality of the two polynomials into
     the equality of their coefficients for a monomial
     that depends on the two polynomials:
     it is the witness of the "
    (xdoc::seetopic "omap::extensionality" "extensionality of omaps")
    ", from which this rule is derived.
     The absence of zero coefficients is critical:
     it makes the entry of a monomial in a polynomial, or the lack thereof,
     determined by the coefficient of the monomial."))

  (defruled assoc-to-dim-poly-coeff
    (implies (and (dim-polyp poly)
                  (dim-poly-canonicalp poly))
             (equal (omap::assoc mono poly)
                    (if (and (dim-listp mono)
                             (not (equal (dim-poly-coeff mono poly) 0)))
                        (cons mono (dim-poly-coeff mono poly))
                      nil)))
    :enable dim-poly-coeff
    :use (not-zero-cdr-assoc-when-dim-poly-canonicalp
          (:instance acl2::cons-car-cdr (acl2::x (omap::assoc mono poly)))))

  (defruled dim-poly-extensionality
    (implies (and (dim-polyp poly1)
                  (dim-polyp poly2)
                  (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2))
             (equal (equal poly1 poly2)
                    (let ((mono (omap::ext-equal-witness poly1 poly2)))
                      (equal (dim-poly-coeff mono poly1)
                             (dim-poly-coeff mono poly2)))))
    :use (:instance omap::extensionality (omap::x poly1) (omap::y poly2))
    :enable assoc-to-dim-poly-coeff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-canonicalp-of-operations
  :short "Preservation of the canonical representation of polynomials
          by the operations on polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "Adding a term with a sorted monomial,
     adding two polynomials,
     negating a polynomial,
     and subtracting a polynomial from another,
     preserve the canonical representation.
     Multiplying a polynomial by a term, or by another polynomial,
     always yields a polynomial in canonical representation,
     because the result is built by adding terms
     whose monomials are products, which are sorted.
     The constant polynomials and the polynomials with a single factor
     are in canonical representation."))

  (defrule dim-poly-canonicalp-of-dim-poly-add-term
    (implies (and (dim-poly-canonicalp poly)
                  (dim-mono-sortedp mono))
             (dim-poly-canonicalp (dim-poly-add-term mono coeff poly)))
    :enable (dim-poly-add-term
             dim-poly-canonicalp-of-update
             dim-poly-canonicalp-of-delete))

  (defrule dim-poly-canonicalp-of-dim-poly-const
    (dim-poly-canonicalp (dim-poly-const coeff))
    :enable dim-poly-const)

  (defrule dim-poly-canonicalp-of-dim-poly-factor
    (dim-poly-canonicalp (dim-poly-factor factor))
    :enable dim-poly-factor)

  (defrule dim-poly-canonicalp-of-dim-poly-add
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2))
             (dim-poly-canonicalp (dim-poly-add poly1 poly2)))
    :induct t
    :enable (dim-poly-add
             dim-poly-canonicalp))

  (defrule dim-poly-canonicalp-of-dim-poly-neg
    (implies (dim-poly-canonicalp poly)
             (dim-poly-canonicalp (dim-poly-neg poly)))
    :induct t
    :enable (dim-poly-neg
             dim-poly-canonicalp
             dim-poly-canonicalp-of-update))

  (defrule dim-poly-canonicalp-of-dim-poly-sub
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2))
             (dim-poly-canonicalp (dim-poly-sub poly1 poly2)))
    :enable dim-poly-sub)

  (defrule dim-poly-canonicalp-of-dim-poly-mul-term
    (dim-poly-canonicalp (dim-poly-mul-term mono coeff poly))
    :induct t
    :enable dim-poly-mul-term)

  (defrule dim-poly-canonicalp-of-dim-poly-mul
    (dim-poly-canonicalp (dim-poly-mul poly1 poly2))
    :induct t
    :enable dim-poly-mul)

  (defrule dim-poly-canonicalp-of-dim-poly-list-sum
    (implies (dim-poly-list-canonicalp polys)
             (dim-poly-canonicalp (dim-poly-list-sum polys)))
    :induct t
    :enable dim-poly-list-sum)

  (defrule dim-poly-canonicalp-of-dim-poly-list-product
    (dim-poly-canonicalp (dim-poly-list-product polys))
    :expand ((dim-poly-list-product polys))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-addition-properties
  :short "Properties of the addition of polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The polynomials in canonical representation
     form an abelian group under addition:
     addition is commutative and associative,
     the zero polynomial (i.e. the empty omap) is its identity,
     and the negation of a polynomial is its additive inverse.
     The zero polynomial is a right identity for all polynomials,
     not only for the ones in canonical representation,
     because @(tsee dim-poly-add) returns its first argument
     when its second argument is the zero polynomial.
     It is a left identity for all canonical polynomials,
     but not for all polynomials:
     adding a polynomial to the zero polynomial
     removes the terms with coefficient 0 from the former.
     The sum of two constant polynomials is
     the constant polynomial of the sum of the constants.")
   (xdoc::p
    "These properties are proved via @(see dim-poly-extensionality),
     which reduces them to the same properties of the integers,
     given that the coefficients of sums and negations
     are the sums and negations of the coefficients.
     The same holds for the properties of the addition of single terms,
     which relate it to the addition of polynomials."))

  (defruled commutativity-of-dim-poly-add
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2))
             (equal (dim-poly-add poly1 poly2)
                    (dim-poly-add poly2 poly1)))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add))

  (defruled associativity-of-dim-poly-add
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2)
                  (dim-poly-canonicalp poly3))
             (equal (dim-poly-add (dim-poly-add poly1 poly2) poly3)
                    (dim-poly-add poly1 (dim-poly-add poly2 poly3))))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add))

  (defruled commutativity-2-of-dim-poly-add
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2)
                  (dim-poly-canonicalp poly3))
             (equal (dim-poly-add poly1 (dim-poly-add poly2 poly3))
                    (dim-poly-add poly2 (dim-poly-add poly1 poly3))))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add))

  (defruled dim-poly-add-of-nil-left
    (implies (dim-poly-canonicalp poly)
             (equal (dim-poly-add nil poly)
                    (dim-poly-fix poly)))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add
             dim-poly-coeff-when-emptyp))

  (defruled dim-poly-add-of-nil-right
    (equal (dim-poly-add poly nil)
           (dim-poly-fix poly))
    :enable dim-poly-add)

  (defruled dim-poly-add-of-dim-poly-neg
    (implies (dim-poly-canonicalp poly)
             (equal (dim-poly-add poly (dim-poly-neg poly))
                    nil))
    :use (:instance dim-poly-extensionality
                    (poly1 (dim-poly-add poly (dim-poly-neg poly)))
                    (poly2 nil))
    :enable (dim-poly-coeff-of-dim-poly-add
             dim-poly-coeff-of-dim-poly-neg
             dim-poly-coeff-when-emptyp))

  (defruled dim-poly-add-term-of-dim-poly-add-term
    (implies (and (dim-poly-canonicalp poly)
                  (dim-mono-sortedp mono1)
                  (dim-mono-sortedp mono2))
             (equal (dim-poly-add-term mono1
                                       coeff1
                                       (dim-poly-add-term mono2
                                                          coeff2
                                                          poly))
                    (dim-poly-add-term mono2
                                       coeff2
                                       (dim-poly-add-term mono1
                                                          coeff1
                                                          poly))))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add-term))

  (defruled dim-poly-add-term-of-dim-poly-add-term-same
    (implies (and (dim-poly-canonicalp poly)
                  (dim-mono-sortedp mono))
             (equal (dim-poly-add-term mono
                                       coeff1
                                       (dim-poly-add-term mono
                                                          coeff2
                                                          poly))
                    (dim-poly-add-term mono
                                       (+ (ifix coeff1) (ifix coeff2))
                                       poly)))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add-term))

  (defruled dim-poly-add-term-of-0
    (implies (and (dim-poly-canonicalp poly)
                  (dim-mono-sortedp mono))
             (equal (dim-poly-add-term mono 0 poly)
                    (dim-poly-fix poly)))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add-term))

  (defruled dim-poly-add-of-dim-poly-add-term-left
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2)
                  (dim-mono-sortedp mono))
             (equal (dim-poly-add (dim-poly-add-term mono coeff poly1) poly2)
                    (dim-poly-add-term mono coeff (dim-poly-add poly1 poly2))))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add
             dim-poly-coeff-of-dim-poly-add-term))

  (defruled dim-poly-add-of-dim-poly-add-term-right
    (implies (and (dim-poly-canonicalp poly1)
                  (dim-poly-canonicalp poly2)
                  (dim-mono-sortedp mono))
             (equal (dim-poly-add poly1 (dim-poly-add-term mono coeff poly2))
                    (dim-poly-add-term mono coeff (dim-poly-add poly1 poly2))))
    :enable (dim-poly-extensionality
             dim-poly-coeff-of-dim-poly-add
             dim-poly-coeff-of-dim-poly-add-term))

  (defruled dim-poly-add-term-of-head-and-tail
    (implies (and (dim-polyp poly)
                  (dim-poly-canonicalp poly)
                  (not (omap::emptyp poly)))
             (equal (dim-poly-add-term (mv-nth 0 (omap::head poly))
                                       (mv-nth 1 (omap::head poly))
                                       (omap::tail poly))
                    poly))
    :use (lemma
          (:instance omap::update-of-head-and-tail (omap::map poly)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (dim-polyp poly)
                     (dim-poly-canonicalp poly)
                     (not (omap::emptyp poly)))
                (equal (dim-poly-add-term (mv-nth 0 (omap::head poly))
                                          (mv-nth 1 (omap::head poly))
                                          (omap::tail poly))
                       (omap::update (mv-nth 0 (omap::head poly))
                                     (mv-nth 1 (omap::head poly))
                                     (omap::tail poly))))
       :enable (dim-poly-add-term
                dim-poly-canonicalp
                dim-poly-coeff-of-tail-when-head-key))))

  (defruled dim-poly-const-of-0
    (equal (dim-poly-const 0)
           nil))

  (defruled dim-poly-add-of-dim-poly-const-and-dim-poly-const
    (equal (dim-poly-add (dim-poly-const coeff1) (dim-poly-const coeff2))
           (dim-poly-const (+ (ifix coeff1) (ifix coeff2))))
    :enable (dim-poly-const
             dim-poly-add-of-dim-poly-add-term-left
             dim-poly-add-of-nil-left
             dim-poly-add-term-of-dim-poly-add-term-same)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-mul-term-properties
  :short "Properties of the multiplication of polynomials by terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key property is that multiplication by a term
     distributes over the addition of a term to a polynomial:
     the result is obtained by adding the product of the two terms
     to the product of the first term and the polynomial.
     This holds for all polynomials, not only for the ones
     in canonical representation.")
   (xdoc::p
    "Since adding a term to a polynomial
     updates or deletes an entry of the omap,
     while multiplication by a term goes through the entries of the omap,
     we prove that property in steps.
     First, we consider the update of an omap with a new key,
     by induction on the omap,
     via an induction scheme for @(tsee omap::update) from the omap library:
     the new entry contributes the product of the two terms,
     which commutes with the contributions of the other entries.
     Second, we consider the deletion of a key from an omap,
     again by induction on the omap:
     we express the result by adding the negation of
     the contribution of the entry (if any) with that key,
     using the previous step for the smallest entry of the omap,
     which the deletion re-adds to the rest of the omap.
     Third, we consider an arbitrary update of an omap,
     which amounts to a deletion followed by an update with a new key.
     The property then follows by cases on
     whether the addition of the term updates or deletes the entry;
     the case split is on whether the coefficient of the added term
     is the opposite of the coefficient in the polynomial,
     which lets ACL2 replace the former with the latter.")
   (xdoc::p
    "From that property, we prove that multiplication by a term
     distributes over the addition of polynomials,
     and that two multiplications by terms
     amount to one multiplication by the product of the terms.
     We also prove that multiplication by the term
     with the empty monomial and coefficient 1
     leaves a polynomial in canonical representation unchanged."))

  (defruled dim-poly-mul-term-when-emptyp
    (implies (omap::emptyp (dim-poly-fix poly))
             (equal (dim-poly-mul-term mono coeff poly)
                    nil))
    :enable dim-poly-mul-term)

  (defruled dim-poly-mul-term-of-update-when-not-assoc
    (implies (and (dim-polyp poly)
                  (dim-listp mono1)
                  (integerp coeff1)
                  (not (omap::assoc mono1 poly)))
             (equal (dim-poly-mul-term mono
                                       coeff
                                       (omap::update mono1 coeff1 poly))
                    (dim-poly-add-term (dim-mono-mul mono mono1)
                                       (* (ifix coeff) coeff1)
                                       (dim-poly-mul-term mono coeff poly))))
    :induct t
    :expand ((dim-poly-mul-term mono coeff (omap::update mono1 coeff1 poly))
             (dim-poly-mul-term mono coeff poly))
    :enable (dim-poly-mul-term-when-emptyp
             dim-poly-add-term-of-dim-poly-add-term)
    :prep-lemmas
    ((defrule lemma
       (implies (and (dim-listp mono1)
                     (integerp coeff1))
                (equal (dim-poly-mul-term mono
                                          coeff
                                          (omap::update mono1 coeff1 nil))
                       (dim-poly-add-term (dim-mono-mul mono mono1)
                                          (* (ifix coeff) coeff1)
                                          nil)))
       :expand ((dim-poly-mul-term mono
                                   coeff
                                   (omap::update mono1 coeff1 nil)))
       :enable dim-poly-mul-term-when-emptyp)))

  (defruled dim-poly-mul-term-of-delete
    (implies (and (dim-polyp poly)
                  (dim-listp mono1))
             (equal (dim-poly-mul-term mono coeff (omap::delete mono1 poly))
                    (dim-poly-add-term
                     (dim-mono-mul mono mono1)
                     (- (* (ifix coeff) (dim-poly-coeff mono1 poly)))
                     (dim-poly-mul-term mono coeff poly))))
    :induct t
    :enable (dim-poly-mul-term
             omap::delete
             dim-poly-mul-term-of-update-when-not-assoc
             dim-poly-coeff-when-emptyp
             dim-poly-coeff-when-not-emptyp
             dim-poly-add-term-of-dim-poly-add-term
             dim-poly-add-term-of-dim-poly-add-term-same
             dim-poly-add-term-of-0))

  (defruled dim-poly-mul-term-of-update
    (implies (and (dim-polyp poly)
                  (dim-listp mono1)
                  (integerp coeff1))
             (equal (dim-poly-mul-term mono
                                       coeff
                                       (omap::update mono1 coeff1 poly))
                    (dim-poly-add-term
                     (dim-mono-mul mono mono1)
                     (- (* (ifix coeff) coeff1)
                        (* (ifix coeff) (dim-poly-coeff mono1 poly)))
                     (dim-poly-mul-term mono coeff poly))))
    :use (:instance dim-poly-mul-term-of-update-when-not-assoc
                    (poly (omap::delete mono1 poly)))
    :enable (dim-poly-mul-term-of-delete
             dim-poly-add-term-of-dim-poly-add-term-same))

  (defruled dim-poly-mul-term-of-dim-poly-add-term
    (equal (dim-poly-mul-term mono
                              coeff
                              (dim-poly-add-term mono1 coeff1 poly))
           (dim-poly-add-term (dim-mono-mul mono mono1)
                              (* (ifix coeff) (ifix coeff1))
                              (dim-poly-mul-term mono coeff poly)))
    :use (:instance lemma (coeff1 (ifix coeff1)))
    :prep-lemmas
    ((defruled lemma
       (implies (integerp coeff1)
                (equal (dim-poly-mul-term
                        mono
                        coeff
                        (dim-poly-add-term mono1 coeff1 poly))
                       (dim-poly-add-term
                        (dim-mono-mul mono mono1)
                        (* (ifix coeff) coeff1)
                        (dim-poly-mul-term mono coeff poly))))
       :cases ((equal coeff1 (- (dim-poly-coeff mono1 poly))))
       :expand ((:free (coeff1) (dim-poly-add-term mono1 coeff1 poly)))
       :enable (dim-poly-mul-term-of-update
                dim-poly-mul-term-of-delete))))

  (defruled dim-poly-mul-term-of-dim-poly-add
    (equal (dim-poly-mul-term mono coeff (dim-poly-add poly1 poly2))
           (dim-poly-add (dim-poly-mul-term mono coeff poly1)
                         (dim-poly-mul-term mono coeff poly2)))
    :induct t
    :enable (dim-poly-add
             dim-poly-mul-term-of-dim-poly-add-term
             dim-poly-mul-term-when-emptyp
             dim-poly-add-of-nil-right
             dim-poly-add-of-dim-poly-add-term-left
             dim-poly-add-of-dim-poly-add-term-right)
    :expand ((dim-poly-mul-term mono coeff poly2)))

  (defruled dim-poly-mul-term-of-dim-poly-mul-term
    (equal (dim-poly-mul-term mono1
                              coeff1
                              (dim-poly-mul-term mono2 coeff2 poly))
           (dim-poly-mul-term (dim-mono-mul mono1 mono2)
                              (* (ifix coeff1) (ifix coeff2))
                              poly))
    :induct t
    :enable (dim-poly-mul-term
             dim-poly-mul-term-of-dim-poly-add-term
             associativity-of-dim-mono-mul))

  (defruled dim-poly-mul-term-of-nil-and-1
    (implies (dim-poly-canonicalp poly)
             (equal (dim-poly-mul-term nil 1 poly)
                    (dim-poly-fix poly)))
    :induct t
    :enable (dim-poly-mul-term
             dim-poly-canonicalp
             dim-poly-fix
             dim-mono-mul-of-nil-when-dim-mono-sortedp
             dim-poly-add-term-of-head-and-tail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-multiplication-properties
  :short "Properties of the multiplication of polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "Multiplication is commutative and associative,
     and distributes over addition,
     for all polynomials, not only for the ones in canonical representation:
     its results are always in canonical representation,
     and the terms with zero coefficients, as well as the order of the factors,
     do not affect them.
     The constant polynomial 1 is the identity of multiplication,
     for the polynomials in canonical representation.
     The product of two constant polynomials is
     the constant polynomial of the product of the constants.")
   (xdoc::p
    "Multiplication is defined by recursion on its first argument:
     it adds the product of the first term and the second argument
     to the product of the rest of the first argument
     and the second argument.
     Thus, left distributivity,
     i.e. the fact that multiplication by a polynomial on the left
     distributes over addition,
     follows by induction from the analogous property of
     the multiplication by a term.
     To prove commutativity,
     we prove that multiplication can be equivalently unfolded
     on its second argument,
     which follows from how multiplication treats
     an update of its second argument with a new key,
     since a non-empty omap is the update of its tail with its head;
     commutativity then follows by induction.
     Right distributivity follows from left distributivity and commutativity.
     Associativity follows by induction from right distributivity
     and from the fact that multiplication by a term
     can be moved inside or outside a multiplication by a polynomial,
     which follows from how multiplication treats
     the addition of a term to its first argument."))

  (defruled dim-poly-mul-when-emptyp-left
    (implies (omap::emptyp (dim-poly-fix poly1))
             (equal (dim-poly-mul poly1 poly2)
                    nil))
    :enable dim-poly-mul)

  (defruled dim-poly-mul-when-emptyp-right
    (implies (omap::emptyp (dim-poly-fix poly2))
             (equal (dim-poly-mul poly1 poly2)
                    nil))
    :induct t
    :enable (dim-poly-mul
             dim-poly-mul-term-when-emptyp))

  (defruled dim-poly-mul-of-dim-poly-add-right
    (equal (dim-poly-mul poly (dim-poly-add poly1 poly2))
           (dim-poly-add (dim-poly-mul poly poly1)
                         (dim-poly-mul poly poly2)))
    :induct t
    :enable (dim-poly-mul
             dim-poly-mul-term-of-dim-poly-add
             associativity-of-dim-poly-add
             commutativity-of-dim-poly-add
             commutativity-2-of-dim-poly-add))

  (defruled dim-poly-mul-of-update-when-not-assoc
    (implies (and (dim-polyp poly2)
                  (dim-listp mono)
                  (integerp coeff)
                  (not (omap::assoc mono poly2)))
             (equal (dim-poly-mul poly1 (omap::update mono coeff poly2))
                    (dim-poly-add (dim-poly-mul-term mono coeff poly1)
                                  (dim-poly-mul poly1 poly2))))
    :induct t
    :enable (dim-poly-mul
             dim-poly-mul-term
             dim-poly-mul-term-of-update-when-not-assoc
             dim-poly-add-of-dim-poly-add-term-left
             commutativity-of-dim-poly-add
             commutativity-2-of-dim-poly-add
             commutativity-of-dim-mono-mul))

  (defruled dim-poly-mul-when-not-emptyp-right
    (implies (and (dim-polyp poly2)
                  (not (omap::emptyp poly2)))
             (equal (dim-poly-mul poly1 poly2)
                    (dim-poly-add
                     (dim-poly-mul-term (mv-nth 0 (omap::head poly2))
                                        (mv-nth 1 (omap::head poly2))
                                        poly1)
                     (dim-poly-mul poly1 (omap::tail poly2)))))
    :use ((:instance dim-poly-mul-of-update-when-not-assoc
                     (poly2 (omap::tail poly2))
                     (mono (mv-nth 0 (omap::head poly2)))
                     (coeff (mv-nth 1 (omap::head poly2))))
          (:instance omap::update-of-head-and-tail (omap::map poly2))))

  (defruled commutativity-of-dim-poly-mul
    (equal (dim-poly-mul poly1 poly2)
           (dim-poly-mul poly2 poly1))
    :induct t
    :expand ((dim-poly-mul poly1 poly2))
    :enable ((:induction dim-poly-mul)
             dim-poly-mul-when-emptyp-right
             dim-poly-mul-when-not-emptyp-right))

  (defruled dim-poly-mul-of-dim-poly-add-left
    (equal (dim-poly-mul (dim-poly-add poly1 poly2) poly)
           (dim-poly-add (dim-poly-mul poly1 poly)
                         (dim-poly-mul poly2 poly)))
    :use ((:instance commutativity-of-dim-poly-mul
                     (poly1 (dim-poly-add poly1 poly2))
                     (poly2 poly))
          dim-poly-mul-of-dim-poly-add-right
          (:instance commutativity-of-dim-poly-mul
                     (poly1 poly)
                     (poly2 poly1))
          (:instance commutativity-of-dim-poly-mul
                     (poly1 poly)
                     (poly2 poly2))))

  (defruled dim-poly-mul-of-dim-poly-add-term-right
    (equal (dim-poly-mul poly1 (dim-poly-add-term mono coeff poly2))
           (dim-poly-add (dim-poly-mul-term mono coeff poly1)
                         (dim-poly-mul poly1 poly2)))
    :induct t
    :enable (dim-poly-mul
             dim-poly-mul-term
             dim-poly-mul-term-of-dim-poly-add-term
             dim-poly-add-of-dim-poly-add-term-left
             commutativity-of-dim-poly-add
             commutativity-2-of-dim-poly-add
             commutativity-of-dim-mono-mul))

  (defruled dim-poly-mul-of-dim-poly-add-term-left
    (equal (dim-poly-mul (dim-poly-add-term mono coeff poly1) poly2)
           (dim-poly-add (dim-poly-mul-term mono coeff poly2)
                         (dim-poly-mul poly1 poly2)))
    :use ((:instance commutativity-of-dim-poly-mul
                     (poly1 (dim-poly-add-term mono coeff poly1)))
          (:instance dim-poly-mul-of-dim-poly-add-term-right
                     (poly1 poly2)
                     (poly2 poly1))
          commutativity-of-dim-poly-mul))

  (defruled dim-poly-mul-of-dim-poly-mul-term
    (equal (dim-poly-mul (dim-poly-mul-term mono coeff poly1) poly2)
           (dim-poly-mul-term mono coeff (dim-poly-mul poly1 poly2)))
    :induct t
    :enable (dim-poly-mul
             dim-poly-mul-term
             dim-poly-mul-of-dim-poly-add-term-left
             dim-poly-mul-term-of-dim-poly-add
             dim-poly-mul-term-of-dim-poly-mul-term))

  (defruled associativity-of-dim-poly-mul
    (equal (dim-poly-mul (dim-poly-mul poly1 poly2) poly3)
           (dim-poly-mul poly1 (dim-poly-mul poly2 poly3)))
    :induct t
    :enable (dim-poly-mul
             dim-poly-mul-of-dim-poly-add-left
             dim-poly-mul-of-dim-poly-mul-term))

  (defruled dim-poly-mul-of-dim-poly-const-1-left
    (implies (dim-poly-canonicalp poly)
             (equal (dim-poly-mul (dim-poly-const 1) poly)
                    (dim-poly-fix poly)))
    :enable (dim-poly-const
             dim-poly-mul-of-dim-poly-add-term-left
             dim-poly-mul-when-emptyp-left
             dim-poly-add-of-nil-right
             dim-poly-mul-term-of-nil-and-1)
    :disable ((:e dim-poly-const)
              (:e dim-poly-add-term)))

  (defruled dim-poly-mul-of-dim-poly-const-1-right
    (implies (dim-poly-canonicalp poly)
             (equal (dim-poly-mul poly (dim-poly-const 1))
                    (dim-poly-fix poly)))
    :use (dim-poly-mul-of-dim-poly-const-1-left
          (:instance commutativity-of-dim-poly-mul
                     (poly1 poly)
                     (poly2 (dim-poly-const 1)))))

  (defruled dim-poly-mul-of-dim-poly-const-and-dim-poly-const
    (equal (dim-poly-mul (dim-poly-const coeff1) (dim-poly-const coeff2))
           (dim-poly-const (* (ifix coeff1) (ifix coeff2))))
    :enable (dim-poly-const
             dim-poly-mul-of-dim-poly-add-term-left
             dim-poly-mul-term-of-dim-poly-add-term
             dim-poly-mul-when-emptyp-left
             dim-poly-mul-term-when-emptyp
             dim-poly-add-of-nil-right)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-list-sum-properties
  :short "Properties of the sum of lists of polynomials."

  (defruled dim-poly-list-sum-of-nil
    (equal (dim-poly-list-sum nil)
           nil))

  (defruled dim-poly-list-sum-of-cons
    (equal (dim-poly-list-sum (cons poly polys))
           (dim-poly-add poly (dim-poly-list-sum polys)))
    :enable dim-poly-list-sum))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-poly-list-product-properties
  :short "Properties of the product of lists of polynomials."

  (defruled dim-poly-list-product-of-nil
    (equal (dim-poly-list-product nil)
           (dim-poly-const 1)))

  (defruled dim-poly-list-product-of-cons
    (equal (dim-poly-list-product (cons poly polys))
           (dim-poly-mul poly (dim-poly-list-product polys)))
    :enable dim-poly-list-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dims-to-polys-properties
  :short "Properties of the translation of dimensions into polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The polynomials that dimensions are turned into
     are in canonical representation.")
   (xdoc::p
    "We also prove theorems that express
     the translation of each kind of dimension,
     and of empty and non-empty lists of dimensions.
     The theorem for subtractions is expressed in terms of
     the list of the polynomials of the operands,
     so that the polynomial is manifestly determined by that list."))

  (defthm-dims-to-polys-flag
    (defthm dim-poly-canonicalp-of-dim-to-poly
      (dim-poly-canonicalp (dim-to-poly dim))
      :flag dim-to-poly)
    (defthm dim-poly-list-canonicalp-of-dim-list-to-poly-list
      (dim-poly-list-canonicalp (dim-list-to-poly-list dims))
      :flag dim-list-to-poly-list)
    :hints (("Goal" :in-theory (enable dim-to-poly dim-list-to-poly-list))))

  (defruled dim-list-to-poly-list-of-nil
    (equal (dim-list-to-poly-list nil)
           nil))

  (defruled dim-list-to-poly-list-of-cons
    (equal (dim-list-to-poly-list (cons dim dims))
           (cons (dim-to-poly dim)
                 (dim-list-to-poly-list dims)))
    :enable dim-list-to-poly-list)

  (defruled consp-of-dim-list-to-poly-list
    (equal (consp (dim-list-to-poly-list dims))
           (consp dims))
    :expand ((dim-list-to-poly-list dims)))

  (defruled dim-to-poly-of-dim-const
    (equal (dim-to-poly (dim-const val))
           (dim-poly-const (nfix val)))
    :enable dim-to-poly)

  (defruled dim-to-poly-of-dim-add
    (equal (dim-to-poly (dim-add dims))
           (dim-poly-list-sum (dim-list-to-poly-list dims)))
    :expand ((dim-to-poly (dim-add dims))))

  (defruled dim-to-poly-of-dim-mul
    (equal (dim-to-poly (dim-mul dims))
           (dim-poly-list-product (dim-list-to-poly-list dims)))
    :expand ((dim-to-poly (dim-mul dims))))

  (defruled dim-to-poly-of-dim-sub
    (equal (dim-to-poly (dim-sub dims))
           (b* ((polys (dim-list-to-poly-list dims)))
             (cond ((endp polys) (dim-poly-factor (dim-sub nil)))
                   ((endp (cdr polys)) (dim-poly-neg (car polys)))
                   (t (dim-poly-sub (car polys)
                                    (dim-poly-list-sum (cdr polys)))))))
    :expand ((dim-to-poly (dim-sub dims))
             (dim-list-to-poly-list dims)
             (dim-list-to-poly-list (cdr dims))
             (dim-list-to-poly-list (dim-list-fix dims))
             (dim-list-to-poly-list (cdr (dim-list-fix dims))))))
