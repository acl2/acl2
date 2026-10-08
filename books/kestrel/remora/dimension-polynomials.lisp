; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/ifix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dimension-polynomials
  :parents (static-semantics)
  :short "Polynomials over the integers in the dimension variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence of dimensions (see @(see ispace-equivalence))
     is the equational theory of commutative rings with identity,
     with the natural number literals as numerals:
     the rules reduce the variadic operations to binary ones,
     and then assert the ring axioms
     and the evaluation of the operations on constants.
     Thus, two dimensions are equivalent exactly when
     they denote the same polynomial, with integer coefficients,
     in the dimension variables;
     the equivalence is decidable by comparing canonical forms.")
   (xdoc::p
    "Here we define a representation of such polynomials,
     along with the arithmetic operations on them,
     in which equal polynomials have identical representations.
     This is used to normalize dimensions
     (see @(see ispace-equivalence-checker)):
     a dimension is turned into the polynomial it denotes
     (see @(tsee dim-to-poly)),
     by interpreting its arithmetic operations
     as the corresponding operations on polynomials,
     and the polynomial is turned back into a dimension in canonical form
     (see @(tsee poly-to-dim)).")
   (xdoc::p
    "A monomial is represented as the list of its factors,
     sorted according to the total order of ACL2 values,
     with repeated factors for powers;
     a factor is a dimension variable,
     or the nullary subtraction as explained below.
     A polynomial is represented as an omap
     from monomials to their integer coefficients;
     the constant term is the omap entry for the empty monomial.
     The representation is canonical by construction:
     the order of the entries is determined by the omap,
     and the operations never produce an entry with a zero coefficient,
     i.e. a monomial that does not occur in the polynomial has no entry.")
   (xdoc::p
    "The nullary subtraction @('(-)') is not a valid dimension
     (see @(see ispace-validity)),
     but the normalization of dimensions must be defined on all dimensions,
     and the rules of dimension equivalence do not reduce @('(-)').
     Thus, we treat it as an additional indeterminate,
     i.e. as a factor just like a dimension variable.
     Since the rules of dimension equivalence quantify over all dimensions,
     this treatment is adequate for all dimensions, not only the valid ones.")
   (xdoc::p
    "Each step of the translation of a dimension into a polynomial
     is justified by a rule of dimension equivalence,
     and so is each step of the translation of a polynomial into a dimension.
     Thus, a dimension is equivalent to its canonical form,
     and two dimensions are equivalent exactly when
     they are turned into the same polynomial,
     i.e. when they have the same canonical form.
     We have not formally proved these facts yet."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sort-dims ((dims dim-listp))
  :returns (sorted-dims dim-listp)
  :short "Sort a list of dimensions, using ACL2's total order of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple insertion sort.
     We do not expect long lists."))
  (cond ((endp dims) nil)
        (t (sort-dims-aux (car dims) (sort-dims (cdr dims)))))
  :verify-guards :after-returns
  :prepwork
  ((define sort-dims-aux ((dim dimp) (dims dim-listp))
     :returns (dims-with-dim dim-listp)
     :parents nil
     (cond ((endp dims) (list (dim-fix dim)))
           ((<< (dim-fix dim) (dim-fix (car dims)))
            (cons (dim-fix dim) (dim-list-fix dims)))
           (t (cons (dim-fix (car dims))
                    (sort-dims-aux dim (cdr dims))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap dim-poly
  :short "Fixtype of polynomials in the dimension variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an omap,
     whose keys are the monomials, as sorted lists of factors,
     and whose values are their coefficients;
     see @(see dimension-polynomials)."))
  :key-type dim-list
  :val-type int
  :pred dim-polyp

  ///

  (defrule integerp-of-head-val-when-dim-polyp-type-prescription
    (implies (and (dim-polyp poly)
                  (not (omap::emptyp poly)))
             (integerp (mv-nth 1 (omap::head poly))))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist dim-poly-list
  :short "Fixtype of lists of polynomials in the dimension variables."
  :elt-type dim-poly
  :true-listp t
  :elementp-of-nil t
  :pred dim-poly-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-coeff ((mono dim-listp) (poly dim-polyp))
  :returns (coeff integerp)
  :short "Coefficient of a monomial in a polynomial."
  :long
  (xdoc::topstring
   (xdoc::p
    "The coefficient is 0 if the monomial has no entry in the polynomial."))
  (b* ((mono+coeff (omap::assoc (dim-list-fix mono) (dim-poly-fix poly))))
    (if mono+coeff
        (lifix (cdr mono+coeff))
      0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-add-term ((mono dim-listp)
                           (coeff integerp)
                           (poly dim-polyp))
  :returns (new-poly dim-polyp)
  :short "Add a term to a polynomial."
  :long
  (xdoc::topstring
   (xdoc::p
    "The term consists of a monomial and a coefficient.
     We add the coefficient to the one of the monomial in the polynomial
     (see @(tsee dim-poly-coeff)).
     If the sum is 0, we remove the entry of the monomial, if any;
     otherwise, we update the entry of the monomial with the sum.
     This maintains the canonical representation of polynomials
     (see @(see dimension-polynomials))."))
  (b* ((sum (+ (lifix coeff) (dim-poly-coeff mono poly)))
       (mono (dim-list-fix mono))
       (poly (dim-poly-fix poly)))
    (if (= sum 0)
        (omap::delete mono poly)
      (omap::update mono sum poly))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-const ((coeff integerp))
  :returns (poly dim-polyp)
  :short "Constant polynomial."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the polynomial with just a constant term,
     or the zero polynomial if the constant is 0."))
  (dim-poly-add-term nil coeff nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-factor ((factor dimp))
  :returns (poly dim-polyp)
  :short "Polynomial consisting of a single factor, with coefficient 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "The factor must be a dimension variable or the nullary subtraction
     (see @(see dimension-polynomials)):
     this is not enforced by the guard,
     but the canonical representation of polynomials relies on it."))
  (dim-poly-add-term (list (dim-fix factor)) 1 nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-add ((poly1 dim-polyp) (poly2 dim-polyp))
  :returns (poly dim-polyp)
  :short "Add two polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add each term of the second polynomial to the first polynomial."))
  (b* (((when (omap::emptyp (dim-poly-fix poly2))) (dim-poly-fix poly1))
       ((mv mono coeff) (omap::head poly2))
       (poly1 (dim-poly-add-term mono coeff poly1)))
    (dim-poly-add poly1 (omap::tail poly2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-neg ((poly dim-polyp))
  :returns (new-poly dim-polyp)
  :short "Negate a polynomial."
  :long
  (xdoc::topstring
   (xdoc::p
    "We negate all the coefficients."))
  (b* (((when (omap::emptyp (dim-poly-fix poly))) nil)
       ((mv mono coeff) (omap::head poly)))
    (omap::update (dim-list-fix mono)
                  (- (lifix coeff))
                  (dim-poly-neg (omap::tail poly))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-sub ((poly1 dim-polyp) (poly2 dim-polyp))
  :returns (poly dim-polyp)
  :short "Subtract a polynomial from another polynomial."
  (dim-poly-add poly1 (dim-poly-neg poly2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-mono-mul ((mono1 dim-listp) (mono2 dim-listp))
  :returns (mono dim-listp)
  :short "Multiply two monomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The factors of the product are the factors of the two monomials,
     sorted (see @(see dimension-polynomials))."))
  (sort-dims (append (dim-list-fix mono1) (dim-list-fix mono2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-mul-term ((mono dim-listp)
                           (coeff integerp)
                           (poly dim-polyp))
  :returns (new-poly dim-polyp)
  :short "Multiply a polynomial by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "We multiply each term of the polynomial by the term,
     adding the resulting terms."))
  (b* (((when (omap::emptyp (dim-poly-fix poly))) nil)
       ((mv mono1 coeff1) (omap::head poly)))
    (dim-poly-add-term (dim-mono-mul mono mono1)
                       (* (lifix coeff) (lifix coeff1))
                       (dim-poly-mul-term mono coeff (omap::tail poly))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-mul ((poly1 dim-polyp) (poly2 dim-polyp))
  :returns (poly dim-polyp)
  :short "Multiply two polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "We multiply the second polynomial by each term of the first polynomial
     (see @(tsee dim-poly-mul-term)),
     adding the resulting polynomials."))
  (b* (((when (omap::emptyp (dim-poly-fix poly1))) nil)
       ((mv mono coeff) (omap::head poly1)))
    (dim-poly-add (dim-poly-mul-term mono coeff poly2)
                  (dim-poly-mul (omap::tail poly1) poly2)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-list-sum ((polys dim-poly-listp))
  :returns (poly dim-polyp)
  :short "Add a list of polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sum of no polynomials is the zero polynomial."))
  (cond ((endp polys) nil)
        (t (dim-poly-add (car polys)
                         (dim-poly-list-sum (cdr polys)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-poly-list-product ((polys dim-poly-listp))
  :returns (poly dim-polyp)
  :short "Multiply a list of polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "The product of no polynomials is the constant polynomial 1."))
  (cond ((endp polys) (dim-poly-const 1))
        (t (dim-poly-mul (car polys)
                         (dim-poly-list-product (cdr polys)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dims-to-polys
  :short "Turn dimensions and lists of dimensions into polynomials."

  ;;;;;;;;;;;;;;;;;;;;

  (define dim-to-poly ((dim dimp))
    :returns (poly dim-polyp)
    :parents (dimension-polynomials dims-to-polys)
    :short "Turn a dimension into the polynomial it denotes."
    :long
    (xdoc::topstring
     (xdoc::p
      "We interpret the arithmetic operations of the dimension
       as the corresponding operations on polynomials
       (see @(see dimension-polynomials)).")
     (xdoc::p
      "A variable is a factor with coefficient 1
       and a constant is a constant polynomial.")
     (xdoc::p
      "An addition is the sum of the polynomials of its addends,
       and a multiplication is the product of the polynomials of its factors;
       the sum of no addends is 0, and the product of no factors is 1.")
     (xdoc::p
      "A subtraction is treated as in Common Lisp
       (see @(tsee integer-list-subtraction)):
       with one operand, it is the negation of the polynomial of the operand;
       with two or more operands, it is the polynomial of the first operand
       minus the sum of the polynomials of the other operands.
       The invalid subtraction with no operands is an indeterminate,
       i.e. a factor with coefficient 1,
       as explained in @(see dimension-polynomials)."))
    (dim-case
     dim
     :var (dim-poly-factor (dim-var dim.name))
     :const (dim-poly-const dim.val)
     :add (dim-poly-list-sum (dim-list-to-poly-list dim.dims))
     :mul (dim-poly-list-product (dim-list-to-poly-list dim.dims))
     :sub (cond ((endp dim.dims) (dim-poly-factor (dim-sub nil)))
                ((endp (cdr dim.dims))
                 (dim-poly-neg (dim-to-poly (car dim.dims))))
                (t (dim-poly-sub
                    (dim-to-poly (car dim.dims))
                    (dim-poly-list-sum
                     (dim-list-to-poly-list (cdr dim.dims)))))))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;

  (define dim-list-to-poly-list ((dims dim-listp))
    :returns (polys dim-poly-listp)
    :parents (dimension-polynomials dims-to-polys)
    :short "Turn a list of dimensions into
            the list of the polynomials they denote."
    (cond ((endp dims) nil)
          (t (cons (dim-to-poly (car dims))
                   (dim-list-to-poly-list (cdr dims)))))
    :measure (dim-list-count dims))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual dims-to-polys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define poly-to-dim ((poly dim-polyp))
  :returns (dim dimp)
  :short "Turn a polynomial into a dimension in canonical form."
  :long
  (xdoc::topstring
   (xdoc::p
    "A term with monomial @('(x1 ... xk)') and positive coefficient @('c')
     is turned into the dimension
     @('c') if there are no factors,
     @('x1') if @('c') is 1 and there is one factor,
     @('(* x1 ... xk)') if @('c') is 1 and there are two or more factors, and
     @('(* c x1 ... xk)') otherwise, i.e. with the coefficient first.")
   (xdoc::p
    "The terms with positive coefficients form
     the positive part of the polynomial,
     and the terms with negative coefficients, with the coefficients negated,
     form the negative part.
     Each part is turned into
     the dimension of its term if there is one term, or
     the addition of the dimensions of its terms if there are two or more,
     in the order of the entries of the polynomial,
     i.e. with the constant term (if any) first.
     The polynomial is turned into
     @('0') if both parts are empty,
     the positive part if the negative part is empty,
     the unary subtraction of the negative part if the positive part is empty,
     and the subtraction of the negative part from the positive part
     otherwise.")
   (xdoc::p
    "Since the representation of polynomials is canonical
     (see @(see dimension-polynomials)),
     equal polynomials are turned into identical dimensions;
     different polynomials are turned into different dimensions,
     so that comparing the resulting dimensions
     amounts to comparing the polynomials."))
  (b* (((mv pos-terms neg-terms) (poly-to-dim-parts poly)))
    (cond ((and (not (consp pos-terms))
                (not (consp neg-terms)))
           (dim-const 0))
          ((not (consp neg-terms))
           (poly-to-dim-sum pos-terms))
          ((not (consp pos-terms))
           (dim-sub (list (poly-to-dim-sum neg-terms))))
          (t (dim-sub (list (poly-to-dim-sum pos-terms)
                            (poly-to-dim-sum neg-terms))))))

  :prepwork

  ((define poly-to-dim-term ((mono dim-listp) (coeff posp))
     :returns (dim dimp)
     :parents nil
     (b* ((mono (dim-list-fix mono))
          (coeff (lposfix coeff)))
       (cond ((endp mono) (dim-const coeff))
             ((= coeff 1) (if (endp (cdr mono))
                              (car mono)
                            (dim-mul mono)))
             (t (dim-mul (cons (dim-const coeff) mono))))))

   (define poly-to-dim-parts ((poly dim-polyp))
     :returns (mv (pos-terms dim-listp)
                  (neg-terms dim-listp))
     :parents nil
     (b* (((when (omap::emptyp (dim-poly-fix poly))) (mv nil nil))
          ((mv mono coeff) (omap::head poly))
          ((mv pos-terms neg-terms)
           (poly-to-dim-parts (omap::tail poly))))
       (cond ((> coeff 0)
              (mv (cons (poly-to-dim-term mono coeff) pos-terms)
                  neg-terms))
             ((< coeff 0)
              (mv pos-terms
                  (cons (poly-to-dim-term mono (- coeff)) neg-terms)))
             (t (mv pos-terms neg-terms)))))

   (define poly-to-dim-sum ((terms dim-listp))
     :guard (consp terms)
     :returns (dim dimp)
     :parents nil
     (if (= (len terms) 1)
         (dim-fix (car terms))
       (dim-add terms)))))
