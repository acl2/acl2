; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-constructors")

(include-book "std/util/definductive" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-inference-rules
  :parents (static-semantics)
  :short "Inference rules for ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the equivalence of ispaces via inference rules.
     Although [thesis], [arxiv], and [esop] do not explicate these rules,
     their existence is arguably implied;
     those publications make use of judgements
     asserting the equivalence of ispaces (called `indices' there),
     and describe the equations according to which
     dimensions are considered equivalent.
     Unlike [impl], those publications only have addition of dimensions,
     but our rules also include their multiplication and subtraction."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dim-equiv-infrules
  :short "Equivalence of dimensions and lists of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially an equational theory over multivariate polynomials,
     with variadic additions and multiplications,
     with a Lisp-like notion of variadic subtraction,
     and with a homomorphic extension to lists.")
   (xdoc::p
    "We start with the obligatory equivalence rules
     (reflexivity, symmetry, and transitivity),
     for both dimensions and lists of dimensions,
     with congruence rules for the arithmetic operations,
     and with a congruence rule for list constructions.")
   (xdoc::p
    "We reduce all variadic additions to binary ones or to non-additions,
     via the rules @('add0'), @('add1'), and @('add3m').
     We do the same for multiplications,
     via the rules @('mul0'), @('mul1'), and @('mul3m').
     We reduce all variadic subtractions to unary ones:
     the nullary one is illegal (only equivalent to itself, via reflexivity);
     a subtraction of two or more dimensions reduces to
     the addition of the first one and
     the unary subtraction of the sum of the remaining ones,
     via the rule @('sub2m').")
   (xdoc::p
    "With the above reductions available,
     we are in a standard situation with binary addition and multiplication,
     and with negation (additive inverse).
     We have rules for:
     commutativity, associativity, and identity of addition and multiplication;
     distributivity of multiplication over addition;
     and inversion of addition.")
   (xdoc::p
    "We also have two rules to calculate
     additions and multiplications of constants.
     Technically the one for multiplication could be derived via induction,
     but we prefer to have it explicit."))

  :preds ((dim= dim1 dim2)
          (dims= dims1 dims2))

  :irules

  ((refl ((dimp x))
         (dim= x x))

   (symm ((dimp x)
          (dimp y)
          (dim= x y))
         (dim= y x))

   (trans ((dimp x)
           (dimp y)
           (dimp z)
           (dim= x y)
           (dim= y z))
          (dim= x z))

   (refl ((dim-listp xs))
         (dims= xs xs))

   (symm ((dim-listp xs)
          (dim-listp ys)
          (dims= xs ys))
         (dims= ys xs))

   (trans ((dim-listp xs)
           (dim-listp ys)
           (dim-listp zs)
           (dims= xs ys)
           (dims= ys zs))
          (dims= xs zs))

   (cong-add ((dim-listp xs)
              (dim-listp ys)
              (dims= xs ys))
             (dim= (dim-add xs)
                   (dim-add ys)))

   (cong-sub ((dim-listp xs)
              (dim-listp ys)
              (dims= xs ys))
             (dim= (dim-sub xs)
                   (dim-sub ys)))

   (cong-mul ((dim-listp xs)
              (dim-listp ys)
              (dims= xs ys))
             (dim= (dim-mul xs)
                   (dim-mul ys)))

   (cong-cons ((dimp x)
               (dimp y)
               (dim-listp xs)
               (dim-listp ys)
               (dim= x y)
               (dims= xs ys))
              (dims= (cons x xs)
                     (cons y ys)))

   (add0 ()
         (dim= (dim+)
               (dim-const 0)))

   (add1 ((dimp x))
         (dim= (dim+ x)
               x))

   (add3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp ws))
          (dim= (dim-add (list* x y z ws))
                (dim-add (cons (dim+ (dim+ x y) z) ws))))

   (mul0 ()
         (dim= (dim*)
               (dim-const 1)))

   (mul1 ((dimp x))
         (dim= (dim* x)
               x))

   (mul3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp ws))
          (dim= (dim-mul (list* x y z ws))
                (dim-mul (cons (dim* (dim* x y) z) ws))))

   (sub2m ((dimp x)
           (dim-listp ys)
           (consp ys))
          (dim= (dim-sub (cons x ys))
                (dim+ x (dim- (dim-add ys)))))

   (add-comm ((dimp x)
              (dimp y))
             (dim= (dim+ x y)
                   (dim+ y x)))

   (add-assoc ((dimp x)
               (dimp y)
               (dimp z))
              (dim= (dim+ (dim+ x y) z)
                    (dim+ x (dim+ y z))))

   (add-id ((dimp x))
           (dim= (dim+ 0 x)
                 x))

   (add-inv ((dimp x))
            (dim= (dim+ x (dim- x))
                  (dim-const 0)))

   (add-const ((natp d1)
               (natp d2))
              (dim= (dim+ (dim-const d1) (dim-const d2))
                    (dim-const (+ d1 d2))))

   (mul-comm ((dimp x)
              (dimp y))
             (dim= (dim* x y)
                   (dim* y x)))

   (mul-assoc ((dimp x)
               (dimp y)
               (dimp z))
              (dim= (dim* (dim* x y) z)
                    (dim* x (dim* y z))))

   (mul-id ((dimp x))
           (dim= (dim* 1 x)
                 x))

   (mul-const ((natp d1)
               (natp d2))
              (dim= (dim* (dim-const d1) (dim-const d2))
                    (dim-const (* d1 d2))))

   (distrib ((dimp x)
             (dimp y)
             (dimp z))
            (dim= (dim* x (dim+ y z))
                  (dim+ (dim* x y) (dim* x z))))))
