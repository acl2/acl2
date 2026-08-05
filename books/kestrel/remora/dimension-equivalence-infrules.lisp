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

(defxdoc+ dimension-equivalence-inference-rules
  :parents (static-semantics)
  :short "Inference rules for dimension equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the equivalence of dimensions via inference rules.
     Although [thesis], [arxiv], and [esop] do not explicate these rules,
     their existence is arguably implied;
     those publications make use of judgements
     asserting the equivalence of ispaces (called `indices' there),
     and describe the equations according to which
     dimensions are considered equivalent.
     Unlike [impl], those publications only have addition,
     but our rules also include multiplication and subtraction."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dimeq-infrules
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

  :preds ((dimeq dim1 dim2)
          (dimseq dims1 dims2))

  :irules

  ((refl ((dimp x))
         (dimeq x x))

   (symm ((dimp x)
          (dimp y)
          (dimeq x y))
         (dimeq y x))

   (trans ((dimp x)
           (dimp y)
           (dimp z)
           (dimeq x y)
           (dimeq y z))
          (dimeq x z))

   (srefl ((dim-listp xs))
          (dimseq xs xs))

   (ssymm ((dim-listp xs)
           (dim-listp ys)
           (dimseq xs ys))
          (dimseq ys xs))

   (strans ((dim-listp xs)
            (dim-listp ys)
            (dim-listp zs)
            (dimseq xs ys)
            (dimseq ys zs))
           (dimseq xs zs))

   (cong-add ((dim-listp xs)
              (dim-listp ys)
              (dimseq xs ys))
             (dimeq (dim-add xs)
                    (dim-add ys)))

   (cong-sub ((dim-listp xs)
              (dim-listp ys)
              (dimseq xs ys))
             (dimeq (dim-sub xs)
                    (dim-sub ys)))

   (cong-mul ((dim-listp xs)
              (dim-listp ys)
              (dimseq xs ys))
             (dimeq (dim-mul xs)
                    (dim-mul ys)))

   (cong-cons ((dimp x)
               (dimp y)
               (dim-listp xs)
               (dim-listp ys)
               (dimeq x y)
               (dimseq xs ys))
              (dimseq (cons x xs)
                      (cons y ys)))

   (add0 ()
         (dimeq (dim+)
                (dim-const 0)))

   (add1 ((dimp x))
         (dimeq (dim+ x)
                x))

   (add3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp ws))
          (dimeq (dim-add (list* x y z ws))
                 (dim-add (cons (dim+ (dim+ x y) z) ws))))

   (mul0 ()
         (dimeq (dim*)
                (dim-const 1)))

   (mul1 ((dimp x))
         (dimeq (dim* x)
                x))

   (mul3m ((dimp x)
           (dimp y)
           (dimp z)
           (dim-listp ws))
          (dimeq (dim-mul (list* x y z ws))
                 (dim-mul (cons (dim* (dim* x y) z) ws))))

   (sub2m ((dimp x)
           (dim-listp ys)
           (consp ys))
          (dimeq (dim-sub (cons x ys))
                 (dim+ x (dim- (dim-add ys)))))

   (add-comm ((dimp x)
              (dimp y))
             (dimeq (dim+ x y)
                    (dim+ y x)))

   (add-assoc ((dimp x)
               (dimp y)
               (dimp z))
              (dimeq (dim+ (dim+ x y) z)
                     (dim+ x (dim+ y z))))

   (add-id ((dimp x))
           (dimeq (dim+ 0 x)
                  x))

   (add-inv ((dimp x))
            (dimeq (dim+ x (dim- x))
                   (dim-const 0)))

   (add-const ((natp d1)
               (natp d2))
              (dimeq (dim+ (dim-const d1) (dim-const d2))
                     (dim-const (+ d1 d2))))

   (mul-comm ((dimp x)
              (dimp y))
             (dimeq (dim* x y)
                    (dim* y x)))

   (mul-assoc ((dimp x)
               (dimp y)
               (dimp z))
              (dimeq (dim* (dim* x y) z)
                     (dim* x (dim* y z))))

   (mul-id ((dimp x))
           (dimeq (dim* 1 x)
                  x))

   (mul-const ((natp d1)
               (natp d2))
              (dimeq (dim* (dim-const d1) (dim-const d2))
                     (dim-const (* d1 d2))))

   (distrib ((dimp x)
             (dimp y)
             (dimp z))
            (dimeq (dim* x (dim+ y z))
                   (dim+ (dim* x y) (dim* x z))))))
