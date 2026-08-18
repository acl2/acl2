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

  (;; equivalence of dimensions:

   (refl ((dimp d))
         (dim= d d))

   (symm ((dimp d1) (dimp d2)
          (dim= d1 d2))
         (dim= d2 d1))

   (trans ((dimp d1) (dimp d2) (dimp d3)
           (dim= d1 d2) (dim= d2 d3))
          (dim= d1 d3))

   ;; equivalence of lists of dimensions:

   (refl ((dim-listp ds))
         (dims= ds ds))

   (symm ((dim-listp ds1) (dim-listp ds2)
          (dims= ds1 ds2))
         (dims= ds2 ds1))

   (trans ((dim-listp ds1) (dim-listp ds2) (dim-listp ds3)
           (dims= ds1 ds2) (dims= ds2 ds3))
          (dims= ds1 ds3))

   ;; congruence of dimensions:

   (cong-add ((dim-listp ds1) (dim-listp ds2)
              (dims= ds1 ds2))
             (dim= (dim-add ds1) (dim-add ds2)))

   (cong-sub ((dim-listp ds1) (dim-listp ds2)
              (dims= ds1 ds2))
             (dim= (dim-sub ds1) (dim-sub ds2)))

   (cong-mul ((dim-listp ds1) (dim-listp ds2)
              (dims= ds1 ds2))
             (dim= (dim-mul ds1) (dim-mul ds2)))

   ;; congruence of lists of dimensions:

   (cong-cons ((dimp d1) (dimp d2)
               (dim-listp ds1) (dim-listp ds2)
               (dim= d1 d2)
               (dims= ds1 ds2))
              (dims= (cons d1 ds1) (cons d2 ds2)))

   ;; normalization of addition:

   (add0 ()
         (dim= (dim+) (dim-const 0)))

   (add1 ((dimp d))
         (dim= (dim+ d) d))

   (add3m ((dimp d1) (dimp d2) (dimp d3) (dim-listp ds))
          (dim= (dim-add (list* d1 d2 d3 ds))
                (dim-add (cons (dim+ (dim+ d1 d2) d3) ds))))

   ;; normalization of multiplication:

   (mul0 ()
         (dim= (dim*) (dim-const 1)))

   (mul1 ((dimp d))
         (dim= (dim* d) d))

   (mul3m ((dimp d1) (dimp d2) (dimp d3) (dim-listp ds))
          (dim= (dim-mul (list* d1 d2 d3 ds))
                (dim-mul (cons (dim* (dim* d1 d2) d3) ds))))

   ;; normalization of subtraction:

   (sub2m ((dimp d) (dim-listp ds) (consp ds))
          (dim= (dim-sub (cons d ds))
                (dim+ d (dim- (dim-add ds)))))

   ;; abelian group properties of addition:

   (add-comm ((dimp d1) (dimp d2))
             (dim= (dim+ d1 d2)
                   (dim+ d2 d1)))

   (add-assoc ((dimp d1) (dimp d2) (dimp d3))
              (dim= (dim+ (dim+ d1 d2) d3)
                    (dim+ d1 (dim+ d2 d3))))

   (add-id ((dimp d))
           (dim= (dim+ 0 d) d))

   (add-inv ((dimp d))
            (dim= (dim+ d (dim- d))
                  (dim-const 0)))

   ;; addition of constants:

   (add-const ((natp n1) (natp n2))
              (dim= (dim+ (dim-const n1) (dim-const n2))
                    (dim-const (+ n1 n2))))

   ;; commutative monoid properties of multiplication:

   (mul-comm ((dimp d1) (dimp d2))
             (dim= (dim* d1 d2)
                   (dim* d2 d1)))

   (mul-assoc ((dimp d1) (dimp d2) (dimp d3))
              (dim= (dim* (dim* d1 d2) d3)
                    (dim* d1 (dim* d2 d3))))

   (mul-id ((dimp d))
           (dim= (dim* 1 d) d))

   ;; multiplication of constants:

   (mul-const ((natp n1) (natp n2))
              (dim= (dim* (dim-const n1) (dim-const n2))
                    (dim-const (* n1 n2))))

   ;; distributivity of multiplication over addition:

   (distrib ((dimp d) (dimp d1) (dimp d2))
            (dim= (dim* d (dim+ d1 d2))
                  (dim+ (dim* d d1) (dim* d d2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive shape/ispace-equiv-infrules
  :short "Equivalence of shapes, ispaces, and lists thereof."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially an equational theory over
     sequences (i.e. free monoid) of dimensions,
     but there are different ways to concatenate:
     turning sequences of dimensions to single shapes,
     concatenating shapes,
     and splicing ispaces into shapes.
     Because of the mutual recursion of shape and ispace ASTs,
     the inference rules are also mutually recursive.
     The following rules build upon
     the equivalence of dimensions and lists of dimensions,
     defined in @(see dim-equiv-infrules).")
   (xdoc::p
    "We start with the equivalence rules
     (reflexivity, symmetry, and transitivity),
     for shapes, lists of shapes, ispaces, and lists of ispaces.
     And congruence rules corresponding to the construction of
     shapes, ispaces, lists of shapes, and lists of ispaces.")
   (xdoc::p
    "We reduce the different forms of dimension concatenation to consist of
     (i) shape variables,
     (ii) shapes consisting of single dimensions,
     (iii) empty @('++') concatenations, and
     (iv) binary @('++') concatenations.
     The rules @('dims0') and @('dims2m') reduce
     shapes consisting of lists of zero or more dimensions
     to @('++') concatenations of zero or more shapes,
     each consisting of a single dimension.
     The rules @('append1') and @('append3m') reduce
     singleton @('++') concatenations to their single shapes
     and @('++') concatenations of three or more shapes to
     left-associated nests of binary @('++') concatenations.
     The rules @('splice0'), @('splice1m-dim'), and @('splice1m-shape') reduce
     splices to empty or binary @('++') concatenations.")
   (xdoc::p
    "With the above reductions available,
     we are in a standard situation with empty and binary concatenation,
     where the empty one plays the role of identity.
     We have rules for associativity as well as left and right identity.")
   (xdoc::p
    "Finally, the rule @('ispace-dim-shape') states the equivalence of
     a dimension ispace and a shape ispace that consists of that dimension."))

  :preds ((shp= shp1 shp2)
          (shps= shps1 shps2)
          (isp= isp1 isp2)
          (isps= isps1 isps2))

  :irules

  (;; equivalence of shapes:

   (refl ((shapep s))
         (shp= s s))

   (symm ((shapep s1) (shapep s2)
          (shp= s1 s2))
         (shp= s2 s1))

   (trans ((shapep s1) (shapep s2) (shapep s3)
           (shp= s1 s2) (shp= s2 s3))
          (shp= s1 s3))

   ;; equivalence of lists of shapes:

   (refl ((shape-listp ss))
         (shps= ss ss))

   (symm ((shape-listp ss1) (shape-listp ss2)
          (shps= ss1 ss2))
         (shps= ss2 ss1))

   (trans ((shape-listp ss1) (shape-listp ss2) (shape-listp ss3)
           (shps= ss1 ss2) (shps= ss2 ss3))
          (shps= ss1 ss3))

   ;; equivalence of ispaces:

   (refl ((ispacep i))
         (isp= i i))

   (symm ((ispacep i1) (ispacep i2)
          (isp= i1 i2))
         (isp= i2 i1))

   (trans ((ispacep i1) (ispacep i2) (ispacep i3)
           (isp= i1 i2) (isp= i2 i3))
          (isp= i1 i3))

   ;; equivalence of lists of ispaces:

   (refl ((ispace-listp is))
         (isps= is is))

   (symm ((ispace-listp is1) (ispace-listp is2)
          (isps= is1 is2))
         (isps= is2 is1))

   (trans ((ispace-listp is1) (ispace-listp is2) (ispace-listp is3)
           (isps= is1 is2) (isps= is2 is3))
          (isps= is1 is3))

   ;; congruence of shapes:

   (cong-dims ((dim-listp ds1) (dim-listp ds2)
               (dims= ds1 ds2))
              (shp= (shape-dims ds1) (shape-dims ds2)))

   (cong-append ((shape-listp ss1) (shape-listp ss2)
                 (shps= ss1 ss2))
                (shp= (shape-append ss1) (shape-append ss2)))

   (cong-splice ((ispace-listp is1) (ispace-listp is2)
                 (isps= is1 is2))
                (shp= (shape-splice is1) (shape-splice is2)))

   ;; congruence of ispaces:

   (cong-dim ((dimp d1) (dimp d2)
              (dim= d1 d2))
             (isp= (ispace-dim d1) (ispace-dim d2)))

   (cong-shape ((shapep s1) (shapep s2)
                (shp= s1 s2))
               (isp= (ispace-shape s1) (ispace-shape s2)))

   ;; congruence of lists of shapes:

   (cong-cons ((shapep s1) (shapep s2)
               (shape-listp ss1) (shape-listp ss2)
               (shp= s1 s2)
               (shps= ss1 ss2))
              (shps= (cons s1 ss1) (cons s2 ss2)))

   ;; congruence of lists of ispaces:

   (cong-cons ((ispacep i1) (ispacep i2)
               (ispace-listp is1) (ispace-listp is2)
               (isp= i1 i2)
               (isps= is1 is2))
              (isps= (cons i1 is1) (cons i2 is2)))

   ;; normalization of shapes built from dimensions:

   (dims0 ()
          (shp= (shp) (shp++)))

   (dims2m ((dimp d) (dim-listp ds) (consp ds))
           (shp= (shape-dims (cons d ds))
                 (shp++ (shp d) (shape-dims ds))))

   ;; normalization of non-empty and non-binary concatenations:

   (append1 ((shapep s))
            (shp= (shp++ s) s))

   (append3m ((shapep s1) (shapep s2) (shape-listp ss) (consp ss))
             (shp= (shape-append (list* s1 s2 ss))
                   (shape-append (cons (shp++ s1 s2) ss))))

   ;; normalization of splices:

   (splice0 ()
            (shp= (shp[]) (shp++)))

   (splice1m-dim ((dimp d) (ispace-listp is))
                 (shp= (shape-splice (cons (ispace-dim d) is))
                       (shp++ (shp d) (shape-splice is))))

   (splice1m-shape ((shapep s) (ispace-listp is))
                   (shp= (shape-splice (cons (ispace-shape s) is))
                         (shp++ s (shape-splice is))))

   ;; monoid properties of concatenation:

   (append-assoc ((shapep s1) (shapep s2) (shapep s3))
                 (shp= (shp++ (shp++ s1 s2) s3)
                       (shp++ s1 (shp++ s2 s3))))

   (append-id-left ((shapep s))
                   (shp= (shp++ (shp++) s) s))

   (append-id-right ((shapep s))
                    (shp= (shp++ s (shp++)) s))

   ;; equivalence of dimension ispace and singleton shape ispace:

   (ispace-dim-shape ((dimp d))
                     (isp= (ispace-dim d) (ispace-shape (shp d))))))
