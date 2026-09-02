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

(defxdoc+ ispace-equivalence
  :parents (static-semantics)
  :short "Equivalence of ispaces."
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

(definductive dim-equivalence-definition
  :short "Inference rules that define dimension equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially an equational theory over multivariate polynomials,
     with variadic additions and multiplications,
     with a Lisp-like notion of variadic subtraction,
     and with a homomorphic extension to lists.")
   (xdoc::p
    "We start with the equivalence rules
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

  :preds ((dim-eq dim1 dim2)
          (dims-eq dims1 dims2))

  :irules

  (;; equivalence of dimensions:

   (refl ((dimp dim))
         (dim-eq dim dim))

   (symm ((dimp dim1) (dimp dim2)
          (dim-eq dim1 dim2))
         (dim-eq dim2 dim1))

   (trans ((dimp dim1) (dimp dim2) (dimp dim3)
           (dim-eq dim1 dim2) (dim-eq dim2 dim3))
          (dim-eq dim1 dim3))

   ;; equivalence of lists of dimensions:

   (refl ((dim-listp dims))
         (dims-eq dims dims))

   (symm ((dim-listp dims1) (dim-listp dims2)
          (dims-eq dims1 dims2))
         (dims-eq dims2 dims1))

   (trans ((dim-listp dims1) (dim-listp dims2) (dim-listp dims3)
           (dims-eq dims1 dims2) (dims-eq dims2 dims3))
          (dims-eq dims1 dims3))

   ;; congruence of dimensions:

   (cong-add ((dim-listp dims1) (dim-listp dims2)
              (dims-eq dims1 dims2))
             (dim-eq (dim-add dims1) (dim-add dims2)))

   (cong-sub ((dim-listp dims1) (dim-listp dims2)
              (dims-eq dims1 dims2))
             (dim-eq (dim-sub dims1) (dim-sub dims2)))

   (cong-mul ((dim-listp dims1) (dim-listp dims2)
              (dims-eq dims1 dims2))
             (dim-eq (dim-mul dims1) (dim-mul dims2)))

   ;; congruence of lists of dimensions:

   (cong-cons ((dimp dim1) (dimp dim2)
               (dim-listp dims1) (dim-listp dims2)
               (dim-eq dim1 dim2)
               (dims-eq dims1 dims2))
              (dims-eq (cons dim1 dims1) (cons dim2 dims2)))

   ;; normalization of addition:

   (add0 ()
         (dim-eq (dim+) (dim-const 0)))

   (add1 ((dimp dim))
         (dim-eq (dim+ dim) dim))

   (add3m ((dimp dim1) (dimp dim2) (dim-listp dims) (consp dims))
          (dim-eq (dim-add (list* dim1 dim2 dims))
                  (dim-add (cons (dim+ dim1 dim2) dims))))

   ;; normalization of multiplication:

   (mul0 ()
         (dim-eq (dim*) (dim-const 1)))

   (mul1 ((dimp dim))
         (dim-eq (dim* dim) dim))

   (mul3m ((dimp dim1) (dimp dim2) (dim-listp dims) (consp dims))
          (dim-eq (dim-mul (list* dim1 dim2 dims))
                  (dim-mul (cons (dim* dim1 dim2) dims))))

   ;; normalization of subtraction:

   (sub2m ((dimp dim) (dim-listp dims) (consp dims))
          (dim-eq (dim-sub (cons dim dims))
                  (dim+ dim (dim- (dim-add dims)))))

   ;; abelian group properties of addition:

   (add-comm ((dimp dim1) (dimp dim2))
             (dim-eq (dim+ dim1 dim2)
                     (dim+ dim2 dim1)))

   (add-assoc ((dimp dim1) (dimp dim2) (dimp dim3))
              (dim-eq (dim+ (dim+ dim1 dim2) dim3)
                      (dim+ dim1 (dim+ dim2 dim3))))

   (add-id ((dimp dim))
           (dim-eq (dim+ 0 dim) dim))

   (add-inv ((dimp dim))
            (dim-eq (dim+ dim (dim- dim))
                    (dim-const 0)))

   ;; addition of constants:

   (add-const ((natp n1) (natp n2))
              (dim-eq (dim+ (dim-const n1) (dim-const n2))
                      (dim-const (+ n1 n2))))

   ;; commutative monoid properties of multiplication:

   (mul-comm ((dimp dim1) (dimp dim2))
             (dim-eq (dim* dim1 dim2)
                     (dim* dim2 dim1)))

   (mul-assoc ((dimp dim1) (dimp dim2) (dimp dim3))
              (dim-eq (dim* (dim* dim1 dim2) dim3)
                      (dim* dim1 (dim* dim2 dim3))))

   (mul-id ((dimp dim))
           (dim-eq (dim* 1 dim) dim))

   ;; multiplication of constants:

   (mul-const ((natp n1) (natp n2))
              (dim-eq (dim* (dim-const n1) (dim-const n2))
                      (dim-const (* n1 n2))))

   ;; distributivity of multiplication over addition:

   (distrib ((dimp dim) (dimp dim1) (dimp dim2))
            (dim-eq (dim* dim (dim+ dim1 dim2))
                    (dim+ (dim* dim dim1) (dim* dim dim2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive shape/ispace-equivalence-definition
  :short "Inference rules that define shape and ispace equivalence."
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
     defined in @(see dim-equivalence-definition).")
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

  :preds ((shape-eq shape1 shape2)
          (shapes-eq shapes1 shapes2)
          (ispace-eq ispace1 ispace2)
          (ispaces-eq ispaces1 ispaces2))

  :irules

  (;; equivalence of shapes:

   (refl ((shapep shape))
         (shape-eq shape shape))

   (symm ((shapep shape1) (shapep shape2)
          (shape-eq shape1 shape2))
         (shape-eq shape2 shape1))

   (trans ((shapep shape1) (shapep shape2) (shapep shape3)
           (shape-eq shape1 shape2) (shape-eq shape2 shape3))
          (shape-eq shape1 shape3))

   ;; equivalence of lists of shapes:

   (refl ((shape-listp shapes))
         (shapes-eq shapes shapes))

   (symm ((shape-listp shapes1) (shape-listp shapes2)
          (shapes-eq shapes1 shapes2))
         (shapes-eq shapes2 shapes1))

   (trans ((shape-listp shapes1) (shape-listp shapes2) (shape-listp shapes3)
           (shapes-eq shapes1 shapes2) (shapes-eq shapes2 shapes3))
          (shapes-eq shapes1 shapes3))

   ;; equivalence of ispaces:

   (refl ((ispacep ispace))
         (ispace-eq ispace ispace))

   (symm ((ispacep ispace1) (ispacep ispace2)
          (ispace-eq ispace1 ispace2))
         (ispace-eq ispace2 ispace1))

   (trans ((ispacep ispace1) (ispacep ispace2) (ispacep ispace3)
           (ispace-eq ispace1 ispace2) (ispace-eq ispace2 ispace3))
          (ispace-eq ispace1 ispace3))

   ;; equivalence of lists of ispaces:

   (refl ((ispace-listp ispaces))
         (ispaces-eq ispaces ispaces))

   (symm ((ispace-listp ispaces1) (ispace-listp ispaces2)
          (ispaces-eq ispaces1 ispaces2))
         (ispaces-eq ispaces2 ispaces1))

   (trans ((ispace-listp ispaces1) (ispace-listp ispaces2)
           (ispace-listp ispaces3)
           (ispaces-eq ispaces1 ispaces2) (ispaces-eq ispaces2 ispaces3))
          (ispaces-eq ispaces1 ispaces3))

   ;; congruence of shapes:

   (cong-dims ((dim-listp dims1) (dim-listp dims2)
               (dims-eq dims1 dims2))
              (shape-eq (shape-dims dims1) (shape-dims dims2)))

   (cong-append ((shape-listp shapes1) (shape-listp shapes2)
                 (shapes-eq shapes1 shapes2))
                (shape-eq (shape-append shapes1) (shape-append shapes2)))

   (cong-splice ((ispace-listp ispaces1) (ispace-listp ispaces2)
                 (ispaces-eq ispaces1 ispaces2))
                (shape-eq (shape-splice ispaces1) (shape-splice ispaces2)))

   ;; congruence of ispaces:

   (cong-dim ((dimp dim1) (dimp dim2)
              (dim-eq dim1 dim2))
             (ispace-eq (ispace-dim dim1) (ispace-dim dim2)))

   (cong-shape ((shapep shape1) (shapep shape2)
                (shape-eq shape1 shape2))
               (ispace-eq (ispace-shape shape1) (ispace-shape shape2)))

   ;; congruence of lists of shapes:

   (cong-cons ((shapep shape1) (shapep shape2)
               (shape-listp shapes1) (shape-listp shapes2)
               (shape-eq shape1 shape2)
               (shapes-eq shapes1 shapes2))
              (shapes-eq (cons shape1 shapes1) (cons shape2 shapes2)))

   ;; congruence of lists of ispaces:

   (cong-cons ((ispacep ispace1) (ispacep ispace2)
               (ispace-listp ispaces1) (ispace-listp ispaces2)
               (ispace-eq ispace1 ispace2)
               (ispaces-eq ispaces1 ispaces2))
              (ispaces-eq (cons ispace1 ispaces1) (cons ispace2 ispaces2)))

   ;; normalization of shapes built from dimensions:

   (dims0 ()
          (shape-eq (shp) (shp++)))

   (dims2m ((dimp dim) (dim-listp dims) (consp dims))
           (shape-eq (shape-dims (cons dim dims))
                     (shp++ (shp dim) (shape-dims dims))))

   ;; normalization of non-empty and non-binary concatenations:

   (append1 ((shapep shape))
            (shape-eq (shp++ shape) shape))

   (append3m ((shapep shape1) (shapep shape2)
              (shape-listp shapes) (consp shapes))
             (shape-eq (shape-append (list* shape1 shape2 shapes))
                       (shape-append (cons (shp++ shape1 shape2) shapes))))

   ;; normalization of splices:

   (splice0 ()
            (shape-eq (shp[]) (shp++)))

   (splice1m-dim ((dimp dim) (ispace-listp ispaces))
                 (shape-eq (shape-splice (cons (ispace-dim dim) ispaces))
                           (shp++ (shp dim) (shape-splice ispaces))))

   (splice1m-shape ((shapep shape) (ispace-listp ispaces))
                   (shape-eq (shape-splice (cons (ispace-shape shape) ispaces))
                             (shp++ shape (shape-splice ispaces))))

   ;; monoid properties of concatenation:

   (append-assoc ((shapep shape1) (shapep shape2) (shapep shape3))
                 (shape-eq (shp++ (shp++ shape1 shape2) shape3)
                           (shp++ shape1 (shp++ shape2 shape3))))

   (append-id-left ((shapep shape))
                   (shape-eq (shp++ (shp++) shape) shape))

   (append-id-right ((shapep shape))
                    (shape-eq (shp++ shape (shp++)) shape))

   ;; equivalence of dimension ispace and singleton shape ispace:

   (ispace-dim-shape ((dimp dim))
                     (ispace-eq (ispace-dim dim) (ispace-shape (shp dim))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equivalence-holds-only-on-dimensions
  :short "The equivalence of dimensions and lists of dimensions
          holds only on dimensions and lists of dimensions."

  (defthm-dim-eq-proof-validp-clique-flag
    (defthmd dimp-when-dim-eq-proof-validp
      (implies (dim-eq-proof-validp proof concl.dim1 concl.dim2)
               (and (dimp concl.dim1)
                    (dimp concl.dim2)))
      :flag dim-eq-proof-validp)
    (defthmd dim-listp-when-dims-eq-proof-validp
      (implies (dims-eq-proof-validp proof concl.dims1 concl.dims2)
               (and (dim-listp concl.dims1)
                    (dim-listp concl.dims2)))
      :flag dims-eq-proof-validp)
    :hints
    (("Goal" :in-theory (enable* dim-equivalence-definition-validp-defs))))

  (defruled dimp-when-dim-eq
    (implies (dim-eq dim1 dim2)
             (and (dimp dim1)
                  (dimp dim2)))
    :enable (dim-eq dimp-when-dim-eq-proof-validp))

  (defruled dim-listp-when-dims-eq
    (implies (dims-eq dims1 dims2)
             (and (dim-listp dims1)
                  (dim-listp dims2)))
    :enable (dims-eq dim-listp-when-dims-eq-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-equivalence-holds-only-on-shapes/ispaces
  :short "The equivalence of shapes, ispaces, and lists thereof
          holds only on shapes, ispaces, and lists thereof."

  (defthm-shape-eq-proof-validp-clique-flag
    (defthmd shapep-when-shape-eq-proof-validp
      (implies (shape-eq-proof-validp proof concl.shape1 concl.shape2)
               (and (shapep concl.shape1)
                    (shapep concl.shape2)))
      :flag shape-eq-proof-validp)
    (defthmd shape-listp-when-shapes-eq-proof-validp
      (implies (shapes-eq-proof-validp proof concl.shapes1 concl.shapes2)
               (and (shape-listp concl.shapes1)
                    (shape-listp concl.shapes2)))
      :flag shapes-eq-proof-validp)
    (defthmd ispacep-when-ispace-eq-proof-validp
      (implies (ispace-eq-proof-validp proof concl.ispace1 concl.ispace2)
               (and (ispacep concl.ispace1)
                    (ispacep concl.ispace2)))
      :flag ispace-eq-proof-validp)
    (defthmd ispace-listp-when-ispaces-eq-proof-validp
      (implies (ispaces-eq-proof-validp proof concl.ispaces1 concl.ispaces2)
               (and (ispace-listp concl.ispaces1)
                    (ispace-listp concl.ispaces2)))
      :flag ispaces-eq-proof-validp)
    :hints (("Goal"
             :in-theory
             (enable* shape/ispace-equivalence-definition-validp-defs))))

  (defruled shapep-when-shape-eq
    (implies (shape-eq shape1 shape2)
             (and (shapep shape1)
                  (shapep shape2)))
    :enable (shape-eq shapep-when-shape-eq-proof-validp))

  (defruled shape-listp-when-shapes-eq
    (implies (shapes-eq shapes1 shapes2)
             (and (shape-listp shapes1)
                  (shape-listp shapes2)))
    :enable (shapes-eq shape-listp-when-shapes-eq-proof-validp))

  (defruled ispacep-when-ispace-eq
    (implies (ispace-eq ispace1 ispace2)
             (and (ispacep ispace1)
                  (ispacep ispace2)))
    :enable (ispace-eq ispacep-when-ispace-eq-proof-validp))

  (defruled ispace-listp-when-ispaces-eq
    (implies (ispaces-eq ispaces1 ispaces2)
             (and (ispace-listp ispaces1)
                  (ispace-listp ispaces2)))
    :enable (ispaces-eq ispace-listp-when-ispaces-eq-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equivalence-guard-verification
  :short "Guard verification of the functions generated by
          @(see dim-equivalence-definition)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The generated functions are not guard-verified by @(tsee definductive),
     so we verify their guards here.
     The rule validity functions must be verified before
     the proof validity functions, which call them;
     the latter form a mutually recursive clique,
     whose guards are verified together.
     All of these verify with no hints:
     the typing premises at the start of each rule discharge
     the guards of the terms in the rest of the rule.")
   (xdoc::p
    "The minimality predicates must be verified after
     the proof validity functions, which they call;
     the equivalence predicates must be verified after
     the minimality predicates, which they call.
     In both, the calls occur after the proof recognizer,
     in a lazy conjunction or as a hypothesis,
     which discharges the guards of those calls."))

  ;; rule validity functions:

  (verify-guards dim-eq-refl-validp)
  (verify-guards dim-eq-symm-validp)
  (verify-guards dim-eq-trans-validp)
  (verify-guards dims-eq-refl-validp)
  (verify-guards dims-eq-symm-validp)
  (verify-guards dims-eq-trans-validp)
  (verify-guards dim-eq-cong-add-validp)
  (verify-guards dim-eq-cong-sub-validp)
  (verify-guards dim-eq-cong-mul-validp)
  (verify-guards dims-eq-cong-cons-validp)
  (verify-guards dim-eq-add0-validp)
  (verify-guards dim-eq-add1-validp)
  (verify-guards dim-eq-add3m-validp)
  (verify-guards dim-eq-mul0-validp)
  (verify-guards dim-eq-mul1-validp)
  (verify-guards dim-eq-mul3m-validp)
  (verify-guards dim-eq-sub2m-validp)
  (verify-guards dim-eq-add-comm-validp)
  (verify-guards dim-eq-add-assoc-validp)
  (verify-guards dim-eq-add-id-validp)
  (verify-guards dim-eq-add-inv-validp)
  (verify-guards dim-eq-add-const-validp)
  (verify-guards dim-eq-mul-comm-validp)
  (verify-guards dim-eq-mul-assoc-validp)
  (verify-guards dim-eq-mul-id-validp)
  (verify-guards dim-eq-mul-const-validp)
  (verify-guards dim-eq-distrib-validp)

  ;; proof validity functions:

  (verify-guards dim-eq-proof-validp)

  ;; minimality predicates:

  (verify-guards dim-eq-proof-minimalp)
  (verify-guards dims-eq-proof-minimalp)

  ;; equivalence predicates:

  (verify-guards dim-eq)
  (verify-guards dims-eq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-equivalence-guard-verification
  :short "Guard verification of the functions generated by
          @(see shape/ispace-equivalence-definition)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see dim-equivalence-guard-verification),
     which must precede this:
     the rules @('cong-dims') and @('cong-dim') have premises
     that call @(tsee dims-eq) and @(tsee dim-eq),
     whose guards are verified there."))

  ;; rule validity functions:

  (verify-guards shape-eq-refl-validp)
  (verify-guards shape-eq-symm-validp)
  (verify-guards shape-eq-trans-validp)
  (verify-guards shapes-eq-refl-validp)
  (verify-guards shapes-eq-symm-validp)
  (verify-guards shapes-eq-trans-validp)
  (verify-guards ispace-eq-refl-validp)
  (verify-guards ispace-eq-symm-validp)
  (verify-guards ispace-eq-trans-validp)
  (verify-guards ispaces-eq-refl-validp)
  (verify-guards ispaces-eq-symm-validp)
  (verify-guards ispaces-eq-trans-validp)
  (verify-guards shape-eq-cong-dims-validp)
  (verify-guards shape-eq-cong-append-validp)
  (verify-guards shape-eq-cong-splice-validp)
  (verify-guards ispace-eq-cong-dim-validp)
  (verify-guards ispace-eq-cong-shape-validp)
  (verify-guards shapes-eq-cong-cons-validp)
  (verify-guards ispaces-eq-cong-cons-validp)
  (verify-guards shape-eq-dims0-validp)
  (verify-guards shape-eq-dims2m-validp)
  (verify-guards shape-eq-append1-validp)
  (verify-guards shape-eq-append3m-validp)
  (verify-guards shape-eq-splice0-validp)
  (verify-guards shape-eq-splice1m-dim-validp)
  (verify-guards shape-eq-splice1m-shape-validp)
  (verify-guards shape-eq-append-assoc-validp)
  (verify-guards shape-eq-append-id-left-validp)
  (verify-guards shape-eq-append-id-right-validp)
  (verify-guards ispace-eq-ispace-dim-shape-validp)

  ;; proof validity functions:

  (verify-guards shape-eq-proof-validp)

  ;; minimality predicates:

  (verify-guards shape-eq-proof-minimalp)
  (verify-guards shapes-eq-proof-minimalp)
  (verify-guards ispace-eq-proof-minimalp)
  (verify-guards ispaces-eq-proof-minimalp)

  ;; equivalence predicates:

  (verify-guards shape-eq)
  (verify-guards shapes-eq)
  (verify-guards ispace-eq)
  (verify-guards ispaces-eq))
