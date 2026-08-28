; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence")
(include-book "all-variable-operations")
(include-book "variable-renaming-operations")

(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence
  :parents (static-semantics)
  :short "Equivalence of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the equivalence of types via inference rules
     that correspond to the ones in [thesis] and [arxiv]
     (while [esop] describes type equivalence
     without giving explicit inference rules).")
   (xdoc::p
    "Type equivalence builds on "
    (xdoc::seetopic "ispace-equivalence" "ispace equivalence")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive type-equiv-infrules
  :short "Inference rules for type equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type equivalence essentially consists of
     lifting of ispace equivalence (in array types),
     alpha equivalence of types with binders,
     and congruence on all types:
     see the inference rules in [thesis] and [arxiv].
     For our formalization of Remora, and to be consistent with [impl],
     some additional inference rules are needed.")
   (xdoc::p
    "All the inference rules start with type premises about the variables,
     for the same reason explained in @(see dim-equiv-infrules).")
   (xdoc::p
    "Following [thesis] and [arxiv], we start with reflexivity.
     We do not state symmetry and transitivity as explicit rules,
     because they should be derivable from the others
     (given that [thesis] and [arxiv] do not include them),
     but we will ensure this is the case by way of formal proof.")
   (xdoc::p
    "Next we have congruence for array types,
     which relies on ispace equivalence.
     The rule in [thesis] and [arxiv] includes a premise for ispace equivalence,
     but, as noted in @(tsee ispace-equivalence),
     [thesis] and [arxiv] do not provide
     explicit inference rules for ispace equivalence.
     We do, and we refer to the predicate defined by those rules.")
   (xdoc::p
    "We formulate congruence for unary function types.
     N-ary function types reduce to unary ones,
     via separate rules described below.")
   (xdoc::p
    "For the same reason,
     we formulate congruence rules for unary universal, product, and sum types.
     The freshness condition is formulated as
     the variable not occurring, free or bound,
     anywhere in the types involved in the equivalence.
     The variable renaming is currently a bit clumsy,
     because the renaming operations take two separate maps;
     we may introduce variants of the renaming operations
     that take just single variables,
     and we may use them here to simplify the rules.
     We do not have premises saying that
     the renaming maps are string-to-string maps,
     because other premises set them to be equal to string-to-string maps.")
   (xdoc::p
    "An array type variable @('*<name>') is sugar for
     an array type @('(A &<name> @<name>)') consisting of
     an atom type variable and a shape variable with the same name.
     Rule @('array-var') lets us perform this reduction.")
   (xdoc::p
    "A bracket type is sugar for an array type
     with the same element type and with the splice of the bracket's ispaces.
     The rule @('bracket') supports this reduction,
     but allows any ispace equivalent to the ispace splice.")
   (xdoc::p
    "An n-ary function type is sugar for
     a nesting of unary function types:
     a nullary function type stands for just its output type
     (rule @('fun0')),
     and a function type with one or more inputs stands for
     a unary function type from the first input
     to the function type with the remaining inputs
     (rule @('fun1m')).")
   (xdoc::p
    "An n-ary universal type, which has two or more parameters,
     is sugar for a nesting of unary universal types:
     one with exactly two parameters stands for
     a unary universal type of the first parameter
     whose body is the unary universal type of the second parameter
     (rule @('forall2')),
     and one with three or more parameters stands for
     a unary universal type of the first parameter
     whose body is the n-ary universal type of the remaining parameters
     (rule @('forall3m')).
     The two rules are separate because
     an n-ary universal type cannot have just one parameter.")
   (xdoc::p
    "An n-ary product type, which has two or more parameters,
     is sugar for a nesting of unary product types:
     one with exactly two parameters stands for
     a unary product type of the first parameter
     whose body is the unary product type of the second parameter
     (rule @('pi2')),
     and one with three or more parameters stands for
     a unary product type of the first parameter
     whose body is the n-ary product type of the remaining parameters
     (rule @('pi3m')).
     The two rules are separate because
     an n-ary product type cannot have just one parameter.")
   (xdoc::p
    "An n-ary sum type, which has two or more parameters,
     is sugar for a nesting of unary sum types:
     one with exactly two parameters stands for
     a unary sum type of the first parameter
     whose body is the unary sum type of the second parameter
     (rule @('sigma2')),
     and one with three or more parameters stands for
     a unary sum type of the first parameter
     whose body is the n-ary sum type of the remaining parameters
     (rule @('sigma3m')).
     The two rules are separate because
     an n-ary sum type cannot have just one parameter."))

  :preds ((type= type1 type2))

  :irules

  (;; reflexivity:

   (refl ((typep type))
         (type= type type))

   ;; array type congruence:

   (array ((typep t1) (typep t2) (ispacep i1) (ispacep i2)
           (type= t1 t2)
           (isp= i1 i2))
          (type= (tarr t1 i1) (tarr t2 i2)))

   ;; function type congruence:

   (fun ((typep in1) (typep in2) (typep out1) (typep out2)
         (type= in1 in2)
         (type= out1 out2))
        (type= (t-> in1 out1) (t-> in2 out2)))

   ;; universal type congruence:

   (forall ((type-varp p1) (type-varp p2) (type-varp p) (typep t1) (typep t2)
            (not (equal p p1))
            (not (equal p p2))
            (not (set::in p (type-all-type-vars t1)))
            (not (set::in p (type-all-type-vars t2)))
            (equal (type-var-kind p) (type-var-kind p1))
            (equal (type-var-kind p) (type-var-kind p2))
            (type-var-case
             p
             :atom
             (and (equal atren1
                         (omap::update (type-var-atom->name p1) p.name nil))
                  (equal atren2
                         (omap::update (type-var-atom->name p2) p.name nil))
                  (equal arren1 nil)
                  (equal arren2 nil))
             :array
             (and (equal atren1 nil)
                  (equal atren2 nil)
                  (equal arren1
                         (omap::update (type-var-array->name p1) p.name nil))
                  (equal arren2
                         (omap::update (type-var-array->name p2) p.name nil))))
            (type= (type-rename-type-vars t1 atren1 arren1)
                   (type-rename-type-vars t2 atren2 arren2)))
           (type= (type-forall p1 t1) (type-forall p2 t2)))

   ;; product type congruence:

   (pi ((ispace-varp p1) (ispace-varp p2) (ispace-varp p) (typep t1) (typep t2)
        (not (equal p p1))
        (not (equal p p2))
        (not (set::in p (type-all-ispace-vars t1)))
        (not (set::in p (type-all-ispace-vars t2)))
        (equal (ispace-var-kind p) (ispace-var-kind p1))
        (equal (ispace-var-kind p) (ispace-var-kind p2))
        (ispace-var-case
         p
         :dim
         (and (equal dren1
                     (omap::update (ispace-var-dim->name p1) p.name nil))
              (equal dren2
                     (omap::update (ispace-var-dim->name p2) p.name nil))
              (equal sren1 nil)
              (equal sren2 nil))
         :shape
         (and (equal dren1 nil)
              (equal dren2 nil)
              (equal sren1
                     (omap::update (ispace-var-shape->name p1) p.name nil))
              (equal sren2
                     (omap::update (ispace-var-shape->name p2) p.name nil))))
        (type= (type-rename-ispace-vars t1 dren1 sren1)
               (type-rename-ispace-vars t2 dren2 sren2)))
       (type= (type-pi p1 t1) (type-pi p2 t2)))

   ;; sum type congruence:

   (sigma ((ispace-varp p1) (ispace-varp p2) (ispace-varp p)
           (typep t1) (typep t2)
           (not (equal p p1))
           (not (equal p p2))
           (not (set::in p (type-all-ispace-vars t1)))
           (not (set::in p (type-all-ispace-vars t2)))
           (equal (ispace-var-kind p) (ispace-var-kind p1))
           (equal (ispace-var-kind p) (ispace-var-kind p2))
           (ispace-var-case
            p
            :dim
            (and (equal dren1
                        (omap::update (ispace-var-dim->name p1) p.name nil))
                 (equal dren2
                        (omap::update (ispace-var-dim->name p2) p.name nil))
                 (equal sren1 nil)
                 (equal sren2 nil))
            :shape
            (and (equal dren1 nil)
                 (equal dren2 nil)
                 (equal sren1
                        (omap::update (ispace-var-shape->name p1) p.name nil))
                 (equal sren2
                        (omap::update (ispace-var-shape->name p2) p.name nil))))
           (type= (type-rename-ispace-vars t1 dren1 sren1)
                  (type-rename-ispace-vars t2 dren2 sren2)))
          (type= (type-sigma p1 t1) (type-sigma p2 t2)))

   ;; normalization of array type variables:

   (array-var ((stringp name))
              (type= (type-var (type-var-array name))
                     (type-array (type-var (type-var-atom name))
                                 (ispace-shape (shape-var name)))))

   ;; normalization of bracket types:

   (bracket ((typep ty) (ispace-listp is) (ispacep i)
             (isp= i (ispace-shape (shape-splice is))))
            (type= (type-bracket ty is)
                   (type-array ty i)))

   ;; normalization of n-ary function types:

   (fun0 ((typep out))
         (type= (type-funn nil out) out))

   (fun1m ((typep in) (type-listp ins) (typep out))
          (type= (type-funn (cons in ins) out)
                 (t-> in (type-funn ins out))))

   ;; normalization of n-ary universal types:

   (forall2 ((type-varp p1) (type-varp p2) (typep ty))
            (type= (type-foralln (list p1 p2) ty)
                   (type-forall p1 (type-forall p2 ty))))

   (forall3m ((type-varp p1) (type-varp p2) (type-var-listp ps) (consp ps)
              (typep ty))
             (type= (type-foralln (list* p1 p2 ps) ty)
                    (type-forall p1 (type-foralln (cons p2 ps) ty))))

   ;; normalization of n-ary product types:

   (pi2 ((ispace-varp p1) (ispace-varp p2) (typep ty))
        (type= (type-pin (list p1 p2) ty)
               (type-pi p1 (type-pi p2 ty))))

   (pi3m ((ispace-varp p1) (ispace-varp p2) (ispace-var-listp ps) (consp ps)
          (typep ty))
         (type= (type-pin (list* p1 p2 ps) ty)
                (type-pi p1 (type-pin (cons p2 ps) ty))))

   ;; normalization of n-ary sum types:

   (sigma2 ((ispace-varp p1) (ispace-varp p2) (typep ty))
           (type= (type-sigman (list p1 p2) ty)
                  (type-sigma p1 (type-sigma p2 ty))))

   (sigma3m ((ispace-varp p1) (ispace-varp p2) (ispace-var-listp ps) (consp ps)
             (typep ty))
            (type= (type-sigman (list* p1 p2 ps) ty)
                   (type-sigma p1 (type-sigman (cons p2 ps) ty))))

  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-equiv-guard-verification
  :short "Guard verification of the functions generated by
          @(see type-equiv-infrules)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see dim-equiv-guard-verification)
     and @(see shape/ispace-equiv-guard-verification).")
   (xdoc::p
    "The proof validity function cannot be guard-verified
     as currently generated.
     The rules @('forall'), @('pi'), and @('sigma') have premises
     that apply the predicate to non-variable arguments
     (the calls of the renaming operations);
     these arguments occur in the cases of the proof validity function,
     as arguments of the recursive calls,
     whose conjuncts precede the rule validity conjunct,
     which is thus unavailable to discharge
     the guard obligations of those arguments,
     which are unprovable from the untyped fields of the proofs.
     This does not arise for dimension, shape, and ispace equivalence,
     whose rules apply the predicates only to variables.
     We should extend @(tsee definductive) to generate
     the rule validity conjunct before the premise proof conjuncts:
     the guard obligations would then follow from that conjunct.
     Consequently, the minimality predicate and the equivalence predicate,
     which call the proof validity function,
     cannot be guard-verified either for now."))

  ;; rule validity functions:

  (verify-guards type=-refl-validp)
  (verify-guards type=-array-validp)
  (verify-guards type=-fun-validp)
  (verify-guards type=-forall-validp)
  (verify-guards type=-pi-validp)
  (verify-guards type=-sigma-validp)
  (verify-guards type=-array-var-validp)
  (verify-guards type=-bracket-validp)
  (verify-guards type=-fun0-validp)
  (verify-guards type=-fun1m-validp)
  (verify-guards type=-forall2-validp)
  (verify-guards type=-forall3m-validp)
  (verify-guards type=-pi2-validp)
  (verify-guards type=-pi3m-validp)
  (verify-guards type=-sigma2-validp)
  (verify-guards type=-sigma3m-validp))
