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

(definductive type-equivalence-definition
  :short "Inference rules that define type equivalence."
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
    "We start with the equivalence rules
     (reflexivity, symmetry, and transitivity).
     [thesis] and [arxiv] only include reflexivity,
     because symmetry and transitivity should be derivable
     from the other rules, via suitable inductions.
     But here we have a richer set of rules,
     including the normalization ones,
     and thus neither symmetry nor transitivity is derivable.")
   (xdoc::p
    "Next we have congruence for array types,
     which relies on ispace equivalence.
     The rule in [thesis] and [arxiv] includes a premise for ispace equivalence,
     but, as noted in @(see ispace-equivalence),
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
    "An atom type is allowed where an array type is expected.
     This is formalized by the rule @('scalar'),
     which says that an atom type is equivalent to
     a scalar (i.e. zero-ranked) array type with the atom type as element.")
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

  :preds ((type-eq type1 type2))

  :irules

  (;; equivalence:

   (refl ((typep type))
         (type-eq type type))

   (symm ((typep type1) (typep type2)
          (type-eq type1 type2))
         (type-eq type2 type1))

   (trans ((typep type1) (typep type2) (typep type3)
           (type-eq type1 type2) (type-eq type2 type3))
          (type-eq type1 type3))

   ;; array type congruence:

   (array ((typep type1) (typep type2) (ispacep ispace1) (ispacep ispace2)
           (type-eq type1 type2)
           (ispace-eq ispace1 ispace2))
          (type-eq (tarr type1 ispace1) (tarr type2 ispace2)))

   ;; function type congruence:

   (fun ((typep type-in1) (typep type-in2) (typep type-out1) (typep type-out2)
         (type-eq type-in1 type-in2)
         (type-eq type-out1 type-out2))
        (type-eq (t-> type-in1 type-out1) (t-> type-in2 type-out2)))

   ;; universal type congruence:

   (forall ((type-varp param1) (type-varp param2) (type-varp param)
            (typep type1) (typep type2)
            (not (equal param param1))
            (not (equal param param2))
            (not (set::in param (type-all-type-vars type1)))
            (not (set::in param (type-all-type-vars type2)))
            (equal (type-var-kind param) (type-var-kind param1))
            (equal (type-var-kind param) (type-var-kind param2))
            (type-var-case
             param
             :atom
             (and (equal atom-ren1
                         (omap::update (type-var-atom->name param1)
                                       param.name nil))
                  (equal atom-ren2
                         (omap::update (type-var-atom->name param2)
                                       param.name nil))
                  (equal array-ren1 nil)
                  (equal array-ren2 nil))
             :array
             (and (equal atom-ren1 nil)
                  (equal atom-ren2 nil)
                  (equal array-ren1
                         (omap::update (type-var-array->name param1)
                                       param.name nil))
                  (equal array-ren2
                         (omap::update (type-var-array->name param2)
                                       param.name nil))))
            (type-eq (type-rename-type-vars type1 atom-ren1 array-ren1)
                     (type-rename-type-vars type2 atom-ren2 array-ren2)))
           (type-eq (type-forall param1 type1) (type-forall param2 type2)))

   ;; product type congruence:

   (pi ((ispace-varp param1) (ispace-varp param2) (ispace-varp param)
        (typep type1) (typep type2)
        (not (equal param param1))
        (not (equal param param2))
        (not (set::in param (type-all-ispace-vars type1)))
        (not (set::in param (type-all-ispace-vars type2)))
        (equal (ispace-var-kind param) (ispace-var-kind param1))
        (equal (ispace-var-kind param) (ispace-var-kind param2))
        (ispace-var-case
         param
         :dim
         (and (equal dim-ren1
                     (omap::update (ispace-var-dim->name param1)
                                   param.name nil))
              (equal dim-ren2
                     (omap::update (ispace-var-dim->name param2)
                                   param.name nil))
              (equal shape-ren1 nil)
              (equal shape-ren2 nil))
         :shape
         (and (equal dim-ren1 nil)
              (equal dim-ren2 nil)
              (equal shape-ren1
                     (omap::update (ispace-var-shape->name param1)
                                   param.name nil))
              (equal shape-ren2
                     (omap::update (ispace-var-shape->name param2)
                                   param.name nil))))
        (type-eq (type-rename-ispace-vars type1 dim-ren1 shape-ren1)
                 (type-rename-ispace-vars type2 dim-ren2 shape-ren2)))
       (type-eq (type-pi param1 type1) (type-pi param2 type2)))

   ;; sum type congruence:

   (sigma ((ispace-varp param1) (ispace-varp param2) (ispace-varp param)
           (typep type1) (typep type2)
           (not (equal param param1))
           (not (equal param param2))
           (not (set::in param (type-all-ispace-vars type1)))
           (not (set::in param (type-all-ispace-vars type2)))
           (equal (ispace-var-kind param) (ispace-var-kind param1))
           (equal (ispace-var-kind param) (ispace-var-kind param2))
           (ispace-var-case
            param
            :dim
            (and (equal dim-ren1
                        (omap::update (ispace-var-dim->name param1)
                                      param.name nil))
                 (equal dim-ren2
                        (omap::update (ispace-var-dim->name param2)
                                      param.name nil))
                 (equal shape-ren1 nil)
                 (equal shape-ren2 nil))
            :shape
            (and (equal dim-ren1 nil)
                 (equal dim-ren2 nil)
                 (equal shape-ren1
                        (omap::update (ispace-var-shape->name param1)
                                      param.name nil))
                 (equal shape-ren2
                        (omap::update (ispace-var-shape->name param2)
                                      param.name nil))))
           (type-eq (type-rename-ispace-vars type1 dim-ren1 shape-ren1)
                    (type-rename-ispace-vars type2 dim-ren2 shape-ren2)))
          (type-eq (type-sigma param1 type1) (type-sigma param2 type2)))

   ;; lifting of atom types to array types:

   (scalar ((typep type)
            (type-atomp type))
           (type-eq type (tarr type (shp++))))

   ;; normalization of array type variables:

   (array-var ((stringp name))
              (type-eq (type-var (type-var-array name))
                       (tarr (type-var (type-var-atom name))
                             (ispace-shape (shape-var name)))))

   ;; normalization of bracket types:

   (bracket ((typep type) (ispace-listp ispaces) (ispacep ispace)
             (ispace-eq ispace (ispace-shape (shape-splice ispaces))))
            (type-eq (type-bracket type ispaces)
                     (tarr type ispace)))

   ;; normalization of n-ary function types:

   (fun0 ((typep type-out))
         (type-eq (type-funn nil type-out) type-out))

   (fun1m ((typep type-in) (type-listp types-in) (typep type-out))
          (type-eq (type-funn (cons type-in types-in) type-out)
                   (t-> type-in (type-funn types-in type-out))))

   ;; normalization of n-ary universal types:

   (forall2 ((type-varp param1) (type-varp param2) (typep type))
            (type-eq (type-foralln (list param1 param2) type)
                     (type-forall param1 (type-forall param2 type))))

   (forall3m ((type-varp param1) (type-varp param2) (type-var-listp params)
              (consp params) (typep type))
             (type-eq (type-foralln (list* param1 param2 params) type)
                      (type-forall param1
                                   (type-foralln (cons param2 params) type))))

   ;; normalization of n-ary product types:

   (pi2 ((ispace-varp param1) (ispace-varp param2) (typep type))
        (type-eq (type-pin (list param1 param2) type)
                 (type-pi param1 (type-pi param2 type))))

   (pi3m ((ispace-varp param1) (ispace-varp param2) (ispace-var-listp params)
          (consp params) (typep type))
         (type-eq (type-pin (list* param1 param2 params) type)
                  (type-pi param1 (type-pin (cons param2 params) type))))

   ;; normalization of n-ary sum types:

   (sigma2 ((ispace-varp param1) (ispace-varp param2) (typep type))
           (type-eq (type-sigman (list param1 param2) type)
                    (type-sigma param1 (type-sigma param2 type))))

   (sigma3m ((ispace-varp param1) (ispace-varp param2)
             (ispace-var-listp params) (consp params) (typep type))
            (type-eq (type-sigman (list* param1 param2 params) type)
                     (type-sigma param1
                                 (type-sigman (cons param2 params) type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-eq-proof-list
  :short "Fixtype of lists of proof trees for type equivalence."
  :elt-type type-eq-proof
  :true-listp t
  :elementp-of-nil nil
  :pred type-eq-proof-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-equivalence-guard-verification
  :short "Guard verification of the functions generated by
          @(see type-equivalence-definition)."

  ;; rule validity functions:

  (verify-guards type-eq-refl-validp)
  (verify-guards type-eq-symm-validp)
  (verify-guards type-eq-trans-validp)
  (verify-guards type-eq-array-validp)
  (verify-guards type-eq-fun-validp)
  (verify-guards type-eq-forall-validp)
  (verify-guards type-eq-pi-validp)
  (verify-guards type-eq-sigma-validp)
  (verify-guards type-eq-scalar-validp)
  (verify-guards type-eq-array-var-validp)
  (verify-guards type-eq-bracket-validp)
  (verify-guards type-eq-fun0-validp)
  (verify-guards type-eq-fun1m-validp)
  (verify-guards type-eq-forall2-validp)
  (verify-guards type-eq-forall3m-validp)
  (verify-guards type-eq-pi2-validp)
  (verify-guards type-eq-pi3m-validp)
  (verify-guards type-eq-sigma2-validp)
  (verify-guards type-eq-sigma3m-validp)

  ;; proof validity function
  ;; (the premises of forall, pi, and sigma apply the predicate to renamings,
  ;; whose guards follow from the preceding rule validity conjuncts
  ;; only if the rule validity functions are enabled):

  (verify-guards type-eq-proof-validp
    :hints
    (("Goal" :in-theory (enable* type-equivalence-definition-validp-defs))))

  ;; minimality predicate:

  (verify-guards type-eq-proof-minimalp)

  ;; equivalence predicate:

  (verify-guards type-eq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-eq-proof-list-validp ((proofs type-eq-proof-listp)
                                   types1
                                   types2)
  :guard (and (equal (len types1) (len proofs))
              (equal (len types2) (len proofs)))
  :returns (yes/no booleanp)
  :short "Check if a list of proof trees for type equivalence
          proves the pairwise equivalence of two lists of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee type-eq-proof-validp) to lists:
     each proof tree must be valid for
     the corresponding types in the two lists.
     The three lists must have the same length,
     but this is a structural property,
     which we therefore express as a guard
     rather than as part of the validity check."))
  (or (endp proofs)
      (and (type-eq-proof-validp (car proofs) (car types1) (car types2))
           (type-eq-proof-list-validp (cdr proofs) (cdr types1) (cdr types2))))
  :guard-hints (("Goal" :in-theory (enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-equivalence-holds-only-on-types
  :short "The equivalence of types holds only on types."

  (defruled typep-when-type-eq-proof-validp
    (implies (type-eq-proof-validp proof concl.type1 concl.type2)
             (and (typep concl.type1)
                  (typep concl.type2)))
    :hints (("Goal"
             :induct (type-eq-proof-validp proof concl.type1 concl.type2)
             :in-theory (enable* type-equivalence-definition-validp-defs
                                 (:induction type-eq-proof-validp)))))

  (defruled typep-when-type-eq
    (implies (type-eq type1 type2)
             (and (typep type1)
                  (typep type2)))
    :enable (type-eq typep-when-type-eq-proof-validp)))
