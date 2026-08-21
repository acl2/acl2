; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-variable-operations")
(include-book "ispace-equivalence")
(include-book "fresh-variable-operations")

(include-book "kestrel/fty/string-string-map-quadruple-result" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable acl2::string-string-map-quadruplep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence
  :parents (static-semantics)
  :short "Equivalence of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora involves
     the equivalence of types, which involves the equivalence of ispaces.
     The latter is discussed in @(see ispace-equivalence).")
   (xdoc::p
    "Like for ispace equivalence,
     we plan to define a high-level notion of type equivalence
     that accommodates undecidability.
     But we start with an executable version
     that has the same restriction as decidable ispace equivalence,
     namely that dimension arithmetic is confined to addition only."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-ispace-var-renaming ((vars1 ispace-var-listp)
                                   (vars2 ispace-var-listp)
                                   (used ispace-var-setp))
  :returns (renams string-string-map-quadruple-resultp)
  :short "Generate fresh variable renamings for two lists of ispace variables,
          ensuring that the two lists match in number and sorts."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when encountering two product or sum types,
     which need to be checked for equivalence.
     As in the rules in Figure 4.9 of [thesis],
     we need to rename the bound variables in the bodies of both types
     to use the same fresh names,
     so that we can proceed to check the equivalence of the bodies.
     The @('used') variable set passed to this function
     is the one of the variables to avoid;
     it is suitably set by the callers.")
   (xdoc::p
    "If successful, this function returns four renaming maps:
     one for the dimension variables in @('vars1'),
     one for the shape variables in @('vars1'),
     one for the dimension variables in @('vars2'), and
     one for the shape variables in @('vars2');
     in that order.
     While [thesis] only shows two renamings,
     one for @($x\\ldots$) (our @('vars1')) and
     one for @($x'\\ldots$) (our @('vars2')),
     we split each into two, for dimension and shape variables,
     which are distinct in our formalization.")
   (xdoc::p
    "As we generate each fresh variable,
     we add it to the set of the variables to avoid."))
  (b* (((when (endp vars1))
        (if (endp vars2)
            (make-string-string-map-quadruple :1st nil :2nd nil :3rd nil :4th nil)
          (reserr nil)))
       ((when (endp vars2)) (reserr nil))
       (var1 (car vars1))
       (var2 (car vars2))
       (used (ispace-var-set-fix used)))
    (ispace-var-case
     var1
     :dim (ispace-var-case
           var2
           :dim (b* (((ispace-var-dim var)
                      (fresh-dim-ispace-var "_fresh_ispace_" used))
                     ((ok (string-string-map-quadruple maps))
                      (fresh-ispace-var-renaming (cdr vars1)
                                                 (cdr vars2)
                                                 (set::insert var used))))
                  (change-string-string-map-quadruple
                   maps
                   :1st (omap::update var1.name var.name maps.1st)
                   :3rd (omap::update var2.name var.name maps.3rd)))
           :shape (reserr nil))
     :shape (ispace-var-case
             var2
             :dim (reserr nil)
             :shape (b* (((ispace-var-shape var)
                          (fresh-shape-ispace-var "_fresh_ispace_" used))
                         ((ok (string-string-map-quadruple maps))
                          (fresh-ispace-var-renaming (cdr vars1)
                                                     (cdr vars2)
                                                     (set::insert var used))))
                      (change-string-string-map-quadruple
                       maps
                       :2nd (omap::update var1.name var.name maps.2nd)
                       :4th (omap::update var2.name var.name maps.4th))))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-type-var-renaming ((vars1 type-var-listp)
                                 (vars2 type-var-listp)
                                 (used type-var-setp))
  :returns (renams string-string-map-quadruple-resultp)
  :short "Generate fresh variable renamings for two lists of type variables,
          ensuring that the two lists match in number and sorts."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when encountering two product or sum type,
     which need to be checked for equivalence.
     As in the rules in Figure 4.9 of [thesis],
     we need to rename the bound variables in the bodies of both types
     to use the same fresh names,
     so that we can proceed to check the equivalence of the bodies.
     The @('used') variable set passed to this function
     is the one of the variables to avoid;
     it is suitably set by the callers.")
   (xdoc::p
    "If successful, this function returns four renaming maps:
     one for the atom variables in @('vars1'),
     one for the array variables in @('vars1'),
     one for the atom variables in @('vars2'), and
     one for the array variables in @('vars2');
     in that order.
     While [thesis] only shows two renamings,
     one for @($x\\ldots$) (our @('vars1')) and
     one for @($x'\\ldots$) (our @('vars2')),
     we split each into two, for atom and array variables,
     which are distinct in our formalization.")
   (xdoc::p
    "As we generate each fresh variable,
     we add it to the set of the variables to avoid."))
  (b* (((when (endp vars1))
        (if (endp vars2)
            (make-string-string-map-quadruple :1st nil :2nd nil :3rd nil :4th nil)
          (reserr nil)))
       ((when (endp vars2)) (reserr nil))
       (var1 (car vars1))
       (var2 (car vars2))
       (used (type-var-set-fix used)))
    (type-var-case
     var1
     :atom (type-var-case
            var2
            :atom (b* (((type-var-atom var)
                        (fresh-atom-type-var "_fresh_type_" used))
                       ((ok (string-string-map-quadruple maps))
                        (fresh-type-var-renaming (cdr vars1)
                                                 (cdr vars2)
                                                 (set::insert var used))))
                    (change-string-string-map-quadruple
                     maps
                     :1st (omap::update var1.name var.name maps.1st)
                     :3rd (omap::update var2.name var.name maps.3rd)))
            :array (reserr nil))
     :array (type-var-case
             var2
             :atom (reserr nil)
             :array (b* (((type-var-array var)
                          (fresh-array-type-var "_fresh_type_" used))
                         ((ok (string-string-map-quadruple maps))
                          (fresh-type-var-renaming (cdr vars1)
                                                   (cdr vars2)
                                                   (set::insert var used))))
                      (change-string-string-map-quadruple
                       maps
                       :2nd (omap::update var1.name var.name maps.2nd)
                       :4th (omap::update var2.name var.name maps.4th))))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-type ((type typep))
  :returns (type1 typep)
  :short "Normalize a scalar type to its element type,
          and a function type without input types to its output type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A scalar (i.e. 0-rank array) type is equivalent to its element atom type,
     because our ASTs allow atom types where array types are expected.
     This function turns such scalar types into their element types,
     and leaves all other types unchanged,
     providing a normalization to facilitate (the rest of) equivalence checking
     in @(tsee type-equivp).")
   (xdoc::p
    "We apply the above normalization to
     both the @(':array') and the @(':bracket') summands,
     provided that their ispaces are equivalent to the empty list of dimensions;
     for bracket types, we form a concatenation prior to the comparison.")
   (xdoc::p
    "An array type variable @('*t') stands for
     the array type @('(A &t @t)') in Remora
     (but not all parts of our formalization follow that yet),
     where the atom type variable and the shape variable
     have the same name as the array type variable
     (without the sigils).
     But since @('@t') is a variable,
     it cannot be equivalent to the shape @('[]'),
     and thus we do not perform any normalization on array type variables.")
   (xdoc::p
    "Additionally, also to facilitate (the rest of) equivalence checking,
     we turn an n-ary function type without input types into its output type,
     to which it is equivalent (see @(tsee type))."))
  (type-case
   type
   :array (if (ispace-equivp type.ispace
                             (ispace-shape (shape-dims nil)))
              type.elem
            (type-fix type))
   :bracket (if (ispace-equivp (ispace-shape
                                (shape-append
                                 (shape-list-from-ispace-list type.ispaces)))
                               (ispace-shape (shape-dims nil)))
                type.elem
              (type-fix type))
   :funn (if (endp type.in)
             type.out
           (type-fix type))
   :otherwise (type-fix type))

  ///

  (defret type-count-of-normalize-type
    (<= (type-count type1)
        (type-count type))
    :rule-classes :linear)

  (defrule type-binders-count-of-normalize-type
    (implies (equal (type-count (normalize-type type))
                    (type-count type))
             (equal (type-binders-count (normalize-type type))
                    (type-binders-count type)))
    :enable (normalize-type type-binders-count)
    :expand ((type-count type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-equivp ((type1 typep) (type2 typep))
  :returns (yes/no booleanp)
  :short "Check if two types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "If one type is a variable, the other type must be the same variable.
     Eventually we will need to generalize this so that
     an array type variable @('*v') is equivalent to @('(A &v @v'),
     i.e. an array type with an atom type variable and a shape variable
     that have the same name as the original variable.")
   (xdoc::p
    "If one type is a base type, the other type must be the same base type.")
   (xdoc::p
    "If one type is in the @(':array') or @(':bracket') summand,
     the other one must be also in the @(':array') or @(':bracket') summand,
     but they do not need to be in the same summand.
     The scalar normalization is handled
     via @(tsee normalize-type) for the second type,
     and directly for the first type.")
   (xdoc::p
    "In the case of function types, we follow the curried view:
     an n-ary function type with one or more input types
     is treated as a unary function type
     whose input is the first input type
     and whose output is the rest of the function type
     (see @(tsee fun-curried-out)).
     Accordingly, when each of the two types
     is a unary or n-ary function type,
     we check the equivalence of the (first) input types
     and the equivalence of the rests.
     This makes an n-ary function type with a single input type,
     which may come from the concrete syntax (see @(tsee type)),
     equivalent to the corresponding unary function type,
     and it also relates n-ary function types
     with different numbers of input types.
     An n-ary function type without input types
     is normalized to its output type,
     via @(tsee normalize-type) for the second type,
     and directly in the @(':funn') case for the first type.")
   (xdoc::p
    "In the case of universal, product, and sum types,
     we follow the curried view,
     as we do for function types:
     we peel one bound variable from each of the two types,
     and we compare what remains.
     We use
     @(tsee fresh-type-var-renaming) for universal types and
     @(tsee fresh-ispace-var-renaming) for product and sum types,
     on the singleton lists of the two peeled bound variables,
     to check that they have the same kind or sort
     and to form renaming maps to a common fresh variable,
     which we apply to what remains of the two types,
     which we then compare for equivalence.
     The fresh variable must not be in any of the two types:
     so we set the set of variables to avoid to
     all the (free and bound) variables in the two types.")
   (xdoc::p
    "What remains of a type, after peeling one bound variable,
     is the body for a unary type,
     and the result of @(tsee forall-curried-body) or analogous operations
     for an n-ary type.
     Thus a unary type may be equivalent to an n-ary one,
     and two n-ary types may be equivalent
     even if they have different numbers of bound variables.
     An n-ary type with no bound variables,
     which is not well-formed,
     is only equivalent to another one with no bound variables,
     with equivalent bodies.")
   (xdoc::p
    "Since we are renaming (ispace and type) variables to fresh ones,
     we do not call the predicates to check for variable capture.
     Once we add those predicates as guards of the renaming operations,
     we will get a proof obligation showing that
     the renamings indeed cause no capture."))
  (type-case
   type1
   :var (b* ((type2 (normalize-type type2)))
          (type-case
           type2
           :var (equal type1.var type2.var)
           :otherwise nil))
   :base (b* ((type2 (normalize-type type2)))
           (type-case
            type2
            :base (equal type1.type type2.type)
            :otherwise nil))
   :array (if (ispace-equivp type1.ispace
                             (ispace-shape (shape-dims nil)))
              (type-equivp type1.elem type2)
            (b* ((type2 (normalize-type type2)))
              (type-case
               type2
               :array (and (type-equivp type1.elem type2.elem)
                           (ispace-equivp type1.ispace type2.ispace))
               :bracket (and (type-equivp type1.elem type2.elem)
                             (ispace-equivp type1.ispace
                                            (ispace-shape
                                             (shape-append
                                              (shape-list-from-ispace-list
                                               type2.ispaces)))))
               :otherwise nil)))
   :bracket (if (ispace-equivp (ispace-shape
                                (shape-append
                                 (shape-list-from-ispace-list type1.ispaces)))
                               (ispace-shape (shape-dims nil)))
                (type-equivp type1.elem type2)
              (b* ((type2 (normalize-type type2)))
                (type-case
                 type2
                 :array (and (type-equivp type1.elem type2.elem)
                             (ispace-equivp (ispace-shape
                                             (shape-append
                                              (shape-list-from-ispace-list
                                               type1.ispaces)))
                                            type2.ispace))
                 :bracket (and (type-equivp type1.elem type2.elem)
                               (ispace-equivp
                                (ispace-shape
                                 (shape-append
                                  (shape-list-from-ispace-list
                                   type1.ispaces)))
                                (ispace-shape
                                 (shape-append
                                  (shape-list-from-ispace-list
                                   type2.ispaces)))))
                 :otherwise nil)))
   :fun (b* ((type2 (normalize-type type2)))
          (type-case
           type2
           :fun (and (type-equivp type1.in type2.in)
                     (type-equivp type1.out type2.out))
           :funn (and (consp type2.in)
                      (type-equivp type1.in (car type2.in))
                      (type-equivp type1.out
                                   (fun-curried-out type2.in type2.out)))
           :otherwise nil))
   :funn (b* (((when (endp type1.in))
               (type-equivp type1.out type2))
              (type2 (normalize-type type2)))
           (type-case
            type2
            :fun (and (type-equivp (car type1.in) type2.in)
                      (type-equivp (fun-curried-out type1.in type1.out)
                                   type2.out))
            :funn (and (consp type2.in)
                       (type-equivp (car type1.in) (car type2.in))
                       (type-equivp (fun-curried-out type1.in type1.out)
                                    (fun-curried-out type2.in type2.out)))
            :otherwise nil))
   :forall (b* ((type2 (normalize-type type2)))
             (type-case
              type2
              :forall (b* ((used (set::union (type-all-type-vars type1)
                                             (type-all-type-vars type2)))
                           (maps (fresh-type-var-renaming (list type1.param)
                                                          (list type2.param)
                                                          used))
                           ((when (reserrp maps)) nil)
                           ((string-string-map-quadruple maps) maps)
                           (body1 (type-rename-type-vars type1.body
                                                         maps.1st
                                                         maps.2nd))
                           (body2 (type-rename-type-vars type2.body
                                                         maps.3rd
                                                         maps.4th)))
                        (type-equivp body1 body2))
              :foralln (b* ((used (set::union (type-all-type-vars type1)
                                              (type-all-type-vars type2)))
                            (maps (fresh-type-var-renaming
                                   (list type1.param)
                                   (list (car type2.params))
                                   used))
                            ((when (reserrp maps)) nil)
                            ((string-string-map-quadruple maps) maps)
                            (body1 (type-rename-type-vars type1.body
                                                          maps.1st
                                                          maps.2nd))
                            (body2 (type-rename-type-vars
                                    (forall-curried-body type2.params
                                                         type2.body)
                                    maps.3rd
                                    maps.4th)))
                         (type-equivp body1 body2))
              :otherwise nil))
   :foralln (b* ((type2 (normalize-type type2)))
              (type-case
               type2
               :forall (b* ((used (set::union (type-all-type-vars type1)
                                              (type-all-type-vars type2)))
                            (maps (fresh-type-var-renaming
                                   (list (car type1.params))
                                   (list type2.param)
                                   used))
                            ((when (reserrp maps)) nil)
                            ((string-string-map-quadruple maps) maps)
                            (body1 (type-rename-type-vars
                                    (forall-curried-body type1.params
                                                         type1.body)
                                    maps.1st
                                    maps.2nd))
                            (body2 (type-rename-type-vars type2.body
                                                          maps.3rd
                                                          maps.4th)))
                         (type-equivp body1 body2))
               :foralln (b* ((used (set::union (type-all-type-vars type1)
                                               (type-all-type-vars type2)))
                             (maps (fresh-type-var-renaming
                                    (list (car type1.params))
                                    (list (car type2.params))
                                    used))
                             ((when (reserrp maps)) nil)
                             ((string-string-map-quadruple maps) maps)
                             (body1 (type-rename-type-vars
                                     (forall-curried-body type1.params
                                                          type1.body)
                                     maps.1st
                                     maps.2nd))
                             (body2 (type-rename-type-vars
                                     (forall-curried-body type2.params
                                                          type2.body)
                                     maps.3rd
                                     maps.4th)))
                          (type-equivp body1 body2))
               :otherwise nil))
   :pi (b* ((type2 (normalize-type type2)))
         (type-case
          type2
          :pi (b* ((used (set::union (type-all-ispace-vars type1)
                                     (type-all-ispace-vars type2)))
                   (maps (fresh-ispace-var-renaming (list type1.param)
                                                    (list type2.param)
                                                    used))
                   ((when (reserrp maps)) nil)
                   ((string-string-map-quadruple maps) maps)
                   (body1 (type-rename-ispace-vars type1.body
                                                   maps.1st
                                                   maps.2nd))
                   (body2 (type-rename-ispace-vars type2.body
                                                   maps.3rd
                                                   maps.4th)))
                (type-equivp body1 body2))
          :pin (b* (((unless (>= (len type2.params) 2)) nil)
                    ;; TODO: remove above check when AST invariant is in
                    (used (set::union (type-all-ispace-vars type1)
                                      (type-all-ispace-vars type2)))
                    (maps (fresh-ispace-var-renaming
                           (list type1.param)
                           (list (car type2.params))
                           used))
                    ((when (reserrp maps)) nil)
                    ((string-string-map-quadruple maps) maps)
                    (body1 (type-rename-ispace-vars type1.body
                                                    maps.1st
                                                    maps.2nd))
                    (body2 (type-rename-ispace-vars
                            (pi-curried-body type2.params type2.body)
                            maps.3rd
                            maps.4th)))
                 (type-equivp body1 body2))
          :otherwise nil))
   :pin (b* ((type2 (normalize-type type2)))
          (type-case
           type2
           :pi (b* (((unless (>= (len type1.params) 2)) nil)
                    ;; TODO: remove above check when AST invariant is in
                    (used (set::union (type-all-ispace-vars type1)
                                      (type-all-ispace-vars type2)))
                    (maps (fresh-ispace-var-renaming
                           (list (car type1.params))
                           (list type2.param)
                           used))
                    ((when (reserrp maps)) nil)
                    ((string-string-map-quadruple maps) maps)
                    (body1 (type-rename-ispace-vars
                            (pi-curried-body type1.params type1.body)
                            maps.1st
                            maps.2nd))
                    (body2 (type-rename-ispace-vars type2.body
                                                    maps.3rd
                                                    maps.4th)))
                 (type-equivp body1 body2))
           :pin (b* (((when (endp type1.params))
                      (and (endp type2.params)
                           (type-equivp type1.body type2.body)))
                     ((when (endp type2.params)) nil)
                     (used (set::union (type-all-ispace-vars type1)
                                       (type-all-ispace-vars type2)))
                     (maps (fresh-ispace-var-renaming
                            (list (car type1.params))
                            (list (car type2.params))
                            used))
                     ((when (reserrp maps)) nil)
                     ((string-string-map-quadruple maps) maps)
                     (body1 (type-rename-ispace-vars
                             (pi-curried-body type1.params type1.body)
                             maps.1st
                             maps.2nd))
                     (body2 (type-rename-ispace-vars
                             (pi-curried-body type2.params type2.body)
                             maps.3rd
                             maps.4th)))
                  (type-equivp body1 body2))
           :otherwise nil))
   :sigma (b* ((type2 (normalize-type type2)))
            (type-case
             type2
             :sigma (b* ((used (set::union (type-all-ispace-vars type1)
                                           (type-all-ispace-vars type2)))
                         (maps (fresh-ispace-var-renaming (list type1.param)
                                                          (list type2.param)
                                                          used))
                         ((when (reserrp maps)) nil)
                         ((string-string-map-quadruple maps) maps)
                         (body1 (type-rename-ispace-vars type1.body
                                                         maps.1st
                                                         maps.2nd))
                         (body2 (type-rename-ispace-vars type2.body
                                                         maps.3rd
                                                         maps.4th)))
                      (type-equivp body1 body2))
             :sigman (b* (((unless (consp type2.params)) nil)
                          (used (set::union (type-all-ispace-vars type1)
                                            (type-all-ispace-vars type2)))
                          (maps (fresh-ispace-var-renaming
                                 (list type1.param)
                                 (list (car type2.params))
                                 used))
                          ((when (reserrp maps)) nil)
                          ((string-string-map-quadruple maps) maps)
                          (body1 (type-rename-ispace-vars type1.body
                                                          maps.1st
                                                          maps.2nd))
                          (body2 (type-rename-ispace-vars
                                  (sigma-curried-body type2.params
                                                      type2.body)
                                  maps.3rd
                                  maps.4th)))
                       (type-equivp body1 body2))
             :otherwise nil))
   :sigman (b* ((type2 (normalize-type type2)))
             (type-case
              type2
              :sigma (b* (((unless (consp type1.params)) nil)
                          (used (set::union (type-all-ispace-vars type1)
                                            (type-all-ispace-vars type2)))
                          (maps (fresh-ispace-var-renaming
                                 (list (car type1.params))
                                 (list type2.param)
                                 used))
                          ((when (reserrp maps)) nil)
                          ((string-string-map-quadruple maps) maps)
                          (body1 (type-rename-ispace-vars
                                  (sigma-curried-body type1.params
                                                      type1.body)
                                  maps.1st
                                  maps.2nd))
                          (body2 (type-rename-ispace-vars type2.body
                                                          maps.3rd
                                                          maps.4th)))
                       (type-equivp body1 body2))
              :sigman (b* (((when (endp type1.params))
                            (and (endp type2.params)
                                 (type-equivp type1.body type2.body)))
                           ((when (endp type2.params)) nil)
                           (used (set::union (type-all-ispace-vars type1)
                                             (type-all-ispace-vars type2)))
                           (maps (fresh-ispace-var-renaming
                                  (list (car type1.params))
                                  (list (car type2.params))
                                  used))
                           ((when (reserrp maps)) nil)
                           ((string-string-map-quadruple maps) maps)
                           (body1 (type-rename-ispace-vars
                                   (sigma-curried-body type1.params
                                                       type1.body)
                                   maps.1st
                                   maps.2nd))
                           (body2 (type-rename-ispace-vars
                                   (sigma-curried-body type2.params
                                                       type2.body)
                                   maps.3rd
                                   maps.4th)))
                        (type-equivp body1 body2))
              :otherwise nil)))
  :measure (two-nats-measure (+ (type-count type1)
                                (type-count type2))
                             (+ (type-binders-count type1)
                                (type-binders-count type2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-equivp ((types1 type-listp) (types2 type-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of types are the same modulo renaming."
  (or (and (endp types1)
           (endp types2))
      (and (consp types1)
           (consp types2)
           (type-equivp (car types1) (car types2))
           (type-list-equivp (cdr types1) (cdr types2))))
  :measure (+ (type-list-count types1)
              (type-list-count types2))

  ///

  (defrule same-len-when-type-list-equivp
    (implies (type-list-equivp types1 types2)
             (equal (len types1) (len types2)))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :induct (acl2::cdr-cdr-induct types1 types2)
             :in-theory (enable acl2::atom)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-all-equivp ((types type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (type-equivp (car types) (cadr types))
           (type-list-all-equivp (cdr types)))))
