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

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
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

(define normalize-scalar-type ((type typep))
  :returns (type1 typep)
  :short "Normalize a scalar type to its element type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A scalar (i.e. 0-rank array) type is equivalent to its element atom type,
     because our ASTs allow atom types where array types are expected.
     This function turns such scalar types into their element types,
     and leaves all other types unchanged,
     providing a normalization to facilitate (the rest of) equivalence checking
     in @(tsee types-equivp).")
   (xdoc::p
    "We transform types in the @(':array') and @(':bracket') summands,
     provided that their ispaces are equivalent to the empty list of dimensions;
     for bracket types, we form a concatenation prior to the comparison."))
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
   :otherwise (type-fix type))

  ///

  (defret type-count-of-normalize-scalar-type
    (<= (type-count type1)
        (type-count type))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines types-equivp
  :short "Check if two types or lists of types are equivalent."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-equivp ((type1 typep) (type2 typep))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-equivp)
    :short "Check if two types are equivalent."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two types must be in the same fixtype summand
       (two variables, or two base types, etc.),
       except that one may be an array type and the other a bracket type,
       and except that scalar (i.e. 0-rank) array types
       are equivalent to their element atom types.")
     (xdoc::p
      "To handle the latter equivalence:
       when the first type is @(':array') or @(':bracket'),
       and has no dimensions (i.e. 0-rank),
       we recursively check equivalence on its element type;
       in all cases, we normalize the second type
       with @(tsee normalize-scalar-type).")
     (xdoc::p
      "In the case of two variables or two base types, they must be identical.
       Note that the renaming to (the same) fresh variables happens
       before reaching the variables.")
     (xdoc::p
      "In the case of two array or bracket types,
       we recursively check the equivalence of the element types
       and the equivalence of the ispaces.")
     (xdoc::p
      "In the case of two function types,
       we recursively check the equivalence
       of the input and output types.")
     (xdoc::p
      "In the case of two universal types,
       we use @(tsee fresh-type-var-renaming) to check that
       they have the same number and kinds of bound variables,
       forming renaming maps to fresh variables,
       which we apply to the bodies of the types,
       which we then compare for equivalence.
       The fresh variables must not be in any of the two types:
       so we set the set of variables to avoid to
       all the (free and bound) variables in the two types.")
     (xdoc::p
      "In the case of two product types or two sum types,
       we use @(tsee fresh-ispace-var-renaming) to check that
       they have the same number and sorts of bound variables,
       forming renaming maps to fresh variables,
       which we apply to the bodies of the types,
       which we then compare for equivalence.
       The fresh variables must not be in any of the two types:
       so we set the set of variables to avoid to
       all the (free and bound) variables in the two types.
       Two unary universal types, and two unary product types,
       are handled the same way,
       on the singleton lists of their bound variables.
       A unary (universal or product) type
       is never equivalent to an n-ary one,
       for now:
       relating the sugar and core forms is left for
       a planned rework of type equivalence.")
     (xdoc::p
      "Since we are renaming (ispace and type) variables to fresh ones,
       we do not call the predicates to check for variable capture.
       Once we add those predicates as guards of the renaming operations,
       we will get a proof obligation showing that
       the renamings indeed cause no capture."))
    (type-case
     type1
     :var (b* ((type2 (normalize-scalar-type type2)))
            (type-case
             type2
             :var (equal type1.var type2.var)
             :otherwise nil))
     :base (b* ((type2 (normalize-scalar-type type2)))
             (type-case
              type2
              :base (equal type1.type type2.type)
              :otherwise nil))
     :array (if (ispace-equivp type1.ispace
                               (ispace-shape (shape-dims nil)))
                (type-equivp type1.elem type2)
              (b* ((type2 (normalize-scalar-type type2)))
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
                (b* ((type2 (normalize-scalar-type type2)))
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
     :fun (b* ((type2 (normalize-scalar-type type2)))
            (type-case
             type2
             :fun (and (type-list-equivp type1.in type2.in)
                       (type-equivp type1.out type2.out))
             :otherwise nil))
     :forall (b* ((type2 (normalize-scalar-type type2)))
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
                :otherwise nil))
     :foralln (b* ((type2 (normalize-scalar-type type2)))
                (type-case
                 type2
                 :foralln (b* ((used (set::union (type-all-type-vars type1)
                                                 (type-all-type-vars type2)))
                               (maps (fresh-type-var-renaming type1.params
                                                              type2.params
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
                 :otherwise nil))
     :pi (b* ((type2 (normalize-scalar-type type2)))
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
            :otherwise nil))
     :pin (b* ((type2 (normalize-scalar-type type2)))
            (type-case
             type2
             :pin (b* ((used (set::union (type-all-ispace-vars type1)
                                         (type-all-ispace-vars type2)))
                       (maps (fresh-ispace-var-renaming type1.params
                                                        type2.params
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
             :otherwise nil))
     :sigman (b* ((type2 (normalize-scalar-type type2)))
               (type-case
                type2
                :sigman (b* ((used (set::union (type-all-ispace-vars type1)
                                              (type-all-ispace-vars type2)))
                             (maps (fresh-ispace-var-renaming type1.params
                                                              type2.params
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
                :otherwise nil)))
    :measure (+ (type-count type1) (type-count type2)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-list-equivp ((types1 type-listp) (types2 type-listp))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-equivp)
    :short "Check if two lists of types are the same modulo renaming."
    (or (and (endp types1)
             (endp types2))
        (and (consp types1)
             (consp types2)
             (type-equivp (car types1) (car types2))
             (type-list-equivp (cdr types1) (cdr types2))))
    :measure (+ (type-list-count types1) (type-list-count types2))

    ///

    (defrule same-len-when-type-list-equivp
      (implies (type-list-equivp types1 types2)
               (equal (len types1) (len types2)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :induct (acl2::cdr-cdr-induct types1 types2)
               :in-theory (enable acl2::atom)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual types-equivp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-all-equivp ((types type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (type-equivp (car types) (cadr types))
           (type-list-all-equivp (cdr types)))))
