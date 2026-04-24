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
(include-book "index-equivalence")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory
  (enable
   stringstringmap-pairp-when-stringstringmap-pair-resultp-and-not-reserrp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence
  :parents (static-semantics)
  :short "Equivalence of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora involves
     the equivalence of types.
     Currently type equivalence in Remora is decidable,
     but the language may evolve towards undecidability.")
   (xdoc::p
    "The current (decidable) equivalence of types
     is described in [arxiv] and [thesis],
     in terms of inference rules
     that involve the semantic equivalence of indices;
     the latter is defined in terms of normalization
     (see @(see index-equivalence)).
     We plan to formalize type equivalence,
     both at a high level and as executable code.
     For now we provide something that is mostly a placeholder."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-index-param-renaming ((params1 index-param-listp)
                                    (params2 index-param-listp))
  :returns (dim-and-shape-maps stringstringmap-pair-resultp)
  :short "Check if two lists of index parameters match in number and sorts,
          and if so return maps between the dimension and shape variables."
  (b* (((when (endp params1))
        (if (endp params2)
            (make-stringstringmap-pair :1st nil :2nd nil)
          (reserr nil)))
       ((when (endp params2)) (reserr nil))
       ((ok (stringstringmap-pair maps))
        (check-index-param-renaming (cdr params1) (cdr params2)))
       (param1 (car params1))
       (param2 (car params2)))
    (index-param-case
     param1
     :dim (index-param-case
           param2
           :dim (make-stringstringmap-pair
                 :1st (omap::update param1.name param2.name maps.1st)
                 :2nd maps.2nd)
           :shape (reserr nil))
     :shape (index-param-case
             param2
             :dim (reserr nil)
             :shape (make-stringstringmap-pair
                     :1st maps.1st
                     :2nd (omap::update param1.name param2.name maps.2nd)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines types-renamep
  :short "Check if two types or lists or types are the same modulo renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three independent renamings:
     one for dimension variables,
     one for shape variables,
     and one for type variables.
     These are modeled as maps from strings to strings,
     which should be injective
     in well-formed types according to inference rules;
     we may explicate injectivity as guards and invariants at some point.
     The three renaming maps contain all the variables in scope;
     we should explicate this invariant at some point;
     some variables may be associated to themselves (i.e. not renamed)
     in the renaming maps."))

  (define type-renamep ((type1 typep)
                        (type2 typep)
                        (dim-renaming string-string-mapp)
                        (shape-renaming string-string-mapp)
                        (type-renaming string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-renamep)
    :short "Check if two types are the same modulo renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two types must be in the same fixtype summand:
       two variables, or two base types, etc.")
     (xdoc::p
      "In the case of two variables,
       since the renaming contains all the variables in scope,
       we check that the first and second variables
       are associated in the renaming map.")
     (xdoc::p
      "In the case of two base types,
       they must be identical, because they do not contain variables.")
     (xdoc::p
      "In the case of two array types,
       we recursively check the equality modulo renaming of the atom types.
       For the shapes,
       first we apply the dimension and shape variable renaming
       to the first shape,
       and then we check equivalence with the second shape.
       Shape equivalence is defined not modulo renaming,
       so we must apply the renaming prior to checking shape equivalence.")
     (xdoc::p
      "In the case of two function types,
       we recursively check the equality modulo renaming
       of the input and output types.")
     (xdoc::p
      "In the case of two universal types,
       we check that they have the same number of bound variables,
       and we form a map between their bound variables,
       with which we update the existing type variable renaming map;
       this update may overwrite some previous associations,
       in line with the fact that the bound variables
       may hide outer variables.
       We then check that the two inner types are equal
       modulo the updated renamings.")
     (xdoc::p
      "In the case of two product types or two sum types,
       we use a separate function to check that
       they have the same number and sorte of bound variables,
       forming two maps between their bound variables,
       one for dimension variables and one for shape variables,
       with which we update the existing variable renaming maps;
       this update may overwrite some previous associations,
       in line with the fact that the bound variables
       may hide outer variables.
       We then check that the two inner types are equal
       modulo the updated renamings."))
    (type-case
     type1
     :var (type-case
           type2
           :var (b* ((type-renaming (string-string-map-fix type-renaming)))
                  (equal (omap::assoc type1.name type-renaming)
                         (cons type1.name type2.name)))
           :otherwise nil)
     :base (type-case
            type2
            :base (equal type1.type type2.type)
            :otherwise nil)
     :array (type-case
             type2
             :array (and (type-renamep type1.type
                                       type2.type
                                       dim-renaming
                                       shape-renaming
                                       type-renaming)
                         (b* ((renamed-shape1
                               (rename-vars-in-shape type1.shape
                                                     dim-renaming
                                                     shape-renaming)))
                           (shape-equivp renamed-shape1 type2.shape)))
             :otherwise nil)
     :fun (type-case
           type2
           :fun (and (type-list-renamep type1.in
                                        type2.in
                                        dim-renaming
                                        shape-renaming
                                        type-renaming)
                     (type-renamep type1.out
                                   type2.out
                                   dim-renaming
                                   shape-renaming
                                   type-renaming))
           :otherwise nil)
     :forall (type-case
              type2
              :forall (and (equal (len type1.vars) (len type2.vars))
                           (b* ((bound-map (omap::from-lists
                                            (kinded-var-list->var type1.vars)
                                            (kinded-var-list->var type2.vars)))
                                (type-renaming
                                 (omap::update*
                                  bound-map
                                  (string-string-map-fix type-renaming))))
                             (type-renamep type1.type
                                           type2.type
                                           dim-renaming
                                           shape-renaming
                                           type-renaming)))
              :otherwise nil)
     :pi (type-case
          type2
          :pi (b* ((maps (check-index-param-renaming type1.params
                                                     type2.params))
                   ((when (reserrp maps)) nil)
                   ((stringstringmap-pair maps) maps)
                   (dim-renaming (omap::update*
                                  maps.1st
                                  (string-string-map-fix dim-renaming)))
                   (shape-renaming (omap::update*
                                    maps.2nd
                                    (string-string-map-fix shape-renaming))))
                (type-renamep type1.type
                              type2.type
                              dim-renaming
                              shape-renaming
                              type-renaming))
          :otherwise nil)
     :sigma (type-case
             type2
             :sigma (b* ((maps (check-index-param-renaming type1.params
                                                           type2.params))
                         ((when (reserrp maps)) nil)
                         ((stringstringmap-pair maps) maps)
                         (dim-renaming (omap::update*
                                        maps.1st
                                        (string-string-map-fix dim-renaming)))
                         (shape-renaming (omap::update*
                                          maps.2nd
                                          (string-string-map-fix
                                           shape-renaming))))
                      (type-renamep type1.type
                                    type2.type
                                    dim-renaming
                                    shape-renaming
                                    type-renaming))
             :otherwise nil))
    :measure (+ (type-count type1) (type-count type2)))

  (define type-list-renamep ((types1 type-listp)
                             (types2 type-listp)
                             (dim-renaming string-string-mapp)
                             (shape-renaming string-string-mapp)
                             (type-renaming string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-renamep)
    :short "Check if two lists of types are the same modulo renaming."
    (or (and (endp types1)
             (endp types2))
        (and (consp types1)
             (consp types2)
             (type-renamep (car types1)
                           (car types2)
                           dim-renaming
                           shape-renaming
                           type-renaming)
             (type-list-renamep (cdr types1)
                                (cdr types2)
                                dim-renaming
                                shape-renaming
                                type-renaming)))
    :measure (+ (type-list-count types1) (type-list-count types2))

    ///

    (defrule same-len-when-type-list-renamep
      (implies (type-list-renamep
                types1 types2 dim-renaming shape-renaming type-renaming)
               (equal (len types1) (len types2)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :induct (acl2::cdr-cdr-induct types1 types2)
               :in-theory (enable acl2::atom)))))

  ///

  (fty::deffixequiv-mutual types-renamep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-equivp ((type1 typep) (type2 typep))
  :returns (yes/no booleanp)
  :short "Check if two types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when they are equal modulo no renamings."))
  (type-renamep type1 type2 nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-equivp ((types1 type-listp) (types2 type-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when they are equal modulo no renamings."))
  (type-list-renamep types1 types2 nil nil nil)

  ///

  (defrule same-len-when-type-list-equivp
    (implies (type-list-equivp types1 types2)
             (equal (len types1) (len types2)))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-all-equivp ((types type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (type-equivp (car types) (cadr types))
           (type-list-all-equivp (cdr types))))
  :prepwork ((local (in-theory (enable type-list-fix)))))
