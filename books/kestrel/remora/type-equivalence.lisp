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
(include-book "fresh-variables")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable stringstringmap-pairp-when-result-not-error)))

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

(define check-ispace-var-renaming ((vars1 ispace-var-listp)
                                   (vars2 ispace-var-listp))
  :returns (dim-and-shape-maps stringstringmap-pair-resultp)
  :short "Check if two lists of ispace variables match in number and sorts,
          and if so return maps between the dimension and shape variables."
  (b* (((when (endp vars1))
        (if (endp vars2)
            (make-stringstringmap-pair :1st nil :2nd nil)
          (reserr nil)))
       ((when (endp vars2)) (reserr nil))
       ((ok (stringstringmap-pair maps))
        (check-ispace-var-renaming (cdr vars1) (cdr vars2)))
       (var1 (car vars1))
       (var2 (car vars2)))
    (ispace-var-case
     var1
     :dim (ispace-var-case
           var2
           :dim (make-stringstringmap-pair
                 :1st (omap::update var1.name var2.name maps.1st)
                 :2nd maps.2nd)
           :shape (reserr nil))
     :shape (ispace-var-case
             var2
             :dim (reserr nil)
             :shape (make-stringstringmap-pair
                     :1st maps.1st
                     :2nd (omap::update var1.name var2.name maps.2nd)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-var-renaming ((vars1 type-var-listp)
                                 (vars2 type-var-listp))
  :returns (atom-and-array-maps stringstringmap-pair-resultp)
  :short "Check if two lists of type variables match in number and kinds,
          and if so return maps between the atom and array variables."
  (b* (((when (endp vars1))
        (if (endp vars2)
            (make-stringstringmap-pair :1st nil :2nd nil)
          (reserr nil)))
       ((when (endp vars2)) (reserr nil))
       ((ok (stringstringmap-pair maps))
        (check-type-var-renaming (cdr vars1) (cdr vars2)))
       (var1 (car vars1))
       (var2 (car vars2)))
    (type-var-case
     var1
     :atom (type-var-case
            var2
            :atom (make-stringstringmap-pair
                   :1st (omap::update var1.name var2.name maps.1st)
                   :2nd maps.2nd)
            :array (reserr nil))
     :array (type-var-case
             var2
             :atom (reserr nil)
             :array (make-stringstringmap-pair
                     :1st maps.1st
                     :2nd (omap::update var1.name var2.name maps.2nd)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines types-renamep
  :short "Check if two types or lists of types are the same modulo renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are four independent renamings:
     one for dimension variables,
     one for shape variables,
     one for atom type variables, and
     one for array type variables.
     These are modeled as maps from strings to strings,
     which should be injective
     in well-formed types according to inference rules;
     we may explicate injectivity as guards and invariants at some point.
     The four renaming maps contain all the variables in scope;
     we should explicate this invariant at some point;
     some variables may be associated to themselves (i.e. not renamed)
     in the renaming maps."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-renamep ((type1 typep)
                        (type2 typep)
                        (dim-renam string-string-mapp)
                        (shape-renam string-string-mapp)
                        (atom-renam string-string-mapp)
                        (array-renam string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-renamep)
    :short "Check if two types are the same modulo renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two types must be in the same fixtype summand
       (two variables, or two base types, etc.),
       except that one may be an array type and the other a bracket type.")
     (xdoc::p
      "In the case of two variables,
       they must have the same kind (atom or array).
       Since the renaming contains all the variables in scope,
       we check that the first and second variables
       are associated in the renaming map.")
     (xdoc::p
      "In the case of two base types,
       they must be identical, because they do not contain variables.")
     (xdoc::p
      "In the case of two array or bracket types,
       we recursively check the equality modulo renaming of the element types.
       For the shapes,
       first we apply the dimension and shape variable renaming
       to the first shape(s),
       and then we check equivalence with the second shape(s).
       Shape equivalence is defined not modulo renaming,
       so we must apply the renaming prior to checking shape equivalence.")
     (xdoc::p
      "In the case of two function types,
       we recursively check the equality modulo renaming
       of the input and output types.")
     (xdoc::p
      "In the case of two universal types,
       we use a separate function to check that
       they have the same number and kinds of bound variables,
       forming two maps between their bound variables,
       one for atom variables and one for array variables,
       with which we update the existing variable renaming maps;
       this update may overwrite some previous associations,
       in line with the fact that the bound variables
       may hide outer variables.
       We then check that the two body types are equal
       modulo the updated renamings.")
     (xdoc::p
      "In the case of two product types or two sum types,
       we use a separate function to check that
       they have the same number and sorts of bound variables,
       forming two maps between their bound variables,
       one for dimension variables and one for shape variables,
       with which we update the existing variable renaming maps;
       this update may overwrite some previous associations,
       in line with the fact that the bound variables
       may hide outer variables.
       We then check that the two body types are equal
       modulo the updated renamings."))
    (type-case
     type1
     :var (type-case
           type2
           :var (type-var-case
                 type1.var
                 :atom (type-var-case
                        type2.var
                        :atom (b* ((atom-renam
                                    (string-string-map-fix atom-renam)))
                                (equal (omap::assoc type1.var.name atom-renam)
                                       (cons type1.var.name type2.var.name)))
                        :array nil)
                 :array (type-var-case
                         type2.var
                         :atom nil
                         :array (b* ((array-renam
                                      (string-string-map-fix array-renam)))
                                  (equal (omap::assoc type1.var.name array-renam)
                                         (cons type1.var.name
                                               type2.var.name)))))
           :otherwise nil)
     :base (type-case
            type2
            :base (equal type1.type type2.type)
            :otherwise nil)
     :array (type-case
             type2
             :array (and (type-renamep type1.elem
                                       type2.elem
                                       dim-renam
                                       shape-renam
                                       atom-renam
                                       array-renam)
                         (b* ((renamed-shape1
                               (shape-rename-ispace-vars type1.shape
                                                         dim-renam
                                                         shape-renam)))
                           (shape-equivp renamed-shape1 type2.shape)))
             :bracket (and (type-renamep type1.elem
                                         type2.elem
                                         dim-renam
                                         shape-renam
                                         atom-renam
                                         array-renam)
                           (b* ((renamed-shape1
                                 (shape-rename-ispace-vars type1.shape
                                                           dim-renam
                                                           shape-renam))
                                (shape2 (shape-append type2.shapes)))
                             (shape-equivp renamed-shape1 shape2)))
             :otherwise nil)
     :bracket (type-case
               type2
               :array (and (type-renamep type1.elem
                                         type2.elem
                                         dim-renam
                                         shape-renam
                                         atom-renam
                                         array-renam)
                           (b* ((renamed-shapes1
                                 (shape-list-rename-ispace-vars type1.shapes
                                                                dim-renam
                                                                shape-renam))
                                (shape1 (shape-append renamed-shapes1)))
                             (shape-equivp shape1 type2.shape)))
               :bracket (and (type-renamep type1.elem
                                           type2.elem
                                           dim-renam
                                           shape-renam
                                           atom-renam
                                           array-renam)
                             (b* ((renamed-shapes1
                                   (shape-list-rename-ispace-vars type1.shapes
                                                                  dim-renam
                                                                  shape-renam)))
                               (shape-equivp (shape-append renamed-shapes1)
                                             (shape-append type2.shapes))))
               :otherwise nil)
     :fun (type-case
           type2
           :fun (and (type-list-renamep type1.in
                                        type2.in
                                        dim-renam
                                        shape-renam
                                        atom-renam
                                        array-renam)
                     (type-renamep type1.out
                                   type2.out
                                   dim-renam
                                   shape-renam
                                   atom-renam
                                   array-renam))
           :otherwise nil)
     :forall (type-case
              type2
              :forall (b* ((maps (check-type-var-renaming type1.params
                                                          type2.params))
                           ((when (reserrp maps)) nil)
                           ((stringstringmap-pair maps) maps)
                           (atom-renam (omap::update*
                                        maps.1st
                                        (string-string-map-fix atom-renam)))
                           (array-renam (omap::update*
                                         maps.2nd
                                         (string-string-map-fix array-renam))))
                        (type-renamep type1.body
                                      type2.body
                                      dim-renam
                                      shape-renam
                                      atom-renam
                                      array-renam))
              :otherwise nil)
     :pi (type-case
          type2
          :pi (b* ((maps (check-ispace-var-renaming type1.params
                                                    type2.params))
                   ((when (reserrp maps)) nil)
                   ((stringstringmap-pair maps) maps)
                   (dim-renam (omap::update*
                               maps.1st
                               (string-string-map-fix dim-renam)))
                   (shape-renam (omap::update*
                                 maps.2nd
                                 (string-string-map-fix shape-renam))))
                (type-renamep type1.body
                              type2.body
                              dim-renam
                              shape-renam
                              atom-renam
                              array-renam))
          :otherwise nil)
     :sigma (type-case
             type2
             :sigma (b* ((maps (check-ispace-var-renaming type1.params
                                                          type2.params))
                         ((when (reserrp maps)) nil)
                         ((stringstringmap-pair maps) maps)
                         (dim-renam (omap::update*
                                     maps.1st
                                     (string-string-map-fix dim-renam)))
                         (shape-renam (omap::update*
                                       maps.2nd
                                       (string-string-map-fix shape-renam))))
                      (type-renamep type1.body
                                    type2.body
                                    dim-renam
                                    shape-renam
                                    atom-renam
                                    array-renam))
             :otherwise nil))
    :measure (+ (type-count type1) (type-count type2)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-list-renamep ((types1 type-listp)
                             (types2 type-listp)
                             (dim-renam string-string-mapp)
                             (shape-renam string-string-mapp)
                             (atom-renam string-string-mapp)
                             (array-renam string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-renamep)
    :short "Check if two lists of types are the same modulo renaming."
    (or (and (endp types1)
             (endp types2))
        (and (consp types1)
             (consp types2)
             (type-renamep (car types1)
                           (car types2)
                           dim-renam
                           shape-renam
                           atom-renam
                           array-renam)
             (type-list-renamep (cdr types1)
                                (cdr types2)
                                dim-renam
                                shape-renam
                                atom-renam
                                array-renam)))
    :measure (+ (type-list-count types1) (type-list-count types2))

    ///

    (defrule same-len-when-type-list-renamep
      (implies (type-list-renamep types1
                                  types2
                                  dim-renam
                                  shape-renam
                                  atom-renam
                                  array-renam)
               (equal (len types1) (len types2)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :induct (acl2::cdr-cdr-induct types1 types2)
               :in-theory (enable acl2::atom)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (type-renamep type1 type2 nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;

(define type-list-equivp ((types1 type-listp)
                          (types2 type-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when they are equal modulo no renamings."))
  (type-list-renamep types1 types2 nil nil nil nil)

  ///

  (defrule same-len-when-type-list-equivp
    (implies (type-list-equivp types1 types2)
             (equal (len types1) (len types2)))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-all-equivp ((types type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (type-equivp (car types) (cadr types))
           (type-list-all-equivp (cdr types))))
  :prepwork ((local (in-theory (enable type-list-fix)))))
