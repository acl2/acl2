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
     the equivalence of types.
     Currently type equivalence in Remora is decidable,
     but the language may evolve towards undecidability.")
   (xdoc::p
    "The current (decidable) equivalence of types
     is described in [arxiv] and [thesis],
     in terms of inference rules
     that involve the semantic equivalence of ispaces;
     the latter is defined in terms of normalization
     (see @(see ispace-equivalence)).
     We plan to formalize type equivalence,
     both at a high level and as executable code.
     For now we provide something that is mostly a placeholder."))
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

(defines atom/array-types-renamep
  :short "Check if two atom types, array types, or lists of array types
          are the same modulo renaming."
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

  (define atom-type-renamep ((type1 atom-typep)
                             (type2 atom-typep)
                             (dim-renam string-string-mapp)
                             (shape-renam string-string-mapp)
                             (atom-renam string-string-mapp)
                             (array-renam string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence atom/array-types-renamep)
    :short "Check if two atom types are the same modulo renaming."
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
    (atom-type-case
     type1
     :var (atom-type-case
           type2
           :var (b* ((atom-renam (string-string-map-fix atom-renam)))
                  (equal (omap::assoc type1.name atom-renam)
                         (cons type1.name type2.name)))
           :otherwise nil)
     :base (atom-type-case
            type2
            :base (equal type1.type type2.type)
            :otherwise nil)
     :fun (atom-type-case
           type2
           :fun (and (array-type-list-renamep type1.in
                                              type2.in
                                              dim-renam
                                              shape-renam
                                              atom-renam
                                              array-renam)
                     (array-type-renamep type1.out
                                         type2.out
                                         dim-renam
                                         shape-renam
                                         atom-renam
                                         array-renam))
           :otherwise nil)
     :forall (atom-type-case
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
                        (array-type-renamep type1.body
                                            type2.body
                                            dim-renam
                                            shape-renam
                                            atom-renam
                                            array-renam))
              :otherwise nil)
     :pi (atom-type-case
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
                (array-type-renamep type1.body
                                    type2.body
                                    dim-renam
                                    shape-renam
                                    atom-renam
                                    array-renam))
          :otherwise nil)
     :sigma (atom-type-case
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
                      (array-type-renamep type1.body
                                          type2.body
                                          dim-renam
                                          shape-renam
                                          atom-renam
                                          array-renam))
             :otherwise nil))
    :measure (+ (atom-type-count type1) (atom-type-count type2)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define array-type-renamep ((type1 array-typep)
                              (type2 array-typep)
                              (dim-renam string-string-mapp)
                              (shape-renam string-string-mapp)
                              (atom-renam string-string-mapp)
                              (array-renam string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence atom/array-types-renamep)
    :short "Check if two array types are the same modulo renaming."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two types must be in the same fixtype summand:
       two variables, or two explicit array types.")
     (xdoc::p
      "In the case of two variables,
       since the renaming contains all the variables in scope,
       we check that the first and second variables
       are associated in the renaming map.")
     (xdoc::p
      "In the case of two explicit array types,
       we recursively check the equality modulo renaming of the body types.
       For the shapes,
       first we apply the dimension and shape variable renaming
       to the first shape,
       and then we check equivalence with the second shape.
       Shape equivalence is defined not modulo renaming,
       so we must apply the renaming prior to checking shape equivalence."))
    (array-type-case
     type1
     :var (array-type-case
           type2
           :var (b* ((array-renam (string-string-map-fix array-renam)))
                  (equal (omap::assoc type1.name array-renam)
                         (cons type1.name type2.name)))
           :otherwise nil)
     :array (array-type-case
             type2
             :array (and (atom-type-renamep type1.elem
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
             :otherwise nil))
    :measure (+ (array-type-count type1) (array-type-count type2)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define array-type-list-renamep ((types1 array-type-listp)
                                   (types2 array-type-listp)
                                   (dim-renam string-string-mapp)
                                   (shape-renam string-string-mapp)
                                   (atom-renam string-string-mapp)
                                   (array-renam string-string-mapp))
    :returns (yes/no booleanp)
    :parents (type-equivalence atom/array-types-renamep)
    :short "Check if two lists of array types are the same modulo renaming."
    (or (and (endp types1)
             (endp types2))
        (and (consp types1)
             (consp types2)
             (array-type-renamep (car types1)
                                 (car types2)
                                 dim-renam
                                 shape-renam
                                 atom-renam
                                 array-renam)
             (array-type-list-renamep (cdr types1)
                                      (cdr types2)
                                      dim-renam
                                      shape-renam
                                      atom-renam
                                      array-renam)))
    :measure (+ (array-type-list-count types1) (array-type-list-count types2))

    ///

    (defrule same-len-when-array-type-list-renamep
      (implies (array-type-list-renamep types1
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

  (fty::deffixequiv-mutual atom/array-types-renamep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-list-renamep ((types1 atom-type-listp)
                                (types2 atom-type-listp)
                                (dim-renam string-string-mapp)
                                (shape-renam string-string-mapp)
                                (atom-renam string-string-mapp)
                                (array-renam string-string-mapp))
  :returns (yes/no booleanp)
  :short "Check if two lists of atom types are the same modulo renaming."
  (or (and (endp types1)
           (endp types2))
      (and (consp types1)
           (consp types2)
           (atom-type-renamep (car types1)
                              (car types2)
                              dim-renam
                              shape-renam
                              atom-renam
                              array-renam)
           (atom-type-list-renamep (cdr types1)
                                   (cdr types2)
                                   dim-renam
                                   shape-renam
                                   atom-renam
                                   array-renam)))

  ///

  (defrule same-len-when-atom-type-list-renamep
    (implies (atom-type-list-renamep types1
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-equivp ((type1 atom-typep) (type2 atom-typep))
  :returns (yes/no booleanp)
  :short "Check if two atom types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when they are equal modulo no renamings."))
  (atom-type-renamep type1 type2 nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;

(define atom-type-list-equivp ((types1 atom-type-listp)
                               (types2 atom-type-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of atom types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when they are equal modulo no renamings."))
  (atom-type-list-renamep types1 types2 nil nil nil nil)

  ///

  (defrule same-len-when-atom-type-list-equivp
    (implies (atom-type-list-equivp types1 types2)
             (equal (len types1) (len types2)))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-type-equivp ((type1 array-typep) (type2 array-typep))
  :returns (yes/no booleanp)
  :short "Check if two array types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when they are equal modulo no renamings."))
  (array-type-renamep type1 type2 nil nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-type-list-all-equivp ((types atom-type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the atom types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (atom-type-equivp (car types) (cadr types))
           (atom-type-list-all-equivp (cdr types))))
  :prepwork ((local (in-theory (enable atom-type-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-type-list-all-equivp ((types array-type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the array types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (array-type-equivp (car types) (cadr types))
           (array-type-list-all-equivp (cdr types))))
  :prepwork ((local (in-theory (enable array-type-list-fix)))))
