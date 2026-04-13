; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "index-equivalence")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

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
     is described in the arXiv paper and dissertation,
     in terms of inference rules
     that involve the semantic equivalence of indices;
     the latter is defined in terms of normalization
     (see @(see index-equivalence).
     We plan to formalize type equivalence,
     both at a high level and as executable code.
     For now we provide something that is mostly a placeholder."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines types-equivp
  :short "Check if two types or two lists of types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is mostly a placeholder for now.
     It makes a strong check:
     the types must be identical,
     except that indices just have to be equivalent,
     as defined in @(see index-equivalence)."))

  (define type-equivp ((type1 typep) (type2 typep))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-equivp)
    :short "Check if two types are equivalent."
    (type-case
     type1
     :var (type-case type2
                     :var (equal type1.name type2.name)
                     :otherwise nil)
     :base (type-case type2
                      :base (equal type1.type type2.type)
                      :otherwise nil)
     :array (type-case type2
                       :array (and (type-equivp type1.type type2.type)
                                   (index-equivp type1.index type2.index))
                       :otherwise nil)
     :fun (type-case type2
                     :fun (and (type-list-equivp type1.in type2.in)
                               (type-equivp type1.out type2.out))
                     :otherwise nil)
     :forall (type-case type2
                        :forall (and (equal type1.vars type2.vars)
                                     (type-equivp type1.type type2.type))
                        :otherwise nil)
     :pi (type-case type2
                    :pi (and (equal type1.vars type2.vars)
                             (type-equivp type1.type type2.type))
                    :otherwise nil)
     :sigma (type-case type2
                       :sigma (and (equal type1.vars type2.vars)
                                   (type-equivp type1.type type2.type))
                       :otherwise nil))
    :measure (+ (type-count type1) (type-count type2)))

  (define type-list-equivp ((types1 type-listp) (types2 type-listp))
    :returns (yes/no booleanp)
    :parents (type-equivalence types-equivp)
    :short "Check if two lists of types are equivalent."
    (or (and (endp types1)
             (endp types2))
        (and (consp types1)
             (consp types2)
             (type-equivp (car types1) (car types2))
             (type-list-equivp (cdr types1) (cdr types2))))
    :measure (+ (type-list-count types1) (type-list-count types2)))

  ///

  (fty::deffixequiv-mutual types-equivp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-all-equivp ((types type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (type-equivp (car types) (cadr types))
           (type-list-all-equivp (cdr types))))
  :prepwork ((local (in-theory (enable type-list-fix)))))
