; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values")
(include-book "type-equivalence")

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable acl2::string-string-map-quadruplep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-value-equivalence
  :parents (dynamic-semantics)
  :short "Equivalence of type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to "
    (xdoc::seetopic "type-equivalence" "type equivalence")
    ", but for type values instead of types.
     Type value equivalence is used in our dynamic semantics
     to perform certain defensive checks.")
   (xdoc::p
    "Similarly to type equivalence,
     for now we restrict type value equivalence to a decidable subset,
     which hinges on a decidable subset of ispace equivalence."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-values-equivp
  :short "Check if two type values or lists of type values are equivalent."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-value-equivp ((tval1 type-valuep) (tval2 type-valuep))
    :returns (yes/no booleanp)
    :parents (type-value-equivalence type-values-equivp)
    :short "Check if two type values are equivalent."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is very similar to @(tsee types-equivp),
       since type values are essentially a subset of types.")
     (xdoc::p
      "The two type values must be in the same summand.")
     (xdoc::p
      "In the case of two base type values, they must be identical.")
     (xdoc::p
      "In the case of two array type values,
       the element types must be equivalent,
       and the dimensions must be the same.
       Unlike array type equivalence,
       we do not need to check shape equivalence,
       because an array type value contains explicit dimensions.")
     (xdoc::p
      "In the case of two function type values,
       the input and output type values must be equivalent.")
     (xdoc::p
      "Universal, product, and sum type values are the same as
       universal, product, and sum types,
       so we check their equivalence in the same way:
       see @(tsee type-equivp)."))
    (type-value-case
     tval1
     :base (type-value-case
            tval2
            :base (equal tval1.type tval2.type)
            :otherwise nil)
     :array (type-value-case
             tval2
             :array (and (type-value-equivp tval1.elem tval2.elem)
                         (equal tval1.dims tval2.dims))
             :otherwise nil)
     :fun (type-value-case
           tval2
           :fun (and (type-value-list-equivp tval1.in tval2.in)
                     (type-value-equivp tval1.out tval2.out))
           :otherwise nil)
     :forall (type-value-case
              tval2
              :forall (b* ((used (set::union
                                  (set::union (set::mergesort tval1.params)
                                              (set::mergesort tval2.params))
                                  (set::union (type-all-type-vars tval1.body)
                                              (type-all-type-vars tval2.body))))
                           (maps (fresh-type-var-renaming tval1.params
                                                          tval2.params
                                                          used))
                           ((when (reserrp maps)) nil)
                           ((string-string-map-quadruple maps) maps)
                           (body1 (type-rename-type-vars tval1.body
                                                         maps.1st
                                                         maps.2nd))
                           (body2 (type-rename-type-vars tval2.body
                                                         maps.3rd
                                                         maps.4th)))
                        (type-equivp body1 body2))
              :otherwise nil)
     :pi (type-value-case
          tval2
          :pi (b* ((used (set::union
                          (set::union (set::mergesort tval1.params)
                                      (set::mergesort tval2.params))
                          (set::union (type-all-ispace-vars tval1.body)
                                      (type-all-ispace-vars tval2.body))))
                   (maps (fresh-ispace-var-renaming tval1.params
                                                    tval2.params
                                                    used))
                   ((when (reserrp maps)) nil)
                   ((string-string-map-quadruple maps) maps)
                   (body1 (type-rename-ispace-vars tval1.body
                                                   maps.1st
                                                   maps.2nd))
                   (body2 (type-rename-ispace-vars tval2.body
                                                   maps.3rd
                                                   maps.4th)))
                (type-equivp body1 body2))
          :otherwise nil)
     :sigma (type-value-case
             tval2
             :sigma (b* ((used (set::union
                                (set::union (set::mergesort tval1.params)
                                            (set::mergesort tval2.params))
                                (set::union (type-all-ispace-vars tval1.body)
                                            (type-all-ispace-vars tval2.body))))
                         (maps (fresh-ispace-var-renaming tval1.params
                                                          tval2.params
                                                          used))
                         ((when (reserrp maps)) nil)
                         ((string-string-map-quadruple maps) maps)
                         (body1 (type-rename-ispace-vars tval1.body
                                                         maps.1st
                                                         maps.2nd))
                         (body2 (type-rename-ispace-vars tval2.body
                                                         maps.3rd
                                                         maps.4th)))
                      (type-equivp body1 body2))
             :otherwise nil))
    :measure (+ (type-value-count tval1) (type-value-count tval2)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-value-list-equivp ((tvals1 type-value-listp)
                                  (tvals2 type-value-listp))
    :returns (yes/no booleanp)
    :parents (type-value-equivalence type-values-equivp)
    :short "Check if two lists of type values are the same modulo renaming."
    (or (and (endp tvals1)
             (endp tvals2))
        (and (consp tvals1)
             (consp tvals2)
             (type-value-equivp (car tvals1) (car tvals2))
             (type-value-list-equivp (cdr tvals1) (cdr tvals2))))
    :measure (+ (type-value-list-count tvals1) (type-value-list-count tvals2))

    ///

    (defrule same-len-when-type-value-list-equivp
      (implies (type-value-list-equivp tvals1 tvals2)
               (equal (len tvals1) (len tvals2)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :induct (acl2::cdr-cdr-induct tvals1 tvals2)
               :in-theory (enable acl2::atom)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual type-values-equivp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-value-list-all-equivp ((tvals type-value-listp))
  :returns (yes/no booleanp)
  :short "Check if all the type values in a list are equivalent."
  (or (endp tvals)
      (endp (cdr tvals))
      (and (type-value-equivp (car tvals) (cadr tvals))
           (type-value-list-all-equivp (cdr tvals)))))
