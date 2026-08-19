; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-infrules")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-properties
  :parents (static-semantics)
  :short "Properties of ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove properties of the equivalence predicates
     defined via inference rules in
     @(see ispace-equivalence-inference-rules).
     These properties help validating the definition of the predicates,
     and also provide reasoning tools for them.")
   (xdoc::ul
    (xdoc::li
     "We show that the predicates hold
      only of values of the expected types
      (e.g. @(tsee dim=) only holds on @(tsee dim) values).")
    (xdoc::li
     "We prove some derived rules to help reason about the predicates.
      Some of these rely on the properties described in the previous bullet
      to shed hypotheses about types of values.")
    (xdoc::li
     "We prove that some of the rules in fact realize
      the reductions claimed in @(see dim-equiv-infrules),
      e.g. that @('add0'), @('add1'), and @('add3m')
      reduce all variadic additions to binary ones
      (while nullary and unary ones reduce to constants).
      To do that, we introduce predicates to formalize these notions,
      and functions to witness the ability to perform the reduction.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-holds-only-on-dimensions
  :short "The equivalence of dimensions and lists of dimensions
          holds only on dimensions and lists of dimensions."

  (defthm-dim=-proof-validp-clique-flag
    (defthmd dimp-when-dim=-proof-validp
      (implies (dim=-proof-validp proof concl.dim1 concl.dim2)
               (and (dimp concl.dim1)
                    (dimp concl.dim2)))
      :flag dim=-proof-validp)
    (defthmd dim-listp-when-dims=-proof-validp
      (implies (dims=-proof-validp proof concl.dims1 concl.dims2)
               (and (dim-listp concl.dims1)
                    (dim-listp concl.dims2)))
      :flag dims=-proof-validp)
    :hints (("Goal" :in-theory (enable dim=-proof-validp
                                       dims=-proof-validp
                                       dim=-refl-validp
                                       dim=-symm-validp
                                       dim=-trans-validp
                                       dims=-refl-validp
                                       dims=-symm-validp
                                       dims=-trans-validp
                                       dim=-cong-add-validp
                                       dim=-cong-sub-validp
                                       dim=-cong-mul-validp
                                       dims=-cong-cons-validp
                                       dim=-add0-validp
                                       dim=-add1-validp
                                       dim=-add3m-validp
                                       dim=-mul0-validp
                                       dim=-mul1-validp
                                       dim=-mul3m-validp
                                       dim=-sub2m-validp
                                       dim=-add-comm-validp
                                       dim=-add-assoc-validp
                                       dim=-add-id-validp
                                       dim=-add-inv-validp
                                       dim=-add-const-validp
                                       dim=-mul-comm-validp
                                       dim=-mul-assoc-validp
                                       dim=-mul-id-validp
                                       dim=-mul-const-validp
                                       dim=-distrib-validp))))

  (defruled dimp-when-dim=
    (implies (dim= dim1 dim2)
             (and (dimp dim1)
                  (dimp dim2)))
    :enable (dim= dimp-when-dim=-proof-validp))

  (defruled dim-listp-when-dims=
    (implies (dims= dims1 dims2)
             (and (dim-listp dims1)
                  (dim-listp dims2)))
    :enable (dims= dim-listp-when-dims=-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-equiv-holds-only-on-shapes/ispaces
  :short "The equivalence of shapes, ispaces, and lists thereof
          holds only on shapes, ispaces, and lists thereof."

  (defthm-shp=-proof-validp-clique-flag
    (defthmd shapep-when-shp=-proof-validp
      (implies (shp=-proof-validp proof concl.shp1 concl.shp2)
               (and (shapep concl.shp1)
                    (shapep concl.shp2)))
      :flag shp=-proof-validp)
    (defthmd shape-listp-when-shps=-proof-validp
      (implies (shps=-proof-validp proof concl.shps1 concl.shps2)
               (and (shape-listp concl.shps1)
                    (shape-listp concl.shps2)))
      :flag shps=-proof-validp)
    (defthmd ispacep-when-isp=-proof-validp
      (implies (isp=-proof-validp proof concl.isp1 concl.isp2)
               (and (ispacep concl.isp1)
                    (ispacep concl.isp2)))
      :flag isp=-proof-validp)
    (defthmd ispace-listp-when-isps=-proof-validp
      (implies (isps=-proof-validp proof concl.isps1 concl.isps2)
               (and (ispace-listp concl.isps1)
                    (ispace-listp concl.isps2)))
      :flag isps=-proof-validp)
    :hints (("Goal" :in-theory (enable shp=-proof-validp
                                       shps=-proof-validp
                                       isp=-proof-validp
                                       isps=-proof-validp
                                       shp=-refl-validp
                                       shp=-symm-validp
                                       shp=-trans-validp
                                       shps=-refl-validp
                                       shps=-symm-validp
                                       shps=-trans-validp
                                       isp=-refl-validp
                                       isp=-symm-validp
                                       isp=-trans-validp
                                       isps=-refl-validp
                                       isps=-symm-validp
                                       isps=-trans-validp
                                       shp=-cong-dims-validp
                                       shp=-cong-append-validp
                                       shp=-cong-splice-validp
                                       isp=-cong-dim-validp
                                       isp=-cong-shape-validp
                                       shps=-cong-cons-validp
                                       isps=-cong-cons-validp
                                       shp=-dims0-validp
                                       shp=-dims2m-validp
                                       shp=-append1-validp
                                       shp=-append3m-validp
                                       shp=-splice0-validp
                                       shp=-splice1m-dim-validp
                                       shp=-splice1m-shape-validp
                                       shp=-append-assoc-validp
                                       shp=-append-id-left-validp
                                       shp=-append-id-right-validp
                                       isp=-ispace-dim-shape-validp))))

  (defruled shapep-when-shp=
    (implies (shp= shp1 shp2)
             (and (shapep shp1)
                  (shapep shp2)))
    :enable (shp= shapep-when-shp=-proof-validp))

  (defruled shape-listp-when-shps=
    (implies (shps= shps1 shps2)
             (and (shape-listp shps1)
                  (shape-listp shps2)))
    :enable (shps= shape-listp-when-shps=-proof-validp))

  (defruled ispacep-when-isp=
    (implies (isp= isp1 isp2)
             (and (ispacep isp1)
                  (ispacep isp2)))
    :enable (isp= ispacep-when-isp=-proof-validp))

  (defruled ispace-listp-when-isps=
    (implies (isps= isps1 isps2)
             (and (ispace-listp isps1)
                  (ispace-listp isps2)))
    :enable (isps= ispace-listp-when-isps=-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-derived-rules
  :short "Some derived inference rules about dimension equivalence."

  (defruled dim=-trans-swapped
    (implies (and (dim= d2 d3)
                  (dim= d1 d2))
             (dim= d1 d3))
    :use dim=-trans
    :enable dimp-when-dim=))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce binaddp
  :short "Check if all the dimension additions are binary."
  :types (dims)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :add (and (dim-list-binaddp dim.dims)
                  (equal (len dim.dims) 2))))
  :name ast-binaddp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-to-binadd-p
  :short "Check whether a dimension is equivalent to
          one with only binary additions."
  (defund-sk dim-equiv-to-binadd-p (dim)
    (exists (dim1)
            (and (dim= dim dim1)
                 (dim-binaddp dim1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binarize-dims-in-add ((dims dim-listp))
  :returns (new-dim dimp)
  :short "Turn a list of dimensions in an addition
          into a dimension with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used, along with @(tsee binarize-add-in-dims),
     to show that every dimension is equivalent to
     one with only binary additions."))
  (cond ((endp dims) (dim-const 0))
        ((endp (cdr dims)) (dim-fix (car dims)))
        ((endp (cddr dims)) (dim-add dims))
        (t (binarize-dims-in-add (cons (dim-add (list (car dims)
                                                   (cadr dims)))
                                    (cddr dims)))))
  :measure (len dims)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defines binarize-add-in-dims
  :short "Turn dimensions into equivalent ones with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used, along with @(tsee binarize-dims-in-add),
     to show that every dimension is equivalent to
     one with only binary additions."))

  (define binarize-add-in-dim ((dim dimp))
    :returns (new-dim dimp)
    :parents (ispace-equivalence-properties binarize-add-in-dims)
    :short "Turn a dimension into
            an equivalent one with only binary additions."
    (dim-case
     dim
     :var (dim-var dim.name)
     :const (dim-const dim.val)
     :add (binarize-dims-in-add (binarize-add-in-dim-list dim.dims))
     :mul (dim-mul (binarize-add-in-dim-list dim.dims))
     :sub (dim-sub (binarize-add-in-dim-list dim.dims)))
    :measure (dim-count dim))

  (define binarize-add-in-dim-list ((dims dim-listp))
    :returns (new-dims dim-listp)
    :parents (ispace-equivalence-properties binarize-add-in-dims)
    :short "Turn a list of dimensions into
            an equivalent one with only binary additions."
    (cond ((endp dims) nil)
          (t (cons (binarize-add-in-dim (car dims))
                   (binarize-add-in-dim-list (cdr dims)))))
    :measure (dim-list-count dims))

  :verify-guards :after-returns

  :flag-local nil

  ///

  (fty::deffixequiv-mutual binarize-add-in-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-to-binadd-p-when-dimp
  :short "Every dimension is equivalent to one with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to validate the intention of
     rules @('add0'), @('add1'), and @('add3m'),
     described in @(see dim-equiv-infrules).")
   (xdoc::p
    "We show that the functions that we have defined
     to reduce variadic additions to binary ones
     (including eliminating nullary and unary additions),
     yield equivalent dimensions with only binary additions."))

  (defret dim=-of-binarize-dims-in-add
    (implies (dim-listp dims)
             (dim= (dim-add dims) new-dim))
    :fn binarize-dims-in-add
    :hints (("Goal"
             :induct t
             :in-theory (enable binarize-dims-in-add
                                dim=-refl
                                dim=-add1
                                dim=-add3m
                                dim=-trans-swapped))
            '(:use (dim=-add0))))

  (defret dim-binaddp-of-binarize-dims-in-add
    (implies (dim-list-binaddp dims)
             (dim-binaddp new-dim))
    :fn binarize-dims-in-add
    :hints (("Goal"
             :induct t
             :in-theory (enable* binarize-dims-in-add
                                 ast-binaddp-rules))
            '(:expand ((dim-binaddp (dim-add dims))
                       (dim-binaddp (dim-add (list (car dims)
                                                   (cadr dims))))))))

  (defret-mutual dim=-of-binarize-add-in-dims
    (defret dim=-of-binarize-add-in-dim
      (implies (dimp dim)
               (dim= dim new-dim))
      :fn binarize-add-in-dim)
    (defret dims=-of-binarize-add-in-dim-list
      (implies (dim-listp dims)
               (dims= dims new-dims))
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (e/d (binarize-add-in-dim
                              binarize-add-in-dim-list
                              dim=-refl
                              dim=-trans-swapped
                              dims=-refl
                              dims=-cong-cons)
                             (dim=-of-binarize-dims-in-add)))
            '(:use ((:instance dim=-of-binarize-dims-in-add
                               (dims (binarize-add-in-dim-list
                                      (dim-add->dims dim))))
                    (:instance dim=-cong-add
                               (ds1 (dim-add->dims dim))
                               (ds2 (binarize-add-in-dim-list
                                     (dim-add->dims dim))))
                    (:instance dim=-cong-mul
                               (ds1 (dim-mul->dims dim))
                               (ds2 (binarize-add-in-dim-list
                                     (dim-mul->dims dim))))
                    (:instance dim=-cong-sub
                               (ds1 (dim-sub->dims dim))
                               (ds2 (binarize-add-in-dim-list
                                     (dim-sub->dims dim)))))))
    :mutual-recursion binarize-add-in-dims)

  (defret-mutual dim-binaddp-of-binarize-add-in-dims
    (defret dim-binaddp-of-binarize-add-in-dim
      (dim-binaddp new-dim)
      :fn binarize-add-in-dim)
    (defret dim-list-binaddp-of-binarize-add-in-dim-list
      (dim-list-binaddp new-dims)
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* binarize-add-in-dim
                                 binarize-add-in-dim-list
                                 ast-binaddp-rules))
            '(:expand ((dim-binaddp dim))))
    :mutual-recursion binarize-add-in-dims)

  (defruled dim-equiv-to-binadd-p-when-dimp
    (implies (dimp dim)
             (dim-equiv-to-binadd-p dim))
    :use (:instance dim-equiv-to-binadd-p-suff
                    (dim1 (binarize-add-in-dim dim)))))
