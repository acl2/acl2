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
  :short "Check if all the dimension additions in dimensions are binary."
  :types (dims)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :add (and (dim-list-binaddp dim.dims)
                  (equal (len dim.dims) 2))))
  :name ast-binaddp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce binmulp
  :short "Check if all the dimension multiplications in dimensions are binary."
  :types (dims)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :mul (and (dim-list-binmulp dim.dims)
                  (equal (len dim.dims) 2))))
  :name ast-binmulp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce unisubp
  :short "Check if all the dimension subtractions in dimensions are unary."
  :types (dims)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :sub (and (dim-list-unisubp dim.dims)
                  (equal (len dim.dims) 1))))
  :name ast-unisubp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nonullsubp
  :short "Check if all the dimension subtractions in dimensions
          are non-nullary."
  :types (dims)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :sub (and (dim-list-nonullsubp dim.dims)
                  (consp dim.dims))))
  :name ast-nonullsubp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-to-binadd-p
  :short "Check whether a dimension is equivalent to
          one with only binary additions."
  (defund-sk dim-equiv-to-binadd-p (dim)
    (exists (dim1)
            (and (dim= dim dim1)
                 (dim-binaddp dim1)))))

;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-to-binmul-p
  :short "Check whether a dimension is equivalent to
          one with only binary multiplications."
  (defund-sk dim-equiv-to-binmul-p (dim)
    (exists (dim1)
            (and (dim= dim dim1)
                 (dim-binmulp dim1)))))

;;;;;;;;;;;;;;;;;;;;

(defsection dim-equiv-to-unisub-p
  :short "Check whether a dimension is equivalent to
          one with only unary subtractions."
  (defund-sk dim-equiv-to-unisub-p (dim)
    (exists (dim1)
            (and (dim= dim dim1)
                 (dim-unisubp dim1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binarize-dims-in-add ((dims dim-listp))
  :returns (new-dim dimp)
  :short "Turn a list of dimensions in an addition
          into a dimension with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the dimension arguments of an addition dimension.")
   (xdoc::p
    "We show that the resulting dimension is equivalent to
     the addition of the argument dimensions.")
   (xdoc::p
    "We show that the resulting dimension
     only has binary additions if the argument dimensions do.
     This function is called after binarizing the dimensions
     passed as arguments to this function (see caller);
     that establishes the hypothesis of the theorem.")
   (xdoc::p
    "The equivalence theorem,
     and the related ones in @(tsee binarize-add-in-dims),
     are proved using the inference rule theorems.
     In the analogous theorems for multiplications,
     we used a different proof approach, for comparison.")
   (xdoc::p
    "We also show that this function preserves
     the binary status of multiplications
     and the unary and non-nullary statuses of subtractions,
     which this function does not affect.
     This serves to compose this transformation
     with the ones for multiplications and subtractions."))
  (cond ((endp dims) (dim-const 0))
        ((endp (cdr dims)) (dim-fix (car dims)))
        ((endp (cddr dims)) (dim-add dims))
        (t (binarize-dims-in-add (cons (dim-add (list (car dims)
                                                      (cadr dims)))
                                       (cddr dims)))))
  :measure (len dims)
  :verify-guards :after-returns

  ///

  (defret dim=-of-binarize-dims-in-add
    (implies (dim-listp dims)
             (dim= (dim-add dims) new-dim))
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
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binaddp-rules))
            '(:expand ((dim-binaddp (dim-add dims))
                       (dim-binaddp (dim-add (list (car dims)
                                                   (cadr dims))))))))

  (defret dim-binmulp-of-binarize-dims-in-add
    (implies (dim-list-binmulp dims)
             (dim-binmulp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binmulp-rules))))

  (defret dim-unisubp-of-binarize-dims-in-add
    (implies (dim-list-unisubp dims)
             (dim-unisubp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unisubp-rules))))

  (defret dim-nonullsubp-of-binarize-dims-in-add
    (implies (dim-list-nonullsubp dims)
             (dim-nonullsubp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nonullsubp-rules)))))

;;;;;;;;;;;;;;;;;;;;

(defines binarize-add-in-dims
  :short "Turn dimensions into equivalent ones with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the resulting dimensions are equivalent to
     the argument ones.")
   (xdoc::p
    "We show that the resulting dimensions only have binary additions.")
   (xdoc::p
    "We also show that these functions preserve
     the binary status of multiplications
     and the unary and non-nullary statuses of subtractions,
     which these functions do not affect.
     This serves to compose this transformation
     with the ones for multiplications and subtractions."))

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

  ///

  (fty::deffixequiv-mutual binarize-add-in-dims)

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
             :in-theory (e/d (dim=-refl
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
                                     (dim-sub->dims dim))))))))

  (defret-mutual dim-binaddp-of-binarize-add-in-dims
    (defret dim-binaddp-of-binarize-add-in-dim
      (dim-binaddp new-dim)
      :fn binarize-add-in-dim)
    (defret dim-list-binaddp-of-binarize-add-in-dim-list
      (dim-list-binaddp new-dims)
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-binaddp-rules))
            '(:expand ((dim-binaddp dim)))))

  (defret len-of-binarize-add-in-dim-list
    (equal (len new-dims)
           (len dims))
    :fn binarize-add-in-dim-list
    :hints (("Goal"
             :induct (len dims)
             :in-theory (enable (:induction len)))))

  (defret consp-of-binarize-add-in-dim-list
    (equal (consp new-dims)
           (consp dims))
    :fn binarize-add-in-dim-list
    :hints (("Goal" :expand ((binarize-add-in-dim-list dims)))))

  (defret-mutual dim-binmulp-of-binarize-add-in-dims
    (defret dim-binmulp-of-binarize-add-in-dim
      (implies (dim-binmulp dim)
               (dim-binmulp new-dim))
      :fn binarize-add-in-dim)
    (defret dim-list-binmulp-of-binarize-add-in-dim-list
      (implies (dim-list-binmulp dims)
               (dim-list-binmulp new-dims))
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-binmulp-rules))
            '(:expand ((dim-binmulp dim)
                       (dim-binmulp (dim-mul (binarize-add-in-dim-list
                                              (dim-mul->dims dim))))))))

  (defret-mutual dim-unisubp-of-binarize-add-in-dims
    (defret dim-unisubp-of-binarize-add-in-dim
      (implies (dim-unisubp dim)
               (dim-unisubp new-dim))
      :fn binarize-add-in-dim)
    (defret dim-list-unisubp-of-binarize-add-in-dim-list
      (implies (dim-list-unisubp dims)
               (dim-list-unisubp new-dims))
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-unisubp-rules))
            '(:expand ((dim-unisubp dim)
                       (dim-unisubp (dim-sub (binarize-add-in-dim-list
                                              (dim-sub->dims dim))))))))

  (defret-mutual dim-nonullsubp-of-binarize-add-in-dims
    (defret dim-nonullsubp-of-binarize-add-in-dim
      (implies (dim-nonullsubp dim)
               (dim-nonullsubp new-dim))
      :fn binarize-add-in-dim)
    (defret dim-list-nonullsubp-of-binarize-add-in-dim-list
      (implies (dim-list-nonullsubp dims)
               (dim-list-nonullsubp new-dims))
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-nonullsubp-rules))
            '(:expand ((dim-nonullsubp dim)
                       (dim-nonullsubp (dim-sub (binarize-add-in-dim-list
                                                 (dim-sub->dims dim)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binarize-dims-in-mul ((dims dim-listp))
  :returns (mv (new-dim dimp)
               (proof dim=-proofp))
  :short "Turn a list of dimensions in a multiplication
          into a dimension with only binary multiplications,
          and construct a proof tree demonstrating equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the dimension arguments of a multiplication dimension.")
   (xdoc::p
    "The proof tree proves the equivalence of
     @('(dim-mul dims)') and the new dimension.
     Its structure mirrors the recursion of this function:
     the base cases use the rules
     @('mul0'), @('mul1'), and @('refl'),
     while the recursive case chains, via the rule @('trans'),
     an instance of the rule @('mul3m')
     with the recursively built proof tree.")
   (xdoc::p
    "We use the constructed proof tree to show the equivalence,
     as we do in the related @(tsee binarize-mul-in-dims).
     This is a different approach than used for additions,
     for comparison of the two approaches.")
   (xdoc::p
    "We show that the resulting dimension
     only has binary multiplications if the argument dimensions do.
     This function is called after binarizing the dimensions
     passed as arguments to this function (see caller);
     that establishes the hypothesis of the theorem.
     This is proved without using the proof trees,
     similarly to additions.")
   (xdoc::p
    "We also show that this function preserves
     the binary status of additions
     and the unary and non-nullary statuses of subtractions,
     which this function does not affect.
     This serves to compose this transformation
     with the ones for additions and subtractions."))
  (cond ((endp dims) (mv (dim-const 1)
                         (dim=-proof-mul0)))
        ((endp (cdr dims)) (mv (dim-fix (car dims))
                               (dim=-proof-mul1 (dim-fix (car dims)))))
        ((endp (cddr dims)) (mv (dim-mul dims)
                                (dim=-proof-refl (dim-mul dims))))
        (t (b* ((dims1 (cons (dim-mul (list (car dims)
                                            (cadr dims)))
                             (cddr dims)))
                ((mv new-dim proof) (binarize-dims-in-mul dims1)))
             (mv new-dim
                 (make-dim=-proof-trans
                  :d1 (dim-mul dims)
                  :d2 (dim-mul dims1)
                  :d3 new-dim
                  :premise1-proof (make-dim=-proof-mul3m
                                   :d1 (dim-fix (car dims))
                                   :d2 (dim-fix (cadr dims))
                                   :ds (dim-list-fix (cddr dims)))
                  :premise2-proof proof)))))
  :measure (len dims)
  :verify-guards :after-returns

  ///

  (defret dim=-proof-validp-of-binarize-dims-in-mul
    (implies (dim-listp dims)
             (dim=-proof-validp proof
                                (dim-mul dims)
                                new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable dim=-proof-validp
                                dim=-refl-validp
                                dim=-trans-validp
                                dim=-mul0-validp
                                dim=-mul1-validp
                                dim=-mul3m-validp))))

  (defret dim-binmulp-of-binarize-dims-in-mul
    (implies (dim-list-binmulp dims)
             (dim-binmulp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binmulp-rules))
            '(:expand ((dim-binmulp (dim-mul dims))
                       (dim-binmulp (dim-mul (list (car dims)
                                                   (cadr dims))))))))

  (defret dim-binaddp-of-binarize-dims-in-mul
    (implies (dim-list-binaddp dims)
             (dim-binaddp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binaddp-rules))))

  (defret dim-unisubp-of-binarize-dims-in-mul
    (implies (dim-list-unisubp dims)
             (dim-unisubp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unisubp-rules))))

  (defret dim-nonullsubp-of-binarize-dims-in-mul
    (implies (dim-list-nonullsubp dims)
             (dim-nonullsubp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nonullsubp-rules)))))

;;;;;;;;;;;;;;;;;;;;

(defines binarize-mul-in-dims
  :short "Turn dimensions into equivalent ones
          with only binary multiplications,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the resulting dimensions are equivalent to
     the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting dimensions only have binary multiplications.")
   (xdoc::p
    "We also show that these functions preserve
     the binary status of additions
     and the unary and non-nullary statuses of subtractions,
     which these functions do not affect.
     This serves to compose this transformation
     with the ones for additions and subtractions."))

  (define binarize-mul-in-dim ((dim dimp))
    :returns (mv (new-dim dimp)
                 (proof dim=-proofp))
    :parents (ispace-equivalence-properties binarize-mul-in-dims)
    :short "Turn a dimension into
            an equivalent one with only binary multiplications,
            and construct a proof tree demonstrating the equivalence."
    (dim-case
     dim
     :var (mv (dim-var dim.name)
              (dim=-proof-refl (dim-var dim.name)))
     :const (mv (dim-const dim.val)
                (dim=-proof-refl (dim-const dim.val)))
     :add (b* (((mv new-dims proof) (binarize-mul-in-dim-list dim.dims)))
            (mv (dim-add new-dims)
                (make-dim=-proof-cong-add
                 :ds1 dim.dims
                 :ds2 new-dims
                 :premise1-proof proof)))
     :mul (b* (((mv new-dims proof) (binarize-mul-in-dim-list dim.dims))
               ((mv new-dim proof1) (binarize-dims-in-mul new-dims)))
            (mv new-dim
                (make-dim=-proof-trans
                 :d1 (dim-mul dim.dims)
                 :d2 (dim-mul new-dims)
                 :d3 new-dim
                 :premise1-proof (make-dim=-proof-cong-mul
                                  :ds1 dim.dims
                                  :ds2 new-dims
                                  :premise1-proof proof)
                 :premise2-proof proof1)))
     :sub (b* (((mv new-dims proof) (binarize-mul-in-dim-list dim.dims)))
            (mv (dim-sub new-dims)
                (make-dim=-proof-cong-sub
                 :ds1 dim.dims
                 :ds2 new-dims
                 :premise1-proof proof))))
    :measure (dim-count dim))

  (define binarize-mul-in-dim-list ((dims dim-listp))
    :returns (mv (new-dims dim-listp)
                 (proof dims=-proofp))
    :parents (ispace-equivalence-properties binarize-mul-in-dims)
    :short "Turn a list of dimensions into
            an equivalent one with only binary multiplications,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp dims)) (mv nil (dims=-proof-refl nil)))
         ((mv new-dim proof1) (binarize-mul-in-dim (car dims)))
         ((mv new-dims proof2) (binarize-mul-in-dim-list (cdr dims))))
      (mv (cons new-dim new-dims)
          (make-dims=-proof-cong-cons
           :d1 (dim-fix (car dims))
           :d2 new-dim
           :ds1 (dim-list-fix (cdr dims))
           :ds2 new-dims
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (dim-list-count dims))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual binarize-mul-in-dims)

  (defret-mutual dim=-proof-validp-of-binarize-mul-in-dims
    (defret dim=-proof-validp-of-binarize-mul-in-dim
      (implies (dimp dim)
               (dim=-proof-validp proof
                                  dim
                                  new-dim))
      :fn binarize-mul-in-dim)
    (defret dims=-proof-validp-of-binarize-mul-in-dim-list
      (implies (dim-listp dims)
               (dims=-proof-validp proof
                                   dims
                                   new-dims))
      :fn binarize-mul-in-dim-list)
    :hints (("Goal"
             :in-theory (enable dim=-proof-validp
                                dims=-proof-validp
                                dim=-refl-validp
                                dim=-trans-validp
                                dim=-cong-add-validp
                                dim=-cong-mul-validp
                                dim=-cong-sub-validp
                                dims=-refl-validp
                                dims=-cong-cons-validp))))

  (defret-mutual dim-binmulp-of-binarize-mul-in-dims
    (defret dim-binmulp-of-binarize-mul-in-dim
      (dim-binmulp new-dim)
      :fn binarize-mul-in-dim)
    (defret dim-list-binmulp-of-binarize-mul-in-dim-list
      (dim-list-binmulp new-dims)
      :fn binarize-mul-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-binmulp-rules))
            '(:expand ((dim-binmulp dim)))))

  (defret len-of-binarize-mul-in-dim-list
    (equal (len new-dims)
           (len dims))
    :fn binarize-mul-in-dim-list
    :hints (("Goal"
             :induct (len dims)
             :in-theory (enable (:induction len)))))

  (defret consp-of-binarize-mul-in-dim-list
    (equal (consp new-dims)
           (consp dims))
    :fn binarize-mul-in-dim-list
    :hints (("Goal" :expand ((binarize-mul-in-dim-list dims)))))

  (defret-mutual dim-binaddp-of-binarize-mul-in-dims
    (defret dim-binaddp-of-binarize-mul-in-dim
      (implies (dim-binaddp dim)
               (dim-binaddp new-dim))
      :fn binarize-mul-in-dim)
    (defret dim-list-binaddp-of-binarize-mul-in-dim-list
      (implies (dim-list-binaddp dims)
               (dim-list-binaddp new-dims))
      :fn binarize-mul-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-binaddp-rules))
            '(:expand ((dim-binaddp dim)
                       (dim-binaddp (dim-add (mv-nth 0 (binarize-mul-in-dim-list
                                                        (dim-add->dims dim)))))))))

  (defret-mutual dim-unisubp-of-binarize-mul-in-dims
    (defret dim-unisubp-of-binarize-mul-in-dim
      (implies (dim-unisubp dim)
               (dim-unisubp new-dim))
      :fn binarize-mul-in-dim)
    (defret dim-list-unisubp-of-binarize-mul-in-dim-list
      (implies (dim-list-unisubp dims)
               (dim-list-unisubp new-dims))
      :fn binarize-mul-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-unisubp-rules))
            '(:expand ((dim-unisubp dim)
                       (dim-unisubp (dim-sub (mv-nth 0 (binarize-mul-in-dim-list
                                                        (dim-sub->dims dim)))))))))

  (defret-mutual dim-nonullsubp-of-binarize-mul-in-dims
    (defret dim-nonullsubp-of-binarize-mul-in-dim
      (implies (dim-nonullsubp dim)
               (dim-nonullsubp new-dim))
      :fn binarize-mul-in-dim)
    (defret dim-list-nonullsubp-of-binarize-mul-in-dim-list
      (implies (dim-list-nonullsubp dims)
               (dim-list-nonullsubp new-dims))
      :fn binarize-mul-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-nonullsubp-rules))
            '(:expand ((dim-nonullsubp dim)
                       (dim-nonullsubp (dim-sub (mv-nth 0 (binarize-mul-in-dim-list
                                                           (dim-sub->dims dim))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unarize-dims-in-sub ((dims dim-listp))
  :returns (mv (new-dim dimp)
               (proof dim=-proofp))
  :short "Turn a list of dimensions in a subtraction
          into a dimension with only unary subtractions,
          and construct a proof tree demonstrating equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the dimension arguments of a subtraction dimension.")
   (xdoc::p
    "A subtraction of two or more dimensions is turned into
     the addition of the first dimension
     and the unary subtraction of the addition of the remaining dimensions,
     according to the rule @('sub2m').
     A subtraction of one dimension is already unary,
     and is left unchanged.
     A subtraction of no dimensions is illegal and cannot be reduced
     (see @(see dim-equiv-infrules)),
     so it is also left unchanged.
     Unlike @(tsee binarize-dims-in-add) and @(tsee binarize-dims-in-mul),
     this function is not recursive,
     because one application of @('sub2m') suffices.")
   (xdoc::p
    "The proof tree proves the equivalence of
     @('(dim-sub dims)') and the new dimension.
     The cases of no dimensions and of one dimension
     use the rule @('refl'),
     while the case of two or more dimensions uses the rule @('sub2m').")
   (xdoc::p
    "We use the constructed proof tree to show the equivalence,
     as we do in the related @(tsee unarize-sub-in-dims).")
   (xdoc::p
    "We show that the resulting dimension only has unary subtractions
     if the argument dimensions do and there is at least one of them.
     This function is called after unarizing the subtractions
     in the dimensions passed as arguments to this function (see caller);
     that establishes the first hypothesis of the theorem."))
  (cond ((endp dims) (mv (dim-sub nil)
                         (dim=-proof-refl (dim-sub nil))))
        ((endp (cdr dims)) (mv (dim-sub dims)
                               (dim=-proof-refl (dim-sub dims))))
        (t (mv (dim-add (list (dim-fix (car dims))
                              (dim-sub (list (dim-add
                                              (dim-list-fix (cdr dims)))))))
               (make-dim=-proof-sub2m
                :d (dim-fix (car dims))
                :ds (dim-list-fix (cdr dims))))))

  ///

  (defret dim=-proof-validp-of-unarize-dims-in-sub
    (implies (dim-listp dims)
             (dim=-proof-validp proof
                                (dim-sub dims)
                                new-dim))
    :hints (("Goal" :in-theory (enable dim=-proof-validp
                                       dim=-refl-validp
                                       dim=-sub2m-validp))))

  (defret dim-unisubp-of-unarize-dims-in-sub
    (implies (and (dim-list-unisubp dims)
                  (consp dims))
             (dim-unisubp new-dim))
    :hints (("Goal"
             :in-theory (enable* ast-unisubp-rules))
            '(:expand ((dim-unisubp (dim-sub dims))
                       (dim-unisubp (dim-sub (list (dim-add
                                                    (cdr dims))))))))))

;;;;;;;;;;;;;;;;;;;;

(defines unarize-sub-in-dims
  :short "Turn dimensions into equivalent ones
          with only unary subtractions,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the resulting dimensions are equivalent to
     the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting dimensions only have unary subtractions
     if the argument ones have no nullary subtractions."))

  (define unarize-sub-in-dim ((dim dimp))
    :returns (mv (new-dim dimp)
                 (proof dim=-proofp))
    :parents (ispace-equivalence-properties unarize-sub-in-dims)
    :short "Turn a dimension into
            an equivalent one with only unary subtractions,
            and construct a proof tree demonstrating the equivalence."
    (dim-case
     dim
     :var (mv (dim-var dim.name)
              (dim=-proof-refl (dim-var dim.name)))
     :const (mv (dim-const dim.val)
                (dim=-proof-refl (dim-const dim.val)))
     :add (b* (((mv new-dims proof) (unarize-sub-in-dim-list dim.dims)))
            (mv (dim-add new-dims)
                (make-dim=-proof-cong-add
                 :ds1 dim.dims
                 :ds2 new-dims
                 :premise1-proof proof)))
     :mul (b* (((mv new-dims proof) (unarize-sub-in-dim-list dim.dims)))
            (mv (dim-mul new-dims)
                (make-dim=-proof-cong-mul
                 :ds1 dim.dims
                 :ds2 new-dims
                 :premise1-proof proof)))
     :sub (b* (((mv new-dims proof) (unarize-sub-in-dim-list dim.dims))
               ((mv new-dim proof1) (unarize-dims-in-sub new-dims)))
            (mv new-dim
                (make-dim=-proof-trans
                 :d1 (dim-sub dim.dims)
                 :d2 (dim-sub new-dims)
                 :d3 new-dim
                 :premise1-proof (make-dim=-proof-cong-sub
                                  :ds1 dim.dims
                                  :ds2 new-dims
                                  :premise1-proof proof)
                 :premise2-proof proof1))))
    :measure (dim-count dim))

  (define unarize-sub-in-dim-list ((dims dim-listp))
    :returns (mv (new-dims dim-listp)
                 (proof dims=-proofp))
    :parents (ispace-equivalence-properties unarize-sub-in-dims)
    :short "Turn a list of dimensions into
            an equivalent one with only unary subtractions,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp dims)) (mv nil (dims=-proof-refl nil)))
         ((mv new-dim proof1) (unarize-sub-in-dim (car dims)))
         ((mv new-dims proof2) (unarize-sub-in-dim-list (cdr dims))))
      (mv (cons new-dim new-dims)
          (make-dims=-proof-cong-cons
           :d1 (dim-fix (car dims))
           :d2 new-dim
           :ds1 (dim-list-fix (cdr dims))
           :ds2 new-dims
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (dim-list-count dims))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unarize-sub-in-dims)

  (defret consp-of-unarize-sub-in-dim-list
    (equal (consp new-dims)
           (consp dims))
    :fn unarize-sub-in-dim-list
    :hints (("Goal" :expand ((unarize-sub-in-dim-list dims)))))

  (defret-mutual dim=-proof-validp-of-unarize-sub-in-dims
    (defret dim=-proof-validp-of-unarize-sub-in-dim
      (implies (dimp dim)
               (dim=-proof-validp proof
                                  dim
                                  new-dim))
      :fn unarize-sub-in-dim)
    (defret dims=-proof-validp-of-unarize-sub-in-dim-list
      (implies (dim-listp dims)
               (dims=-proof-validp proof
                                   dims
                                   new-dims))
      :fn unarize-sub-in-dim-list)
    :hints (("Goal"
             :in-theory (enable dim=-proof-validp
                                dims=-proof-validp
                                dim=-refl-validp
                                dim=-trans-validp
                                dim=-cong-add-validp
                                dim=-cong-mul-validp
                                dim=-cong-sub-validp
                                dims=-refl-validp
                                dims=-cong-cons-validp))))

  (defret-mutual dim-unisubp-of-unarize-sub-in-dims
    (defret dim-unisubp-of-unarize-sub-in-dim
      (implies (dim-nonullsubp dim)
               (dim-unisubp new-dim))
      :fn unarize-sub-in-dim)
    (defret dim-list-unisubp-of-unarize-sub-in-dim-list
      (implies (dim-list-nonullsubp dims)
               (dim-list-unisubp new-dims))
      :fn unarize-sub-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-unisubp-rules
                                 ast-nonullsubp-rules))
            '(:expand ((dim-nonullsubp dim)
                       (dim-unisubp dim))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dim-equiv-to-binadd-p-when-dimp
  :short "Every dimension is equivalent to one with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rules @('add0'), @('add1'), and @('add3m'),
     described in @(see dim-equiv-infrules)."))
  (implies (dimp dim)
           (dim-equiv-to-binadd-p dim))
  :use (:instance dim-equiv-to-binadd-p-suff
                  (dim1 (binarize-add-in-dim dim))))

;;;;;;;;;;;;;;;;;;;;

(defruled dim-equiv-to-binmul-p-when-dimp
  :short "Every dimension is equivalent to one
          with only binary multiplications."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to validate the intention of
     rules @('mul0'), @('mul1'), and @('mul3m'),
     described in @(see dim-equiv-infrules)."))
  (implies (dimp dim)
           (dim-equiv-to-binmul-p dim))
  :use ((:instance dim-equiv-to-binmul-p-suff
                   (dim1 (mv-nth 0 (binarize-mul-in-dim dim))))
        (:instance dim=-suff
                   (proof (mv-nth 1 (binarize-mul-in-dim dim)))
                   (dim1 dim)
                   (dim2 (mv-nth 0 (binarize-mul-in-dim dim))))))

;;;;;;;;;;;;;;;;;;;;

(defruled dim-equiv-to-unisub-p-when-dimp-and-nonullsubp
  :short "Every dimension without nullary subtractions
          is equivalent to one with only unary subtractions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of rule @('sub2m'),
     described in @(see dim-equiv-infrules):
     variadic subtractions are reduced to unary ones.
     Since nullary subtractions are illegal and cannot be reduced
     (each one is only equivalent to itself, via reflexivity),
     the theorem assumes that the dimension has no nullary subtractions."))
  (implies (and (dimp dim)
                (dim-nonullsubp dim))
           (dim-equiv-to-unisub-p dim))
  :use ((:instance dim-equiv-to-unisub-p-suff
                   (dim1 (mv-nth 0 (unarize-sub-in-dim dim))))
        (:instance dim=-suff
                   (proof (mv-nth 1 (unarize-sub-in-dim dim)))
                   (dim1 dim)
                   (dim2 (mv-nth 0 (unarize-sub-in-dim dim))))))
