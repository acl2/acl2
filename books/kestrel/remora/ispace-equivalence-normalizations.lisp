; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-derived-rules")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-normalizations
  :parents (static-semantics)
  :short "Properties of ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that some of the rules in fact realize
     the reductions claimed in @(see dim-equiv-infrules),
     e.g. that @('add0'), @('add1'), and @('add3m')
     reduce all variadic additions to binary ones
     (while nullary and unary ones reduce to constants).
     To do that, we introduce predicates to formalize these notions,
     and functions to witness the ability to perform the reduction."))
  :order-subtopics t
  :default-parent t)

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

(fty::deffold-reduce unidimsp
  :short "Check if all the dimension shapes in shapes and ispaces are unary."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if all the shapes built from lists of dimensions
     are built from lists of exactly one dimension.
     The dimensions themselves are not constrained."))
  :types (shapes/ispaces)
  :result booleanp
  :default t
  :combine and
  :override
  ((shape :dims (equal (len shape.dims) 1)))
  :name ast-unidimsp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nullbinappendp
  :short "Check if all the shape concatenations in shapes and ispaces
          are binary or empty."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike additions and multiplications of dimensions,
     whose nullary forms are reduced to constants by the rules,
     the empty concatenation is itself a normal form,
     playing the role of the identity of concatenation;
     there is no rule to eliminate it.
     Thus, this predicate allows empty concatenations,
     besides binary ones."))
  :types (shapes/ispaces)
  :result booleanp
  :default t
  :combine and
  :override
  ((shape :append (and (shape-list-nullbinappendp shape.shapes)
                       (or (endp shape.shapes)
                           (equal (len shape.shapes) 2)))))
  :name ast-nullbinappendp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nosplicep
  :short "Check if there are no shape splices in shapes and ispaces."
  :types (shapes/ispaces)
  :result booleanp
  :default t
  :combine and
  :override
  ((shape :splice nil))
  :name ast-nosplicep)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nodimispacep
  :short "Check if there are no dimension ispaces in shapes and ispaces."
  :types (shapes/ispaces)
  :result booleanp
  :default t
  :combine and
  :override
  ((ispace :dim nil))
  :name ast-nodimispacep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-binadd-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only binary additions."
  (exists (dim1)
          (and (dim= dim dim1)
               (dim-binaddp dim1)))
  :verify-guards nil) ; because DIM= is not guard-verified

;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-binmul-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only binary multiplications."
  (exists (dim1)
          (and (dim= dim dim1)
               (dim-binmulp dim1)))
  :verify-guards nil) ; because DIM= is not guard-verified

;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-unisub-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only unary subtractions."
  (exists (dim1)
          (and (dim= dim dim1)
               (dim-unisubp dim1)))
  :verify-guards nil) ; because DIM= is not guard-verified

;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-binadd-binmul-unisub-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only
          binary additions,
          binary multiplications,
          and unary subtractions."
  (exists (dim1)
          (and (dim= dim dim1)
               (dim-binaddp dim1)
               (dim-binmulp dim1)
               (dim-unisubp dim1)))
  :verify-guards nil) ; because DIM= is not guard-verified

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk shape-equiv-to-unidims-p (shape)
  :returns (yes/no booleanp)
  :short "Check whether a shape is equivalent to
          one with only unary dimension shapes."
  (exists (shape1)
          (and (shp= shape shape1)
               (shape-unidimsp shape1)))
  :verify-guards nil) ; because SHP= is not guard-verified

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;

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
    :parents (ispace-equivalence-normalizations binarize-add-in-dims)
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
    :parents (ispace-equivalence-normalizations binarize-add-in-dims)
    :short "Turn a list of dimensions into
            an equivalent one with only binary additions."
    (cond ((endp dims) nil)
          (t (cons (binarize-add-in-dim (car dims))
                   (binarize-add-in-dim-list (cdr dims)))))
    :measure (dim-list-count dims)

    ///

    (defret len-of-binarize-add-in-dim-list
      (equal (len new-dims)
             (len dims))
      :hints (("Goal"
               :induct (len dims)
               :in-theory (enable (:induction len)))))

    (defret consp-of-binarize-add-in-dim-list
      (equal (consp new-dims)
             (consp dims))
      :hints (("Goal" :expand ((binarize-add-in-dim-list dims))))))

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

;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;

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
    :parents (ispace-equivalence-normalizations binarize-mul-in-dims)
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
    :parents (ispace-equivalence-normalizations binarize-mul-in-dims)
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
    :measure (dim-list-count dims)

    ///

    (defret len-of-binarize-mul-in-dim-list
      (equal (len new-dims)
             (len dims))
      :hints (("Goal"
               :induct (len dims)
               :in-theory (enable (:induction len)))))

    (defret consp-of-binarize-mul-in-dim-list
      (equal (consp new-dims)
             (consp dims))
      :hints (("Goal" :expand ((binarize-mul-in-dim-list dims))))))

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
                       (dim-binaddp
                        (dim-add (mv-nth 0 (binarize-mul-in-dim-list
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
                       (dim-unisubp
                        (dim-sub (mv-nth 0 (binarize-mul-in-dim-list
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
                       (dim-nonullsubp
                        (dim-sub (mv-nth 0 (binarize-mul-in-dim-list
                                            (dim-sub->dims dim))))))))))

;;;;;;;;;;;;;;;;;;;;

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
     that establishes the first hypothesis of the theorem.")
   (xdoc::p
    "We also show that this function preserves
     the binary status of multiplications,
     which this function does not affect.
     Unlike the other transformations,
     this function does not preserve the binary status of additions:
     the right-hand side of the rule @('sub2m') introduces
     an addition of the remaining argument dimensions,
     which is binary only when there are exactly three argument dimensions.
     Thus, the binarization of additions must be applied
     after this transformation, to binarize the introduced additions."))
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
                                                    (cdr dims)))))))))

  (defret dim-binmulp-of-unarize-dims-in-sub
    (implies (dim-list-binmulp dims)
             (dim-binmulp new-dim))
    :hints (("Goal" :in-theory (enable* ast-binmulp-rules)))))

;;;;;;;;;;

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
     if the argument ones have no nullary subtractions.")
   (xdoc::p
    "We also show that these functions preserve
     the binary status of multiplications,
     which these functions do not affect.
     They do not preserve the binary status of additions,
     because of the additions introduced by the rule @('sub2m')
     (see @(tsee unarize-dims-in-sub))."))

  (define unarize-sub-in-dim ((dim dimp))
    :returns (mv (new-dim dimp)
                 (proof dim=-proofp))
    :parents (ispace-equivalence-normalizations unarize-sub-in-dims)
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
    :parents (ispace-equivalence-normalizations unarize-sub-in-dims)
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
    :measure (dim-list-count dims)

    ///

    (defret len-of-unarize-sub-in-dim-list
      (equal (len new-dims)
             (len dims))
      :hints (("Goal"
               :induct (len dims)
               :in-theory (enable (:induction len)))))

    (defret consp-of-unarize-sub-in-dim-list
      (equal (consp new-dims)
             (consp dims))
      :hints (("Goal" :expand ((unarize-sub-in-dim-list dims))))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unarize-sub-in-dims)

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
                       (dim-unisubp dim)))))

  (defret-mutual dim-binmulp-of-unarize-sub-in-dims
    (defret dim-binmulp-of-unarize-sub-in-dim
      (implies (dim-binmulp dim)
               (dim-binmulp new-dim))
      :fn unarize-sub-in-dim)
    (defret dim-list-binmulp-of-unarize-sub-in-dim-list
      (implies (dim-list-binmulp dims)
               (dim-list-binmulp new-dims))
      :fn unarize-sub-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* ast-binmulp-rules))
            '(:expand ((dim-binmulp dim)
                       (dim-binmulp
                        (dim-mul (mv-nth 0 (unarize-sub-in-dim-list
                                            (dim-mul->dims dim))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unarize-shape-dims ((dims dim-listp))
  :returns (mv (new-shape shapep)
               (proof shp=-proofp))
  :short "Turn a list of dimensions in a dimension shape
          into a shape with only unary dimension shapes,
          and construct a proof tree demonstrating equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the dimension arguments of a dimension shape.")
   (xdoc::p
    "A dimension shape with no dimensions
     is turned into the empty concatenation,
     according to the rule @('dims0').
     A dimension shape with one dimension is already unary,
     and is left unchanged.
     A dimension shape with two or more dimensions is turned into
     the concatenation of the unary dimension shape of the first dimension
     and the unarization of the dimension shape of the remaining dimensions,
     according to the rule @('dims2m').")
   (xdoc::p
    "The proof tree proves the equivalence of
     @('(shape-dims dims)') and the new shape.
     Unlike the folds for the dimension operations,
     the recursion continues inside a component of the constructed shape,
     so the proof tree for the case of two or more dimensions
     chains, via the rule @('trans'),
     an instance of the rule @('dims2m')
     with a congruence that wraps the recursively built proof tree.")
   (xdoc::p
    "We use the constructed proof tree to show the equivalence.")
   (xdoc::p
    "We show that the resulting shape only has unary dimension shapes.
     We also show that
     it only has binary or empty concatenations,
     it has no splices,
     and it has no dimension ispaces.
     Since the input is just a list of dimensions,
     all these hold unconditionally."))
  (cond ((endp dims) (mv (shape-append nil)
                         (shp=-proof-dims0)))
        ((endp (cdr dims)) (mv (shape-dims dims)
                               (shp=-proof-refl (shape-dims dims))))
        (t (b* ((d (dim-fix (car dims)))
                (ds (dim-list-fix (cdr dims)))
                (shape1 (shape-dims (list d)))
                ((mv shape2 proof2) (unarize-shape-dims (cdr dims)))
                (mid-shape (shape-append (list shape1 (shape-dims ds))))
                (new-shape (shape-append (list shape1 shape2))))
             (mv new-shape
                 (make-shp=-proof-trans
                  :s1 (shape-dims (cons d ds))
                  :s2 mid-shape
                  :s3 new-shape
                  :premise1-proof (make-shp=-proof-dims2m
                                   :d d
                                   :ds ds)
                  :premise2-proof
                  (make-shp=-proof-cong-append
                   :ss1 (list shape1 (shape-dims ds))
                   :ss2 (list shape1 shape2)
                   :premise1-proof
                   (make-shps=-proof-cong-cons
                    :s1 shape1
                    :s2 shape1
                    :ss1 (list (shape-dims ds))
                    :ss2 (list shape2)
                    :premise1-proof (shp=-proof-refl shape1)
                    :premise2-proof
                    (make-shps=-proof-cong-cons
                     :s1 (shape-dims ds)
                     :s2 shape2
                     :ss1 nil
                     :ss2 nil
                     :premise1-proof proof2
                     :premise2-proof (shps=-proof-refl nil)))))))))
  :measure (len dims)
  :verify-guards :after-returns

  ///

  (defret shp=-proof-validp-of-unarize-shape-dims
    (implies (dim-listp dims)
             (shp=-proof-validp proof
                                (shape-dims dims)
                                new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable shp=-proof-validp
                                shps=-proof-validp
                                shp=-refl-validp
                                shp=-trans-validp
                                shp=-dims0-validp
                                shp=-dims2m-validp
                                shp=-cong-append-validp
                                shps=-refl-validp
                                shps=-cong-cons-validp))))

  (defret shape-unidimsp-of-unarize-shape-dims
    (shape-unidimsp new-shape)
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unidimsp-rules))
            '(:expand ((shape-unidimsp (shape-dims dims))
                       (shape-unidimsp (shape-dims (list (car dims))))))))

  (defret shape-nullbinappendp-of-unarize-shape-dims
    (shape-nullbinappendp new-shape)
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp
                        (shape-append
                         (list (shape-dims (list (car dims)))
                               (mv-nth 0 (unarize-shape-dims
                                          (cdr dims))))))))))

  (defret shape-nosplicep-of-unarize-shape-dims
    (shape-nosplicep new-shape)
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nosplicep-rules))))

  (defret shape-nodimispacep-of-unarize-shape-dims
    (shape-nodimispacep new-shape)
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nodimispacep-rules)))))

;;;;;;;;;;

(defines unarize-dims-in-shapes/ispaces
  :short "Turn shapes and ispaces into equivalent ones
          with only unary dimension shapes,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the resulting shapes and ispaces are equivalent to
     the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting shapes and ispaces
     only have unary dimension shapes.")
   (xdoc::p
    "We also show that these functions preserve
     the binary or empty status of concatenations,
     the absence of splices,
     and the absence of dimension ispaces,
     which these functions do not affect."))

  (define unarize-dims-in-shape ((shape shapep))
    :returns (mv (new-shape shapep)
                 (proof shp=-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn a shape into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (shape-case
     shape
     :var (mv (shape-var shape.name)
              (shp=-proof-refl (shape-var shape.name)))
     :dims (unarize-shape-dims shape.dims)
     :append (b* (((mv new-shapes proof)
                   (unarize-dims-in-shape-list shape.shapes)))
               (mv (shape-append new-shapes)
                   (make-shp=-proof-cong-append
                    :ss1 shape.shapes
                    :ss2 new-shapes
                    :premise1-proof proof)))
     :splice (b* (((mv new-ispaces proof)
                   (unarize-dims-in-ispace-list shape.ispaces)))
               (mv (shape-splice new-ispaces)
                   (make-shp=-proof-cong-splice
                    :is1 shape.ispaces
                    :is2 new-ispaces
                    :premise1-proof proof))))
    :measure (shape-count shape))

  (define unarize-dims-in-shape-list ((shapes shape-listp))
    :returns (mv (new-shapes shape-listp)
                 (proof shps=-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn a list of shapes into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp shapes)) (mv nil (shps=-proof-refl nil)))
         ((mv new-shape proof1) (unarize-dims-in-shape (car shapes)))
         ((mv new-shapes proof2) (unarize-dims-in-shape-list (cdr shapes))))
      (mv (cons new-shape new-shapes)
          (make-shps=-proof-cong-cons
           :s1 (shape-fix (car shapes))
           :s2 new-shape
           :ss1 (shape-list-fix (cdr shapes))
           :ss2 new-shapes
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (shape-list-count shapes)

    ///

    (defret len-of-unarize-dims-in-shape-list
      (equal (len new-shapes)
             (len shapes))
      :hints (("Goal"
               :induct (len shapes)
               :in-theory (enable (:induction len)))))

    (defret consp-of-unarize-dims-in-shape-list
      (equal (consp new-shapes)
             (consp shapes))
      :hints (("Goal" :expand ((unarize-dims-in-shape-list shapes))))))

  (define unarize-dims-in-ispace ((ispace ispacep))
    :returns (mv (new-ispace ispacep)
                 (proof isp=-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn an ispace into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (ispace-case
     ispace
     :dim (mv (ispace-dim ispace.dim)
              (isp=-proof-refl (ispace-dim ispace.dim)))
     :shape (b* (((mv new-shape proof) (unarize-dims-in-shape ispace.shape)))
              (mv (ispace-shape new-shape)
                  (make-isp=-proof-cong-shape
                   :s1 ispace.shape
                   :s2 new-shape
                   :premise1-proof proof))))
    :measure (ispace-count ispace))

  (define unarize-dims-in-ispace-list ((ispaces ispace-listp))
    :returns (mv (new-ispaces ispace-listp)
                 (proof isps=-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn a list of ispaces into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp ispaces)) (mv nil (isps=-proof-refl nil)))
         ((mv new-ispace proof1) (unarize-dims-in-ispace (car ispaces)))
         ((mv new-ispaces proof2) (unarize-dims-in-ispace-list (cdr ispaces))))
      (mv (cons new-ispace new-ispaces)
          (make-isps=-proof-cong-cons
           :i1 (ispace-fix (car ispaces))
           :i2 new-ispace
           :is1 (ispace-list-fix (cdr ispaces))
           :is2 new-ispaces
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (ispace-list-count ispaces))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unarize-dims-in-shapes/ispaces)

  (defret-mutual shp=-proof-validp-of-unarize-dims-in-shapes/ispaces
    (defret shp=-proof-validp-of-unarize-dims-in-shape
      (implies (shapep shape)
               (shp=-proof-validp proof
                                  shape
                                  new-shape))
      :fn unarize-dims-in-shape)
    (defret shps=-proof-validp-of-unarize-dims-in-shape-list
      (implies (shape-listp shapes)
               (shps=-proof-validp proof
                                   shapes
                                   new-shapes))
      :fn unarize-dims-in-shape-list)
    (defret isp=-proof-validp-of-unarize-dims-in-ispace
      (implies (ispacep ispace)
               (isp=-proof-validp proof
                                  ispace
                                  new-ispace))
      :fn unarize-dims-in-ispace)
    (defret isps=-proof-validp-of-unarize-dims-in-ispace-list
      (implies (ispace-listp ispaces)
               (isps=-proof-validp proof
                                   ispaces
                                   new-ispaces))
      :fn unarize-dims-in-ispace-list)
    :hints (("Goal"
             :in-theory (e/d (shp=-proof-validp
                              shps=-proof-validp
                              isp=-proof-validp
                              isps=-proof-validp
                              shp=-refl-validp
                              shp=-cong-append-validp
                              shp=-cong-splice-validp
                              isp=-refl-validp
                              isp=-cong-shape-validp
                              shps=-refl-validp
                              shps=-cong-cons-validp
                              isps=-refl-validp
                              isps=-cong-cons-validp)
                             (shp=-proof-validp-of-unarize-shape-dims)))
            '(:use ((:instance shp=-proof-validp-of-unarize-shape-dims
                               (dims (shape-dims->dims shape)))))))

  (defret-mutual shape-unidimsp-of-unarize-dims-in-shapes/ispaces
    (defret shape-unidimsp-of-unarize-dims-in-shape
      (shape-unidimsp new-shape)
      :fn unarize-dims-in-shape)
    (defret shape-list-unidimsp-of-unarize-dims-in-shape-list
      (shape-list-unidimsp new-shapes)
      :fn unarize-dims-in-shape-list)
    (defret ispace-unidimsp-of-unarize-dims-in-ispace
      (ispace-unidimsp new-ispace)
      :fn unarize-dims-in-ispace)
    (defret ispace-list-unidimsp-of-unarize-dims-in-ispace-list
      (ispace-list-unidimsp new-ispaces)
      :fn unarize-dims-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-unidimsp-rules))
            '(:expand ((shape-unidimsp shape)
                       (ispace-unidimsp ispace)))))

  (defret-mutual shape-nullbinappendp-of-unarize-dims-in-shapes/ispaces
    (defret shape-nullbinappendp-of-unarize-dims-in-shape
      (implies (shape-nullbinappendp shape)
               (shape-nullbinappendp new-shape))
      :fn unarize-dims-in-shape)
    (defret shape-list-nullbinappendp-of-unarize-dims-in-shape-list
      (implies (shape-list-nullbinappendp shapes)
               (shape-list-nullbinappendp new-shapes))
      :fn unarize-dims-in-shape-list)
    (defret ispace-nullbinappendp-of-unarize-dims-in-ispace
      (implies (ispace-nullbinappendp ispace)
               (ispace-nullbinappendp new-ispace))
      :fn unarize-dims-in-ispace)
    (defret ispace-list-nullbinappendp-of-unarize-dims-in-ispace-list
      (implies (ispace-list-nullbinappendp ispaces)
               (ispace-list-nullbinappendp new-ispaces))
      :fn unarize-dims-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp shape)
                       (shape-nullbinappendp
                        (shape-append (mv-nth 0 (unarize-dims-in-shape-list
                                                 (shape-append->shapes
                                                  shape)))))))))

  (defret-mutual shape-nosplicep-of-unarize-dims-in-shapes/ispaces
    (defret shape-nosplicep-of-unarize-dims-in-shape
      (implies (shape-nosplicep shape)
               (shape-nosplicep new-shape))
      :fn unarize-dims-in-shape)
    (defret shape-list-nosplicep-of-unarize-dims-in-shape-list
      (implies (shape-list-nosplicep shapes)
               (shape-list-nosplicep new-shapes))
      :fn unarize-dims-in-shape-list)
    (defret ispace-nosplicep-of-unarize-dims-in-ispace
      (implies (ispace-nosplicep ispace)
               (ispace-nosplicep new-ispace))
      :fn unarize-dims-in-ispace)
    (defret ispace-list-nosplicep-of-unarize-dims-in-ispace-list
      (implies (ispace-list-nosplicep ispaces)
               (ispace-list-nosplicep new-ispaces))
      :fn unarize-dims-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosplicep-rules))
            '(:expand ((shape-nosplicep shape)))))

  (defret-mutual shape-nodimispacep-of-unarize-dims-in-shapes/ispaces
    (defret shape-nodimispacep-of-unarize-dims-in-shape
      (implies (shape-nodimispacep shape)
               (shape-nodimispacep new-shape))
      :fn unarize-dims-in-shape)
    (defret shape-list-nodimispacep-of-unarize-dims-in-shape-list
      (implies (shape-list-nodimispacep shapes)
               (shape-list-nodimispacep new-shapes))
      :fn unarize-dims-in-shape-list)
    (defret ispace-nodimispacep-of-unarize-dims-in-ispace
      (implies (ispace-nodimispacep ispace)
               (ispace-nodimispacep new-ispace))
      :fn unarize-dims-in-ispace)
    (defret ispace-list-nodimispacep-of-unarize-dims-in-ispace-list
      (implies (ispace-list-nodimispacep ispaces)
               (ispace-list-nodimispacep new-ispaces))
      :fn unarize-dims-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nodimispacep-rules))
            '(:expand ((ispace-nodimispacep ispace))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    "This validates the intention of
     rules @('mul0'), @('mul1'), and @('mul3m'),
     described in @(see dim-equiv-infrules)."))
  (implies (dimp dim)
           (dim-equiv-to-binmul-p dim))
  :use ((:instance dim-equiv-to-binmul-p-suff
                   (dim1 (mv-nth 0 (binarize-mul-in-dim dim))))
        (:instance dim=-when-proof-validp
                   (proof (mv-nth 1 (binarize-mul-in-dim dim)))
                   (concl.dim1 dim)
                   (concl.dim2 (mv-nth 0 (binarize-mul-in-dim dim))))))

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
        (:instance dim=-when-proof-validp
                   (proof (mv-nth 1 (unarize-sub-in-dim dim)))
                   (concl.dim1 dim)
                   (concl.dim2 (mv-nth 0 (unarize-sub-in-dim dim))))))

;;;;;;;;;;;;;;;;;;;;

(defruled dim-equiv-to-binadd-binmul-unisub-p-when-dimp-and-nonullsubp
  :short "Every dimension without nullary subtractions
          is equivalent to one with only
          binary additions,
          binary multiplications,
          and unary subtractions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a corollary of composing the three transformations,
     in the order:
     unarize subtractions, binarize additions, binarize multiplications.
     Each transformation establishes its own status,
     and preserves the statuses established by the preceding ones.
     Unarizing subtractions must precede binarizing additions,
     because the former introduces additions
     (see @(tsee unarize-dims-in-sub));
     binarizing multiplications could be otherwise reordered,
     since the other two transformations preserve
     the binary status of multiplications.")
   (xdoc::p
    "This is not the only sequence of transformations
     that achieves the desired statuses of the dimension.
     For instance,
     we could swap the binarization of additions and multiplications.
     But not all sequences work, as noted earlier.
     In general, the sequences that work are exactly the ones where
     the unarization of subtraction precedes the binarization of addition."))
  (implies (and (dimp dim)
                (dim-nonullsubp dim))
           (dim-equiv-to-binadd-binmul-unisub-p dim))
  :use ((:instance dim-equiv-to-binadd-binmul-unisub-p-suff
                   (dim1 (mv-nth 0 (binarize-mul-in-dim
                                    (binarize-add-in-dim
                                     (mv-nth 0 (unarize-sub-in-dim dim)))))))
        (:instance dim=-when-proof-validp
                   (proof (mv-nth 1 (unarize-sub-in-dim dim)))
                   (concl.dim1 dim)
                   (concl.dim2 (mv-nth 0 (unarize-sub-in-dim dim))))
        (:instance dim=-of-binarize-add-in-dim
                   (dim (mv-nth 0 (unarize-sub-in-dim dim))))
        (:instance dim=-when-proof-validp
                   (proof (mv-nth 1 (binarize-mul-in-dim
                                     (binarize-add-in-dim
                                      (mv-nth 0 (unarize-sub-in-dim dim))))))
                   (concl.dim1 (binarize-add-in-dim
                                (mv-nth 0 (unarize-sub-in-dim dim))))
                   (concl.dim2 (mv-nth 0 (binarize-mul-in-dim
                                          (binarize-add-in-dim
                                           (mv-nth 0 (unarize-sub-in-dim
                                                      dim))))))))
  :enable dim=-trans-swapped
  :disable dim=-of-binarize-add-in-dim)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled shape-equiv-to-unidims-p-when-shapep
  :short "Every shape is equivalent to one
          with only unary dimension shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rules @('dims0') and @('dims2m'),
     described in @(see shape/ispace-equiv-infrules)."))
  (implies (shapep shape)
           (shape-equiv-to-unidims-p shape))
  :use ((:instance shape-equiv-to-unidims-p-suff
                   (shape1 (mv-nth 0 (unarize-dims-in-shape shape))))
        (:instance shp=-when-proof-validp
                   (proof (mv-nth 1 (unarize-dims-in-shape shape)))
                   (concl.shp1 shape)
                   (concl.shp2 (mv-nth 0 (unarize-dims-in-shape shape))))))
