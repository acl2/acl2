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
  :short "Normalizations in ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that some of the rules in fact realize
     the reductions claimed in @(see dim-equivalence-definition),
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
          (and (dim-eq dim dim1)
               (dim-binaddp dim1)))
  :guard-hints (("Goal" :in-theory (enable dimp-when-dim-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-binmul-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only binary multiplications."
  (exists (dim1)
          (and (dim-eq dim dim1)
               (dim-binmulp dim1)))
  :guard-hints (("Goal" :in-theory (enable dimp-when-dim-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-unisub-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only unary subtractions."
  (exists (dim1)
          (and (dim-eq dim dim1)
               (dim-unisubp dim1)))
  :guard-hints (("Goal" :in-theory (enable dimp-when-dim-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk dim-equiv-to-binadd-binmul-unisub-p (dim)
  :returns (yes/no booleanp)
  :short "Check whether a dimension is equivalent to
          one with only
          binary additions,
          binary multiplications,
          and unary subtractions."
  (exists (dim1)
          (and (dim-eq dim dim1)
               (dim-binaddp dim1)
               (dim-binmulp dim1)
               (dim-unisubp dim1)))
  :guard-hints (("Goal" :in-theory (enable dimp-when-dim-eq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk shape-equiv-to-unidims-p (shape)
  :returns (yes/no booleanp)
  :short "Check whether a shape is equivalent to
          one with only unary dimension shapes."
  (exists (shape1)
          (and (shape-eq shape shape1)
               (shape-unidimsp shape1)))
  :guard-hints (("Goal" :in-theory (enable shapep-when-shape-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk shape-equiv-to-nullbinappend-p (shape)
  :returns (yes/no booleanp)
  :short "Check whether a shape is equivalent to
          one with only binary or empty concatenations."
  (exists (shape1)
          (and (shape-eq shape shape1)
               (shape-nullbinappendp shape1)))
  :guard-hints (("Goal" :in-theory (enable shapep-when-shape-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk shape-equiv-to-nosplice-p (shape)
  :returns (yes/no booleanp)
  :short "Check whether a shape is equivalent to one without splices."
  (exists (shape1)
          (and (shape-eq shape shape1)
               (shape-nosplicep shape1)))
  :guard-hints (("Goal" :in-theory (enable shapep-when-shape-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk shape-equiv-to-nodimispace-p (shape)
  :returns (yes/no booleanp)
  :short "Check whether a shape is equivalent to
          one without dimension ispaces."
  (exists (shape1)
          (and (shape-eq shape shape1)
               (shape-nodimispacep shape1)))
  :guard-hints (("Goal" :in-theory (enable shapep-when-shape-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk shape-equiv-to-unidims-nullbinappend-nosplice-nodimispace-p (shape)
  :returns (yes/no booleanp)
  :short "Check whether a shape is equivalent to one
          with only unary dimension shapes,
          with only binary or empty concatenations,
          without splices, and
          without dimension ispaces."
  (exists (shape1)
          (and (shape-eq shape shape1)
               (shape-unidimsp shape1)
               (shape-nullbinappendp shape1)
               (shape-nosplicep shape1)
               (shape-nodimispacep shape1)))
  :guard-hints (("Goal" :in-theory (enable shapep-when-shape-eq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binarize-add-dims ((dims dim-listp))
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
        (t (binarize-add-dims (cons (dim-add (list (car dims)
                                                   (cadr dims)))
                                    (cddr dims)))))
  :measure (len dims)
  :verify-guards :after-returns

  ///

  (defret dim-eq-of-binarize-add-dims
    (implies (dim-listp dims)
             (dim-eq (dim-add dims) new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable binarize-add-dims
                                dim-eq-refl
                                dim-eq-add1
                                dim-eq-add3m
                                dim-eq-trans-swapped))
            '(:use (dim-eq-add0))))

  (defret dim-binaddp-of-binarize-add-dims
    (implies (dim-list-binaddp dims)
             (dim-binaddp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binaddp-rules))
            '(:expand ((dim-binaddp (dim-add dims))
                       (dim-binaddp (dim-add (list (car dims)
                                                   (cadr dims))))))))

  (defret dim-binmulp-of-binarize-add-dims
    (implies (dim-list-binmulp dims)
             (dim-binmulp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binmulp-rules))))

  (defret dim-unisubp-of-binarize-add-dims
    (implies (dim-list-unisubp dims)
             (dim-unisubp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unisubp-rules))))

  (defret dim-nonullsubp-of-binarize-add-dims
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
     :add (binarize-add-dims (binarize-add-in-dim-list dim.dims))
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

  (defret-mutual dim-eq-of-binarize-add-in-dims
    (defret dim-eq-of-binarize-add-in-dim
      (implies (dimp dim)
               (dim-eq dim new-dim))
      :fn binarize-add-in-dim)
    (defret dims-eq-of-binarize-add-in-dim-list
      (implies (dim-listp dims)
               (dims-eq dims new-dims))
      :fn binarize-add-in-dim-list)
    :hints (("Goal"
             :in-theory (e/d (dim-eq-refl
                              dim-eq-trans-swapped
                              dims-eq-refl
                              dims-eq-cong-cons)
                             (dim-eq-of-binarize-add-dims)))
            '(:use ((:instance dim-eq-of-binarize-add-dims
                               (dims (binarize-add-in-dim-list
                                      (dim-add->dims dim))))
                    (:instance dim-eq-cong-add
                               (dims1 (dim-add->dims dim))
                               (dims2 (binarize-add-in-dim-list
                                       (dim-add->dims dim))))
                    (:instance dim-eq-cong-mul
                               (dims1 (dim-mul->dims dim))
                               (dims2 (binarize-add-in-dim-list
                                       (dim-mul->dims dim))))
                    (:instance dim-eq-cong-sub
                               (dims1 (dim-sub->dims dim))
                               (dims2 (binarize-add-in-dim-list
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

(define binarize-mul-dims ((dims dim-listp))
  :returns (mv (new-dim dimp)
               (proof dim-eq-proofp))
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
                         (dim-eq-proof-mul0)))
        ((endp (cdr dims)) (mv (dim-fix (car dims))
                               (dim-eq-proof-mul1 (dim-fix (car dims)))))
        ((endp (cddr dims)) (mv (dim-mul dims)
                                (dim-eq-proof-refl (dim-mul dims))))
        (t (b* ((dims1 (cons (dim-mul (list (car dims)
                                            (cadr dims)))
                             (cddr dims)))
                ((mv new-dim proof) (binarize-mul-dims dims1)))
             (mv new-dim
                 (make-dim-eq-proof-trans
                  :dim1 (dim-mul dims)
                  :dim2 (dim-mul dims1)
                  :dim3 new-dim
                  :premise1-proof (make-dim-eq-proof-mul3m
                                   :dim1 (dim-fix (car dims))
                                   :dim2 (dim-fix (cadr dims))
                                   :dims (dim-list-fix (cddr dims)))
                  :premise2-proof proof)))))
  :measure (len dims)
  :verify-guards :after-returns

  ///

  (defret dim-eq-proof-validp-of-binarize-mul-dims
    (implies (dim-listp dims)
             (dim-eq-proof-validp proof
                                  (dim-mul dims)
                                  new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* dim-equivalence-definition-validp-defs))))

  (defret dim-binmulp-of-binarize-mul-dims
    (implies (dim-list-binmulp dims)
             (dim-binmulp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binmulp-rules))
            '(:expand ((dim-binmulp (dim-mul dims))
                       (dim-binmulp (dim-mul (list (car dims)
                                                   (cadr dims))))))))

  (defret dim-binaddp-of-binarize-mul-dims
    (implies (dim-list-binaddp dims)
             (dim-binaddp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-binaddp-rules))))

  (defret dim-unisubp-of-binarize-mul-dims
    (implies (dim-list-unisubp dims)
             (dim-unisubp new-dim))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unisubp-rules))))

  (defret dim-nonullsubp-of-binarize-mul-dims
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
                 (proof dim-eq-proofp))
    :parents (ispace-equivalence-normalizations binarize-mul-in-dims)
    :short "Turn a dimension into
            an equivalent one with only binary multiplications,
            and construct a proof tree demonstrating the equivalence."
    (dim-case
     dim
     :var (mv (dim-var dim.name)
              (dim-eq-proof-refl (dim-var dim.name)))
     :const (mv (dim-const dim.val)
                (dim-eq-proof-refl (dim-const dim.val)))
     :add (b* (((mv new-dims proof) (binarize-mul-in-dim-list dim.dims)))
            (mv (dim-add new-dims)
                (make-dim-eq-proof-cong-add
                 :dims1 dim.dims
                 :dims2 new-dims
                 :premise1-proof proof)))
     :mul (b* (((mv new-dims proof) (binarize-mul-in-dim-list dim.dims))
               ((mv new-dim proof1) (binarize-mul-dims new-dims)))
            (mv new-dim
                (make-dim-eq-proof-trans
                 :dim1 (dim-mul dim.dims)
                 :dim2 (dim-mul new-dims)
                 :dim3 new-dim
                 :premise1-proof (make-dim-eq-proof-cong-mul
                                  :dims1 dim.dims
                                  :dims2 new-dims
                                  :premise1-proof proof)
                 :premise2-proof proof1)))
     :sub (b* (((mv new-dims proof) (binarize-mul-in-dim-list dim.dims)))
            (mv (dim-sub new-dims)
                (make-dim-eq-proof-cong-sub
                 :dims1 dim.dims
                 :dims2 new-dims
                 :premise1-proof proof))))
    :measure (dim-count dim))

  (define binarize-mul-in-dim-list ((dims dim-listp))
    :returns (mv (new-dims dim-listp)
                 (proof dims-eq-proofp))
    :parents (ispace-equivalence-normalizations binarize-mul-in-dims)
    :short "Turn a list of dimensions into
            an equivalent one with only binary multiplications,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp dims)) (mv nil (dims-eq-proof-refl nil)))
         ((mv new-dim proof1) (binarize-mul-in-dim (car dims)))
         ((mv new-dims proof2) (binarize-mul-in-dim-list (cdr dims))))
      (mv (cons new-dim new-dims)
          (make-dims-eq-proof-cong-cons
           :dim1 (dim-fix (car dims))
           :dim2 new-dim
           :dims1 (dim-list-fix (cdr dims))
           :dims2 new-dims
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

  (defret-mutual dim-eq-proof-validp-of-binarize-mul-in-dims
    (defret dim-eq-proof-validp-of-binarize-mul-in-dim
      (implies (dimp dim)
               (dim-eq-proof-validp proof
                                    dim
                                    new-dim))
      :fn binarize-mul-in-dim)
    (defret dims-eq-proof-validp-of-binarize-mul-in-dim-list
      (implies (dim-listp dims)
               (dims-eq-proof-validp proof
                                     dims
                                     new-dims))
      :fn binarize-mul-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* dim-equivalence-definition-validp-defs))))

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

(define unarize-sub-dims ((dims dim-listp))
  :returns (mv (new-dim dimp)
               (proof dim-eq-proofp))
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
     (see @(see dim-equivalence-definition)),
     so it is also left unchanged.
     Unlike @(tsee binarize-add-dims) and @(tsee binarize-mul-dims),
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
                         (dim-eq-proof-refl (dim-sub nil))))
        ((endp (cdr dims)) (mv (dim-sub dims)
                               (dim-eq-proof-refl (dim-sub dims))))
        (t (mv (dim-add (list (dim-fix (car dims))
                              (dim-sub (list (dim-add
                                              (dim-list-fix (cdr dims)))))))
               (make-dim-eq-proof-sub2m
                :dim (dim-fix (car dims))
                :dims (dim-list-fix (cdr dims))))))

  ///

  (defret dim-eq-proof-validp-of-unarize-sub-dims
    (implies (dim-listp dims)
             (dim-eq-proof-validp proof
                                  (dim-sub dims)
                                  new-dim))
    :hints
    (("Goal" :in-theory (enable* dim-equivalence-definition-validp-defs))))

  (defret dim-unisubp-of-unarize-sub-dims
    (implies (and (dim-list-unisubp dims)
                  (consp dims))
             (dim-unisubp new-dim))
    :hints (("Goal"
             :in-theory (enable* ast-unisubp-rules))
            '(:expand ((dim-unisubp (dim-sub dims))
                       (dim-unisubp (dim-sub (list (dim-add
                                                    (cdr dims)))))))))

  (defret dim-binmulp-of-unarize-sub-dims
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
     (see @(tsee unarize-sub-dims))."))

  (define unarize-sub-in-dim ((dim dimp))
    :returns (mv (new-dim dimp)
                 (proof dim-eq-proofp))
    :parents (ispace-equivalence-normalizations unarize-sub-in-dims)
    :short "Turn a dimension into
            an equivalent one with only unary subtractions,
            and construct a proof tree demonstrating the equivalence."
    (dim-case
     dim
     :var (mv (dim-var dim.name)
              (dim-eq-proof-refl (dim-var dim.name)))
     :const (mv (dim-const dim.val)
                (dim-eq-proof-refl (dim-const dim.val)))
     :add (b* (((mv new-dims proof) (unarize-sub-in-dim-list dim.dims)))
            (mv (dim-add new-dims)
                (make-dim-eq-proof-cong-add
                 :dims1 dim.dims
                 :dims2 new-dims
                 :premise1-proof proof)))
     :mul (b* (((mv new-dims proof) (unarize-sub-in-dim-list dim.dims)))
            (mv (dim-mul new-dims)
                (make-dim-eq-proof-cong-mul
                 :dims1 dim.dims
                 :dims2 new-dims
                 :premise1-proof proof)))
     :sub (b* (((mv new-dims proof) (unarize-sub-in-dim-list dim.dims))
               ((mv new-dim proof1) (unarize-sub-dims new-dims)))
            (mv new-dim
                (make-dim-eq-proof-trans
                 :dim1 (dim-sub dim.dims)
                 :dim2 (dim-sub new-dims)
                 :dim3 new-dim
                 :premise1-proof (make-dim-eq-proof-cong-sub
                                  :dims1 dim.dims
                                  :dims2 new-dims
                                  :premise1-proof proof)
                 :premise2-proof proof1))))
    :measure (dim-count dim))

  (define unarize-sub-in-dim-list ((dims dim-listp))
    :returns (mv (new-dims dim-listp)
                 (proof dims-eq-proofp))
    :parents (ispace-equivalence-normalizations unarize-sub-in-dims)
    :short "Turn a list of dimensions into
            an equivalent one with only unary subtractions,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp dims)) (mv nil (dims-eq-proof-refl nil)))
         ((mv new-dim proof1) (unarize-sub-in-dim (car dims)))
         ((mv new-dims proof2) (unarize-sub-in-dim-list (cdr dims))))
      (mv (cons new-dim new-dims)
          (make-dims-eq-proof-cong-cons
           :dim1 (dim-fix (car dims))
           :dim2 new-dim
           :dims1 (dim-list-fix (cdr dims))
           :dims2 new-dims
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

  (defret-mutual dim-eq-proof-validp-of-unarize-sub-in-dims
    (defret dim-eq-proof-validp-of-unarize-sub-in-dim
      (implies (dimp dim)
               (dim-eq-proof-validp proof
                                    dim
                                    new-dim))
      :fn unarize-sub-in-dim)
    (defret dims-eq-proof-validp-of-unarize-sub-in-dim-list
      (implies (dim-listp dims)
               (dims-eq-proof-validp proof
                                     dims
                                     new-dims))
      :fn unarize-sub-in-dim-list)
    :hints (("Goal"
             :in-theory (enable* dim-equivalence-definition-validp-defs))))

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
               (proof shape-eq-proofp))
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
                         (shape-eq-proof-dims0)))
        ((endp (cdr dims)) (mv (shape-dims dims)
                               (shape-eq-proof-refl (shape-dims dims))))
        (t (b* ((dim (car dims))
                (dims (cdr dims))
                (shape1 (shape-dims (list dim)))
                ((mv shape2 proof2) (unarize-shape-dims dims))
                (mid-shape (shape-append (list shape1 (shape-dims dims))))
                (new-shape (shape-append (list shape1 shape2))))
             (mv new-shape
                 (make-shape-eq-proof-trans
                  :shape1 (shape-dims (cons dim dims))
                  :shape2 mid-shape
                  :shape3 new-shape
                  :premise1-proof (make-shape-eq-proof-dims2m
                                   :dim (dim-fix dim)
                                   :dims (dim-list-fix dims))
                  :premise2-proof
                  (make-shape-eq-proof-cong-append
                   :shapes1 (list shape1 (shape-dims dims))
                   :shapes2 (list shape1 shape2)
                   :premise1-proof
                   (make-shapes-eq-proof-cong-cons
                    :shape1 shape1
                    :shape2 shape1
                    :shapes1 (list (shape-dims dims))
                    :shapes2 (list shape2)
                    :premise1-proof (shape-eq-proof-refl shape1)
                    :premise2-proof
                    (make-shapes-eq-proof-cong-cons
                     :shape1 (shape-dims dims)
                     :shape2 shape2
                     :shapes1 nil
                     :shapes2 nil
                     :premise1-proof proof2
                     :premise2-proof (shapes-eq-proof-refl nil)))))))))
  :measure (len dims)
  :verify-guards :after-returns

  ///

  (defret shape-eq-proof-validp-of-unarize-shape-dims
    (implies (dim-listp dims)
             (shape-eq-proof-validp proof
                                    (shape-dims dims)
                                    new-shape))
    :hints (("Goal"
             :induct t
             :in-theory
             (enable* shape/ispace-equivalence-definition-validp-defs))))

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
                 (proof shape-eq-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn a shape into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (shape-case
     shape
     :var (mv (shape-var shape.name)
              (shape-eq-proof-refl (shape-var shape.name)))
     :dims (unarize-shape-dims shape.dims)
     :append (b* (((mv new-shapes proof)
                   (unarize-dims-in-shape-list shape.shapes)))
               (mv (shape-append new-shapes)
                   (make-shape-eq-proof-cong-append
                    :shapes1 shape.shapes
                    :shapes2 new-shapes
                    :premise1-proof proof)))
     :splice (b* (((mv new-ispaces proof)
                   (unarize-dims-in-ispace-list shape.ispaces)))
               (mv (shape-splice new-ispaces)
                   (make-shape-eq-proof-cong-splice
                    :ispaces1 shape.ispaces
                    :ispaces2 new-ispaces
                    :premise1-proof proof))))
    :measure (shape-count shape))

  (define unarize-dims-in-shape-list ((shapes shape-listp))
    :returns (mv (new-shapes shape-listp)
                 (proof shapes-eq-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn a list of shapes into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp shapes)) (mv nil (shapes-eq-proof-refl nil)))
         ((mv new-shape proof1) (unarize-dims-in-shape (car shapes)))
         ((mv new-shapes proof2) (unarize-dims-in-shape-list (cdr shapes))))
      (mv (cons new-shape new-shapes)
          (make-shapes-eq-proof-cong-cons
           :shape1 (shape-fix (car shapes))
           :shape2 new-shape
           :shapes1 (shape-list-fix (cdr shapes))
           :shapes2 new-shapes
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
                 (proof ispace-eq-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn an ispace into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (ispace-case
     ispace
     :dim (mv (ispace-dim ispace.dim)
              (ispace-eq-proof-refl (ispace-dim ispace.dim)))
     :shape (b* (((mv new-shape proof) (unarize-dims-in-shape ispace.shape)))
              (mv (ispace-shape new-shape)
                  (make-ispace-eq-proof-cong-shape
                   :shape1 ispace.shape
                   :shape2 new-shape
                   :premise1-proof proof))))
    :measure (ispace-count ispace))

  (define unarize-dims-in-ispace-list ((ispaces ispace-listp))
    :returns (mv (new-ispaces ispace-listp)
                 (proof ispaces-eq-proofp))
    :parents (ispace-equivalence-normalizations unarize-dims-in-shapes/ispaces)
    :short "Turn a list of ispaces into
            an equivalent one with only unary dimension shapes,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp ispaces)) (mv nil (ispaces-eq-proof-refl nil)))
         ((mv new-ispace proof1) (unarize-dims-in-ispace (car ispaces)))
         ((mv new-ispaces proof2) (unarize-dims-in-ispace-list (cdr ispaces))))
      (mv (cons new-ispace new-ispaces)
          (make-ispaces-eq-proof-cong-cons
           :ispace1 (ispace-fix (car ispaces))
           :ispace2 new-ispace
           :ispaces1 (ispace-list-fix (cdr ispaces))
           :ispaces2 new-ispaces
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (ispace-list-count ispaces))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unarize-dims-in-shapes/ispaces)

  (defret-mutual shape-eq-proof-validp-of-unarize-dims-in-shapes/ispaces
    (defret shape-eq-proof-validp-of-unarize-dims-in-shape
      (implies (shapep shape)
               (shape-eq-proof-validp proof
                                      shape
                                      new-shape))
      :fn unarize-dims-in-shape)
    (defret shapes-eq-proof-validp-of-unarize-dims-in-shape-list
      (implies (shape-listp shapes)
               (shapes-eq-proof-validp proof
                                       shapes
                                       new-shapes))
      :fn unarize-dims-in-shape-list)
    (defret ispace-eq-proof-validp-of-unarize-dims-in-ispace
      (implies (ispacep ispace)
               (ispace-eq-proof-validp proof
                                       ispace
                                       new-ispace))
      :fn unarize-dims-in-ispace)
    (defret ispaces-eq-proof-validp-of-unarize-dims-in-ispace-list
      (implies (ispace-listp ispaces)
               (ispaces-eq-proof-validp proof
                                        ispaces
                                        new-ispaces))
      :fn unarize-dims-in-ispace-list)
    :hints (("Goal"
             :in-theory (e/d* (shape/ispace-equivalence-definition-validp-defs)
                              (shape-eq-proof-validp-of-unarize-shape-dims)))
            '(:use ((:instance shape-eq-proof-validp-of-unarize-shape-dims
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

;;;;;;;;;;;;;;;;;;;;

(define nullbinarize-append-shapes ((shapes shape-listp))
  :returns (mv (new-shape shapep)
               (proof shape-eq-proofp))
  :short "Turn a list of shapes in a concatenation
          into a shape with only binary or empty concatenations,
          and construct a proof tree demonstrating equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the shape arguments of a concatenation shape.")
   (xdoc::p
    "A concatenation of no shapes is itself a normal form,
     and is left unchanged;
     so is a concatenation of two shapes.
     A concatenation of one shape is turned into that shape,
     according to the rule @('append1').
     A concatenation of three or more shapes is turned into
     a left-associated nest of binary concatenations,
     according to the rule @('append3m'),
     whose instances are chained, via the rule @('trans'),
     with the recursively built proof trees,
     analogously to the multiplication of dimensions.")
   (xdoc::p
    "We use the constructed proof tree to show the equivalence.")
   (xdoc::p
    "We show that the resulting shape
     only has binary or empty concatenations
     if the argument shapes do.
     This function is called after normalizing the concatenations
     in the shapes passed as arguments to this function (see caller);
     that establishes the hypothesis of the theorem.")
   (xdoc::p
    "We also show that this function preserves
     the unary status of dimension shapes,
     the absence of splices,
     and the absence of dimension ispaces,
     which this function does not affect."))
  (cond ((endp shapes) (mv (shape-append nil)
                           (shape-eq-proof-refl (shape-append nil))))
        ((endp (cdr shapes)) (mv (shape-fix (car shapes))
                                 (shape-eq-proof-append1
                                  (shape-fix (car shapes)))))
        ((endp (cddr shapes)) (mv (shape-append shapes)
                                  (shape-eq-proof-refl (shape-append shapes))))
        (t (b* ((shapes1 (cons (shape-append (list (car shapes)
                                                   (cadr shapes)))
                               (cddr shapes)))
                ((mv new-shape proof) (nullbinarize-append-shapes shapes1)))
             (mv new-shape
                 (make-shape-eq-proof-trans
                  :shape1 (shape-append shapes)
                  :shape2 (shape-append shapes1)
                  :shape3 new-shape
                  :premise1-proof (make-shape-eq-proof-append3m
                                   :shape1 (shape-fix (car shapes))
                                   :shape2 (shape-fix (cadr shapes))
                                   :shapes (shape-list-fix (cddr shapes)))
                  :premise2-proof proof)))))
  :measure (len shapes)
  :verify-guards :after-returns

  ///

  (defret shape-eq-proof-validp-of-nullbinarize-append-shapes
    (implies (shape-listp shapes)
             (shape-eq-proof-validp proof
                                    (shape-append shapes)
                                    new-shape))
    :hints (("Goal"
             :induct t
             :in-theory
             (enable* shape/ispace-equivalence-definition-validp-defs))))

  (defret shape-nullbinappendp-of-nullbinarize-append-shapes
    (implies (shape-list-nullbinappendp shapes)
             (shape-nullbinappendp new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp (shape-append shapes))
                       (shape-nullbinappendp
                        (shape-append (list (car shapes)
                                            (cadr shapes))))))))

  (defret shape-unidimsp-of-nullbinarize-append-shapes
    (implies (shape-list-unidimsp shapes)
             (shape-unidimsp new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unidimsp-rules))))

  (defret shape-nosplicep-of-nullbinarize-append-shapes
    (implies (shape-list-nosplicep shapes)
             (shape-nosplicep new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nosplicep-rules))))

  (defret shape-nodimispacep-of-nullbinarize-append-shapes
    (implies (shape-list-nodimispacep shapes)
             (shape-nodimispacep new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nodimispacep-rules)))))

;;;;;;;;;;

(defines nullbinarize-append-in-shapes/ispaces
  :short "Turn shapes and ispaces into equivalent ones
          with only binary or empty concatenations,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the resulting shapes and ispaces are equivalent to
     the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting shapes and ispaces
     only have binary or empty concatenations.")
   (xdoc::p
    "We also show that these functions preserve
     the unary status of dimension shapes,
     the absence of splices,
     and the absence of dimension ispaces,
     which these functions do not affect."))

  (define nullbinarize-append-in-shape ((shape shapep))
    :returns (mv (new-shape shapep)
                 (proof shape-eq-proofp))
    :parents (ispace-equivalence-normalizations
              nullbinarize-append-in-shapes/ispaces)
    :short "Turn a shape into
            an equivalent one with only binary or empty concatenations,
            and construct a proof tree demonstrating the equivalence."
    (shape-case
     shape
     :var (mv (shape-var shape.name)
              (shape-eq-proof-refl (shape-var shape.name)))
     :dims (mv (shape-dims shape.dims)
               (shape-eq-proof-refl (shape-dims shape.dims)))
     :append (b* (((mv new-shapes proof)
                   (nullbinarize-append-in-shape-list shape.shapes))
                  ((mv new-shape proof1)
                   (nullbinarize-append-shapes new-shapes)))
               (mv new-shape
                   (make-shape-eq-proof-trans
                    :shape1 (shape-append shape.shapes)
                    :shape2 (shape-append new-shapes)
                    :shape3 new-shape
                    :premise1-proof (make-shape-eq-proof-cong-append
                                     :shapes1 shape.shapes
                                     :shapes2 new-shapes
                                     :premise1-proof proof)
                    :premise2-proof proof1)))
     :splice (b* (((mv new-ispaces proof)
                   (nullbinarize-append-in-ispace-list shape.ispaces)))
               (mv (shape-splice new-ispaces)
                   (make-shape-eq-proof-cong-splice
                    :ispaces1 shape.ispaces
                    :ispaces2 new-ispaces
                    :premise1-proof proof))))
    :measure (shape-count shape))

  (define nullbinarize-append-in-shape-list ((shapes shape-listp))
    :returns (mv (new-shapes shape-listp)
                 (proof shapes-eq-proofp))
    :parents (ispace-equivalence-normalizations
              nullbinarize-append-in-shapes/ispaces)
    :short "Turn a list of shapes into
            an equivalent one with only binary or empty concatenations,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp shapes)) (mv nil (shapes-eq-proof-refl nil)))
         ((mv new-shape proof1) (nullbinarize-append-in-shape (car shapes)))
         ((mv new-shapes proof2)
          (nullbinarize-append-in-shape-list (cdr shapes))))
      (mv (cons new-shape new-shapes)
          (make-shapes-eq-proof-cong-cons
           :shape1 (shape-fix (car shapes))
           :shape2 new-shape
           :shapes1 (shape-list-fix (cdr shapes))
           :shapes2 new-shapes
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (shape-list-count shapes))

  (define nullbinarize-append-in-ispace ((ispace ispacep))
    :returns (mv (new-ispace ispacep)
                 (proof ispace-eq-proofp))
    :parents (ispace-equivalence-normalizations
              nullbinarize-append-in-shapes/ispaces)
    :short "Turn an ispace into
            an equivalent one with only binary or empty concatenations,
            and construct a proof tree demonstrating the equivalence."
    (ispace-case
     ispace
     :dim (mv (ispace-dim ispace.dim)
              (ispace-eq-proof-refl (ispace-dim ispace.dim)))
     :shape (b* (((mv new-shape proof)
                  (nullbinarize-append-in-shape ispace.shape)))
              (mv (ispace-shape new-shape)
                  (make-ispace-eq-proof-cong-shape
                   :shape1 ispace.shape
                   :shape2 new-shape
                   :premise1-proof proof))))
    :measure (ispace-count ispace))

  (define nullbinarize-append-in-ispace-list ((ispaces ispace-listp))
    :returns (mv (new-ispaces ispace-listp)
                 (proof ispaces-eq-proofp))
    :parents (ispace-equivalence-normalizations
              nullbinarize-append-in-shapes/ispaces)
    :short "Turn a list of ispaces into
            an equivalent one with only binary or empty concatenations,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp ispaces)) (mv nil (ispaces-eq-proof-refl nil)))
         ((mv new-ispace proof1) (nullbinarize-append-in-ispace (car ispaces)))
         ((mv new-ispaces proof2)
          (nullbinarize-append-in-ispace-list (cdr ispaces))))
      (mv (cons new-ispace new-ispaces)
          (make-ispaces-eq-proof-cong-cons
           :ispace1 (ispace-fix (car ispaces))
           :ispace2 new-ispace
           :ispaces1 (ispace-list-fix (cdr ispaces))
           :ispaces2 new-ispaces
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (ispace-list-count ispaces))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual nullbinarize-append-in-shapes/ispaces)

  (defret-mutual shape-eq-proof-validp-of-nullbinarize-append-in-shapes/ispaces
    (defret shape-eq-proof-validp-of-nullbinarize-append-in-shape
      (implies (shapep shape)
               (shape-eq-proof-validp proof
                                      shape
                                      new-shape))
      :fn nullbinarize-append-in-shape)
    (defret shapes-eq-proof-validp-of-nullbinarize-append-in-shape-list
      (implies (shape-listp shapes)
               (shapes-eq-proof-validp proof
                                       shapes
                                       new-shapes))
      :fn nullbinarize-append-in-shape-list)
    (defret ispace-eq-proof-validp-of-nullbinarize-append-in-ispace
      (implies (ispacep ispace)
               (ispace-eq-proof-validp proof
                                       ispace
                                       new-ispace))
      :fn nullbinarize-append-in-ispace)
    (defret ispaces-eq-proof-validp-of-nullbinarize-append-in-ispace-list
      (implies (ispace-listp ispaces)
               (ispaces-eq-proof-validp proof
                                        ispaces
                                        new-ispaces))
      :fn nullbinarize-append-in-ispace-list)
    :hints (("Goal"
             :in-theory
             (enable* shape/ispace-equivalence-definition-validp-defs))))

  (defret-mutual shape-nullbinappendp-of-nullbinarize-append-in-shapes/ispaces
    (defret shape-nullbinappendp-of-nullbinarize-append-in-shape
      (shape-nullbinappendp new-shape)
      :fn nullbinarize-append-in-shape)
    (defret shape-list-nullbinappendp-of-nullbinarize-append-in-shape-list
      (shape-list-nullbinappendp new-shapes)
      :fn nullbinarize-append-in-shape-list)
    (defret ispace-nullbinappendp-of-nullbinarize-append-in-ispace
      (ispace-nullbinappendp new-ispace)
      :fn nullbinarize-append-in-ispace)
    (defret ispace-list-nullbinappendp-of-nullbinarize-append-in-ispace-list
      (ispace-list-nullbinappendp new-ispaces)
      :fn nullbinarize-append-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp shape)
                       (ispace-nullbinappendp ispace)))))

  (defret-mutual shape-unidimsp-of-nullbinarize-append-in-shapes/ispaces
    (defret shape-unidimsp-of-nullbinarize-append-in-shape
      (implies (shape-unidimsp shape)
               (shape-unidimsp new-shape))
      :fn nullbinarize-append-in-shape)
    (defret shape-list-unidimsp-of-nullbinarize-append-in-shape-list
      (implies (shape-list-unidimsp shapes)
               (shape-list-unidimsp new-shapes))
      :fn nullbinarize-append-in-shape-list)
    (defret ispace-unidimsp-of-nullbinarize-append-in-ispace
      (implies (ispace-unidimsp ispace)
               (ispace-unidimsp new-ispace))
      :fn nullbinarize-append-in-ispace)
    (defret ispace-list-unidimsp-of-nullbinarize-append-in-ispace-list
      (implies (ispace-list-unidimsp ispaces)
               (ispace-list-unidimsp new-ispaces))
      :fn nullbinarize-append-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-unidimsp-rules))
            '(:expand ((shape-unidimsp shape)
                       (ispace-unidimsp ispace)))))

  (defret-mutual shape-nosplicep-of-nullbinarize-append-in-shapes/ispaces
    (defret shape-nosplicep-of-nullbinarize-append-in-shape
      (implies (shape-nosplicep shape)
               (shape-nosplicep new-shape))
      :fn nullbinarize-append-in-shape)
    (defret shape-list-nosplicep-of-nullbinarize-append-in-shape-list
      (implies (shape-list-nosplicep shapes)
               (shape-list-nosplicep new-shapes))
      :fn nullbinarize-append-in-shape-list)
    (defret ispace-nosplicep-of-nullbinarize-append-in-ispace
      (implies (ispace-nosplicep ispace)
               (ispace-nosplicep new-ispace))
      :fn nullbinarize-append-in-ispace)
    (defret ispace-list-nosplicep-of-nullbinarize-append-in-ispace-list
      (implies (ispace-list-nosplicep ispaces)
               (ispace-list-nosplicep new-ispaces))
      :fn nullbinarize-append-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosplicep-rules))
            '(:expand ((shape-nosplicep shape)))))

  (defret-mutual shape-nodimispacep-of-nullbinarize-append-in-shapes/ispaces
    (defret shape-nodimispacep-of-nullbinarize-append-in-shape
      (implies (shape-nodimispacep shape)
               (shape-nodimispacep new-shape))
      :fn nullbinarize-append-in-shape)
    (defret shape-list-nodimispacep-of-nullbinarize-append-in-shape-list
      (implies (shape-list-nodimispacep shapes)
               (shape-list-nodimispacep new-shapes))
      :fn nullbinarize-append-in-shape-list)
    (defret ispace-nodimispacep-of-nullbinarize-append-in-ispace
      (implies (ispace-nodimispacep ispace)
               (ispace-nodimispacep new-ispace))
      :fn nullbinarize-append-in-ispace)
    (defret ispace-list-nodimispacep-of-nullbinarize-append-in-ispace-list
      (implies (ispace-list-nodimispacep ispaces)
               (ispace-list-nodimispacep new-ispaces))
      :fn nullbinarize-append-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nodimispacep-rules))
            '(:expand ((ispace-nodimispacep ispace))))))

;;;;;;;;;;;;;;;;;;;;

(define unsplice-ispaces ((ispaces ispace-listp))
  :returns (mv (new-shape shapep)
               (proof shape-eq-proofp))
  :short "Turn a list of ispaces in a splice
          into a shape without splices at the top level,
          and construct a proof tree demonstrating equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the ispace arguments of a splice shape.")
   (xdoc::p
    "A splice of no ispaces is turned into the empty concatenation,
     according to the rule @('splice0').
     A splice of one or more ispaces is turned into
     the concatenation of a shape corresponding to the first ispace
     and the unsplicing of the splice of the remaining ispaces:
     if the first ispace is a dimension,
     the shape is the unary dimension shape of that dimension,
     according to the rule @('splice1m-dim');
     if the first ispace is a shape,
     the shape is that very shape,
     according to the rule @('splice1m-shape').
     These two cases are exhaustive on the kinds of ispaces.")
   (xdoc::p
    "The proof tree proves the equivalence of
     @('(shape-splice ispaces)') and the new shape.
     Like @(tsee unarize-shape-dims),
     the recursion continues inside a component of the constructed shape,
     so the proof tree for the case of one or more ispaces
     chains, via the rule @('trans'),
     an instance of the rule @('splice1m-dim') or @('splice1m-shape')
     with a congruence that wraps the recursively built proof tree.")
   (xdoc::p
    "We use the constructed proof tree to show the equivalence.")
   (xdoc::p
    "We show that the resulting shape has no splices
     if the argument ispaces have none inside;
     the splices at the top level are eliminated by this function.
     This function is called after unsplicing
     the ispaces passed as arguments to this function (see caller);
     that establishes the hypothesis of the theorem.")
   (xdoc::p
    "We also show that this function preserves
     the unary status of dimension shapes,
     the binary or empty status of concatenations,
     and the absence of dimension ispaces,
     which this function does not affect."))
  (b* (((when (endp ispaces)) (mv (shape-append nil)
                                  (shape-eq-proof-splice0)))
       (ispace (ispace-fix (car ispaces)))
       (is (ispace-list-fix (cdr ispaces)))
       ((mv new-shape2 proof2) (unsplice-ispaces (cdr ispaces))))
    (ispace-case
     ispace
     :dim (b* ((shape1 (shape-dims (list ispace.dim)))
               (mid-shape (shape-append (list shape1 (shape-splice is))))
               (new-shape (shape-append (list shape1 new-shape2))))
            (mv new-shape
                (make-shape-eq-proof-trans
                 :shape1 (shape-splice (cons ispace is))
                 :shape2 mid-shape
                 :shape3 new-shape
                 :premise1-proof (make-shape-eq-proof-splice1m-dim
                                  :dim ispace.dim
                                  :ispaces is)
                 :premise2-proof
                 (make-shape-eq-proof-cong-append
                  :shapes1 (list shape1 (shape-splice is))
                  :shapes2 (list shape1 new-shape2)
                  :premise1-proof
                  (make-shapes-eq-proof-cong-cons
                   :shape1 shape1
                   :shape2 shape1
                   :shapes1 (list (shape-splice is))
                   :shapes2 (list new-shape2)
                   :premise1-proof (shape-eq-proof-refl shape1)
                   :premise2-proof
                   (make-shapes-eq-proof-cong-cons
                    :shape1 (shape-splice is)
                    :shape2 new-shape2
                    :shapes1 nil
                    :shapes2 nil
                    :premise1-proof proof2
                    :premise2-proof (shapes-eq-proof-refl nil)))))))
     :shape (b* ((shape1 ispace.shape)
                 (mid-shape (shape-append (list shape1 (shape-splice is))))
                 (new-shape (shape-append (list shape1 new-shape2))))
              (mv new-shape
                  (make-shape-eq-proof-trans
                   :shape1 (shape-splice (cons ispace is))
                   :shape2 mid-shape
                   :shape3 new-shape
                   :premise1-proof (make-shape-eq-proof-splice1m-shape
                                    :shape ispace.shape
                                    :ispaces is)
                   :premise2-proof
                   (make-shape-eq-proof-cong-append
                    :shapes1 (list shape1 (shape-splice is))
                    :shapes2 (list shape1 new-shape2)
                    :premise1-proof
                    (make-shapes-eq-proof-cong-cons
                     :shape1 shape1
                     :shape2 shape1
                     :shapes1 (list (shape-splice is))
                     :shapes2 (list new-shape2)
                     :premise1-proof (shape-eq-proof-refl shape1)
                     :premise2-proof
                     (make-shapes-eq-proof-cong-cons
                      :shape1 (shape-splice is)
                      :shape2 new-shape2
                      :shapes1 nil
                      :shapes2 nil
                      :premise1-proof proof2
                      :premise2-proof (shapes-eq-proof-refl nil)))))))))
  :measure (len ispaces)
  :verify-guards :after-returns

  ///

  (defret shape-eq-proof-validp-of-unsplice-ispaces
    (implies (ispace-listp ispaces)
             (shape-eq-proof-validp proof
                                    (shape-splice ispaces)
                                    new-shape))
    :hints (("Goal"
             :induct t
             :in-theory
             (enable* shape/ispace-equivalence-definition-validp-defs))))

  (defret shape-nosplicep-of-unsplice-ispaces
    (implies (ispace-list-nosplicep ispaces)
             (shape-nosplicep new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nosplicep-rules))
            '(:expand ((ispace-nosplicep (car ispaces))))))

  (defret shape-unidimsp-of-unsplice-ispaces
    (implies (ispace-list-unidimsp ispaces)
             (shape-unidimsp new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-unidimsp-rules))
            '(:expand ((shape-unidimsp
                        (shape-dims (list (ispace-dim->dim
                                           (car ispaces)))))))))

  (defret shape-nullbinappendp-of-unsplice-ispaces
    (implies (ispace-list-nullbinappendp ispaces)
             (shape-nullbinappendp new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp
                        (shape-append
                         (list (shape-dims (list (ispace-dim->dim
                                                  (car ispaces))))
                               (mv-nth 0 (unsplice-ispaces
                                          (cdr ispaces))))))
                       (shape-nullbinappendp
                        (shape-append
                         (list (ispace-shape->shape (car ispaces))
                               (mv-nth 0 (unsplice-ispaces
                                          (cdr ispaces))))))))))

  (defret shape-nodimispacep-of-unsplice-ispaces
    (implies (ispace-list-nodimispacep ispaces)
             (shape-nodimispacep new-shape))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nodimispacep-rules))
            '(:expand ((ispace-nodimispacep (car ispaces)))))))

;;;;;;;;;;

(defines unsplice-in-shapes/ispaces
  :short "Turn shapes and ispaces into equivalent ones without splices,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the resulting shapes and ispaces are equivalent to
     the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting shapes and ispaces have no splices.")
   (xdoc::p
    "We also show that these functions preserve
     the unary status of dimension shapes,
     the binary or empty status of concatenations,
     and the absence of dimension ispaces,
     which these functions do not affect."))

  (define unsplice-in-shape ((shape shapep))
    :returns (mv (new-shape shapep)
                 (proof shape-eq-proofp))
    :parents (ispace-equivalence-normalizations unsplice-in-shapes/ispaces)
    :short "Turn a shape into
            an equivalent one without splices,
            and construct a proof tree demonstrating the equivalence."
    (shape-case
     shape
     :var (mv (shape-var shape.name)
              (shape-eq-proof-refl (shape-var shape.name)))
     :dims (mv (shape-dims shape.dims)
               (shape-eq-proof-refl (shape-dims shape.dims)))
     :append (b* (((mv new-shapes proof)
                   (unsplice-in-shape-list shape.shapes)))
               (mv (shape-append new-shapes)
                   (make-shape-eq-proof-cong-append
                    :shapes1 shape.shapes
                    :shapes2 new-shapes
                    :premise1-proof proof)))
     :splice (b* (((mv new-ispaces proof)
                   (unsplice-in-ispace-list shape.ispaces))
                  ((mv new-shape proof1)
                   (unsplice-ispaces new-ispaces)))
               (mv new-shape
                   (make-shape-eq-proof-trans
                    :shape1 (shape-splice shape.ispaces)
                    :shape2 (shape-splice new-ispaces)
                    :shape3 new-shape
                    :premise1-proof (make-shape-eq-proof-cong-splice
                                     :ispaces1 shape.ispaces
                                     :ispaces2 new-ispaces
                                     :premise1-proof proof)
                    :premise2-proof proof1))))
    :measure (shape-count shape))

  (define unsplice-in-shape-list ((shapes shape-listp))
    :returns (mv (new-shapes shape-listp)
                 (proof shapes-eq-proofp))
    :parents (ispace-equivalence-normalizations unsplice-in-shapes/ispaces)
    :short "Turn a list of shapes into
            an equivalent one without splices,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp shapes)) (mv nil (shapes-eq-proof-refl nil)))
         ((mv new-shape proof1) (unsplice-in-shape (car shapes)))
         ((mv new-shapes proof2) (unsplice-in-shape-list (cdr shapes))))
      (mv (cons new-shape new-shapes)
          (make-shapes-eq-proof-cong-cons
           :shape1 (shape-fix (car shapes))
           :shape2 new-shape
           :shapes1 (shape-list-fix (cdr shapes))
           :shapes2 new-shapes
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (shape-list-count shapes)

    ///

    (defret len-of-unsplice-in-shape-list
      (equal (len new-shapes)
             (len shapes))
      :hints (("Goal"
               :induct (len shapes)
               :in-theory (enable (:induction len)))))

    (defret consp-of-unsplice-in-shape-list
      (equal (consp new-shapes)
             (consp shapes))
      :hints (("Goal" :expand ((unsplice-in-shape-list shapes))))))

  (define unsplice-in-ispace ((ispace ispacep))
    :returns (mv (new-ispace ispacep)
                 (proof ispace-eq-proofp))
    :parents (ispace-equivalence-normalizations unsplice-in-shapes/ispaces)
    :short "Turn an ispace into
            an equivalent one without splices,
            and construct a proof tree demonstrating the equivalence."
    (ispace-case
     ispace
     :dim (mv (ispace-dim ispace.dim)
              (ispace-eq-proof-refl (ispace-dim ispace.dim)))
     :shape (b* (((mv new-shape proof) (unsplice-in-shape ispace.shape)))
              (mv (ispace-shape new-shape)
                  (make-ispace-eq-proof-cong-shape
                   :shape1 ispace.shape
                   :shape2 new-shape
                   :premise1-proof proof))))
    :measure (ispace-count ispace))

  (define unsplice-in-ispace-list ((ispaces ispace-listp))
    :returns (mv (new-ispaces ispace-listp)
                 (proof ispaces-eq-proofp))
    :parents (ispace-equivalence-normalizations unsplice-in-shapes/ispaces)
    :short "Turn a list of ispaces into
            an equivalent one without splices,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp ispaces)) (mv nil (ispaces-eq-proof-refl nil)))
         ((mv new-ispace proof1) (unsplice-in-ispace (car ispaces)))
         ((mv new-ispaces proof2) (unsplice-in-ispace-list (cdr ispaces))))
      (mv (cons new-ispace new-ispaces)
          (make-ispaces-eq-proof-cong-cons
           :ispace1 (ispace-fix (car ispaces))
           :ispace2 new-ispace
           :ispaces1 (ispace-list-fix (cdr ispaces))
           :ispaces2 new-ispaces
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (ispace-list-count ispaces))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unsplice-in-shapes/ispaces)

  (defret-mutual shape-eq-proof-validp-of-unsplice-in-shapes/ispaces
    (defret shape-eq-proof-validp-of-unsplice-in-shape
      (implies (shapep shape)
               (shape-eq-proof-validp proof
                                      shape
                                      new-shape))
      :fn unsplice-in-shape)
    (defret shapes-eq-proof-validp-of-unsplice-in-shape-list
      (implies (shape-listp shapes)
               (shapes-eq-proof-validp proof
                                       shapes
                                       new-shapes))
      :fn unsplice-in-shape-list)
    (defret ispace-eq-proof-validp-of-unsplice-in-ispace
      (implies (ispacep ispace)
               (ispace-eq-proof-validp proof
                                       ispace
                                       new-ispace))
      :fn unsplice-in-ispace)
    (defret ispaces-eq-proof-validp-of-unsplice-in-ispace-list
      (implies (ispace-listp ispaces)
               (ispaces-eq-proof-validp proof
                                        ispaces
                                        new-ispaces))
      :fn unsplice-in-ispace-list)
    :hints (("Goal"
             :in-theory
             (enable* shape/ispace-equivalence-definition-validp-defs))))

  (defret-mutual shape-nosplicep-of-unsplice-in-shapes/ispaces
    (defret shape-nosplicep-of-unsplice-in-shape
      (shape-nosplicep new-shape)
      :fn unsplice-in-shape)
    (defret shape-list-nosplicep-of-unsplice-in-shape-list
      (shape-list-nosplicep new-shapes)
      :fn unsplice-in-shape-list)
    (defret ispace-nosplicep-of-unsplice-in-ispace
      (ispace-nosplicep new-ispace)
      :fn unsplice-in-ispace)
    (defret ispace-list-nosplicep-of-unsplice-in-ispace-list
      (ispace-list-nosplicep new-ispaces)
      :fn unsplice-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosplicep-rules))
            '(:expand ((shape-nosplicep shape)
                       (ispace-nosplicep ispace)))))

  (defret-mutual shape-unidimsp-of-unsplice-in-shapes/ispaces
    (defret shape-unidimsp-of-unsplice-in-shape
      (implies (shape-unidimsp shape)
               (shape-unidimsp new-shape))
      :fn unsplice-in-shape)
    (defret shape-list-unidimsp-of-unsplice-in-shape-list
      (implies (shape-list-unidimsp shapes)
               (shape-list-unidimsp new-shapes))
      :fn unsplice-in-shape-list)
    (defret ispace-unidimsp-of-unsplice-in-ispace
      (implies (ispace-unidimsp ispace)
               (ispace-unidimsp new-ispace))
      :fn unsplice-in-ispace)
    (defret ispace-list-unidimsp-of-unsplice-in-ispace-list
      (implies (ispace-list-unidimsp ispaces)
               (ispace-list-unidimsp new-ispaces))
      :fn unsplice-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-unidimsp-rules))
            '(:expand ((shape-unidimsp shape)
                       (ispace-unidimsp ispace)))))

  (defret-mutual shape-nullbinappendp-of-unsplice-in-shapes/ispaces
    (defret shape-nullbinappendp-of-unsplice-in-shape
      (implies (shape-nullbinappendp shape)
               (shape-nullbinappendp new-shape))
      :fn unsplice-in-shape)
    (defret shape-list-nullbinappendp-of-unsplice-in-shape-list
      (implies (shape-list-nullbinappendp shapes)
               (shape-list-nullbinappendp new-shapes))
      :fn unsplice-in-shape-list)
    (defret ispace-nullbinappendp-of-unsplice-in-ispace
      (implies (ispace-nullbinappendp ispace)
               (ispace-nullbinappendp new-ispace))
      :fn unsplice-in-ispace)
    (defret ispace-list-nullbinappendp-of-unsplice-in-ispace-list
      (implies (ispace-list-nullbinappendp ispaces)
               (ispace-list-nullbinappendp new-ispaces))
      :fn unsplice-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp shape)
                       (shape-nullbinappendp
                        (shape-append (mv-nth 0 (unsplice-in-shape-list
                                                 (shape-append->shapes
                                                  shape)))))))))

  (defret-mutual shape-nodimispacep-of-unsplice-in-shapes/ispaces
    (defret shape-nodimispacep-of-unsplice-in-shape
      (implies (shape-nodimispacep shape)
               (shape-nodimispacep new-shape))
      :fn unsplice-in-shape)
    (defret shape-list-nodimispacep-of-unsplice-in-shape-list
      (implies (shape-list-nodimispacep shapes)
               (shape-list-nodimispacep new-shapes))
      :fn unsplice-in-shape-list)
    (defret ispace-nodimispacep-of-unsplice-in-ispace
      (implies (ispace-nodimispacep ispace)
               (ispace-nodimispacep new-ispace))
      :fn unsplice-in-ispace)
    (defret ispace-list-nodimispacep-of-unsplice-in-ispace-list
      (implies (ispace-list-nodimispacep ispaces)
               (ispace-list-nodimispacep new-ispaces))
      :fn unsplice-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nodimispacep-rules))
            '(:expand ((ispace-nodimispacep ispace))))))

;;;;;;;;;;;;;;;;;;;;

(defines undim-in-shapes/ispaces
  :short "Turn shapes and ispaces into equivalent ones
          without dimension ispaces,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each dimension ispace is turned into
     the corresponding shape ispace with a unary dimension shape,
     according to the rule @('ispace-dim-shape').")
   (xdoc::p
    "We show that the resulting shapes and ispaces are equivalent to
     the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting shapes and ispaces
     have no dimension ispaces.")
   (xdoc::p
    "We also show that these functions preserve
     the unary status of dimension shapes,
     the binary or empty status of concatenations,
     and the absence of splices,
     which these functions do not affect."))

  (define undim-in-shape ((shape shapep))
    :returns (mv (new-shape shapep)
                 (proof shape-eq-proofp))
    :parents (ispace-equivalence-normalizations undim-in-shapes/ispaces)
    :short "Turn a shape into
            an equivalent one without dimension ispaces,
            and construct a proof tree demonstrating the equivalence."
    (shape-case
     shape
     :var (mv (shape-var shape.name)
              (shape-eq-proof-refl (shape-var shape.name)))
     :dims (mv (shape-dims shape.dims)
               (shape-eq-proof-refl (shape-dims shape.dims)))
     :append (b* (((mv new-shapes proof)
                   (undim-in-shape-list shape.shapes)))
               (mv (shape-append new-shapes)
                   (make-shape-eq-proof-cong-append
                    :shapes1 shape.shapes
                    :shapes2 new-shapes
                    :premise1-proof proof)))
     :splice (b* (((mv new-ispaces proof)
                   (undim-in-ispace-list shape.ispaces)))
               (mv (shape-splice new-ispaces)
                   (make-shape-eq-proof-cong-splice
                    :ispaces1 shape.ispaces
                    :ispaces2 new-ispaces
                    :premise1-proof proof))))
    :measure (shape-count shape))

  (define undim-in-shape-list ((shapes shape-listp))
    :returns (mv (new-shapes shape-listp)
                 (proof shapes-eq-proofp))
    :parents (ispace-equivalence-normalizations undim-in-shapes/ispaces)
    :short "Turn a list of shapes into
            an equivalent one without dimension ispaces,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp shapes)) (mv nil (shapes-eq-proof-refl nil)))
         ((mv new-shape proof1) (undim-in-shape (car shapes)))
         ((mv new-shapes proof2) (undim-in-shape-list (cdr shapes))))
      (mv (cons new-shape new-shapes)
          (make-shapes-eq-proof-cong-cons
           :shape1 (shape-fix (car shapes))
           :shape2 new-shape
           :shapes1 (shape-list-fix (cdr shapes))
           :shapes2 new-shapes
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (shape-list-count shapes)

    ///

    (defret len-of-undim-in-shape-list
      (equal (len new-shapes)
             (len shapes))
      :hints (("Goal"
               :induct (len shapes)
               :in-theory (enable (:induction len)))))

    (defret consp-of-undim-in-shape-list
      (equal (consp new-shapes)
             (consp shapes))
      :hints (("Goal" :expand ((undim-in-shape-list shapes))))))

  (define undim-in-ispace ((ispace ispacep))
    :returns (mv (new-ispace ispacep)
                 (proof ispace-eq-proofp))
    :parents (ispace-equivalence-normalizations undim-in-shapes/ispaces)
    :short "Turn an ispace into
            an equivalent one without dimension ispaces,
            and construct a proof tree demonstrating the equivalence."
    (ispace-case
     ispace
     :dim (mv (ispace-shape (shape-dims (list ispace.dim)))
              (make-ispace-eq-proof-ispace-dim-shape :dim ispace.dim))
     :shape (b* (((mv new-shape proof) (undim-in-shape ispace.shape)))
              (mv (ispace-shape new-shape)
                  (make-ispace-eq-proof-cong-shape
                   :shape1 ispace.shape
                   :shape2 new-shape
                   :premise1-proof proof))))
    :measure (ispace-count ispace))

  (define undim-in-ispace-list ((ispaces ispace-listp))
    :returns (mv (new-ispaces ispace-listp)
                 (proof ispaces-eq-proofp))
    :parents (ispace-equivalence-normalizations undim-in-shapes/ispaces)
    :short "Turn a list of ispaces into
            an equivalent one without dimension ispaces,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp ispaces)) (mv nil (ispaces-eq-proof-refl nil)))
         ((mv new-ispace proof1) (undim-in-ispace (car ispaces)))
         ((mv new-ispaces proof2) (undim-in-ispace-list (cdr ispaces))))
      (mv (cons new-ispace new-ispaces)
          (make-ispaces-eq-proof-cong-cons
           :ispace1 (ispace-fix (car ispaces))
           :ispace2 new-ispace
           :ispaces1 (ispace-list-fix (cdr ispaces))
           :ispaces2 new-ispaces
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (ispace-list-count ispaces))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual undim-in-shapes/ispaces)

  (defret-mutual shape-eq-proof-validp-of-undim-in-shapes/ispaces
    (defret shape-eq-proof-validp-of-undim-in-shape
      (implies (shapep shape)
               (shape-eq-proof-validp proof
                                      shape
                                      new-shape))
      :fn undim-in-shape)
    (defret shapes-eq-proof-validp-of-undim-in-shape-list
      (implies (shape-listp shapes)
               (shapes-eq-proof-validp proof
                                       shapes
                                       new-shapes))
      :fn undim-in-shape-list)
    (defret ispace-eq-proof-validp-of-undim-in-ispace
      (implies (ispacep ispace)
               (ispace-eq-proof-validp proof
                                       ispace
                                       new-ispace))
      :fn undim-in-ispace)
    (defret ispaces-eq-proof-validp-of-undim-in-ispace-list
      (implies (ispace-listp ispaces)
               (ispaces-eq-proof-validp proof
                                        ispaces
                                        new-ispaces))
      :fn undim-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* shape/ispace-equivalence-definition-validp-defs))))

  (defret-mutual shape-nodimispacep-of-undim-in-shapes/ispaces
    (defret shape-nodimispacep-of-undim-in-shape
      (shape-nodimispacep new-shape)
      :fn undim-in-shape)
    (defret shape-list-nodimispacep-of-undim-in-shape-list
      (shape-list-nodimispacep new-shapes)
      :fn undim-in-shape-list)
    (defret ispace-nodimispacep-of-undim-in-ispace
      (ispace-nodimispacep new-ispace)
      :fn undim-in-ispace)
    (defret ispace-list-nodimispacep-of-undim-in-ispace-list
      (ispace-list-nodimispacep new-ispaces)
      :fn undim-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nodimispacep-rules))
            '(:expand ((shape-nodimispacep shape)
                       (ispace-nodimispacep ispace)))))

  (defret-mutual shape-unidimsp-of-undim-in-shapes/ispaces
    (defret shape-unidimsp-of-undim-in-shape
      (implies (shape-unidimsp shape)
               (shape-unidimsp new-shape))
      :fn undim-in-shape)
    (defret shape-list-unidimsp-of-undim-in-shape-list
      (implies (shape-list-unidimsp shapes)
               (shape-list-unidimsp new-shapes))
      :fn undim-in-shape-list)
    (defret ispace-unidimsp-of-undim-in-ispace
      (implies (ispace-unidimsp ispace)
               (ispace-unidimsp new-ispace))
      :fn undim-in-ispace)
    (defret ispace-list-unidimsp-of-undim-in-ispace-list
      (implies (ispace-list-unidimsp ispaces)
               (ispace-list-unidimsp new-ispaces))
      :fn undim-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-unidimsp-rules))
            '(:expand ((shape-unidimsp shape)
                       (ispace-unidimsp ispace)
                       (shape-unidimsp
                        (shape-dims (list (ispace-dim->dim ispace))))))))

  (defret-mutual shape-nullbinappendp-of-undim-in-shapes/ispaces
    (defret shape-nullbinappendp-of-undim-in-shape
      (implies (shape-nullbinappendp shape)
               (shape-nullbinappendp new-shape))
      :fn undim-in-shape)
    (defret shape-list-nullbinappendp-of-undim-in-shape-list
      (implies (shape-list-nullbinappendp shapes)
               (shape-list-nullbinappendp new-shapes))
      :fn undim-in-shape-list)
    (defret ispace-nullbinappendp-of-undim-in-ispace
      (implies (ispace-nullbinappendp ispace)
               (ispace-nullbinappendp new-ispace))
      :fn undim-in-ispace)
    (defret ispace-list-nullbinappendp-of-undim-in-ispace-list
      (implies (ispace-list-nullbinappendp ispaces)
               (ispace-list-nullbinappendp new-ispaces))
      :fn undim-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nullbinappendp-rules))
            '(:expand ((shape-nullbinappendp shape)
                       (shape-nullbinappendp
                        (shape-append (mv-nth 0 (undim-in-shape-list
                                                 (shape-append->shapes
                                                  shape)))))))))

  (defret-mutual shape-nosplicep-of-undim-in-shapes/ispaces
    (defret shape-nosplicep-of-undim-in-shape
      (implies (shape-nosplicep shape)
               (shape-nosplicep new-shape))
      :fn undim-in-shape)
    (defret shape-list-nosplicep-of-undim-in-shape-list
      (implies (shape-list-nosplicep shapes)
               (shape-list-nosplicep new-shapes))
      :fn undim-in-shape-list)
    (defret ispace-nosplicep-of-undim-in-ispace
      (implies (ispace-nosplicep ispace)
               (ispace-nosplicep new-ispace))
      :fn undim-in-ispace)
    (defret ispace-list-nosplicep-of-undim-in-ispace-list
      (implies (ispace-list-nosplicep ispaces)
               (ispace-list-nosplicep new-ispaces))
      :fn undim-in-ispace-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosplicep-rules))
            '(:expand ((shape-nosplicep shape)
                       (ispace-nosplicep ispace))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dim-equiv-to-binadd-p-when-dimp
  :short "Every dimension is equivalent to one with only binary additions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rules @('add0'), @('add1'), and @('add3m'),
     described in @(see dim-equivalence-definition)."))
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
     described in @(see dim-equivalence-definition)."))
  (implies (dimp dim)
           (dim-equiv-to-binmul-p dim))
  :use ((:instance dim-equiv-to-binmul-p-suff
                   (dim1 (mv-nth 0 (binarize-mul-in-dim dim))))
        (:instance dim-eq-when-proof-validp
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
     described in @(see dim-equivalence-definition):
     variadic subtractions are reduced to unary ones.
     Since nullary subtractions are illegal and cannot be reduced
     (each one is only equivalent to itself, via reflexivity),
     the theorem assumes that the dimension has no nullary subtractions."))
  (implies (and (dimp dim)
                (dim-nonullsubp dim))
           (dim-equiv-to-unisub-p dim))
  :use ((:instance dim-equiv-to-unisub-p-suff
                   (dim1 (mv-nth 0 (unarize-sub-in-dim dim))))
        (:instance dim-eq-when-proof-validp
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
     (see @(tsee unarize-sub-dims));
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
        (:instance dim-eq-when-proof-validp
                   (proof (mv-nth 1 (unarize-sub-in-dim dim)))
                   (concl.dim1 dim)
                   (concl.dim2 (mv-nth 0 (unarize-sub-in-dim dim))))
        (:instance dim-eq-of-binarize-add-in-dim
                   (dim (mv-nth 0 (unarize-sub-in-dim dim))))
        (:instance dim-eq-when-proof-validp
                   (proof (mv-nth 1 (binarize-mul-in-dim
                                     (binarize-add-in-dim
                                      (mv-nth 0 (unarize-sub-in-dim dim))))))
                   (concl.dim1 (binarize-add-in-dim
                                (mv-nth 0 (unarize-sub-in-dim dim))))
                   (concl.dim2 (mv-nth 0 (binarize-mul-in-dim
                                          (binarize-add-in-dim
                                           (mv-nth 0 (unarize-sub-in-dim
                                                      dim))))))))
  :enable dim-eq-trans-swapped
  :disable dim-eq-of-binarize-add-in-dim)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled shape-equiv-to-unidims-p-when-shapep
  :short "Every shape is equivalent to one
          with only unary dimension shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rules @('dims0') and @('dims2m'),
     described in @(see shape/ispace-equivalence-definition)."))
  (implies (shapep shape)
           (shape-equiv-to-unidims-p shape))
  :use ((:instance shape-equiv-to-unidims-p-suff
                   (shape1 (mv-nth 0 (unarize-dims-in-shape shape))))
        (:instance shape-eq-when-proof-validp
                   (proof (mv-nth 1 (unarize-dims-in-shape shape)))
                   (concl.shape1 shape)
                   (concl.shape2 (mv-nth 0 (unarize-dims-in-shape shape))))))

;;;;;;;;;;;;;;;;;;;;

(defruled shape-equiv-to-nullbinappend-p-when-shapep
  :short "Every shape is equivalent to one
          with only binary or empty concatenations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rules @('append1') and @('append3m'),
     described in @(see shape/ispace-equivalence-definition)."))
  (implies (shapep shape)
           (shape-equiv-to-nullbinappend-p shape))
  :use ((:instance shape-equiv-to-nullbinappend-p-suff
                   (shape1 (mv-nth 0 (nullbinarize-append-in-shape shape))))
        (:instance shape-eq-when-proof-validp
                   (proof (mv-nth 1 (nullbinarize-append-in-shape shape)))
                   (concl.shape1 shape)
                   (concl.shape2 (mv-nth 0 (nullbinarize-append-in-shape
                                            shape))))))

;;;;;;;;;;;;;;;;;;;;

(defruled shape-equiv-to-nosplice-p-when-shapep
  :short "Every shape is equivalent to one without splices."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rules @('splice0'), @('splice1m-dim'), and @('splice1m-shape'),
     described in @(see shape/ispace-equivalence-definition)."))
  (implies (shapep shape)
           (shape-equiv-to-nosplice-p shape))
  :use ((:instance shape-equiv-to-nosplice-p-suff
                   (shape1 (mv-nth 0 (unsplice-in-shape shape))))
        (:instance shape-eq-when-proof-validp
                   (proof (mv-nth 1 (unsplice-in-shape shape)))
                   (concl.shape1 shape)
                   (concl.shape2 (mv-nth 0 (unsplice-in-shape shape))))))

;;;;;;;;;;;;;;;;;;;;

(defruled shape-equiv-to-nodimispace-p-when-shapep
  :short "Every shape is equivalent to one without dimension ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     rule @('ispace-dim-shape'),
     described in @(see shape/ispace-equivalence-definition)."))
  (implies (shapep shape)
           (shape-equiv-to-nodimispace-p shape))
  :use ((:instance shape-equiv-to-nodimispace-p-suff
                   (shape1 (mv-nth 0 (undim-in-shape shape))))
        (:instance shape-eq-when-proof-validp
                   (proof (mv-nth 1 (undim-in-shape shape)))
                   (concl.shape1 shape)
                   (concl.shape2 (mv-nth 0 (undim-in-shape shape))))))

;;;;;;;;;;;;;;;;;;;;

(defruled shape-equiv-to-unidims-nullbinappend-nosplice-nodimispace-p-when-shapep
  :short "Every shape is equivalent to one
          with only unary dimension shapes,
          with only binary or empty concatenations,
          without splices, and
          without dimension ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a corollary of composing the four transformations,
     in the order:
     unarize dimension shapes,
     make concatenations binary or empty,
     eliminate splices,
     eliminate dimension ispaces.
     Each transformation establishes its own status,
     and preserves the statuses established by the preceding ones.")
   (xdoc::p
    "Unlike the analogous corollary for dimensions
     (see @(tsee dim-equiv-to-binadd-binmul-unisub-p-when-dimp-and-nonullsubp)),
     any order of the four transformations works,
     because each transformation preserves
     the statuses established by the other three."))
  (implies (shapep shape)
           (shape-equiv-to-unidims-nullbinappend-nosplice-nodimispace-p shape))
  :use ((:instance
         shape-equiv-to-unidims-nullbinappend-nosplice-nodimispace-p-suff
         (shape1
          (mv-nth 0 (undim-in-shape
                     (mv-nth 0 (unsplice-in-shape
                                (mv-nth 0 (nullbinarize-append-in-shape
                                           (mv-nth 0 (unarize-dims-in-shape
                                                      shape))))))))))
        (:instance
         shape-eq-when-proof-validp
         (proof (mv-nth 1 (unarize-dims-in-shape shape)))
         (concl.shape1 shape)
         (concl.shape2 (mv-nth 0 (unarize-dims-in-shape shape))))
        (:instance
         shape-eq-when-proof-validp
         (proof
          (mv-nth 1 (nullbinarize-append-in-shape
                     (mv-nth 0 (unarize-dims-in-shape shape)))))
         (concl.shape1 (mv-nth 0 (unarize-dims-in-shape shape)))
         (concl.shape2
          (mv-nth 0 (nullbinarize-append-in-shape
                     (mv-nth 0 (unarize-dims-in-shape shape))))))
        (:instance
         shape-eq-when-proof-validp
         (proof
          (mv-nth 1 (unsplice-in-shape
                     (mv-nth 0 (nullbinarize-append-in-shape
                                (mv-nth 0 (unarize-dims-in-shape shape)))))))
         (concl.shape1
          (mv-nth 0 (nullbinarize-append-in-shape
                     (mv-nth 0 (unarize-dims-in-shape shape)))))
         (concl.shape2
          (mv-nth 0 (unsplice-in-shape
                     (mv-nth 0 (nullbinarize-append-in-shape
                                (mv-nth 0 (unarize-dims-in-shape shape))))))))
        (:instance
         shape-eq-when-proof-validp
         (proof
          (mv-nth 1 (undim-in-shape
                     (mv-nth 0 (unsplice-in-shape
                                (mv-nth 0 (nullbinarize-append-in-shape
                                           (mv-nth 0 (unarize-dims-in-shape
                                                      shape)))))))))
         (concl.shape1
          (mv-nth 0 (unsplice-in-shape
                     (mv-nth 0 (nullbinarize-append-in-shape
                                (mv-nth 0 (unarize-dims-in-shape shape)))))))
         (concl.shape2
          (mv-nth 0 (undim-in-shape
                     (mv-nth 0 (unsplice-in-shape
                                (mv-nth 0 (nullbinarize-append-in-shape
                                           (mv-nth 0 (unarize-dims-in-shape
                                                      shape)))))))))))
  :enable shape-eq-trans-swapped)
