; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "std/util/definductive" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-validity
  :parents (static-semantics)
  :short "Validity of ispaces, including dimensions and shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sorting rules for ispaces in [thesis] [arxiv] [esop]
     prove judgements of the form
     @($\\Theta \\vdash \\iota :: \\gamma$),
     where
     @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\iota$) is an ispace (called `index' in those publications), and
     @($\\gamma$) is a sort (`dimension' or `shape').")
   (xdoc::p
    "Since our ASTs include sort information as part of the syntax,
     our inference rules prove judgements (i.e. define predicates)
     that omit explicit sort information,
     i.e. just include @($\\Theta$) and @($\\iota$),
     but not @($\\gamma$):
     they say that the ispace satisfies all the static validity conditions
     in the context of the sort environment.
     Since ispace variables carry their own sorts,
     our sort environment is just a set of ispace variables in scope.")
   (xdoc::p
    "We define validity predicates for dimension, shape, and ispace ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dim-validity-definition
  :short "Inference rules that define dimension validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the predicate for individual dimensions,
     we define one for lists of dimensions,
     via the two rules @('empty') and @('cons');
     this corresponds to the use of @($\\cdots$) in [thesis] [arxiv] [esop].
     The rules for individual dimensions follow [thesis] [arxiv] [esop],
     with the addition of rules for multiplication and subtraction,
     which are analogous to the one for addition,
     except that subtraction needs at least one argument."))

  :preds ((dim-ok ivars dim)
          (dims-ok ivars dims))

  :irules

  (;; dimensions:

   (var ((ispace-var-setp ivars)
         (stringp name)
         (set::in (ispace-var-dim name) ivars))
        (dim-ok ivars (dim-var name)))

   (const ((ispace-var-setp ivars)
           (natp val))
          (dim-ok ivars (dim-const val)))

   (add ((ispace-var-setp ivars)
         (dim-listp dims)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-add dims)))

   (mul ((ispace-var-setp ivars)
         (dim-listp dims)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-mul dims)))

   (sub ((ispace-var-setp ivars)
         (dim-listp dims)
         (consp dims)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-sub dims)))

   ;; lists of dimensions:

   (empty ((ispace-var-setp ivars))
          (dims-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (dimp dim)
          (dim-listp dims)
          (dim-ok ivars dim)
          (dims-ok ivars dims))
         (dims-ok ivars (cons dim dims)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive shape/ispace-validity-definition
  :short "Inference rules that define shape and ispace validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(see dim-validity-definition),
     besides predicates for individual shapes and ispaces,
     we define predicates for lists of shapes and lists of ispaces.")
   (xdoc::p
    "The rules for individual shapes and ispaces follow [thesis] [arxiv] [esop],
     with the necessary structural adaptations to our ASTs,
     and with additional rules for splices."))

  :preds ((shape-ok ivars shape)
          (shapes-ok ivars shapes)
          (ispace-ok ivars ispace)
          (ispaces-ok ivars ispaces))

  :irules

  (;; shapes:

   (var ((ispace-var-setp ivars)
         (stringp name)
         (set::in (ispace-var-shape name) ivars))
        (shape-ok ivars (shape-var name)))

   (dims ((ispace-var-setp ivars)
          (dim-listp dims)
          (dims-ok ivars dims))
         (shape-ok ivars (shape-dims dims)))

   (append ((ispace-var-setp ivars)
            (shape-listp shapes)
            (shapes-ok ivars shapes))
           (shape-ok ivars (shape-append shapes)))

   (splice ((ispace-var-setp ivars)
            (ispace-listp ispaces)
            (ispaces-ok ivars ispaces))
           (shape-ok ivars (shape-splice ispaces)))

   ;; lists of shapes:

   (empty ((ispace-var-setp ivars))
          (shapes-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (shapep shape)
          (shape-listp shapes)
          (shape-ok ivars shape)
          (shapes-ok ivars shapes))
         (shapes-ok ivars (cons shape shapes)))

   ;; ispaces:

   (dim ((ispace-var-setp ivars)
         (dimp dim)
         (dim-ok ivars dim))
        (ispace-ok ivars (ispace-dim dim)))

   (shape ((ispace-var-setp ivars)
           (shapep shape)
           (shape-ok ivars shape))
          (ispace-ok ivars (ispace-shape shape)))

   ;; lists of ispaces:

   (empty ((ispace-var-setp ivars))
          (ispaces-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (ispacep ispace)
          (ispace-listp ispaces)
          (ispace-ok ivars ispace)
          (ispaces-ok ivars ispaces))
         (ispaces-ok ivars (cons ispace ispaces)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-validity-guard-verification
  :short "Guard verification of the functions generated by
          @(see dim-validity-definition)."

  ;; rule validity functions:

  (verify-guards dim-ok-var-validp)
  (verify-guards dim-ok-const-validp)
  (verify-guards dim-ok-add-validp)
  (verify-guards dim-ok-mul-validp)
  (verify-guards dim-ok-sub-validp)
  (verify-guards dims-ok-empty-validp)
  (verify-guards dims-ok-cons-validp)

  ;; proof validity functions:

  (verify-guards dim-ok-proof-validp)

  ;; minimality predicates:

  (verify-guards dim-ok-proof-minimalp)
  (verify-guards dims-ok-proof-minimalp)

  ;; validity predicates:

  (verify-guards dim-ok)
  (verify-guards dims-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-validity-guard-verification
  :short "Guard verification of the functions generated by
          @(see shape/ispace-validity-definition)."

  ;; rule validity functions:

  (verify-guards shape-ok-var-validp)
  (verify-guards shape-ok-dims-validp)
  (verify-guards shape-ok-append-validp)
  (verify-guards shape-ok-splice-validp)
  (verify-guards shapes-ok-empty-validp)
  (verify-guards shapes-ok-cons-validp)
  (verify-guards ispace-ok-dim-validp)
  (verify-guards ispace-ok-shape-validp)
  (verify-guards ispaces-ok-empty-validp)
  (verify-guards ispaces-ok-cons-validp)

  ;; proof validity functions:

  (verify-guards shape-ok-proof-validp)

  ;; minimality predicates:

  (verify-guards shape-ok-proof-minimalp)
  (verify-guards shapes-ok-proof-minimalp)
  (verify-guards ispace-ok-proof-minimalp)
  (verify-guards ispaces-ok-proof-minimalp)

  ;; validity predicates:

  (verify-guards shape-ok)
  (verify-guards shapes-ok)
  (verify-guards ispace-ok)
  (verify-guards ispaces-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-validity-holds-only-on-dimensions
  :short "The validity of dimensions and lists of dimensions
          holds only on dimensions and lists of dimensions."

  (defthm-dim-ok-proof-validp-clique-flag
    (defthmd dimp-when-dim-ok-proof-validp
      (implies (dim-ok-proof-validp proof concl.ivars concl.dim)
               (dimp concl.dim))
      :flag dim-ok-proof-validp)
    (defthmd dim-listp-when-dims-ok-proof-validp
      (implies (dims-ok-proof-validp proof concl.ivars concl.dims)
               (dim-listp concl.dims))
      :flag dims-ok-proof-validp)
    :hints
    (("Goal" :in-theory (enable* dim-validity-definition-validp-defs))))

  (defruled dimp-when-dim-ok
    (implies (dim-ok ivars dim)
             (dimp dim))
    :enable (dim-ok dimp-when-dim-ok-proof-validp))

  (defruled dim-listp-when-dims-ok
    (implies (dims-ok ivars dims)
             (dim-listp dims))
    :enable (dims-ok dim-listp-when-dims-ok-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-validity-holds-only-on-shapes/ispaces
  :short "The validity of shapes, ispaces, and lists thereof
          holds only on shapes, ispaces, and lists thereof."

  (defthm-shape-ok-proof-validp-clique-flag
    (defthmd shapep-when-shape-ok-proof-validp
      (implies (shape-ok-proof-validp proof concl.ivars concl.shape)
               (shapep concl.shape))
      :flag shape-ok-proof-validp)
    (defthmd shape-listp-when-shapes-ok-proof-validp
      (implies (shapes-ok-proof-validp proof concl.ivars concl.shapes)
               (shape-listp concl.shapes))
      :flag shapes-ok-proof-validp)
    (defthmd ispacep-when-ispace-ok-proof-validp
      (implies (ispace-ok-proof-validp proof concl.ivars concl.ispace)
               (ispacep concl.ispace))
      :flag ispace-ok-proof-validp)
    (defthmd ispace-listp-when-ispaces-ok-proof-validp
      (implies (ispaces-ok-proof-validp proof concl.ivars concl.ispaces)
               (ispace-listp concl.ispaces))
      :flag ispaces-ok-proof-validp)
    :hints (("Goal"
             :in-theory
             (enable* shape/ispace-validity-definition-validp-defs))))

  (defruled shapep-when-shape-ok
    (implies (shape-ok ivars shape)
             (shapep shape))
    :enable (shape-ok shapep-when-shape-ok-proof-validp))

  (defruled shape-listp-when-shapes-ok
    (implies (shapes-ok ivars shapes)
             (shape-listp shapes))
    :enable (shapes-ok shape-listp-when-shapes-ok-proof-validp))

  (defruled ispacep-when-ispace-ok
    (implies (ispace-ok ivars ispace)
             (ispacep ispace))
    :enable (ispace-ok ispacep-when-ispace-ok-proof-validp))

  (defruled ispace-listp-when-ispaces-ok
    (implies (ispaces-ok ivars ispaces)
             (ispace-listp ispaces))
    :enable (ispaces-ok ispace-listp-when-ispaces-ok-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-validity-holds-only-on-environments
  :short "The validity of dimensions and lists of dimensions
          holds only on sort environments,
          i.e. sets of ispace variables."

  (defthm-dim-ok-proof-validp-clique-flag
    (defthmd ispace-var-setp-when-dim-ok-proof-validp
      (implies (dim-ok-proof-validp proof concl.ivars concl.dim)
               (ispace-var-setp concl.ivars))
      :flag dim-ok-proof-validp)
    (defthmd ispace-var-setp-when-dims-ok-proof-validp
      (implies (dims-ok-proof-validp proof concl.ivars concl.dims)
               (ispace-var-setp concl.ivars))
      :flag dims-ok-proof-validp)
    :hints
    (("Goal" :in-theory (enable* dim-validity-definition-validp-defs))))

  (defruled ispace-var-setp-when-dim-ok
    (implies (dim-ok ivars dim)
             (ispace-var-setp ivars))
    :enable (dim-ok ispace-var-setp-when-dim-ok-proof-validp))

  (defruled ispace-var-setp-when-dims-ok
    (implies (dims-ok ivars dims)
             (ispace-var-setp ivars))
    :enable (dims-ok ispace-var-setp-when-dims-ok-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-validity-holds-only-on-environments
  :short "The validity of shapes, ispaces, and lists thereof
          holds only on sort environments,
          i.e. sets of ispace variables."

  (defthm-shape-ok-proof-validp-clique-flag
    (defthmd ispace-var-setp-when-shape-ok-proof-validp
      (implies (shape-ok-proof-validp proof concl.ivars concl.shape)
               (ispace-var-setp concl.ivars))
      :flag shape-ok-proof-validp)
    (defthmd ispace-var-setp-when-shapes-ok-proof-validp
      (implies (shapes-ok-proof-validp proof concl.ivars concl.shapes)
               (ispace-var-setp concl.ivars))
      :flag shapes-ok-proof-validp)
    (defthmd ispace-var-setp-when-ispace-ok-proof-validp
      (implies (ispace-ok-proof-validp proof concl.ivars concl.ispace)
               (ispace-var-setp concl.ivars))
      :flag ispace-ok-proof-validp)
    (defthmd ispace-var-setp-when-ispaces-ok-proof-validp
      (implies (ispaces-ok-proof-validp proof concl.ivars concl.ispaces)
               (ispace-var-setp concl.ivars))
      :flag ispaces-ok-proof-validp)
    :hints (("Goal"
             :in-theory
             (enable* shape/ispace-validity-definition-validp-defs))))

  (defruled ispace-var-setp-when-shape-ok
    (implies (shape-ok ivars shape)
             (ispace-var-setp ivars))
    :enable (shape-ok ispace-var-setp-when-shape-ok-proof-validp))

  (defruled ispace-var-setp-when-shapes-ok
    (implies (shapes-ok ivars shapes)
             (ispace-var-setp ivars))
    :enable (shapes-ok ispace-var-setp-when-shapes-ok-proof-validp))

  (defruled ispace-var-setp-when-ispace-ok
    (implies (ispace-ok ivars ispace)
             (ispace-var-setp ivars))
    :enable (ispace-ok ispace-var-setp-when-ispace-ok-proof-validp))

  (defruled ispace-var-setp-when-ispaces-ok
    (implies (ispaces-ok ivars ispaces)
             (ispace-var-setp ivars))
    :enable (ispaces-ok ispace-var-setp-when-ispaces-ok-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-validity-stronger-rules
  :short "Stronger versions of
          some of the defining rules of dimension validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "These omit hypotheses
     that follow from @(see dim-validity-holds-only-on-dimensions)
     and @(see dim-validity-holds-only-on-environments),
     or that are absorbed by the fixing operated by fixtype constructors.")
   (xdoc::p
    "The @('!') at the end of the name conveys the idea of `stronger'.")
   (xdoc::p
    "The proof trees for these rules are the same as the weaker variants,
     up to the fixing of the variables in the rules proved via fixing."))

  ;; dimensions:

  (defruled dim-ok-var!
    (implies (and (ispace-var-setp ivars)
                  (set::in (ispace-var-dim name) ivars))
             (dim-ok ivars (dim-var name)))
    :use (:instance dim-ok-var (name (str-fix name))))

  (defruled dim-ok-const!
    (implies (ispace-var-setp ivars)
             (dim-ok ivars (dim-const val)))
    :use (:instance dim-ok-const (val (nfix val))))

  (defruled dim-ok-add!
    (implies (dims-ok ivars dims)
             (dim-ok ivars (dim-add dims)))
    :use dim-ok-add
    :enable (ispace-var-setp-when-dims-ok dim-listp-when-dims-ok))

  (defruled dim-ok-mul!
    (implies (dims-ok ivars dims)
             (dim-ok ivars (dim-mul dims)))
    :use dim-ok-mul
    :enable (ispace-var-setp-when-dims-ok dim-listp-when-dims-ok))

  (defruled dim-ok-sub!
    (implies (and (consp dims)
                  (dims-ok ivars dims))
             (dim-ok ivars (dim-sub dims)))
    :use dim-ok-sub
    :enable (ispace-var-setp-when-dims-ok dim-listp-when-dims-ok))

  ;; lists of dimensions:

  (defruled dims-ok-cons!
    (implies (and (dim-ok ivars dim)
                  (dims-ok ivars dims))
             (dims-ok ivars (cons dim dims)))
    :use dims-ok-cons
    :enable (ispace-var-setp-when-dim-ok
             dimp-when-dim-ok
             dim-listp-when-dims-ok)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-validity-stronger-rules
  :short "Stronger versions of
          some of the defining rules of shape and ispace validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are analogous to @(see dim-validity-stronger-rules)."))

  ;; shapes:

  (defruled shape-ok-var!
    (implies (and (ispace-var-setp ivars)
                  (set::in (ispace-var-shape name) ivars))
             (shape-ok ivars (shape-var name)))
    :use (:instance shape-ok-var (name (str-fix name))))

  (defruled shape-ok-dims!
    (implies (dims-ok ivars dims)
             (shape-ok ivars (shape-dims dims)))
    :use shape-ok-dims
    :enable (ispace-var-setp-when-dims-ok dim-listp-when-dims-ok))

  (defruled shape-ok-append!
    (implies (shapes-ok ivars shapes)
             (shape-ok ivars (shape-append shapes)))
    :use shape-ok-append
    :enable (ispace-var-setp-when-shapes-ok shape-listp-when-shapes-ok))

  (defruled shape-ok-splice!
    (implies (ispaces-ok ivars ispaces)
             (shape-ok ivars (shape-splice ispaces)))
    :use shape-ok-splice
    :enable (ispace-var-setp-when-ispaces-ok ispace-listp-when-ispaces-ok))

  ;; lists of shapes:

  (defruled shapes-ok-cons!
    (implies (and (shape-ok ivars shape)
                  (shapes-ok ivars shapes))
             (shapes-ok ivars (cons shape shapes)))
    :use shapes-ok-cons
    :enable (ispace-var-setp-when-shape-ok
             shapep-when-shape-ok
             shape-listp-when-shapes-ok))

  ;; ispaces:

  (defruled ispace-ok-dim!
    (implies (dim-ok ivars dim)
             (ispace-ok ivars (ispace-dim dim)))
    :use ispace-ok-dim
    :enable (ispace-var-setp-when-dim-ok dimp-when-dim-ok))

  (defruled ispace-ok-shape!
    (implies (shape-ok ivars shape)
             (ispace-ok ivars (ispace-shape shape)))
    :use ispace-ok-shape
    :enable (ispace-var-setp-when-shape-ok shapep-when-shape-ok))

  ;; lists of ispaces:

  (defruled ispaces-ok-cons!
    (implies (and (ispace-ok ivars ispace)
                  (ispaces-ok ivars ispaces))
             (ispaces-ok ivars (cons ispace ispaces)))
    :use ispaces-ok-cons
    :enable (ispace-var-setp-when-ispace-ok
             ispacep-when-ispace-ok
             ispace-listp-when-ispaces-ok)))
