; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")
(include-book "ispace-validity")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-validity
  :parents (static-semantics)
  :short "Validity of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The kinding rules for types in [thesis] [arxiv]
     prove judgements of the form
     @($\\Theta; \\Delta \\vdash \\tau :: k$),
     where
     @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\Delta$) is a kind environment that assigns kinds to variables,
     @($\\tau$) is a type, and
     @($k$) is a kind (`atom' or `array').
     ([esop] actually omits the kind in the judgement,
     but it is an earlier formulation than [thesis] [arxiv].)")
   (xdoc::p
    "Since our ASTs include kind information as part of the syntax,
     our inference rules prove judgements (i.e. define predicates)
     that omit explicit kind information,
     i.e. just include @($\\Theta$), @($\\Delta$), and @($\\tau$),
     but not @($k$):
     they say that the type satisfies all the static validity conditions
     in the context of the sort and kind environments.
     We model sort environments as in @(see ispace-validity),
     and we similarly model kind environments as sets of type variables,
     which carry their own kinds
     similarly to ispace variables carrying their own sorts."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive type-validity-definition
  :short "Inference rules that define type validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the predicate for individual types,
     we define one for lists of types,
     via the two rules @('empty') and @('cons');
     this corresponds to the use of @($\\cdots$) in [thesis] [arxiv] [esop].")
   (xdoc::p
    "The rules follow [thesis] [arxiv] [esop],
     with the necessary adaptations to the richer forms for our ASTs.
     Where those rules require types of atom or array kinds,
     we use @(tsee type-atom-kindp) and @(tsee type-array-kindp)
     on the types to check that.
     Although the ASTs allow atom-kinded types
     where array-kinded types are expected,
     by lifting atom types to scalar (i.e. zero-ranked) array types,
     our type validity rules are stricter,
     requiring the lifting to be explicit:
     the explicit lifting can be performed as part of type inference.")
   (xdoc::p
    "Since nullary function types stand for their output types,
     we have a rule @('fun0') for nullary function types,
     separate from the rule @('fun1m') with one or more input types."))

  :preds ((type-ok ivars tvars type)
          (types-ok ivars tvars types))

  :irules

  (;; type variables:

   (var ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (type-varp tvar)
         (set::in tvar tvars))
        (type-ok ivars tvars (type-var tvar)))

   ;; base types:

   (base ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (base-typep btype))
         (type-ok ivars tvars (type-base btype)))

   ;; array and bracket types:

   (array ((ispace-var-setp ivars)
           (type-var-setp tvars)
           (typep type)
           (ispacep ispace)
           (type-ok ivars tvars type)
           (type-atom-kindp type)
           (ispace-ok ivars ispace))
          (type-ok ivars tvars (type-array type ispace)))

   (bracket ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (typep type)
             (ispace-listp ispaces)
             (type-ok ivars tvars type)
             (type-atom-kindp type)
             (ispaces-ok ivars ispaces))
            (type-ok ivars tvars (type-bracket type ispaces)))

   ;; function types:

   (fun ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (typep type-in)
         (typep type-out)
         (type-ok ivars tvars type-in)
         (type-ok ivars tvars type-out)
         (type-array-kindp type-in)
         (type-array-kindp type-out))
        (type-ok ivars tvars (type-fun type-in type-out)))

   (fun0 ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (typep type)
          (type-ok ivars tvars type))
         (type-ok ivars tvars (type-funn nil type)))

   (fun1m ((ispace-var-setp ivars)
           (type-var-setp tvars)
           (type-listp types-in)
           (consp types-in)
           (typep type-out)
           (types-ok ivars tvars types-in)
           (type-ok ivars tvars type-out)
           (type-list-array-kindp types-in)
           (type-array-kindp type-out))
          (type-ok ivars tvars (type-funn types-in type-out)))

   ;; universal types:

   (forall ((ispace-var-setp ivars)
            (type-var-setp tvars)
            (type-varp param)
            (typep type)
            (type-ok ivars (set::insert param tvars) type)
            (type-array-kindp type))
           (type-ok ivars tvars (type-forall param type)))

   (foralln ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (type-var-listp params)
             (>= (len params) 2)
             (typep type)
             (type-ok ivars (set::union (set::mergesort params) tvars) type)
             (type-array-kindp type))
            (type-ok ivars tvars (type-foralln params type)))

   ;; product types:

   (pi ((ispace-var-setp ivars)
        (type-var-setp tvars)
        (ispace-varp param)
        (typep type)
        (type-ok (set::insert param ivars) tvars type)
        (type-array-kindp type))
       (type-ok ivars tvars (type-pi param type)))

   (pin ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (ispace-var-listp params)
         (>= (len params) 2)
         (typep type)
         (type-ok (set::union (set::mergesort params) ivars) tvars type)
         (type-array-kindp type))
        (type-ok ivars tvars (type-pin params type)))

   ;; sum types:

   (sigma ((ispace-var-setp ivars)
           (type-var-setp tvars)
           (ispace-varp param)
           (typep type)
           (type-ok (set::insert param ivars) tvars type)
           (type-array-kindp type))
          (type-ok ivars tvars (type-sigma param type)))

   (sigman ((ispace-var-setp ivars)
            (type-var-setp tvars)
            (ispace-var-listp params)
            (>= (len params) 2)
            (typep type)
            (type-ok (set::union (set::mergesort params) ivars) tvars type)
            (type-array-kindp type))
           (type-ok ivars tvars (type-sigman params type)))

   ;; lists of types:

   (empty ((ispace-var-setp ivars)
           (type-var-setp tvars))
          (types-ok ivars tvars nil))

   (cons ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (typep type)
          (type-listp types)
          (type-ok ivars tvars type)
          (types-ok ivars tvars types))
         (types-ok ivars tvars (cons type types)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-validity-guard-verification
  :short "Guard verification of the functions generated by
          @(see type-validity-definition)."

  ;; rule validity functions:

  (verify-guards type-ok-var-validp)
  (verify-guards type-ok-base-validp)
  (verify-guards type-ok-array-validp)
  (verify-guards type-ok-bracket-validp)
  (verify-guards type-ok-fun-validp)
  (verify-guards type-ok-fun0-validp)
  (verify-guards type-ok-fun1m-validp)
  (verify-guards type-ok-forall-validp)
  (verify-guards type-ok-foralln-validp)
  (verify-guards type-ok-pi-validp)
  (verify-guards type-ok-pin-validp)
  (verify-guards type-ok-sigma-validp)
  (verify-guards type-ok-sigman-validp)
  (verify-guards types-ok-empty-validp)
  (verify-guards types-ok-cons-validp)

  ;; proof validity functions
  ;; (the premises of the rules for universal, product, and sum types
  ;; apply the predicates to extended environments,
  ;; whose guards follow from the preceding rule validity conjuncts
  ;; only if the rule validity functions are enabled):

  (verify-guards type-ok-proof-validp
    :hints
    (("Goal" :in-theory (enable* type-validity-definition-validp-defs))))

  ;; minimality predicates:

  (verify-guards type-ok-proof-minimalp)
  (verify-guards types-ok-proof-minimalp)

  ;; validity predicates:

  (verify-guards type-ok)
  (verify-guards types-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-validity-holds-only-on-types
  :short "The validity of types and lists of types
          holds only on types and lists of types."

  (defthm-type-ok-proof-validp-clique-flag
    (defthmd typep-when-type-ok-proof-validp
      (implies (type-ok-proof-validp proof concl.ivars concl.tvars concl.type)
               (typep concl.type))
      :flag type-ok-proof-validp)
    (defthmd type-listp-when-types-ok-proof-validp
      (implies (types-ok-proof-validp proof
                                      concl.ivars
                                      concl.tvars
                                      concl.types)
               (type-listp concl.types))
      :flag types-ok-proof-validp)
    :hints
    (("Goal" :in-theory (enable* type-validity-definition-validp-defs))))

  (defruled typep-when-type-ok
    (implies (type-ok ivars tvars type)
             (typep type))
    :enable (type-ok typep-when-type-ok-proof-validp))

  (defruled type-listp-when-types-ok
    (implies (types-ok ivars tvars types)
             (type-listp types))
    :enable (types-ok type-listp-when-types-ok-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-validity-holds-only-on-environments
  :short "The validity of types and lists of types
          holds only on sort and kind environments,
          i.e. sets of ispace variables and sets of type variables."

  (defthm-type-ok-proof-validp-clique-flag
    (defthmd ispace-var-setp-and-type-var-setp-when-type-ok-proof-validp
      (implies (type-ok-proof-validp proof concl.ivars concl.tvars concl.type)
               (and (ispace-var-setp concl.ivars)
                    (type-var-setp concl.tvars)))
      :flag type-ok-proof-validp)
    (defthmd ispace-var-setp-and-type-var-setp-when-types-ok-proof-validp
      (implies (types-ok-proof-validp proof
                                      concl.ivars
                                      concl.tvars
                                      concl.types)
               (and (ispace-var-setp concl.ivars)
                    (type-var-setp concl.tvars)))
      :flag types-ok-proof-validp)
    :hints
    (("Goal" :in-theory (enable* type-validity-definition-validp-defs))))

  (defruled ispace-var-setp-and-type-var-setp-when-type-ok
    (implies (type-ok ivars tvars type)
             (and (ispace-var-setp ivars)
                  (type-var-setp tvars)))
    :enable (type-ok
             ispace-var-setp-and-type-var-setp-when-type-ok-proof-validp))

  (defruled ispace-var-setp-and-type-var-setp-when-types-ok
    (implies (types-ok ivars tvars types)
             (and (ispace-var-setp ivars)
                  (type-var-setp tvars)))
    :enable (types-ok
             ispace-var-setp-and-type-var-setp-when-types-ok-proof-validp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-validity-stronger-rules
  :short "Stronger versions of some of the defining rules of type validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are analogous to @(see dim-validity-stronger-rules)."))

  ;; type variables:

  (defruled type-ok-var!
    (implies (and (ispace-var-setp ivars)
                  (type-var-setp tvars)
                  (set::in tvar tvars))
             (type-ok ivars tvars (type-var tvar)))
    :use type-ok-var)

  ;; base types:

  (defruled type-ok-base!
    (implies (and (ispace-var-setp ivars)
                  (type-var-setp tvars))
             (type-ok ivars tvars (type-base btype)))
    :use (:instance type-ok-base (btype (base-type-fix btype))))

  ;; array and bracket types:

  (defruled type-ok-array!
    (implies (and (type-ok ivars tvars type)
                  (type-atom-kindp type)
                  (ispace-ok ivars ispace))
             (type-ok ivars tvars (type-array type ispace)))
    :use type-ok-array
    :enable (ispace-var-setp-and-type-var-setp-when-type-ok
             typep-when-type-ok
             ispacep-when-ispace-ok))

  (defruled type-ok-bracket!
    (implies (and (type-ok ivars tvars type)
                  (type-atom-kindp type)
                  (ispaces-ok ivars ispaces))
             (type-ok ivars tvars (type-bracket type ispaces)))
    :use type-ok-bracket
    :enable (ispace-var-setp-and-type-var-setp-when-type-ok
             typep-when-type-ok
             ispace-listp-when-ispaces-ok))

  ;; function types:

  (defruled type-ok-fun!
    (implies (and (type-ok ivars tvars type-in)
                  (type-ok ivars tvars type-out)
                  (type-array-kindp type-in)
                  (type-array-kindp type-out))
             (type-ok ivars tvars (type-fun type-in type-out)))
    :use type-ok-fun
    :enable (ispace-var-setp-and-type-var-setp-when-type-ok
             typep-when-type-ok))

  (defruled type-ok-fun0!
    (implies (type-ok ivars tvars type)
             (type-ok ivars tvars (type-funn nil type)))
    :use type-ok-fun0
    :enable (ispace-var-setp-and-type-var-setp-when-type-ok
             typep-when-type-ok))

  (defruled type-ok-fun1m!
    (implies (and (consp types-in)
                  (types-ok ivars tvars types-in)
                  (type-ok ivars tvars type-out)
                  (type-list-array-kindp types-in)
                  (type-array-kindp type-out))
             (type-ok ivars tvars (type-funn types-in type-out)))
    :use type-ok-fun1m
    :enable (ispace-var-setp-and-type-var-setp-when-type-ok
             type-listp-when-types-ok
             typep-when-type-ok))

  ;; universal types:

  (defruled type-ok-forall!
    (implies (and (type-var-setp tvars)
                  (type-ok ivars (set::insert param tvars) type)
                  (type-array-kindp type))
             (type-ok ivars tvars (type-forall param type)))
    :use (type-ok-forall
          (:instance ispace-var-setp-and-type-var-setp-when-type-ok
                     (tvars (set::insert param tvars))))
    :enable typep-when-type-ok)

  (defruled type-ok-foralln!
    (implies (and (type-var-setp tvars)
                  (type-var-listp params)
                  (>= (len params) 2)
                  (type-ok ivars
                           (set::union (set::mergesort params) tvars)
                           type)
                  (type-array-kindp type))
             (type-ok ivars tvars (type-foralln params type)))
    :use (type-ok-foralln
          (:instance ispace-var-setp-and-type-var-setp-when-type-ok
                     (tvars (set::union (set::mergesort params) tvars))))
    :enable typep-when-type-ok)

  ;; product types:

  (defruled type-ok-pi!
    (implies (and (ispace-var-setp ivars)
                  (type-ok (set::insert param ivars) tvars type)
                  (type-array-kindp type))
             (type-ok ivars tvars (type-pi param type)))
    :use (type-ok-pi
          (:instance ispace-var-setp-and-type-var-setp-when-type-ok
                     (ivars (set::insert param ivars))))
    :enable typep-when-type-ok)

  (defruled type-ok-pin!
    (implies (and (ispace-var-setp ivars)
                  (ispace-var-listp params)
                  (>= (len params) 2)
                  (type-ok (set::union (set::mergesort params) ivars)
                           tvars
                           type)
                  (type-array-kindp type))
             (type-ok ivars tvars (type-pin params type)))
    :use (type-ok-pin
          (:instance ispace-var-setp-and-type-var-setp-when-type-ok
                     (ivars (set::union (set::mergesort params) ivars))))
    :enable typep-when-type-ok)

  ;; sum types:

  (defruled type-ok-sigma!
    (implies (and (ispace-var-setp ivars)
                  (type-ok (set::insert param ivars) tvars type)
                  (type-array-kindp type))
             (type-ok ivars tvars (type-sigma param type)))
    :use (type-ok-sigma
          (:instance ispace-var-setp-and-type-var-setp-when-type-ok
                     (ivars (set::insert param ivars))))
    :enable typep-when-type-ok)

  (defruled type-ok-sigman!
    (implies (and (ispace-var-setp ivars)
                  (ispace-var-listp params)
                  (>= (len params) 2)
                  (type-ok (set::union (set::mergesort params) ivars)
                           tvars
                           type)
                  (type-array-kindp type))
             (type-ok ivars tvars (type-sigman params type)))
    :use (type-ok-sigman
          (:instance ispace-var-setp-and-type-var-setp-when-type-ok
                     (ivars (set::union (set::mergesort params) ivars))))
    :enable typep-when-type-ok)

  ;; lists of types:

  (defruled types-ok-cons!
    (implies (and (type-ok ivars tvars type)
                  (types-ok ivars tvars types))
             (types-ok ivars tvars (cons type types)))
    :use types-ok-cons
    :enable (ispace-var-setp-and-type-var-setp-when-type-ok
             typep-when-type-ok
             type-listp-when-types-ok)))
