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
     where @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\Delta$) is a kind environment that assigns kinds to variables,
     @($\\tau$) is a type,
     and @($k$) is a kind (`atom' or `array').
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
     Where those rules require types of the atom kind,
     we use @(tsee type-atomp) to check that on the type itself.
     Where those rules require types of the array kind,
     we actually allow all types, because in our formalization
     we regard atom types as equivalent to zero-rank array types;
     see @(see type-equivalence)."))

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
           (type-atomp type)
           (ispace-ok ivars ispace))
          (type-ok ivars tvars (type-array type ispace)))

   (bracket ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (typep type)
             (ispace-listp ispaces)
             (type-ok ivars tvars type)
             (type-atomp type)
             (ispaces-ok ivars ispaces))
            (type-ok ivars tvars (type-bracket type ispaces)))

   ;; function types:

   (fun ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (typep type-in)
         (typep type-out)
         (type-ok ivars tvars type-in)
         (type-ok ivars tvars type-out))
        (type-ok ivars tvars (type-fun type-in type-out)))

   (funn ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (type-listp types-in)
          (typep type-out)
          (types-ok ivars tvars types-in)
          (type-ok ivars tvars type-out))
         (type-ok ivars tvars (type-funn types-in type-out)))

   ;; universal types:

   (forall ((ispace-var-setp ivars)
            (type-var-setp tvars)
            (type-varp param)
            (typep type)
            (type-ok ivars (set::insert param tvars) type))
           (type-ok ivars tvars (type-forall param type)))

   (foralln ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (type-var-listp params)
             (>= (len params) 2)
             (typep type)
             (type-ok ivars (set::union (set::mergesort params) tvars) type))
            (type-ok ivars tvars (type-foralln params type)))

   ;; product types:

   (pi ((ispace-var-setp ivars)
        (type-var-setp tvars)
        (ispace-varp param)
        (typep type)
        (type-ok (set::insert param ivars) tvars type))
       (type-ok ivars tvars (type-pi param type)))

   (pin ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (ispace-var-listp params)
         (>= (len params) 2)
         (typep type)
         (type-ok (set::union (set::mergesort params) ivars) tvars type))
        (type-ok ivars tvars (type-pin params type)))

   ;; sum types:

   (sigma ((ispace-var-setp ivars)
           (type-var-setp tvars)
           (ispace-varp param)
           (typep type)
           (type-ok (set::insert param ivars) tvars type))
          (type-ok ivars tvars (type-sigma param type)))

   (sigman ((ispace-var-setp ivars)
            (type-var-setp tvars)
            (ispace-var-listp params)
            (>= (len params) 2)
            (typep type)
            (type-ok (set::union (set::mergesort params) ivars) tvars type))
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
  (verify-guards type-ok-funn-validp)
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
