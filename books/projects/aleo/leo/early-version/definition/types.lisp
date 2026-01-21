; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "bit-sizes")
(include-book "identifiers")

(include-book "kestrel/fty/defresult" :dir :system)

; to have FTY::DEFLIST generate theorems about NTH:
(local (include-book "std/lists/nth" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (abstract-syntax)
  :short "Leo types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize an abstract syntactic representation
     of all the Leo types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes type/typelist

  (fty::deftagsum type
    :short "Fixtype of Leo types."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are the primitive types,
       identifiers (used as types),
       and the tuple types.")
     (xdoc::p
      "Tuple types have two or more components, but we do not require that here.
       We can formulate and prove that invariant separately.
       Keeping the abstract syntax of types more general
       also facilitates a possible future extension of Leo
       in which tuple types with one component are actually allowed.")
     (xdoc::p
       "Instead of a zero-element tuple type, we have a primitive unit type."))
    (:bool ())
    (:unsigned ((size bitsize)))
    (:signed ((size bitsize)))
    (:field ())
    (:group ())
    (:scalar ())
    (:address ())
    (:string ())
    (:internal-named ((get identifier)
                      (recordp bool)))
    (:external-named ((get locator)
                      (recordp bool)))
    (:unit ())
    (:tuple ((components type-list)))
    :pred typep)

  (fty::deflist type-list
    :short "Fixtype of lists of types."
    :elt-type type
    :true-listp t
    :elementp-of-nil nil
    :pred type-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-option
  type
  :short "Fixtype of optional types."
  :pred type-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-option-set
  :short "Fixtype of sets of optional types."
  :elt-type type-option
  :pred type-option-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-result
  :short "Fixtype of types and @(see errors)."
  :ok type
  :pred type-resultp
  :prepwork ((local (in-theory (e/d (type-kind) (typep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-list-result
  :short "Fixtype of lists of types and @(see errors)."
  :ok type-list
  :pred type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-option-result
  :short "Fixtype of optional types and @(see errors)."
  :ok type-option
  :pred type-option-resultp
  :prepwork ((local (in-theory (enable typep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-option-set-result
  :short "Fixtype of errors and sets of optional types."
  :ok type-option-set
  :pred type-option-set-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod name+type
  :short "Fixtype of pairs consisting of a name (identifier) and a type."
  ((name identifier)
   (type type))
  :tag :name+type
  :pred name+type-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult name+type-result
  :short "Fixtype of errors and pairs consisting of a name and a type."
  :ok name+type
  :pred name+type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap type-map
  :short "Fixtype of finite maps from identifiers to types."
  :key-type identifier
  :val-type type
  :pred type-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-map-result
  :short "Fixtype of errors and finite maps from identifiers to types."
  :ok type-map
  :pred type-map-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an integer type."
  (or (type-case type :unsigned)
      (type-case type :signed))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an arithmetic type."
  (or (type-integerp type)
      (type-case type :field)
      (type-case type :group)
      (type-case type :scalar))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-primitivep ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a primitive type."
  (or (type-arithmeticp type)
      (type-case type :bool)
      (type-case type :address)
      (type-case type :string))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-namedp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a named type."
  (or (type-primitivep type)
      (type-case type :internal-named)
      (type-case type :external-named))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-identifiers
  :short "Set of identifiers that occur in a type."

  (define type-identifiers ((type typep))
    :returns (ids identifier-setp)
    (type-case type
               :bool nil
               :unsigned nil
               :signed nil
               :field nil
               :group nil
               :scalar nil
               :address nil
               :string nil
               :internal-named (set::insert type.get nil)
               ;; Note, users of type-identifiers will need to be extended
               ;; before the set returned starts returning locators.
               ;; We might not want locators if the external program
               ;; dependencies form a DAG.
               ;; For now, we omit external named types.
               :external-named nil
               :unit nil
               :tuple (type-list-identifiers type.components))
    :measure (type-count type))

  (define type-list-identifiers ((types type-listp))
    :returns (ids identifier-setp)
    (cond ((endp types) nil)
          (t (set::union (type-identifiers (car types))
                         (type-list-identifiers (cdr types)))))
    :measure (type-list-count types))

  :verify-guards nil ; done below
  ///
  (verify-guards type-identifiers)

  (fty::deffixequiv-mutual type-identifiers))
