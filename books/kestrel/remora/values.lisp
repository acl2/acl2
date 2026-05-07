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

(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/basic/rfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (dynamic-semantics)
  :short "Values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for the values that
     Remora expressions and atoms evaluate to.
     [thesis], [arxiv], and [esop],
     in line with much programming language literature,
     define values as subsets of expressions and atoms,
     namely the ones that cannot be further reduced.
     While we could follow the same approach here,
     instead we start with defining instead separate fixtypes for values.")
   (xdoc::p
    "This separation seems a bit cleaner,
     also given the higher level of detail of our formalization
     (compared to the aforementioned publications).
     For instance, base literals in @(tsee base-lit)
     contain syntactic information that is semantically irrelevant.
     We normally think of integer values as mathematical integers,
     not as ASTs with optional signs and sequences of digits
     (although the mapping from the latter to the former
     is fairly straightforward).
     The difference is even more pronounced for floats.")
   (xdoc::p
    "Nonetheless, if we discover that it is more convenient
     to define as subsets of expressions and atoms,
     we will switch to that approach."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-value
  :short "Fixtype of integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "[thesis] does not pin down the details of integer values,
     leaving them abstract.
     [impl] use Haskell's @('Int'),
     which consists of fixed-precision integers with at least 30 bits.")
   (xdoc::p
    "We do not yet know the definite intention for integer in Remora,
     e.g. whether it should prescribe one portable integer format,
     or allow a range of formats,
     or even allow multiple integer types.
     For now, we use ACL2 integers."))
  ((int int))
  :pred int-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum float-value
  :short "Fixtype of float values."
  :long
  (xdoc::topstring
   (xdoc::p
    "[thesis] does not pin down the details of float values,
     leaving them abstract.
     [impl] uses Haskell's @('Float'),
     which consists of single-precision floating-point numbers,
     ``desired'' (according to the Haskell documentation)
     to comply with the IEEE standard.")
   (xdoc::p
    "We do not yet know the definite intention for floats in Remora,
     e.g. whether it should prescribe one portable float format,
     or allow a range of formats,
     or even allow multiple float types.
     For now, we use ACL2 rationals,
     with the addition of negative zero (rational 0 being the positive one),
     negative and positive infinities, and not-a-number.
     This is really a placeholder for
     a more realistic representation of float values,
     e.g. in terms of IEEE floatings from @('[books]/kestrel/floats'),
     which we plan to use once the Remora design is clarified."))
  (:ratio ((ratio rational)))
  ;; no :pos0, which is just :ratio 0
  (:neg0 ())
  (:posinf ())
  (:neginf ())
  (:nan ())
  :pred float-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-value
  :short "Fixtype of base values."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are booleans, integers, and floats."))
  (:bool ((val bool)))
  (:int ((val int-value)))
  (:float ((val float-value)))
  :pred base-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes atomvalues/values
  :short "Fixtypes of atom values, (array) values, and lists thereof."
  :long
  (xdoc::topstring
   (xdoc::p
    "As in [thesis] (@($\\mathit{Val}$) and @($\\mathit{Atval}$) in Figure 4.2),
     we distinguish atom and array values,
     but we generally use the unqualified `values' to refer to array values,
     because in a way these are the ``primary'' values of interest.
     This partitioning of values reflects the one of atoms and expressions.
     In contrast, [impl] has one Haskell type for all values."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum atom-value
    :parents (values atomvalues/values)
    :short "Fixtype of atom values."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       base values,
       lambda abstractions,
       and boxed array values.
       This corresponds to @($\\mathit{Atval}$) in [thesis],
       with the difference that we do not have @($\\mathfrak{o}$) here,
       because in our ASTs, as in [impl],
       primitive operations are represented as variables
       (whose values are predefined).")
     (xdoc::p
      "Our current definition of box values follows [thesis],
       but we may be able to derive ispaces and types
       from the array value itself.
       This will be investigated soon."))
    (:base ((val base-value)))
    (:lambda ((params var+type-list)
              (body expr)))
    (:tlambda ((params type-var-list)
               (body expr)))
    (:ilambda ((parms ispace-var-list)
               (body expr)))
    (:box ((ispaces ispace-list)
           (array value)
           (type type)))
    :pred atom-valuep
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum value
    :parents (values atomvalues/values)
    :short "Fixtype of (array) values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We depart from [thesis] and [impl],
       and define an array value as
       either a scalar (zero-ranked)
       or a vector (i.e. list) of one or more values,
       or an empty vector that carries its type.
       So a one-dimensional array is a vector of scalars,
       a two-dimensional array is a vector of one-dimensional arrays,
       and so on.
       The type in an empty vector is the type of the whole vector,
       not of its elements,
       unlike @(':arrray-empty') and @(':frame-empty') in @(tsee expr).")
     (xdoc::p
      "The non-emptiness of the value list in @(':vector')
       is not captured in this fixtype.
       The FTY @(':require') feature does not seem to work here,
       perhaps because of the interaction with the mutually recursive fixtypes.
       We can enforce this non-emptiness via well-formedness predicates,
       which we need to enforce other constraints on our model of values,
       e.g. that all the array values of a vector have the same shape."))
    (:scalar ((atom atom-value)))
    (:vector ((elems value-list)))
    (:vector-empty ((type type)))
    :pred valuep
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist value-list
    :parents (values atomvalues/values)
    :short "Fixtype of lists of (array) values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp
    :measure (two-nats-measure (acl2-count x) 0)))
