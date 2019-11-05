; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-types
  :parents (syntax)
  :short "Java primitive types [JLS:4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize Java primitive types as syntactic entities.
     Primitive values are formalized "
    (xdoc::seeurl "primitive-values" "here")
    ".")
   (xdoc::p
    "According to the grammar rule for @('primitive-type') [JLS:4.2],
     primitive types (as syntactic entities) include annotations.
     The grammar also includes a rule for @('unann-primitive-type') [JLS:8.3],
     which captures the ``core'' eight primitive types without annotations,
     as they were in the pre-annotations versions of Java.
     However, note that the rules for
     @('integral-type'), @('floating-point-type'), and @('numeric-type')
     do not include annotations,
     even though integral, floating-point, and numeric types
     are considered a subset of the primitive types.")
   (xdoc::p
    "For our formalization,
     it seems more practical to define the `primitive types'
     as the ones without annotations,
     and have a separate notion for `annotated primitive types'.
     This is just nomenclature, the substance does not change.")
   (xdoc::p
    "For now we just define (unannotated) primitive types.
     Annotated primitive types will be added later.")
   (xdoc::p
    "We also formalize the subtype relation on primitive types [JLS:4.10]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum primitive-type
  :short "Java (unannotated) primitive types [JLS:4.2] [JLS:8.3]."
  (:boolean ())
  (:char ())
  (:byte ())
  (:short ())
  (:int ())
  (:long ())
  (:float ())
  (:double ())
  :pred primitive-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum numeric-type
  :short "Java numeric types [JLS:4.2]."
  (:char ())
  (:byte ())
  (:short ())
  (:int ())
  (:long ())
  (:float ())
  (:double ())
  :pred numeric-typep
  ///

  (defrule primitive-type-when-numeric-typep
    (implies (numeric-typep type)
             (primitive-typep type))
    :enable (numeric-typep primitive-typep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum integral-type
  :short "Java integral types [JLS:4.2]."
  (:char ())
  (:byte ())
  (:short ())
  (:int ())
  (:long ())
  :pred integral-typep
  ///

  (defrule numeric-type-when-integral-typep
    (implies (integral-typep type)
             (numeric-typep type))
    :enable (integral-typep numeric-typep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum floating-point-type
  :short "Java floating-point types [JLS:4.2]."
  (:float ())
  (:double ())
  :pred floating-point-typep
  ///

  (defrule numeric-type-when-floating-point-typep
    (implies (floating-point-typep type)
             (numeric-typep type))
    :enable (floating-point-typep numeric-typep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitive-type-<1 ((sub primitive-typep) (sup primitive-typep))
  :returns (yes/no booleanp)
  :short "Direct subtype relation over primitive types [JLS:4.10.1]."
  :long
  (xdoc::topstring-p
   "This is denoted (for all types) @($<_1$) in [JLS].")
  (or (and (primitive-type-case sub :byte)
           (primitive-type-case sup :short))
      (and (primitive-type-case sub :short)
           (primitive-type-case sup :int))
      (and (primitive-type-case sub :int)
           (primitive-type-case sup :long))
      (and (primitive-type-case sub :long)
           (primitive-type-case sup :float))
      (and (primitive-type-case sub :float)
           (primitive-type-case sup :double))
      (and (primitive-type-case sub :char)
           (primitive-type-case sup :int)))
  :hooks (:fix)
  ///

  (defrule primitive-type-<1-irreflexive
    (not (primitive-type-<1 x x))))
