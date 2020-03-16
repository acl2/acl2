; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-types
  :parents (syntax)
  :short "Java primitive types [JLS:4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize Java primitive types as syntactic entities.
     Primitive values are formalized "
    (xdoc::seetopic "primitive-values" "here")
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
  :short "Fixtype of Java (unannotated) primitive types [JLS:4.2] [JLS:8.3]."
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
  :short "Fixtype of Java numeric types [JLS:4.2]."
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
  :short "Fixtype of Java integral types [JLS:4.2]."
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
  :short "Fixtype of Java floating-point types [JLS:4.2]."
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
  (xdoc::topstring
   (xdoc::p
    "This is denoted (for all types) @($<_1$) in [JLS].")
   (xdoc::p
    "The direct subtype relation is irreflexive.
     Since this function fixes its arguments,
     we can express irreflexivity more strongly
     on equivalent (not necessarily equal) primitive types."))
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
    (implies (primitive-type-equiv x y)
             (not (primitive-type-<1 x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitive-type-< ((sub primitive-typep) (sup primitive-typep))
  :returns (yes/no booleanp)
  :short "Proper subtype relation over primitive types [JLS:4.10]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is denoted (for all types) @($<1$) in [JLS].")
   (xdoc::p
    "It is the transitive closure of
     the direct subtype relation @(tsee primitive-type-<1)."))
  (primitive-type-case sub
                       :boolean nil
                       :char (or (primitive-type-case sup :int)
                                 (primitive-type-case sup :long)
                                 (primitive-type-case sup :float)
                                 (primitive-type-case sup :double))
                       :byte (or (primitive-type-case sup :short)
                                 (primitive-type-case sup :int)
                                 (primitive-type-case sup :long)
                                 (primitive-type-case sup :float)
                                 (primitive-type-case sup :double))
                       :short (or (primitive-type-case sup :int)
                                  (primitive-type-case sup :long)
                                  (primitive-type-case sup :float)
                                  (primitive-type-case sup :double))
                       :int (or (primitive-type-case sup :long)
                                (primitive-type-case sup :float)
                                (primitive-type-case sup :double))
                       :long (or (primitive-type-case sup :float)
                                 (primitive-type-case sup :double))
                       :float (primitive-type-case sup :double)
                       :double nil)
  :hooks (:fix)
  ///

  (defrule primitive-type-<-when-primitive-type-<1
    (implies (primitive-type-<1 x y)
             (primitive-type-< x y))
    :enable primitive-type-<1)

  (defrule primitive-type-<-transitive
    (implies (and (primitive-type-< x y)
                  (primitive-type-< y z))
             (primitive-type-< x z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitive-type-<= ((sub primitive-typep) (sup primitive-typep))
  :returns (yes/no booleanp)
  :short "Subtype relation over primitive types [JLS:4.10]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is denoted (for all types) @($<:$) in [JLS].")
   (xdoc::p
    "It is the reflexive and transitive closure of
     the direct subtype relation @(tsee primitive-type-<1),
     or equivalently the reflexive closure of @(tsee primitive-type-<).")
   (xdoc::p
    "The subtype relation is a partial order:
     reflexive, antisymmetric, and transitive.
     Antisymmetry must be stated modulo fixing,
     because this function is defined to fix its arguments.
     Since this function fixes its arguments,
     reflexivity can be stated more strongly
     on equivalent (not necessarily equal) primitive-types."))
  (or (primitive-type-equiv sub sup)
      (primitive-type-< sub sup))
  :hooks (:fix)
  ///

  (defrule primitive-type-<=-when-primitive-type-<1
    (implies (primitive-type-<1 x y)
             (primitive-type-<= x y))
    :enable (primitive-type-<1 primitive-type-<))

  (defrule primitive-type-<=-reflexive
    (implies (primitive-type-equiv x y)
             (primitive-type-<= x y)))

  (defrule primitive-type-<=-antisymmetric
    (implies (and (primitive-type-<= x y)
                  (primitive-type-<= y x))
             (primitive-type-equiv x y))
    :enable primitive-type-<)

  (defrule primitive-type-<=-transitive
    (implies (and (primitive-type-<= x y)
                  (primitive-type-<= y z))
             (primitive-type-<= x z))
    :use primitive-type-<-transitive))
