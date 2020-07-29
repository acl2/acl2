; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "package-names")
(include-book "primitive-types")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ reference-types
  :parents (syntax)
  :short "Java reference types [JLS:4.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize Java reference types as syntactic entities.
     Reference values are formalized "
    (xdoc::seetopic "reference-values" "here")
    ".")
   (xdoc::p
    "The relevant grammar rules are
     the ones in [JLS:4.3] (for @('reference-type') etc.)
     and the ones in [JLS:4.5.1] (for @('type-arguments') etc.).
     The rules in [JLS:4.3] include annotations,
     but the grammar also includes rules for unannotated reference types
     in [JLS:8.3] (for @('unann-reference-type') etc.).
     Note, however, that also the rules for @('unann-reference-type') etc.
     include some annotations in certain places.")
   (xdoc::p
    "As done in the "
    (xdoc::seetopic "primitive-types" "formalization of primitive types")
    ", in our formalization of reference types it seems more practical
     to define the `reference types' as the ones without annotations
     (not even the ones in the rules for @('unann-reference-type') etc.,
     and have a separate notion for `annotated reference types'.
     This is just nomenclature, the substance does not change.")
   (xdoc::p
    "For now we just define (unannotated) reference types.
     Annotated reference types will be added later."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes reference-types-definition
  :short "Fixtypes of Java (unannotated) reference types
          and mutually recursive companions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since all the summands of @('class-type') are recursive,
     we need to supply a @(':base-case-override') and a measure;
     see @(tsee fty::deftagsum) for details."))

  (fty::deftagsum reference-type
    :short "Fixtype of Java (unannotated) reference types [JLS:4.3] [JLS:8.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to the grammar rule for @('unann-reference-type').")
     (xdoc::p
      "As explained in @(tsee class-type),
       our @(tsee class-type) fixtype corresponds to
       @('unann-class-or-interface-type'),
       @('unann-class-type'), and
       @('unann-interface-type')
       in the grammar.")
     (xdoc::p
      "An (unannotated) type variable is a type identifier,
       according to the rule for @('unann-type-variable')."))
    (:class ((get class-type)))
    (:array ((get array-type)))
    (:variable ((get tidentifier)))
    :pred reference-typep
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum class-type
    :short "Fixtype of Java (unannotated) class (and interface) types
            [JLS:4.3] [JLS:8.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "According to the grammar,
       @('unann-interface-type') is a synonym of @('unann-class-type'),
       and @('interface-type') is a synonym of @('class-type').
       These synonyms have been presumably introduced
       to emphasize the difference between classes and interfaces.
       However, in our formalization, it seems more convenient
       to just define one syntactic entity for both, called `class type'.
       This is not unlike other uses, in [JLS] and [JVMS],
       of `class' in an attributive role to means `class or interface':
       examples are `class loader' and `class file'.
       We may revisit this choice in the future,
       if we found it actually more convenient to make a distinction
       between classes and interfaces at the syntactic level.")
     (xdoc::p
      "There are three kinds of class types.
       The first one consists of
       a type identifier and some optional type arguments:
       this corresponds to simple names [JLS:6].
       The second one consists of
       a package name, a type identifier, and some optional type arguments:
       this corresponds to a name qualified by a package name [JLS:6].
       The third one consists of
       a class type, a type identifier, and some optional type arguments:
       this denotes a nested class [JLS:8].")
     (xdoc::p
      "Since the three summands of this fixtype have two fields in common,
       an alternative formalization approach is
       to define a class type as a product of those two fields
       plus a qualified that is nothing (for simple names)
       or a package name or a class type;
       that is, to factor the common fields.
       We may do that in the future, if it turns out to be more convenient."))
    (:simple ((name tidentifier)
              (arguments type-argument-list)))
    (:package ((package package-name)
               (name tidentifier)
               (arguments type-argument-list)))
    (:nested ((enclosing class-type)
              (name tidentifier)
              (arguments type-argument-list)))
    :pred class-typep
    :base-case-override :simple
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deftagsum array-type
    :short "Fixtype of Java (unannotated) array types [JLS:4.3] [JLS:8.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "An array type consists of an element type and one or more dimensions
       [JLS:10.1].
       The element type may be
       a primitive type, a class type, or a type variable,
       but not an array type:
       recall the distinction between array components and elements [JLS:10].")
     (xdoc::p
      "The dimensions are simply captured by a positive integer.")
     (xdoc::p
      "Since the three summands of this fixtype have a field in common,
       an alternative formalization approach is
       to define an array type as a product of
       an array element type and a number of dimensions.
       We may do that in the future, if it turns out to be more convenient."))
    (:primitive ((element primitive-type) (dimensions pos)))
    (:class ((element class-type) (dimensions pos)))
    (:variable ((element tidentifier) (dimensions pos)))
    :pred array-typep
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum type-argument
    :short "Fixtype of Java (unannotated) type arguments [JLS:4.5.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "A type argument is a reference type or a wildcard.
       A wildcard may have an upper bound, a lower bound, or no bound."))
    (:reftype ((get reference-type)))
    (:wildcard ())
    (:wildcard-extends ((bound reference-type)))
    (:wildcard-super ((bound reference-type)))
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist type-argument-list
    :short "Fixtype of lists of Java (unannotated) type arguments."
    :elt-type type-argument
    :true-listp t
    :elementp-of-nil nil
    :pred type-argument-listp
    :measure (two-nats-measure (acl2-count x) 0)))
