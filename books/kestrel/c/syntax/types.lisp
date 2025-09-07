; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")
(include-book "implementation-environments")
(include-book "formalized")
(include-book "langdef-mapping")

(include-book "../language/types")

(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (validation-information)
  :short "C types used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a model of C types,
     along with some operations over those types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type
  :short "Fixtype of C types [C17:6.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we do not model all the C types in detail,
     but only an approximate version of them,
     which still lets us perform some validation.
     We plan to refine the types, and the rest of the validator,
     to cover exactly all the validity checks prescribed by [C17]
     (as well as applicable GCC extensions).")
   (xdoc::p
    "We capture the following types:")
   (xdoc::ul
    (xdoc::li
     "The @('void') type [C17:6.2.5/19].")
    (xdoc::li
     "The plain @('char') type [C17:6.2.5/3].")
    (xdoc::li
     "The five standard signed integer types [C17:6.2.5/4]
      and the corresponding unsigned integer types [C17:6.2.5/6].")
    (xdoc::li
     "The three real floating point types [C17:6.2.5/10].")
    (xdoc::li
     "The three complex types [C17:6.2.5/11].
      These are a conditional feature,
      but they must be included in this fixtype
      because this fixtype consists of all the possible types.")
    (xdoc::li
     "The @('_Bool') type [C17:6.2.5/2].")
    (xdoc::li
     "A family of structure types [C17:6.2.5/20].
      Structure types are characterized by an optional tag.
      This is an approximation,
      because there may be different structure types of a given tag,
      or different tagless structure types.")
    (xdoc::li
     "A collective type for all union types [C17:6.2.5/20].
      This is an approximation,
      because there are different union types.")
    (xdoc::li
     "A collective type for all enumeration types [C17:6.2.5/20].
      This is an approximation,
      because there are different enumeration types.")
    (xdoc::li
     "An array types [C17:6.2.5/20],
      derived from the ``element type.''
      This is an approximation,
      because we do not track the size of the array type.")
    (xdoc::li
     "A pointer type [C17:6.2.5/20],
      derived from the ``referenced type.''")
    (xdoc::li
     "A collective type for all function types [C17:6.2.5/20].
      This is an approximation,
      because there are different function types.")
    (xdoc::li
     "An ``unknown'' type that we need due to our current approximation.
      Our validator must not reject valid code.
      But due to our approximate treatment of types,
      we cannot always calculate a type,
      e.g. for a member expression of the form @('s.m')
      where @('s') is an expression with structure type.
      Since our approximate type for all structure types
      has no information about the members,
      we cannot calculate any actual type for @('s.m');
      but if the expression is used elsewhere,
      we need to accept it, because it could have the right type.
      We use this unknown type for this purpose:
      the expression @('s.m') has unknown type,
      and unknown types are always acceptable."))
   (xdoc::p
    "Besides the approximations noted above,
     currently we do not capture atomic types [C17:6.2.5/20],
     which we approximate as the underlying (argument) type.
     We also do not capture @('typedef') names,
     which are instead expanded to their normal form.
     Furthermore, we do not capture qualified types [C17:6.2.5/26]."))
  (:void ())
  (:char ())
  (:schar ())
  (:uchar ())
  (:sshort ())
  (:ushort ())
  (:sint ())
  (:uint ())
  (:slong ())
  (:ulong ())
  (:sllong ())
  (:ullong ())
  (:float ())
  (:double ())
  (:ldouble ())
  (:floatc ())
  (:doublec ())
  (:ldoublec ())
  (:bool ())
  (:struct ((tag? ident-optionp)))
  (:union ())
  (:enum ())
  (:array ((of type)))
  (:pointer ((to type)))
  (:function ())
  (:unknown ())
  :pred typep
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-type
  :short "An irrelevant type."
  :type typep
  :body (type-void))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-option
  type
  :short "Fixtype of optional types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Types are defined in @(tsee type)."))
  :pred type-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-list
  :short "Fixtype of lists of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Types are defined in @(tsee type)."))
  :elt-type type
  :true-listp t
  :elementp-of-nil nil
  :pred type-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-set
  :short "Fixtype of sets of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Types are defined in @(tsee type)."))
  :elt-type type
  :elementp-of-nil nil
  :pred type-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-option-set
  :short "Fixtype of sets of optional types."
  :elt-type type-option
  :elementp-of-nil t
  :pred type-option-setp

  ///

  (defruled type-setp-when-type-option-setp-and-nil-not-member
    (implies (and (type-option-setp types)
                  (not (set::in nil types)))
             (type-setp types))
    :induct t
    :enable (type-setp
             type-option-setp
             set::in
             set::head
             set::tail
             set::emptyp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist type-option-type-alist
  :short "Fixtype of alists from optional types to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Types are defined in @(tsee type)."))
  :key-type type-option
  :val-type type
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred type-option-type-alistp
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-signed-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard signed integer type [C17:6.2.5/4]."
  (and (member-eq (type-kind type) '(:schar :sshort :sint :slong :sllong))
       t)
  :hooks (:fix)

  ///

  (defrule type-standard-signed-integerp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-standard-signed-integerp type)
                    (and (member-equal kind
                                       '(:schar :sshort :sint :slong :sllong))
                         t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-signed-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a signed integer type [C17:6.2.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not model any extended signed integer types,
     so the signed integer types coincide with
     the standard signed integer types."))
  (type-standard-signed-integerp type)
  :hooks (:fix)

  ///

  (defrule type-signed-integerp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-signed-integerp type)
                    (type-standard-signed-integerp type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard unsigned integer type [C17:6.2.5/6]."
  (and (member-eq (type-kind type) '(:bool :uchar :ushort :uint :ulong :ullong))
       t)
  :hooks (:fix)

  ///

  (defrule type-standard-unsigned-integerp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-standard-unsigned-integerp type)
                    (and (member-equal
                           kind
                           '(:bool :uchar :ushort :uint :ulong :ullong))
                         t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an unsigned integer type [C17:6.2.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not model any extended unsigned integer types,
     so the unsigned integer types coincide with
     the standard unsigned integer types."))
  (type-standard-unsigned-integerp type)
  :hooks (:fix)

  ///

  (defrule type-unsigned-integerp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-unsigned-integerp type)
                    (type-standard-unsigned-integerp type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard integer type [C17:6.2.5/7]."
  (or (type-standard-signed-integerp type)
      (type-standard-unsigned-integerp type))
  :hooks (:fix)

  ///

  (defrule type-standard-integerp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-standard-integerp type)
                    (or (type-standard-signed-integerp type)
                        (type-standard-unsigned-integerp type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-real-floatingp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real floating type [C17:6.2.5/10]."
  (and (member-eq (type-kind type) '(:float :double :ldouble))
       t)
  :hooks (:fix)

  ///

  (defrule type-real-floatingp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-real-floatingp type)
                    (and (member-equal kind '(:float :double :ldouble))
                         t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-complexp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a complex type [C17:6.2.5/11]."
  (and (member-eq (type-kind type) '(:floatc :doublec :ldoublec))
       t)
  :hooks (:fix)

  ///

  (defrule type-complexp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-complexp type)
                    (and (member-equal kind '(:floatc :doublec :ldoublec))
                         t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-floatingp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a floating type [C17:6.2.5/11]."
  (or (type-real-floatingp type)
      (type-complexp type))
  :hooks (:fix)

  ///

  (defrule type-floatingp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-floatingp type)
                    (or (type-real-floatingp type)
                        (type-complexp type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-basicp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a basic type [C17:6.2.5/14]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type)
      (type-floatingp type))
  :hooks (:fix)

  ///

  (defrule type-basicp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-basicp type)
                    (or (equal kind :char)
                        (type-signed-integerp type)
                        (type-unsigned-integerp type)
                        (type-floatingp type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-characterp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a character type [C17:6.2.5/15]."
  (and (member-eq (type-kind type) '(:char :schar :uchar))
       t)
  :hooks (:fix)

  ///

  (defrule type-characterp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-characterp type)
                    (and (member-equal kind '(:char :schar :uchar))
                         t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an integer type [C17:6.2.5/17]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type)
      (type-case type :enum))
  :hooks (:fix)

  ///

  (defrule type-integerp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-integerp type)
                    (or (equal kind :char)
                        (type-signed-integerp type)
                        (type-unsigned-integerp type)
                        (type-case type :enum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-realp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real type [C17:6.2.5/17]."
  (or (type-integerp type)
      (type-real-floatingp type))
  :hooks (:fix)

  ///

  (defrule type-realp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-realp type)
                    (or (type-integerp type)
                        (type-real-floatingp type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an arithmetic type [C17:6.2.5/18]."
  (or (type-integerp type)
      (type-floatingp type))
  :hooks (:fix)

  ///

  (defrule type-arithmeticp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-arithmeticp type)
                    (or (type-integerp type)
                        (type-floatingp type)))))

  (defrule type-arithmeticp-when-type-integerp
    (implies (type-integerp type)
             (type-arithmeticp type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalarp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a scalar type [C17:6.2.5/21]."
  (or (type-arithmeticp type)
      (type-case type :pointer))
  :hooks (:fix)

  ///

  (defrule type-scalarp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-scalarp type)
                    (or (type-arithmeticp type)
                        (type-case type :pointer))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-aggregatep ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an aggregate type [C17:6.2.5/21]."
  (or (type-case type :array)
      (type-case type :struct))
  :hooks (:fix)

  ///

  (defrule type-aggregatep-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-aggregatep type)
                    (or (type-case type :array)
                        (type-case type :struct))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-promotedp ((type typep))
  :guard (type-arithmeticp type)
  :returns (yes/no booleanp)
  :short "Check if an arithmetic type is a promoted one."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if it is a possible result of @(tsee type-promote).
     This holds for all types except
     the integer ones with rank below @('int')."))
  (not (member-eq (type-kind type)
                  '(:bool :char :schar :uchar :sshort :ushort :enum)))
  :hooks (:fix)

  ///

  (defrule type-promotedp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-promotedp type)
                    (not (member-equal kind
                                       '(:bool :char :schar :uchar :sshort
                                         :ushort :enum)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-apconvert ((type typep))
  :returns (new-type typep)
  :short "Convert array types to pointer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the conversion in [C17:6.3.2.1/3].
     It leaves non-array types unchanged."))
  (type-case
    type
    :array (make-type-pointer :to type.of)
    :otherwise (type-fix type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-fpconvert ((type typep))
  :returns (new-type typep)
  :short "Convert function types to pointer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the conversion in [C17:6.3.2.1/4].
     It leaves non-function types unchanged.")
   (xdoc::p
    "In our currently approximate type system,
     there is just one type for functions.
     Therefore, the sole function type is converted to
     a pointer type derived from the function type."))
  (if (type-case type :function)
      (make-type-pointer :to (type-function))
    (type-fix type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-promote ((type typep) (ienv ienvp))
  :guard (type-arithmeticp type)
  :returns (new-type typep)
  :short "Perform integer promotions on an arithmetic type [C17:6.3.1.1/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This only changes integer types of rank lower than @('int');
     the other types are left unchanged.
     We need the implementation environment
     because the new type may depend on
     the relative range of the initial type and @('signed int').
     The range of @('_Bool') always fits within @('signed int'),
     and so do @('signed char') and @('signed short').
     For @('unsigned char') and @('unsigned short'),
     as well as for @('char')
     (which may have the same range as @('unsigned char')),
     we need to compare the maxima,
     and return either @('signed int') or @('unsigned int')
     as the promoted type.")
   (xdoc::p
    "The rank of an enumerated type (which is an integer type)
     is implementation-defined,
     and could even vary based on the program,
     as mentioned in footnote 131 of [C17:6.7.2.2/4].
     Thus, for now we promote the (one) enumerated type to unknown."))
  (type-case
   type
   :bool (type-sint)
   :char (if (<= (ienv->char-max ienv) (ienv->sint-max ienv))
             (type-sint)
           (type-uint))
   :schar (type-sint)
   :uchar (if (<= (ienv->uchar-max ienv) (ienv->sint-max ienv))
              (type-sint)
            (type-uint))
   :sshort (type-sint)
   :ushort (if (<= (ienv->ushort-max ienv) (ienv->sint-max ienv))
               (type-sint)
             (type-uint))
   :enum (type-unknown)
   :otherwise (type-fix type))
  :hooks (:fix)

  ///

  (more-returns
   (new-type type-promotedp
             :hints (("Goal" :in-theory (enable type-promotedp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-signed ((type1 typep) (type2 typep))
  :guard (and (type-signed-integerp type1)
              (type-signed-integerp type2)
              (type-promotedp type1)
              (type-promotedp type2))
  :returns (new-type typep)
  :short "Convert two promoted signed integer types to their common type,
          according to the usual arithmetic conversions [C17:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the two promoted operands have (different) signed integer types,
     the common type is the one with highest rank."))
  (cond
   ((or (type-case type1 :sllong)
        (type-case type2 :sllong))
    (type-sllong))
   ((or (type-case type1 :slong)
        (type-case type2 :slong))
    (type-slong))
   (t (type-sint)))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-unsigned ((type1 typep) (type2 typep))
  :guard (and (type-unsigned-integerp type1)
              (type-unsigned-integerp type2)
              (type-promotedp type1)
              (type-promotedp type2))
  :returns (new-type typep)
  :short "Convert two promoted unsigned integer types to their common type,
          according to the usual arithmetic conversions [C17:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the two promoted operands have (different) unsigned integer types,
     the common type is the one with highest rank."))
  (cond
   ((or (type-case type1 :ullong)
        (type-case type2 :ullong))
    (type-ullong))
   ((or (type-case type1 :ulong)
        (type-case type2 :ulong))
    (type-ulong))
   (t (type-uint)))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-signed-unsigned ((type1 typep)
                                        (type2 typep)
                                        (ienv ienvp))
  :guard (and (type-signed-integerp type1)
              (type-unsigned-integerp type2)
              (type-promotedp type1)
              (type-promotedp type2))
  :returns (new-type typep)
  :short "Convert a promoted signed integer type
          and a promoted unsigned integer type
          to their common type,
          according to the usual arithmetic conversions [C17:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the unsigned type is @('unsigned long long int'),
     its rank is always greater than or equal to
     the rank of the signed integer type,
     and thus the result is @('unsigned long long int').")
   (xdoc::p
    "If the unsigned type is @('unsigned long int'), there are two cases.
     If the signed type is @('signed long long int'),
     its rank is higher than the unsigned type, and we have two sub-cases:
     if the signed type can represent the whole range of the unsigned type,
     the result is the signed type;
     otherwise, the result is the unsigned type
     corresponding to the signed type, i.e. @('unsigned long long int').
     If instead the signed type is not @('signed long long int'),
     then its rank is less than or equal to @('unsigned long int'),
     which is therefore the result.")
   (xdoc::p
    "If the unsigned type is @('unsigned int'),
     there are three cases to consider instead of two as just above,
     but the overall logic is similar to just above.")
   (xdoc::p
    "The unsigned type cannot be anything else,
     so we have covered all the cases."))
  (cond
   ((type-case type2 :ullong)
    (type-ullong))
   ((type-case type2 :ulong)
    (cond ((type-case type1 :sllong)
           (if (<= (ienv->ulong-max ienv) (ienv->sllong-max ienv))
               (type-sllong)
             (type-ullong)))
          (t (type-ulong))))
   ((type-case type2 :uint)
    (cond ((type-case type1 :sllong)
           (if (<= (ienv->uint-max ienv) (ienv->sllong-max ienv))
               (type-sllong)
             (type-ullong)))
          ((type-case type1 :slong)
           (if (<= (ienv->uint-max ienv) (ienv->slong-max ienv))
               (type-slong)
             (type-ulong)))
          (t (type-uint))))
   (t (prog2$ (impossible) (irr-type))))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-integerp
                                           type-promotedp
                                           type-unsigned-integerp
                                           type-signed-integerp
                                           type-standard-unsigned-integerp
                                           type-standard-signed-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert ((type1 typep) (type2 typep) (ienv ienvp))
  :guard (and (type-arithmeticp type1)
              (type-arithmeticp type2))
  :returns (new-type typep)
  :short "Perform the usual arithmetic conversions on two arithmetic types
          [C17:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the common type to which the operands are converted,
     which is normally also the type of
     the result of the arithmetic operation.")
   (xdoc::p
    "If either type is unkwnon, the result is the unkwnon type too.
     This case will eventually go away,
     once we have a full type system in our validator.")
   (xdoc::p
    "If at least one type is @('long double _Complex'),
     the result is @('long double _Complex');
     note that [C17:6.3.1.8] talks about a corresponding real type,
     but adds that the result is complex if at least one operand is.
     Otherwise, if at least one type is @('double _Complex'),
     the result is @('double _Complex'),
     according to analogous reasoning.
     Otherwise, the same is the case for @('float _Complex').")
   (xdoc::p
    "Otherwise, none of the types is complex,
     and we have three analogous cases for
     @('long double'), @('double'), and @('float').")
   (xdoc::p
    "Otherwise, none of the types is floating,
     and we apply the integer promotions to both types.
     Then we apply the remaining rules, for integer types, in [C17:6.3.1.8],
     via separate functions (see their documentation)."))
  (cond
   ((or (type-case type1 :ldoublec)
        (type-case type2 :ldoublec))
    (type-ldoublec))
   ((or (type-case type1 :doublec)
        (type-case type2 :doublec))
    (type-doublec))
   ((or (type-case type1 :floatc)
        (type-case type2 :floatc))
    (type-floatc))
   ((or (type-case type1 :ldouble)
        (type-case type2 :ldouble))
    (type-ldouble))
   ((or (type-case type1 :double)
        (type-case type2 :double))
    (type-double))
   ((or (type-case type1 :float)
        (type-case type2 :float))
    (type-float))
   (t (b* ((type1 (type-promote type1 ienv))
           (type2 (type-promote type2 ienv)))
        (cond
         ((or (type-case type1 :unknown)
              (type-case type2 :unknown))
          (type-unknown))
         ((equal type1 type2)
          type1)
         ((and (type-signed-integerp type1)
               (type-signed-integerp type2))
          (type-uaconvert-signed type1 type2))
         ((and (type-unsigned-integerp type1)
               (type-unsigned-integerp type2))
          (type-uaconvert-unsigned type1 type2))
         ((and (type-signed-integerp type1)
               (type-unsigned-integerp type2))
          (type-uaconvert-signed-unsigned type1 type2 ienv))
         ((and (type-unsigned-integerp type1)
               (type-signed-integerp type2))
          (type-uaconvert-signed-unsigned type2 type1 ienv))
         (t (prog2$ (impossible) (irr-type)))))))
  :guard-hints (("Goal"
                 :do-not '(preprocess)
                 :in-theory (e/d (type-arithmeticp
                                  type-integerp
                                  type-unsigned-integerp
                                  type-signed-integerp
                                  type-standard-unsigned-integerp
                                  type-standard-signed-integerp
                                  type-promote
                                  type-promotedp
                                  type-floatingp
                                  type-real-floatingp
                                  type-complexp)
                                 ((:e tau-system)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-compatiblep ((x typep) (y typep))
  :returns (yes/no booleanp)
  :short "Check that two @(see type)s are compatible [C17:6.2.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type compatibility affects whether a redeclaration is permissible,
     whether one type may be used when another is expected,
     and whether two declarations referring to the same object or function are
     well-defined.
     This is a little weaker than type equality.
     For instance,
     an enumeration type is different than an integer type [C17:6.2.5/16],
     but all enumeration types are compatible with some integer type
     [C17:6.7.2.2/4].")
   (xdoc::p
    "Because we currently only model an approximation of C types,
     our notion of compatibility is also approximate.
     Specifically, this relation overapproximates true type compatibility.
     Compatible types should always be recognized as such,
     but incompatible types may also be recognized.")
   (xdoc::p
    "Our approximate notion of type compatibility
     is established by the following cases:")
   (xdoc::ul
    (xdoc::li
     "If either type is unknown, the types are compatible.")
    (xdoc::li
     "Structure types are compatible if they share the same tag;
      For now we do not consider members [6.2.7/1].")
    (xdoc::li
     "Due to their approximate representations,
      all union types are considered compatible [6.2.7/1].
      The same applies to enumeration types [[C17:6.7.2.2/4]]
      and function types [C17:6.7.6.3/15].")
    (xdoc::li
     "Pointer types are compatible if they are derived from compatible types;
      we do not currently consider whether the types are qualified
      [C17:6.7.6.1/2].")
    (xdoc::li
     "Array types are considered compatible
      if their element types are compatible;
      their size is not currently considered [C17:6.7.6.2/6].")
    (xdoc::li
     "Enumeration types are considered compatible
      with <i>all</i> integer types.
      This is an approximation because the standard says each enumeration type
      must be compatible with <i>some</i> integer type.
      However, the particular type is implementation-defined,
      may vary for different enumeration types [C17:6.7.2.2/4].")
    (xdoc::li
     "For any other case, the types are compatible only if they are equal."))
   (xdoc::p
    "Eventually, we shall refine the notion of compatibility,
     alongside our representation of types,
     in order to reflect true type compatibility.
     This may require an additional argument
     representing the implementation environment
     so that we may establish <i>which</i> integer type
     is to be considered compatible with @('enum') types.")
   (xdoc::p
    "True type compatibility is an equivalence relation,
     but our approximate notion of compatibility is not.
     That is because @('type-compatiblep') is not transitive.
     For instance,
     @(':void') is compatible with @(':unknown'),
     as is @(':bool'),
     but @(':void') is <i>not</i> compatible with @(':bool')."))
  (or (type-case y :unknown)
      (type-case
        x
        :unknown t
        :array (type-case
                 y
                 :array (type-compatiblep x.of y.of)
                 :otherwise nil)
        :pointer (type-case
                   y
                   :pointer (type-compatiblep x.to y.to)
                   :otherwise nil)
        :otherwise (or (equal (type-fix x) (type-fix y))
                       (and (type-integerp x) (type-case y :enum))
                       (and (type-case x :enum) (type-integerp y)))))
  :measure (type-count x)
  :hooks (:fix)

  ///

  (defrule type-compatiblep-reflexive
    (type-compatiblep x x)
    :induct t)

  (defrule type-compatiblep-symmetric
    (equal (type-compatiblep y x)
           (type-compatiblep x y))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-composite ((x typep) (y typep))
  :guard (type-compatiblep x y)
  :returns (composite typep)
  :short "Construct a composite @(see type) [C17:6.2.7/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our current approximate type system, the composite type is
     @('x') if @('y') is unknown,
     @('y') if @('x') is unknown,
     and an arbitrary choice between the two if neither are derived types.
     For derived types, this is applied recursively."))
  (type-case
    x
    :array (type-case
             y
             :array (make-type-array :of (type-composite x.of y.of))
             :unknown (type-fix x)
             :otherwise (prog2$ (impossible) (irr-type)))
    :pointer (type-case
               y
               :pointer (make-type-pointer :to (type-composite x.to y.to))
               :unknown (type-fix x)
               :otherwise (prog2$ (impossible) (irr-type)))
    :unknown (type-fix y)
    :otherwise (type-fix x))
  :measure (type-count x)
  :guard-hints (("Goal" :in-theory (enable type-compatiblep)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule type-compatiblep-of-arg1-and-type-composite
    (implies (type-compatiblep x y)
             (type-compatiblep x (type-composite x y)))
    :induct t
    :enable type-compatiblep)

  (defrule type-compatiblep-of-arg2-and-type-composite
    (implies (type-compatiblep x y)
             (type-compatiblep y (type-composite x y)))
    :induct t
    :enable type-compatiblep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap ident-type-map
  :short "Fixtype of omaps from identifiers to types."
  :key-type ident
  :val-type type
  :pred ident-type-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-pointers-to ((pointers typequal/attribspec-list-listp)
                          (type typep))
  :returns (new-type typep)
  :short "Derive a pointer type for each type qualifier and attribute specifier
          list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This takes the list of lists of type qualifiers and attribute specifiers
     from a declarator or abstract declarator,
     and creates the corresponding (possibly pointer) type.")
   (xdoc::p
    "Since our approximate type system does not incorporate type qualifiers,
     each cons of the @('pointers') list
     is used only to derive a pointer from the type."))
  (if (endp pointers)
      (type-fix type)
    (make-type-pointer :to (make-pointers-to (rest pointers) type)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-formalp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is supported in our formal semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "By `supported' we mean that the type corresponds to
     one in the fixtype @(tsee c::type) of types in our formal semantics.
     This consists of @('void'),
     plain @('char'),
     the standard integer types except @('_Bool'),
     pointer types,
     and struct types with tags.")
   (xdoc::p
    "The array types are not supported because
     they are too coarse compared to their @(tsee c::type) counterparts:
     they do not include size information.
     Struct types without tag are not supported,
     because they always have a tag in @(tsee c::type).")
   (xdoc::p
    "This predicate can be regarded as an extension of
     the collection of @('-formalp') predicates in @(see formalized-subset)."))
  (or (and (member-eq (type-kind type)
                      '(:void
                        :char :uchar :schar
                        :ushort :sshort
                        :uint :sint
                        :ulong :slong
                        :ullong :sllong))
           t)
      (and (type-case type :pointer)
           (type-formalp (type-pointer->to type)))
      (and (type-case type :struct)
           (type-struct->tag? type)
           (ident-formalp (type-struct->tag? type))))
  :measure (type-count type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-option-formalp ((type? type-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional type is supported in our formal semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case if the type is absent or supported."))
  (type-option-case type?
                    :some (type-formalp type?.val)
                    :none t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-set-formalp ((types type-setp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a set
          are supported in our formal semantics of C."
  (or (set::emptyp (type-set-fix types))
      (and (type-formalp (set::head types))
           (type-set-formalp (set::tail types))))
  :prepwork ((local (in-theory (enable emptyp-of-type-set-fix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-option-set-formalp ((type?s type-option-setp))
  :returns (yes/no booleanp)
  :short "Check if all the optional types in a set
          are supported in our formal semantics of C."
  (or (set::emptyp (type-option-set-fix type?s))
      (and (type-option-formalp (set::head type?s))
           (type-option-set-formalp (set::tail type?s))))
  :prepwork ((local (in-theory (enable emptyp-of-type-option-set-fix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type ((type typep))
  :returns (mv erp (type1 c::typep))
  :short "Map a type in @(tsee type) to a type in the language definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function can be regarded as an extension of
     the collection of @('ldm-') functions
     in @(see mapping-to-language-definition).
     The supported types are the same as discussed in @(tsee type-formalp)."))
  (b* (((reterr) (c::type-void)))
    (type-case
     type
     :void (retok (c::type-void))
     :char (retok (c::type-char))
     :schar (retok (c::type-schar))
     :uchar (retok (c::type-uchar))
     :sshort (retok (c::type-sshort))
     :ushort (retok (c::type-ushort))
     :sint (retok (c::type-sint))
     :uint (retok (c::type-uint))
     :slong (retok (c::type-slong))
     :ulong (retok (c::type-ulong))
     :sllong (retok (c::type-sllong))
     :ullong (retok (c::type-ullong))
     :float (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :double (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :ldouble (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :floatc (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :doublec (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :ldoublec (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :bool (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :struct (if type.tag?
                 (b* (((erp tag) (ldm-ident type.tag?)))
                   (retok (c::type-struct tag)))
               (reterr (msg "Type ~x0 not supported." (type-fix type))))
     :union (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :enum (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :array (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :pointer (b* (((erp refd-type) (ldm-type type.to)))
                (retok (c::make-type-pointer :to refd-type)))
     :function (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :unknown (reterr (msg "Type ~x0 not supported." (type-fix type)))))
  :measure (type-count type)
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret ldm-type-when-type-formalp
    (not erp)
    :hyp (type-formalp type)
    :hints (("Goal" :induct t
                    :in-theory (enable type-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-option ((type? type-optionp))
  :returns (mv erp (type?1 c::type-optionp))
  :short "Map an optional type in @(tsee type-option)
          to an optional type in the language definition."
  (type-option-case type?
                    :some (ldm-type type?.val)
                    :none (mv nil nil))
  :hooks (:fix)

  ///

  (defret ldm-type-option-when-type-option-formalp
    (not erp)
    :hyp (type-option-formalp type?)
    :hints (("Goal" :in-theory (enable type-option-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-set ((types type-setp))
  :returns (mv erp (types1 c::type-setp))
  :short "Map a set of types in @(tsee type-set)
          to a set of types in the language definition."
  (b* (((when (set::emptyp (type-set-fix types))) (mv nil nil))
       ((mv erp type) (ldm-type (set::head types)))
       ((when erp) (mv erp nil))
       ((mv erp types) (ldm-type-set (set::tail types)))
       ((when erp) (mv erp nil)))
    (mv nil (set::insert type types)))
  :prepwork ((local (in-theory (enable emptyp-of-type-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret ldm-type-set-when-type-set-formalp
    (not erp)
    :hyp (type-set-formalp types)
    :hints (("Goal" :induct t :in-theory (enable type-set-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-type-option-set ((type?s type-option-setp))
  :returns (mv erp (type?s1 c::type-option-setp))
  :short "Map a set of optional types in @(tsee type-option-set)
          to a set of optional types in the language definition."
  (b* (((when (set::emptyp (type-option-set-fix type?s))) (mv nil nil))
       ((mv erp type?) (ldm-type-option (set::head type?s)))
       ((when erp) (mv erp nil))
       ((mv erp type?s) (ldm-type-option-set (set::tail type?s)))
       ((when erp) (mv erp nil)))
    (mv nil (set::insert type? type?s)))
  :prepwork ((local (in-theory (enable emptyp-of-type-option-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret ldm-type-option-set-when-type-option-set-formalp
    (not erp)
    :hyp (type-option-set-formalp type?s)
    :hints (("Goal" :induct t :in-theory (enable type-option-set-formalp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-to-value-kind ((type typep))
  :returns (kind keywordp
                 :hints (("Goal" :in-theory (enable type-kind))))
  :short "Map a type to the corresponding @(tsee c::value) kind."
  :long
  (xdoc::topstring
   (xdoc::p
    "We throw a hard error unless the type has
     a corresponding kind of values in the formal semantics.
     This function is always called when this condition is satisfied;
     the hard error signals an implementation error."))
  (if (type-formalp type)
      (type-kind type)
    (prog2$ (raise "Internal error: type ~x0 has no corresponding value kind.")
            :irrelevant))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-type ((ctype c::typep))
  :returns (type typep)
  :short "Map a type in the language formalization to a type in @(tsee type)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee ldm-type),
     hence the @('i') for `inverse'.")
   (xdoc::p
    "Since our current type system is approximate (see @(tsee type)),
     this mapping abstracts away information in some cases."))
  (c::type-case
   ctype
   :void (type-void)
   :char (type-char)
   :schar (type-schar)
   :uchar (type-uchar)
   :sshort (type-sshort)
   :ushort (type-ushort)
   :sint (type-sint)
   :uint (type-uint)
   :slong (type-slong)
   :ulong (type-ulong)
   :sllong (type-sllong)
   :ullong (type-ullong)
   :struct (type-struct (ident (c::ident->name ctype.tag)))
   :pointer (make-type-pointer :to (ildm-type ctype.to))
   :array (make-type-array :of (ildm-type ctype.of)))
  :measure (c::type-count ctype)
  :verify-guards :after-returns
  :hooks (:fix))
