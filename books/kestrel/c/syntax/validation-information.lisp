; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax")
(include-book "implementation-environments")

(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-information
  :parents (syntax-for-tools)
  :short "Information calculated and used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validator calculates and uses information, such as types,
     and annotates the abstract syntax with some of this information.
     Here we introduce fixtypes for this information,
     and operations on those fixtypes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type
  :short "Fixtype of C types [C:6.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we do not model all the C types in detail,
     but only an approximate version of them,
     which still lets us perform some validation.
     We plan to refine the types, and the rest of the validator,
     to cover exactly all the validity checks prescribed by [C]
     (as well as applicable GCC extensions).")
   (xdoc::p
    "We capture the following types:")
   (xdoc::ul
    (xdoc::li
     "The @('void') type [C:6.2.5/19].")
    (xdoc::li
     "The plain @('char') type [C:6.2.5/3].")
    (xdoc::li
     "The five standard signed integer types [C:6.2.5/4]
      and the corresponding unsigned integer types [C:6.2.5/6].")
    (xdoc::li
     "The three real floating point types [C:6.2.5/10].")
    (xdoc::li
     "The three complex types [C:6.2.5/11].
      These are a conditional feature,
      but they must be included in this fixtype
      because this fixtype consists of all the possible types.")
    (xdoc::li
     "The @('_Bool') type [C:6.2.5/2].")
    (xdoc::li
     "A collective type for all structure types [C:6.2.5/20].
      This is an approximation,
      because there are different structure types.")
    (xdoc::li
     "A collective type for all union types [C:6.2.5/20].
      This is an approximation,
      because there are different union types.")
    (xdoc::li
     "A collective type for all enumeration types [C:6.2.5/20].
      This is an approximation,
      because there are different enumeration types.")
    (xdoc::li
     "A collective type for all array types [C:6.2.5/20].
      This is an approximation,
      because there are different array types.")
    (xdoc::li
     "A collective type for all pointer types [C:6.2.5/20].
      This is an approximation,
      because there are different pointer types.")
    (xdoc::li
     "A collective type for all function types [C:6.2.5/20].
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
     currently we do not capture atomic types [C:6.2.5/20],
     which we approximate as the underlying (argument) type.
     We also do not capture @('typedef') names,
     which we approximate as unknown types.
     Furthermore, we do not capture qualified types [C:6.2.5/26]."))
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
  (:struct ())
  (:union ())
  (:enum ())
  (:array ())
  (:pointer ())
  (:function ())
  (:unknown ())
  :pred typep)

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
  :short "Check if a type is a standard signed integer type [C:6.2.5/4]."
  (and (member-eq (type-kind type) '(:schar :sshort :sint :slong :sllong))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-signed-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a signed integer type [C:6.2.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not model any extended signed integer types,
     so the signed integer types coincide with
     the standard signed integer types."))
  (type-standard-signed-integerp type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard unsigned integer type [C:6.2.5/6]."
  (and (member-eq (type-kind type) '(:bool :uchar :ushort :uint :ulong :ullong))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an unsigned integer type [C:6.2.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not model any extended unsigned integer types,
     so the unsigned integer types coincide with
     the standard unsigned integer types."))
  (type-standard-unsigned-integerp type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard integer type [C:6.2.5/7]."
  (or (type-standard-signed-integerp type)
      (type-standard-unsigned-integerp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-real-floatingp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real floating type [C:6.2.5/10]."
  (and (member-eq (type-kind type) '(:float :double :ldouble))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-complexp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a complex type [C:6.2.5/11]."
  (and (member-eq (type-kind type) '(:floatc :doublec :ldoublec))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-floatingp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a floating type [C:6.2.5/11]."
  (or (type-real-floatingp type)
      (type-complexp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-basicp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a basic type [C:6.2.5/14]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type)
      (type-floatingp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-characterp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a character type [C:6.2.5/15]."
  (and (member-eq (type-kind type) '(:char :schar :uchar))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an integer type [C:6.2.5/17]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type)
      (type-case type :enum))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-realp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real type [C:6.2.5/17]."
  (or (type-integerp type)
      (type-real-floatingp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an arithmetic type [C:6.2.5/18]."
  (or (type-integerp type)
      (type-floatingp type))
  :hooks (:fix)

  ///

  (defrule type-arithmeticp-when-type-integerp
    (implies (type-integerp type)
             (type-arithmeticp type)))

  (defrule type-arithmeticp-when-bool
    (implies (type-case type :bool)
             (type-arithmeticp type))
    :enable (type-integerp
             type-unsigned-integerp
             type-standard-unsigned-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalarp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a scalar type [C:6.2.5/21]."
  (or (type-arithmeticp type)
      (type-case type :pointer))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-aggregatep ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an aggregate type [C:6.2.5/21]."
  (or (type-case type :array)
      (type-case type :struct))
  :hooks (:fix)

  ///

  (defrule type-aggregatep-when-array
    (implies (type-case type :array)
             (type-aggregatep type)))

  (defrule type-aggregatep-when-struct
    (implies (type-case type :struct)
             (type-aggregatep type))))

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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-apconvert ((type typep))
  :returns (new-type typep)
  :short "Convert array types to pointer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the conversion in [C:6.3.2.1/3].
     It leaves non-array types unchanged.")
   (xdoc::p
    "In our currently approximate type system,
     there is just one type for arrays and one type for pointers."))
  (if (type-case type :array)
      (type-pointer)
    (type-fix type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-fpconvert ((type typep))
  :returns (new-type typep)
  :short "Convert function types to pointer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the conversion in [C:6.3.2.1/4].
     It leaves non-function types unchanged.")
   (xdoc::p
    "In our currently approximate type system,
     there is just one type for functions and one type for pointers."))
  (if (type-case type :function)
      (type-pointer)
    (type-fix type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-promote ((type typep) (ienv ienvp))
  :guard (type-arithmeticp type)
  :returns (new-type typep)
  :short "Perform integer promotions on an arithmetic type [C:6.3.1.1/2]."
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
     as mentioned in footnote 131 of [C:6.7.2.2/4].
     Thus, for now we promote the (one) enumerated type to unknown."))
  (type-case
   type
   :bool (type-sint)
   :char (if (<= (char-max ienv) (sint-max ienv))
             (type-sint)
           (type-uint))
   :schar (type-sint)
   :uchar (if (<= (uchar-max) (sint-max ienv))
              (type-sint)
            (type-uint))
   :sshort (type-sint)
   :ushort (if (<= (ushort-max ienv) (sint-max ienv))
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
          according to the usual arithmetic conversions [C:6.3.1.8]."
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
          according to the usual arithmetic conversions [C:6.3.1.8]."
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
          according to the usual arithmetic conversions [C:6.3.1.8]."
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
           (if (<= (ulong-max ienv) (sllong-max ienv))
               (type-sllong)
             (type-ullong)))
          (t (type-ulong))))
   ((type-case type2 :uint)
    (cond ((type-case type1 :sllong)
           (if (<= (uint-max ienv) (sllong-max ienv))
               (type-sllong)
             (type-ullong)))
          ((type-case type1 :slong)
           (if (<= (uint-max ienv) (slong-max ienv))
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
          [C:6.3.1.8]."
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
     note that [C:6.3.1.8] talks about a corresponding real type,
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
     Then we apply the remaining rules, for integer types, in [C:6.3.1.8],
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum linkage
  :short "Fixtype of linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three kinds of linkages: external, internal, and none
     [C:6.2.2/1]."))
  (:external ())
  (:internal ())
  (:none ())
  :pred linkagep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-linkage
  :short "An irrelevant linkage."
  :type linkagep
  :body (linkage-none))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption linkage-option
  linkage
  :short "Fixtype of optional linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Linkages are defined in @(tsee linkage)."))
  :pred linkage-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lifetime
  :short "Fixtype of lifetimes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This represents a storage duration [C:6.2.4],
     but only three kinds, excluding the allocated kind.
     We use the term `liftetime' because it is just one word,
     and also to avoid implying that there are only three storage durations,
     when there are in fact four.
     Since a storage duration defines the kind of lifetime of an object,
     one could argue that there are four kinds of lifetimes too;
     however, for practicality, we need a fixtype for
     only these three kinds of lifetimes (or storage durations),
     and so we use the term `lifetime'.
     This must be thought as the possible kinds of lifetime of declared objects;
     allocated objects are not declared, but just created via library calls."))
  (:static ())
  (:thread ())
  (:auto ())
  :pred lifetimep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lifetime
  :short "An irrelevant lifetime."
  :type lifetimep
  :body (lifetime-auto))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption lifetime-option
  lifetime
  :short "Fixtype of optional lifetimes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lifetimes are defined in @(tsee lifetime)."))
  :pred lifetime-optionp)
