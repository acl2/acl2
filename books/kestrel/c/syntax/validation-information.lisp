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
(include-book "unambiguity")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))

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
    "The @(see validator) calculates and uses information, such as types,
     and annotates the abstract syntax with some of this information.
     Here we introduce fixtypes for this information,
     and operations on those fixtypes.")
   (xdoc::p
    "We also introduce predicates over the abstract syntax,
     to check that the annotations from the validator are present.
     This is not the same as saying that the constructs are validated;
     the predicates just say that information of the right type is present."))
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
     "A collective type for all structure types [C17:6.2.5/20].
      This is an approximation,
      because there are different structure types.")
    (xdoc::li
     "A collective type for all union types [C17:6.2.5/20].
      This is an approximation,
      because there are different union types.")
    (xdoc::li
     "A collective type for all enumeration types [C17:6.2.5/20].
      This is an approximation,
      because there are different enumeration types.")
    (xdoc::li
     "A collective type for all array types [C17:6.2.5/20].
      This is an approximation,
      because there are different array types.")
    (xdoc::li
     "A collective type for all pointer types [C17:6.2.5/20].
      This is an approximation,
      because there are different pointer types.")
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
     which we approximate as unknown types.
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
  :short "Check if a type is a standard signed integer type [C17:6.2.5/4]."
  (and (member-eq (type-kind type) '(:schar :sshort :sint :slong :sllong))
       t)
  :hooks (:fix))

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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-unsigned-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard unsigned integer type [C17:6.2.5/6]."
  (and (member-eq (type-kind type) '(:bool :uchar :ushort :uint :ulong :ullong))
       t)
  :hooks (:fix))

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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard integer type [C17:6.2.5/7]."
  (or (type-standard-signed-integerp type)
      (type-standard-unsigned-integerp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-real-floatingp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real floating type [C17:6.2.5/10]."
  (and (member-eq (type-kind type) '(:float :double :ldouble))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-complexp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a complex type [C17:6.2.5/11]."
  (and (member-eq (type-kind type) '(:floatc :doublec :ldoublec))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-floatingp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a floating type [C17:6.2.5/11]."
  (or (type-real-floatingp type)
      (type-complexp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-basicp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a basic type [C17:6.2.5/14]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type)
      (type-floatingp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-characterp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a character type [C17:6.2.5/15]."
  (and (member-eq (type-kind type) '(:char :schar :uchar))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an integer type [C17:6.2.5/17]."
  (or (type-case type :char)
      (type-signed-integerp type)
      (type-unsigned-integerp type)
      (type-case type :enum))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-realp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a real type [C17:6.2.5/17]."
  (or (type-integerp type)
      (type-real-floatingp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmeticp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an arithmetic type [C17:6.2.5/18]."
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
  :short "Check if a type is a scalar type [C17:6.2.5/21]."
  (or (type-arithmeticp type)
      (type-case type :pointer))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-aggregatep ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is an aggregate type [C17:6.2.5/21]."
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
    "This performs the conversion in [C17:6.3.2.1/3].
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
    "This performs the conversion in [C17:6.3.2.1/4].
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
    "Informally, two types are compatible if they represent \"the same\"
     type.")
   (xdoc::p
    "Because we currently only model an approximation of C types,
     our notion of compatibility is also approximate.
     Specifically, this relation overapproximates true type compatibility.
     Compatible types should always be recognized as such,
     but incompatible types may also be recognized.")
   (xdoc::p
    "In particular:"
    (xdoc::ul
     (xdoc::li
      "All structure types are currently considered compatible,
       due to their approximate representations.
       The same applies to
       union, enumeration, array, pointer, and function types.")
     (xdoc::li "Type qualifiers are ignored.")
     (xdoc::li
      "All types are compatible with the abstract @(':unknown') type.")
     (xdoc::li
      "Enumeration types are compatible with
       <i>all</i> integer types (not just one particular type).")))
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
  (b* ((x (type-fix x))
       (y (type-fix y)))
    (or (equal x y)
        (type-case x :unknown)
        (type-case y :unknown)
        (and (type-integerp x) (type-case y :enum))
        (and (type-case x :enum) (type-integerp y))))
  :hooks (:fix)

  ///

  (defrule type-compatiblep-reflexive
    (type-compatiblep x x)
    :enable type-compatiblep)

  (defrule type-compatiblep-symmetric
    (equal (type-compatiblep y x)
           (type-compatiblep x y))
    :enable type-compatiblep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-null-pointer-constp ((expr exprp) (type typep))
  (declare (ignore expr))
  :returns (yes/no booleanp)
  :short "Check whether an expression of a given type is potentially a null
          pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Due to the approximate representation of types and our lack of constant
     expression evaluation,
     this recognizer is highly overappoximating.
     It will recognize any pointer or integer type."))
  (or (type-case type :pointer)
      (type-integerp type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-expr-null-pointer-constp ((const-expr const-exprp) (type typep))
  :returns (yes/no booleanp)
  :short "Check whether a constant expression of a given type is potentially a
          null pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee expr-null-pointer-constp)."))
  (b* (((const-expr const-expr) const-expr))
    (expr-null-pointer-constp const-expr.expr type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum linkage
  :short "Fixtype of linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three kinds of linkages: external, internal, and none
     [C17:6.2.2/1]."))
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
    "This represents a storage duration [C17:6.2.4],
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum valid-defstatus
  :short "Fixtype of definition statuses for validation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to objects and functions, which may be
     undefined, defined, or tentatively defined [C17:6.7/5] [C17:6.9.2],
     with the latter actually only applying to objects, not functions."))
  (:undefined ())
  (:tentative ())
  (:defined ())
  :pred valid-defstatusp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum valid-ord-info
  :short "Fixtype of validation information about ordinary identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ordinary identifiers [C17:6.2.3/1] denote
     objects, functions, enumeration constants, and @('typedef') names;
     Ordinary identifiers form their own name space.
     The other entities denoted by identifiers [C17:6.2.1/1]
     are in other name spaces, disjoint from the one of ordinary identifiers.")
   (xdoc::p
    "This fixtype formalizes the information about ordinary identifiers
     tracked by our current validator.
     Since our model of types includes both object and function types,
     the information for both objects and functions includes (different) types;
     that information also includes the linkage [C17:6.2.2],
     as well as definition status (see @(tsee valid-defstatus)).
     For enumeration constants names,
     for now we only track that they are enumeration constants.
     For @('typedef') names, we track the type corresponding to its
     definition.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)
            (defstatus valid-defstatus)))
  (:enumconst ())
  (:typedef ((def type)))
  :pred valid-ord-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-ord-info-option
  valid-ord-info
  :short "Fixtype of
          optional validation information about ordinary identifiers."
  :pred valid-ord-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist valid-ord-scope
  :short "Fixtype of validation scopes of ordinary identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     In each scope, for each name space,
     each identifier must have one meaning (if any) [C17:6.2.1/2].
     Thus, we use an alist from identifiers
     to the validation information about ordinary identifiers,
     to track each scope in the name space of ordinary identifiers."))
  :key-type ident
  :val-type valid-ord-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred valid-ord-scopep
  :prepwork ((set-induction-depth-limit 1))
  ///

  (defrule valid-ord-infop-of-cdr-assoc-when-valid-ord-scopep
    (implies (and (valid-ord-scopep scope)
                  (assoc-equal ident scope))
             (valid-ord-infop (cdr (assoc-equal ident scope))))
    :induct t
    :enable (valid-ord-scopep assoc-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-scope
  :short "Fixtype of validation scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     This fixtype contains all the information about a scope,
     which currently only considers the name space of ordinary identifiers.
     We will extend this fixtype to contain additional information,
     particularly about tag of structure, union, and enumeration types."))
  ((ord valid-ord-scope))
  :pred valid-scopep)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist valid-scope-list
  :short "Fixtype of lists of validation scopes."
  :elt-type valid-scope
  :true-listp t
  :elementp-of-nil nil
  :pred valid-scope-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-table
  :short "Fixtype of validation tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scopes are treated in a stack-like manner [C17:6.2.1].
     Thus, we define a validation table as
     containing a list (i.e. stack) of scopes.
     The stack grows from right to left:
     the leftmost scope is the top, and the rightmost scope is the bottom;
     in other words, in the nesting of scopes in the stack,
     the leftmost scope is the innermost,
     and the rightmost scope is the outermost
     (i.e. the file scope [C17:6.2.1/4].)")
   (xdoc::p
    "We wrap the list of scopes into a @(tsee fty::defprod)
     for abstraction and extensibility."))
  ((scopes valid-scope-list))
  :pred valid-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-valid-table
  :short "An irrelevant validation table."
  :type valid-tablep
  :body (valid-table nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod iconst-info
  :short "Fixtype of validation information for integer constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to integer constants,
     i.e. the @(tsee iconst) constructs.
     The information consists of the type of the constant
     (which for now we do not constrain to be an integer type),
     and the numeric value of the constant, as an ACL2 natural number."))
  ((type type)
   (value nat))
  :pred iconst-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-iconst-info
  :short "An irrelevant validation information for integer constants."
  :type iconst-infop
  :body (make-iconst-info :type (irr-type)
                          :value 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-iconst-info (x)
  :returns (info iconst-infop)
  :short "Coerce a valud to @(tsee iconst-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (iconst-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy ICONST-INFOP." x)
            (irr-iconst-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var-info
  :short "Fixtype of validation information for variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that the validator adds to variables,
     i.e. identifiers used as expressions,
     i.e. the @(':ident') case of @(tsee expr).
     The information for a variable consists of
     the type and linkage of the object denoted by the variable."))
  ((type type)
   (linkage linkage))
  :pred var-infop)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-var-info
  :short "An irrelevant validation information for variables."
  :type var-infop
  :body (make-var-info :type (irr-type)
                       :linkage (irr-linkage)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-var-info (x)
  :returns (info var-infop)
  :short "Coerce a value to @(tsee var-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (var-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy VAR-INFOP." x)
            (irr-var-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod unary-info
  :short "Fixtype of validation information for unary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to unary expressions,
     i.e. the @(':unary') case of @(tsee expr).
     The information for a unary expression consists of its type."))
  ((type type))
  :pred unary-infop)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-unary-info
  :short "An irrelevant validation information for unary expressions."
  :type unary-infop
  :body (make-unary-info :type (irr-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-unary-info (x)
  :returns (info unary-infop)
  :short "Coerce a value to @(tsee unary-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (unary-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy UNARY-INFOP." x)
            (irr-unary-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod binary-info
  :short "Fixtype of validation information for binary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to binary expressions,
     i.e. the @(':binary') case of @(tsee expr).
     The information for a binary expression consists of its type."))
  ((type type))
  :pred binary-infop)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-binary-info
  :short "An irrelevant validation information for binary expressions."
  :type binary-infop
  :body (make-binary-info :type (irr-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-binary-info (x)
  :returns (info binary-infop)
  :short "Coerce a value to @(tsee binary-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (binary-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy BINARY-INFOP." x)
            (irr-binary-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit-info
  :short "Fixtype of validation information for translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation units.
     The information consists of
     the final validation table for the translation unit.
     We wrap it into a product fixtype for easier future extensibility."))
  ((table valid-table))
  :pred transunit-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit-info
  :short "An irrelevant validation information for translation units."
  :type transunit-infop
  :body (make-transunit-info :table (irr-valid-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-transunit-info (x)
  :returns (info transunit-infop)
  :short "Coerce a value to @(tsee transunit-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (transunit-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy TRANSUNIT-INFOP." x)
            (irr-transunit-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce annop
  :short "Definition of the predicates that check whether
          the abstract syntax is annotated with validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
   (xdoc::p
    "The @(':default') value is @('t'),
     meaning that there are no constraints by default.")
   (xdoc::p
    "The @(':combine') operator is @(tsee and),
     because we need to check all the constructs, recursively.")
   (xdoc::p
    "We override the predicate for
     the constructs for which the validator adds information.")
   (xdoc::p
    "Since for now the validator accepts GCC attribute and other extensions
     without actually checking them and their constituents,
     we also have the annotation predicates accept those constructs,
     by overriding those cases to return @('t').")
   (xdoc::p
    "The validator operates on unambiguous abstract syntax,
     which satisfies the @(see unambiguity) predicates.
     Ideally, the annotation predicates should use
     the unambiguity predicates as guards,
     but @(tsee fty::deffold-reduce) does not support that feature yet.
     Thus, for now we add run-time checks, in the form of @(tsee raise),
     for the cases in which the unambiguity predicates do not hold;
     note that @(tsee raise) is logically @('nil'),
     so the annotation predicates are false on ambiguous constructs."))
  :types (ident
          ident-list
          ident-option
          iconst
          iconst-option
          const
          const-option
          attrib-name
          exprs/decls/stmts
          fundef
          extdecl
          extdecl-list
          transunit
          filepath-transunit-map
          transunit-ensemble)
  :result booleanp
  :default t
  :combine and
  :override
  ((iconst (iconst-infop (iconst->info iconst)))
   (expr :ident (var-infop expr.info))
   (expr :unary (unary-infop expr.info))
   (expr :sizeof-ambig (raise "Internal error: ambiguous ~x0."
                              (expr-fix expr)))
   (expr :binary (binary-infop expr.info))
   (expr :cast/call-ambig (raise "Internal error: ambiguous ~x0."
                                 (expr-fix expr)))
   (expr :cast/mul-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :cast/add-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :cast/sub-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :cast/and-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (type-spec :typeof-ambig (raise "Internal error: ambiguous ~x0."
                                   (type-spec-fix type-spec)))
   (align-spec :alignas-ambig (raise "Internal error: ambiguous ~x0."
                                     (align-spec-fix align-spec)))
   (dirabsdeclor :dummy-base (raise "Internal error: ~
                                       dummy base case of ~
                                       direct abstract declarator."))
   (attrib t)
   (attrib-spec t)
   (asm-output t)
   (asm-input t)
   (asm-stmt t)
   (stmt :for-ambig (raise "Internal error: ambiguous ~x0."
                           (stmt-fix stmt)))
   (block-item :ambig (raise "Internal error: ambiguous ~x0."
                             (block-item-fix block-item)))
   (amb-expr/tyname (raise "Internal error: ambiguous ~x0."
                           (amb-expr/tyname-fix amb-expr/tyname)))
   (amb-declor/absdeclor (raise "Internal error: ambiguous ~x0."
                                (amb-declor/absdeclor-fix
                                 amb-declor/absdeclor)))
   (amb-decl/stmt (raise "Internal error: ambiguous ~x0."
                         (amb-decl/stmt-fix amb-decl/stmt)))
   (transunit (and (extdecl-list-annop (transunit->decls transunit))
                   (transunit-infop (transunit->info transunit))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled transunit-annop-of-head-when-filepath-transunit-map-annop
  (implies (and (filepath-transunit-mapp map)
                (filepath-transunit-map-annop map)
                (not (omap::emptyp map)))
           (transunit-annop (mv-nth 1 (omap::head map))))
  :induct t
  :enable filepath-transunit-map-annop)

(add-to-ruleset abstract-syntax-annop-rules
                '(transunit-annop-of-head-when-filepath-transunit-map-annop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled filepath-transunit-map-annop-of-tail
  (implies (and (filepath-transunit-mapp map)
                (filepath-transunit-map-annop map))
           (filepath-transunit-map-annop (omap::tail map)))
  :induct t
  :enable filepath-transunit-map-annop)

(add-to-ruleset abstract-syntax-annop-rules
                '(filepath-transunit-map-annop-of-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-type ((expr exprp))
  :guard (expr-unambp expr)
  :returns (type typep)
  :short "Type of an expression, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type is calculated from
     the validation information present in the expression,
     without performing any type calculation
     of the kind performed by the validator
     (e.g. this function does not attempt to calculate
     the type of a binary expression based on
     the operator and the types of the operands.
     If there is not enough information,
     the unknown type is returned."))
  (expr-case
   expr
   :ident (var-info->type (coerce-var-info expr.info))
   :const (if (const-case expr.const :int)
              (iconst-info->type
               (coerce-iconst-info
                (iconst->info
                 (const-int->unwrap expr.const))))
            (type-unknown))
   :string (type-unknown)
   :paren (expr-type expr.inner)
   :gensel (type-unknown)
   :arrsub (type-unknown)
   :funcall (type-unknown)
   :member (type-unknown)
   :memberp (type-unknown)
   :complit (type-unknown)
   :unary (unary-info->type (coerce-unary-info expr.info))
   :sizeof (type-unknown)
   :alignof (type-unknown)
   :cast (type-unknown)
   :binary (binary-info->type (coerce-binary-info expr.info))
   :cond (type-unknown)
   :comma (expr-type expr.next)
   :stmt (type-unknown)
   :tycompat (type-unknown)
   :offsetof (type-unknown)
   :va-arg (type-unknown)
   :extension (expr-type expr.expr)
   :otherwise (prog2$ (impossible) (type-unknown)))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))
