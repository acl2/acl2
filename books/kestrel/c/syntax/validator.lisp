; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")
(include-book "implementation-environments")
(include-book "unambiguity")

(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "std/alists/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator
  :parents (syntax-for-tools)
  :short "Validator of the C abstract syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides syntactic validity,
     C code must satisfy a number of additional constraints
     in order to be compiled.
     These constraints form the static semantics of C.
     C compilers check that the code satisfies these constraints
     prior to translating it.")
   (xdoc::p
    "Here we provide a validator of C code,
     whose purpose is to check those constraints,
     i.e. to check whether the C code is valid and compilable.")
   (xdoc::p
    "We start with an approximate validator
     that should accept all valid C code
     but also some invalid C code (due to the approximation).
     Even in its approximate form,
     this may be useful to perform some validation,
     and to calculate information (approximate types)
     that may be useful for manipulating the abstract syntax
     (e.g. for C-to-C transformations).")
   (xdoc::p
    "In a sense, the validator extends the @(see disambiguator),
     which performs an even more approximate validation,
     just enough to disambiguate the abstract syntax.
     Thus, there are structural similarities between
     the validator and the disambiguator.")
   (xdoc::p
    "Similarly to a compiler, the validator makes use of a symbol table,
     which tracks information about the symbols (identifiers) in the code.
     These symbol tables, called `validation tables', are, in some sense,
     an extension of the disambiguation tables used by the disambiguator.")
   (xdoc::p
    "We use "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " to handle errors in the validator.")
   (xdoc::p
    "The ACL2 functions that validate the various parts of the abstract syntax
     follow the @('valid-<fixtype>') naming scheme,
     where @('<fixtype>') is the name of
     the fixtype of the abstract syntax part,
     and where @('valid') is best read as an abbreviation of `validate'
     rather than as the adjective `valid'.")
   (xdoc::p
    "This validator is work in progress."))
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
     This must be though as the possible kinds of lifetime of declared objects;
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
     undefined, defined, or tentatively defined [C:6.7/5] [C:6.9.2],
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
    "Ordinary identifiers [C:6.2.3/1] denote
     objects, functions, enumeration constants, and @('typedef') names;
     Ordinary identifiers form their own name space.
     The other entities denoted by identifiers [C:6.2.1/1]
     are in other name spaces, disjoint from the one of ordinary identifiers.")
   (xdoc::p
    "This fixtype formalizes the information about ordinary identifiers
     tracked by our current validator.
     Since our model of types includes both object and function types,
     the information for both objects and functions includes (different) types;
     that information also includes the linkage [C:6.2.2],
     as well as definition status (see @(tsee valid-defstatus)).
     For enumeration constants and for @('typedef') names,
     for now we only track that they are
     enumeration constants and @('typedef') names.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)
            (defstatus valid-defstatus)))
  (:enumconst ())
  (:typedef ())
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
    "Identifiers have scopes [C:6.2.1], which the validator tracks.
     In each scope, for each name space,
     each identifier must have one meaning (if any) [C:6.2.1/2].
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
    "Identifiers have scopes [C:6.2.1], which the validator tracks.
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
    "Scopes are treated in a stack-like manner [C:6.2.1].
     Thus, we define a validation table as
     containing a list (i.e. stack) of scopes.
     The stack grows from right to left:
     the leftmost scope is the top, and the rightmost scope is the bottom;
     in other words, in the nesting of scopes in the stack,
     the leftmost scope is the innermost,
     and the rightmost scope is the outermost
     (i.e. the file scope [C:6.2.1/4].)")
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

(define valid-empty-scope ()
  :returns (scope valid-scopep)
  :short "Empty validator scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scopes always start empty, i.e. with no identifiers.
     This function returns the empty scope."))
  (make-valid-scope :ord nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-init-table ()
  :returns (table valid-tablep)
  :short "Initial validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains one empty scope (the initial file scope)."))
  (make-valid-table :scopes (list (valid-empty-scope))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-table-num-scopes ((table valid-tablep))
  :returns (num natp)
  :short "Number of scopes in a validation table."
  (len (valid-table->scopes table))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-push-scope ((table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Push a scope onto the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The newly pushed scope is always empty."))
  (b* ((scopes (valid-table->scopes table))
       (new-scopes (cons (valid-empty-scope) scopes)))
    (change-valid-table table :scopes new-scopes))
  :hooks (:fix)
  ///

  (defret valid-table-num-scopes-of-valid-push-scope
    (equal (valid-table-num-scopes new-table)
           (1+ (valid-table-num-scopes table)))
    :hints (("Goal" :in-theory (enable valid-table-num-scopes len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-pop-scope ((table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Pop a scope from the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard requires that there are is at least one scope.")
   (xdoc::p
    "The popped scope is discarded."))
  (b* (((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (valid-table-fix table))
       (scopes (valid-table->scopes table))
       (new-scopes (cdr scopes)))
    (change-valid-table table :scopes new-scopes))
  :hooks (:fix)
  ///

  (defret valid-table-num-scopes-of-valid-pop-scope
    (equal (valid-table-num-scopes new-table)
           (1- (valid-table-num-scopes table)))
    :hyp (> (valid-table-num-scopes table) 0)
    :hints (("Goal" :in-theory (enable valid-table-num-scopes len max fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-ord ((ident identp) (table valid-tablep))
  :returns (mv (info? valid-ord-info-optionp) (currentp booleanp))
  :short "Look up an ordinary identifier in a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the visibility and hiding rules [C:6.2.1/2],
     we look up the identifier starting from the innermost scope.
     We stop as soon as we find a match.
     We return @('nil') if we reach the outermost scope
     without finding a match.")
   (xdoc::p
    "We also return a flag saying whether the identifier was found
     in the current (i.e. innermost) scope or in some other scope.
     We initialize this flag to @('t'),
     and we set to @('nil') when we perform the recursive call.
     The flag is irrelevant if the first result is @('nil'),
     but in this case the returned flag is @('nil') too."))
  (valid-lookup-ord-loop ident (valid-table->scopes table) t)
  :hooks (:fix)

  :prepwork
  ((define valid-lookup-ord-loop ((ident identp)
                                  (scopes valid-scope-listp)
                                  (currentp booleanp))
     :returns (mv (info? valid-ord-info-optionp) (updated-currentp booleanp))
     :parents nil
     (b* (((when (endp scopes)) (mv nil nil))
          (scope (car scopes))
          (ord-scope (valid-scope->ord scope))
          (ident+info (assoc-equal (ident-fix ident) ord-scope))
          ((when ident+info) (mv (cdr ident+info) (bool-fix currentp))))
       (valid-lookup-ord-loop ident (cdr scopes) nil))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-ord-file-scope ((ident identp) (table valid-tablep))
  :returns (info? valid-ord-info-optionp)
  :short "Look up an ordinary identifier
          in the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee valid-lookup-ord), this skips any block scopes,
     and directly looks up the identifier in the file scope.
     It is used in some situations."))
  (b* ((scopes (valid-table->scopes table))
       ((when (endp scopes)) (raise "Internal error: no scopes."))
       (scope (car (last scopes)))
       (ident+info (assoc-equal (ident-fix ident)
                                (valid-scope->ord scope)))
       ((when ident+info) (cdr ident+info)))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-add-ord ((ident identp)
                       (info valid-ord-infop)
                       (table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Add an ordinary identifier to the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the information to associate to the identifier.")
   (xdoc::p
    "The identifier is always added to
     the first (i.e. innermost, i.e. current) scope.
     We check the existence of at least one scope;
     recall that there must be always a file scope.")
   (xdoc::p
    "If the identifier is already present in the current scope,
     its information is overwritten,
     but we only call this function after checking that
     this overwriting is acceptable,
     i.e. when it ``refines'' the validation information for the identifier.
     We could consider adding a guard to this function
     that characterizes the acceptable overwriting."))
  (b* (((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (valid-table-fix table))
       (scopes (valid-table->scopes table))
       (scope (car scopes))
       (ord-scope (valid-scope->ord scope))
       (new-ord-scope (acons (ident-fix ident)
                             (valid-ord-info-fix info)
                             ord-scope))
       (new-scope (change-valid-scope scope :ord new-ord-scope))
       (new-scopes (cons new-scope (cdr scopes))))
    (change-valid-table table :scopes new-scopes))
  :guard-hints (("Goal" :in-theory (enable valid-table-num-scopes acons)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define valid-add-ord-file-scope ((ident identp)
                                  (info valid-ord-infop)
                                  (table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Add an ordinary identifier
          to the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee valid-add-ord), this skips any block scopes,
     and directly updates the file scope at the bottom of the stack.
     It is used in some situations."))
  (b* ((scopes (valid-table->scopes table))
       ((when (endp scopes))
        (raise "Internal error: no scopes.")
        (irr-valid-table))
       (scope (car (last scopes)))
       (ord-scope (valid-scope->ord scope))
       (new-ord-scope (acons (ident-fix ident)
                             (valid-ord-info-fix info)
                             ord-scope))
       (new-scope (change-valid-scope scope :ord new-ord-scope))
       (new-scopes (append (butlast scopes 1) (list new-scope))))
    (change-valid-table table :scopes new-scopes))
  :guard-hints (("Goal" :in-theory (enable acons)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-dec/oct/hex-const ((const dec/oct/hex-constp))
  :returns (value natp)
  :short "Validate a decimal, octal, or hexadecimal constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of constant is always valid,
     but for this function we use the naming scheme @('valid-...')
     for uniformity with the other validator's functions.")
   (xdoc::p
    "This function actually evaluates the constant, to a natural number.
     This is needed by the validator in order to assign
     types to integer constants.
     This function returns a natural number,
     which can be arbitrarily large;
     whether an integer constant is too large is checked elsewhere.")
   (xdoc::p
    "For a decimal or octal constant, the value is a component of the fixtype.
     For a hexadecimal constant, we use a library function
     to convert the digits into a value;
     the digits are as they appear in the concrete syntax,
     i.e. in big-endian order."))
  (dec/oct/hex-const-case
   const
   :dec const.value
   :oct const.value
   :hex (str::hex-digit-chars-value const.digits))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-iconst ((iconst iconstp) (ienv ienvp))
  :returns (mv erp (type typep))
  :short "Validate an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "An integer constant is valid iff
     it has a type according to the table in [C:6.4.4.1/5].
     We formalize that table here, and we return the type of the constant.
     If the constant is too large,
     it does not have a type, and it is invalid."))
  (b* (((reterr) (irr-type))
       ((iconst iconst) iconst)
       (value (valid-dec/oct/hex-const iconst.core)))
    (cond
     ((not iconst.suffix?)
      (if (dec/oct/hex-const-case iconst.core :dec)
          (cond ((sint-rangep value ienv) (retok (type-sint)))
                ((slong-rangep value ienv) (retok (type-slong)))
                ((sllong-rangep value ienv) (retok (type-sllong)))
                (t (reterr (msg "The constant ~x0 is too large."
                                (iconst-fix iconst)))))
        (cond ((sint-rangep value ienv) (retok (type-sint)))
              ((uint-rangep value ienv) (retok (type-uint)))
              ((slong-rangep value ienv) (retok (type-slong)))
              ((ulong-rangep value ienv) (retok (type-ulong)))
              ((sllong-rangep value ienv) (retok (type-sllong)))
              ((ullong-rangep value ienv) (retok (type-ullong)))
              (t (reterr (msg "The constant ~x0 is too large."
                              (iconst-fix iconst)))))))
     ((isuffix-case iconst.suffix? :u)
      (cond ((uint-rangep value ienv) (retok (type-uint)))
            ((ulong-rangep value ienv) (retok (type-ulong)))
            ((ullong-rangep value ienv) (retok (type-ullong)))
            (t (reterr (msg "The constant ~x0 is too large."
                            (iconst-fix iconst))))))
     ((isuffix-case iconst.suffix? :l)
      (cond ((member-eq (lsuffix-kind (isuffix-l->length iconst.suffix?))
                        '(:locase-l :upcase-l))
             (if (dec/oct/hex-const-case iconst.core :dec)
                 (cond ((slong-rangep value ienv) (retok (type-slong)))
                       ((sllong-rangep value ienv) (retok (type-sllong)))
                       (t (reterr (msg "The constant ~x0 is too large."
                                       (iconst-fix iconst)))))
               (cond ((slong-rangep value ienv) (retok (type-slong)))
                     ((ulong-rangep value ienv) (retok (type-ulong)))
                     ((sllong-rangep value ienv) (retok (type-sllong)))
                     ((ullong-rangep value ienv) (retok (type-ullong)))
                     (t (reterr (msg "The constant ~x0 is too large."
                                     (iconst-fix iconst)))))))
            ((member-eq (lsuffix-kind (isuffix-l->length iconst.suffix?))
                        '(:locase-ll :upcase-ll))
             (if (dec/oct/hex-const-case iconst.core :dec)
                 (cond ((sllong-rangep value ienv) (retok (type-sllong)))
                       (t (reterr (msg "The constant ~x0 is too large."
                                       (iconst-fix iconst)))))
               (cond ((sllong-rangep value ienv) (retok (type-sllong)))
                     ((ullong-rangep value ienv) (retok (type-ullong)))
                     (t (reterr (msg "The constant ~x0 is too large."
                                     (iconst-fix iconst)))))))
            (t (prog2$ (impossible) (reterr t)))))
     ((or (and (isuffix-case iconst.suffix? :ul)
               (member-eq (lsuffix-kind (isuffix-ul->length iconst.suffix?))
                          '(:locase-l :upcase-l)))
          (and (isuffix-case iconst.suffix? :lu)
               (member-eq (lsuffix-kind (isuffix-lu->length iconst.suffix?))
                          '(:locase-l :upcase-l))))
      (cond ((ulong-rangep value ienv) (retok (type-ulong)))
            ((ullong-rangep value ienv) (retok (type-ullong)))
            (t (reterr (msg "The constant ~x0 is too large."
                            (iconst-fix iconst))))))
     ((or (and (isuffix-case iconst.suffix? :ul)
               (member-eq (lsuffix-kind (isuffix-ul->length iconst.suffix?))
                          '(:locase-ll :upcase-ll)))
          (and (isuffix-case iconst.suffix? :lu)
               (member-eq (lsuffix-kind (isuffix-lu->length iconst.suffix?))
                          '(:locase-ll :upcase-ll))))
      (cond ((ullong-rangep value ienv) (retok (type-ullong)))
            (t (reterr (msg "The constant ~x0 is too large."
                            (iconst-fix iconst))))))
     (t (prog2$ (impossible) (reterr t)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-fconst ((fconst fconstp))
  :returns (type typep)
  :short "Validate a floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "A floating constant is always valid:
     [C:6.4.4.2] states no restrictions,
     except for a recommended practice
     to provide a diagnostic message in certain cases,
     which also instructs to proceed with compilation nonetheless,
     suggesting that it should be only a warning, not an error.")
   (xdoc::p
    "The type is determined solely by the suffix, including its absence
     [C:6.4.4.2/4]."))
  (b* ((suffix? (fconst-case fconst
                             :dec fconst.suffix?
                             :hex fconst.suffix?)))
    (cond ((not suffix?) (type-double))
          ((or (fsuffix-case suffix? :locase-f)
               (fsuffix-case suffix? :upcase-f))
           (type-float))
          ((or (fsuffix-case suffix? :locase-l)
               (fsuffix-case suffix? :upcase-l))
           (type-ldouble))
          (t (prog2$ (impossible) (irr-type)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-univ-char-name ((ucn univ-char-name-p) (max natp))
  :returns (mv erp (code natp))
  :short "Validate a universal character name."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation is successful, we return the numeric code of the character.")
   (xdoc::p
    "[C:6.4.3/2] states some restriction on the character code.
     [C:6.4.4.4/4] and (implicitly) [C:6.4.5/4]
     state type-based restrictions on
     the character codes of octal and hexadecimal escapes,
     based on the (possibly absent) prefix of
     the character constant or string literal.
     But it seems reasonable that the same range restrictions
     should also apply to universal character names;
     some experiments with the C compiler on Mac confirms this."))
  (b* (((reterr) 0)
       (code (univ-char-name-case
              ucn
              :locase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad)
                               (hex-quad->2nd ucn.quad)
                               (hex-quad->3rd ucn.quad)
                               (hex-quad->4th ucn.quad)))
              :upcase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad1)
                               (hex-quad->2nd ucn.quad1)
                               (hex-quad->3rd ucn.quad1)
                               (hex-quad->4th ucn.quad1)
                               (hex-quad->1st ucn.quad2)
                               (hex-quad->2nd ucn.quad2)
                               (hex-quad->3rd ucn.quad2)
                               (hex-quad->4th ucn.quad2)))))
       ((when (and (< code #xa0)
                   (not (= code #x24))
                   (not (= code #x40))
                   (not (= code #x60))))
        (reterr (msg "The universal character name ~x0 ~
                      has a code ~x1 that is below A0h ~
                      but is not 24h or 40h or 60h."
                     (univ-char-name-fix ucn) code)))
       ((when (and (<= #xd800 code)
                   (<= code #xdfff)))
        (reterr (msg "The universal character name ~x0 ~
                      has a code ~x1 between D800h and DFFFh."
                     (univ-char-name-fix ucn) code)))
       ((when (> code (nfix max)))
        (reterr (msg "The universal character name ~x0 ~
                      has a code ~x1 above ~x2."
                     (univ-char-name-fix ucn) code (nfix max)))))
    (retok code))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-simple-escape ((esc simple-escapep))
  :returns (code natp)
  :short "Validate a simple escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "Simple escapes are always valid.
     This function returns their ASCII codes.
     Note that these always fit in any of the types
     mentioned in [C:6.4.4.4/4].
     The GCC escape @('\\%') is like the character @('%')."))
  (simple-escape-case
   esc
   :squote (char-code #\')
   :dquote (char-code #\")
   :qmark (char-code #\?)
   :bslash (char-code #\\)
   :a 7
   :b 8
   :f 12
   :n 10
   :r 13
   :t 9
   :v 11
   :percent (char-code #\%))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-oct-escape ((esc oct-escapep) (max natp))
  :returns (mv erp (code natp))
  :short "Validate an octal escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C:6.4.4.4/9] states restrictions on
     the numeric value of an octal escape used in a character constant,
     based on the prefix of the character constant;
     similarly restrictions apply to octal escapes in string literals
     [C:6.4.5/4].
     This ACL2 function is used to check
     both octal escapes in character constants
     and octal escapes in string literals:
     we pass as input the maximum allowed character code,
     which is determined from the character constant or string literal prefix
     if present (see callers),
     and suffices to express the applicable restrictions."))
  (b* (((reterr) 0)
       (code (oct-escape-case
              esc
              :one (str::oct-digit-char-value esc.digit)
              :two (str::oct-digit-chars-value (list esc.digit1
                                                     esc.digit2))
              :three (str::oct-digit-chars-value (list esc.digit1
                                                       esc.digit2
                                                       esc.digit3)))))
    (if (<= code (nfix max))
        (retok code)
      (reterr (msg "The octal escape sequence ~x0 ~
                    has value ~x1, which exceeds the maximum allowed ~x2, ~
                    required in the context of where this octal escape occurs."
                   (oct-escape-fix esc)
                   code
                   (nfix max)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-escape ((esc escapep) (max natp))
  :returns (mv erp (code natp))
  :short "Validate an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the escape sequence is valid, we return its character code.
     For simple and octal escapes, and for universal character names,
     we use separate validation functions.
     For a hexadecimal escape, we calculate the numeric value,
     and we subject them to same restrictions as octal escapes
     [C:6.4.4.4/9] [C:6.4.5/4].")
   (xdoc::p
    "Although [C] does not seem to state that explicitly,
     it seems reasonable that the same restriction applies to
     universal character names;
     we will revise this if that turns out to be not the case."))
  (b* (((reterr) 0))
    (escape-case
     esc
     :simple (retok (valid-simple-escape esc.unwrap))
     :oct (valid-oct-escape esc.unwrap max)
     :hex (b* ((code (str::hex-digit-chars-value esc.unwrap)))
            (if (<= code (nfix max))
                (retok code)
              (reterr (msg "The hexadecimal escape sequence ~x0 ~
                            has value ~x1, which exceeds ~
                            the maximum allowed ~x2, ~
                            required in the context where ~
                            this hexadecimal escape occurs."
                           (escape-fix esc)
                           code
                           (nfix max)))))
     :univ (valid-univ-char-name esc.unwrap max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-c-char ((cchar c-char-p) (prefix? cprefix-optionp))
  :returns (mv erp (code natp))
  :short "Validate a character of a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation succeeds, we return the character code.")
   (xdoc::p
    "The grammar [C:6.4.4.4/1] excludes (direct) character codes
     for single quote and new-line.
     For the latter, we check both line feed and carriage return.
     Note that our lexer normalizes both to line feed,
     and excludes line feed when lexing @('c-char');
     here we make an independent check,
     but in the future we could make that
     an invariant in the abstract syntax.")
   (xdoc::p
    "[C:6.4.4.4/4] says that, based on the (possibly absent) prefix
     of the character constant of which this character is part,
     the character code of an octal or hexadecimal escape must fit in
     @('unsigned char'), or
     @('wchar_t'), or
     @('char16_t'), or
     @('char32_t').
     To properly capture the range of the latter three types,
     we should probably extend our implementation environments
     with information about which built-in types those types expand to,
     and then use again the implementation environment
     to obtain the maximun values of such built-in types.
     For now, we just use the maximum Unicode code points,
     i.e. effectively we do not enforce any restriction."))
  (b* (((reterr) 0)
       (max (if prefix?
                #x10ffff
              (uchar-max))))
    (c-char-case
     cchar
     :char (cond ((= cchar.unwrap (char-code #\'))
                  (reterr (msg "Single quote cannot be used directly ~
                                in a character constant.")))
                 ((= cchar.unwrap 10)
                  (reterr (msg "Line feed cannot be used directly ~
                                in a character constant.")))
                 ((= cchar.unwrap 13)
                  (reterr (msg "Carriage return cannot be used directly ~
                                in a character constant.")))
                 ((> cchar.unwrap max)
                  (reterr (msg "The character with code ~x0 ~
                                exceeed the maximum ~x1 allowed for ~
                                a character constant with prefix ~x2."
                               cchar.unwrap max (cprefix-option-fix prefix?))))
                 (t (retok cchar.unwrap)))
     :escape (valid-escape cchar.unwrap max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-c-char-list ((cchars c-char-listp) (prefix? cprefix-optionp))
  :returns (mv erp (codes nat-listp))
  :short "Validate a list of characters of a character constant."
  (b* (((reterr) nil)
       ((when (endp cchars)) (retok nil))
       ((erp code) (valid-c-char (car cchars) prefix?))
       ((erp codes) (valid-c-char-list (cdr cchars) prefix?)))
    (retok (cons code codes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cconst ((cconst cconstp))
  :returns (mv erp (type typep))
  :short "Validate a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the characters that form the constant,
     with respect to the prefix (if any).
     If validation is successful, we return the type of the constant.
     According to [C:6.4.4.4/10],
     a character constant without prefix has type @('int').
     According to [C:6.4.4.4/11],
     a character constant with a prefix has type
     @('wchar_t'), @('char16_t'), or @('char32_t');
     since for now we do not model these,
     we return an unknown type in this case.")
   (xdoc::p
    "The types @('wchar_t'), @('char16_t'), and @('char32_t')
     may vary across implementations.
     In order to handle these in a general way,
     we should probably extend our implementation environments
     with information about which built-in types those types expand to.
     Once we do that, we will be able to perform
     a full validation of character constants here."))
  (b* (((reterr) (irr-type))
       ((cconst cconst) cconst)
       ((erp &) (valid-c-char-list cconst.cchars cconst.prefix?)))
    (if cconst.prefix?
        (retok (type-unknown))
      (retok (type-sint))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-enum-const ((econst identp) (table valid-tablep))
  :returns (mv erp (type typep))
  :short "Validate an enumeration constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we validate an enumeration constant that occurs as an expression.
     Thus, the validation table must include that (ordinary) identifier,
     with the information of being an enumeration constant.
     Its type is always @('int') [C:6.7.2.2/3],
     so this function always returns that type if validation succeeds;
     so we could have this function return nothing if there's no error,
     but we have it return the @('int') type for uniformity and simplicity."))
  (b* (((reterr) (irr-type))
       ((mv info &) (valid-lookup-ord econst table))
       ((unless info)
        (reterr (msg "The identifier ~x0, used as an enumeration constant, ~
                      is not in scope."
                     (ident-fix econst))))
       ((unless (valid-ord-info-case info :enumconst))
        (reterr (msg "The identifier ~x0, used as an enumeration constant, ~
                      is in scope, but it is not an enumeration constant: ~
                      its information is ~x1."
                     (ident-fix econst) info))))
    (retok (type-sint)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-const ((const constp) (table valid-tablep) (ienv ienvp))
  :returns (mv erp (type typep))
  :short "Validate a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation is successful, we return the type of the constant."))
  (const-case
   const
   :int (valid-iconst const.unwrap ienv)
   :float (retok (valid-fconst const.unwrap))
   :enum (valid-enum-const const.unwrap table)
   :char (valid-cconst const.unwrap))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-s-char ((schar s-char-p) (prefix? eprefix-optionp))
  :returns (mv erp (code natp))
  :short "Validate a character of a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation succeeds, we return the character code.
     [C:6.4.5/4] says that the same restrictions that apply
     to @('c-char')s in character constants
     also apply to @('s-char')s in string literals.
     So this function is similar to @(tsee valid-c-char),
     except that we prohibit double quote instead of single quote,
     based on the grammar in [C:6.4.5/1]."))
  (b* (((reterr) 0)
       (max (if prefix?
                #x10ffff
              (uchar-max))))
    (s-char-case
     schar
     :char (cond ((= schar.unwrap (char-code #\"))
                  (reterr (msg "Double quote cannot be used directly ~
                                in a string literal.")))
                 ((= schar.unwrap 10)
                  (reterr (msg "Line feed cannot be used directly ~
                                in a character consant.")))
                 ((= schar.unwrap 13)
                  (reterr (msg "Carriage return cannot be used directly ~
                                in a character consant.")))
                 ((> schar.unwrap max)
                  (reterr (msg "The character with code ~x0 ~
                                exceeed the maximum ~x1 allowed for ~
                                a character constant with prefix ~x2."
                               schar.unwrap max (eprefix-option-fix prefix?))))
                 (t (retok schar.unwrap)))
     :escape (valid-escape schar.unwrap max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-s-char-list ((cchars s-char-listp) (prefix? eprefix-optionp))
  :returns (mv erp (codes nat-listp))
  :short "Validate a list of characters of a string literal."
  (b* (((reterr) nil)
       ((when (endp cchars)) (retok nil))
       ((erp code) (valid-s-char (car cchars) prefix?))
       ((erp codes) (valid-s-char-list (cdr cchars) prefix?)))
    (retok (cons code codes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stringlit ((strlit stringlitp))
  :returns (mv erp (type typep))
  :short "Validate a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the characters that form the string literal,
     with respect to the prefix (if any).
     If validation is successful, we return the type of the string literal,
     which according to [C:6.4.5/6], is an array type
     of @('char') or @('wchar_t') or @('char16_t') or @('char32_t').
     In our current approximate type system,
     we just have a single type for arrays, so we return that."))
  (b* (((reterr) (irr-type))
       ((stringlit strlit) strlit)
       ((erp &) (valid-s-char-list strlit.schars strlit.prefix?)))
    (retok (type-array)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stringlit-list ((strlits stringlit-listp))
  :returns (mv erp (type typep))
  :short "Validate a list of string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our abstract syntax preserves information about
     adjacent string literals [C:5.1.1.2/6],
     by using lists of string literals, instead of single string literals,
     in various places.
     So the validator also operates on such lists of string literals.")
   (xdoc::p
    "One basic requirement is that the list is not empty,
     because there must be at least one string literal;
     in the future we could built that constraint into the abstract syntax,
     but for now we put that as a check in the validator.")
   (xdoc::p
    "Another requirement is that
     there cannot be both UTF-8 and wide prefixes [C:6.4.5/2],
     where these kinds of prefixes are defined in [C:6.4.5/3].
     We check that by projecting the optional prefixes
     and checking for incompatible occurrences.")
   (xdoc::p
    "Whether string literals with different prefixes
     (satisfying the requirement just mentioned)
     can be concatenated, and what their combined type is,
     is implementation-defined [C:6.4.5/5].
     We plan to extend our implementation environments
     with information about how to treat those cases,
     but for now we allow all concatenations,
     and the resulting type is just our approximate type for all arrays."))
  (b* (((reterr) (irr-type))
       ((unless (consp strlits))
        (reterr (msg "There must be at least one string literal.")))
       (prefixes (stringlit-list->prefix?-list strlits))
       ((when (and (member-equal (eprefix-locase-u8) prefixes)
                   (or (member-equal (eprefix-locase-u) prefixes)
                       (member-equal (eprefix-upcase-u) prefixes)
                       (member-equal (eprefix-upcase-l) prefixes))))
        (reterr (msg "Incompatible prefixes ~x0 ~
                      in the list of string literals."
                     prefixes))))
    (retok (type-array)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-var ((var identp) (table valid-tablep))
  :returns (mv erp (type typep))
  :short "Validate a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to validate the @(':ident') case of the @(tsee expr) fixtype.
     This is the case of a variable, not an enumeration constant,
     which is part of the @(':const') case of @(tsee expr).
     Recall that the parser initially parses all identifiers used as expressions
     under the @(':ident') case, but the disambiguator re-classifies
     some of them under the @(':const') case, as appropriate.")
   (xdoc::p
    "A variable (i.e. identifier) is valid if
     it is found in the validation table,
     recorded as denoting an object or function
     [C:6.5.1/2].
     The type is obtained from the table."))
  (b* (((reterr) (irr-type))
       ((mv info &) (valid-lookup-ord var table))
       ((unless info)
        (reterr (msg "The variable ~x0 is not in scope." (ident-fix var))))
       ((unless (valid-ord-info-case info :objfun))
        (reterr (msg "The identifier ~x0, used as a variable, ~
                      is in scope, but does not denote ~
                      an object or function."
                     (ident-fix var)))))
    (retok (valid-ord-info-objfun->type info)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-gensel ((expr exprp)
                      (type typep)
                      (type-alist type-option-type-alistp))
  :guard (expr-case expr :gensel)
  :returns (mv erp (type typep))
  :short "Validate a generic selection expression,
          given the types for the components."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not perform any of the checks prescribed in [C:6.5.1.1/2].
     We will perform them later, when we refine our validator.
     We return the unknown type."))
  (declare (ignore expr type type-alist))
  (retok (type-unknown))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-arrsub ((expr exprp) (type-arg1 typep) (type-arg2 typep))
  :guard (expr-case expr :arrsub)
  :returns (mv erp (type typep))
  :short "Validate an array subscripting expression,
          given the types of the two sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After converting array types to pointer types,
     one sub-expression must have pointer type,
     and the other sub-expression must have integer type
     [C:6.5.2.1/1].
     The expression should have the type referenced by the pointer type,
     but since for now we model just one pointer type,
     the type of the expression is unknown.")
   (xdoc::p
    "There is no need to perform function-to-pointer conversion,
     because that would result in a pointer to function,
     which is disallowed,
     as it has to be a pointer to a complete object type [C:6.5.2.1/1].
     So by leaving function types as such, we automatically disallow them."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok (type-unknown)))
       (type1 (type-apconvert type-arg1))
       (type2 (type-apconvert type-arg2))
       ((unless (or (and (type-case type1 :pointer)
                         (type-integerp type2))
                    (and (type-integerp type1)
                         (type-case type2 :pointer))))
        (reterr (msg "In the array subscripting expression ~x0, ~
                      the first sub-expression has type ~x1, ~
                      and the second sub-expression has type ~x2."
                     (expr-fix expr)
                     (type-fix type-arg1)
                     (type-fix type-arg2)))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-funcall ((expr exprp) (type-fun typep) (types-arg type-listp))
  :guard (expr-case expr :funcall)
  :returns (mv erp (type typep))
  :short "Validate a function call expression,
          given the types of the sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After converting function types to pointer types,
     the first sub-expression must have pointer type [C:6.5.2.2/1];
     since we currently have just one pointer type,
     we cannot check that it is a pointer to a function.
     For the same reason,
     we do not check the argument types against the function type [C:6.5.2.2/2].
     Also for the same reason,
     we return the unknown type,
     because we do not have information about the result type.")
   (xdoc::p
    "There is no need to perform array-to-pointer conversion,
     because array types cannot have function element types,
     but only (complete) object element types [C:6.2.5/20].
     Thus, the conversion could never result into a pointer to a function."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-fun :unknown)
                  (member-equal (type-unknown) (type-list-fix types-arg))))
        (retok (type-unknown)))
       (type (type-fpconvert type-fun))
       ((unless (type-case type :pointer))
        (reterr (msg "In the function call expression ~x0, ~
                      the first sub-expression has type ~x1."
                     (expr-fix expr)
                     (type-fix type-fun)))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-member ((expr exprp) (type-arg typep))
  :guard (expr-case expr :member)
  :returns (mv erp (type typep))
  :short "Validate a member expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The argument type must be a structure or union type [C:6.5.2.3/1].
     Since a pointer type is not allowed here,
     there is no need to convert arrays or functions to pointers.")
   (xdoc::p
    "For now we only have one type for structures and one type for unions.
     We cannot look up the member type, so we return the unknown type."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       ((unless (or (type-case type-arg :struct)
                    (type-case type-arg :union)))
        (reterr (msg "In the member expression ~x0, ~
                      the sub-expression has type ~x1."
                     (expr-fix expr) (type-fix type-arg)))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-memberp ((expr exprp) (type-arg typep))
  :guard (expr-case expr :memberp)
  :returns (mv erp (type typep))
  :short "Validate a member pointer expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the sub-expression is
     calculated (recursively) by @(tsee valid-expr).")
   (xdoc::p
    "The argument type must be a pointer to a structure or union type
     [C:6.5.2.3/2].
     We need to convert arrays to pointers,
     and then we just check that we have the (one) pointer type;
     we will refine this when we refine our type system.
     We do not conver functions to pointers,
     because that would result into a pointer to function,
     which is not a pointer to structure or union as required;
     thus, by leaving function types unchanged, we reject them here.")
   (xdoc::p
    "Since we cannot yet look up members in structure and union types,
     we return the unknown type."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       (type (type-apconvert type-arg))
       ((unless (type-case type :pointer))
        (reterr (msg "In the member pointer expression ~x0, ~
                      the sub-expression has type ~x1."
                     (expr-fix expr) (type-fix type-arg)))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-unary ((expr exprp) (op unopp) (type-arg typep) (ienv ienvp))
  :guard (expr-case expr :unary)
  :returns (mv erp (type typep))
  :short "Validate a unary expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('&') operator requires an lvalue of any type as operand
     [C:6.5.3.2/1] [C:6.5.3.2/3],
     but we are not yet distinguishing lvalues from non-lvalues,
     so we allow any type of operand, and we return the (one) pointer type.")
   (xdoc::p
    "The @('*') unary operator requires an operand of a pointer type
     [C:6.5.3.2/2],
     after array-to-pointer and function-to-pointer conversions;
     as always, we also need to allow the unknown type.
     Since we only have one type for pointers for now,
     the resulting type is unknown.")
   (xdoc::p
    "The @('+') and @('-') unary operators
     require an operand of an arithmetic type [C:6.5.3.3/1],
     and the result has the promoted type [C:6.5.3.3/2].
     There is no need for array-to-pointer and function-to-pointer conversions,
     because they never result in arithmetic types.")
   (xdoc::p
    "The @('~') operator requires an operand of an integer type [C:6.5.3.3/1],
     and the result has the promoted type [C:.6.5.3.3/4].
     There is no need for array-to-pointer and function-to-pointer conversions,
     because they never result in arithmetic types.")
   (xdoc::p
    "The @('!') operator requires an operand of a scalar type [C:6.5.3.3/1],
     and result is always @('signed int') [C:6.5.3.3/5].
     Since pointers may be involved, we perform
     array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('sizeof') operator applied to an expression
     requires a non-function complete type [C:6.5.3.4/1].
     In our current approximate type system,
     we just exclude function types,
     but we do not have a notion of complete types yet.
     The result has type @('size_t') [C:6.5.3.4/5],
     whose definition is implementation-defined,
     so for now we just return the unknown type;
     we will need to extend implementation environments
     with information about the definition of @('size_t').")
   (xdoc::p
    "The @('++') pre-increment and @('--') pre-decrement operators
     require a real or pointer operand [C:6.5.3.1/1].
     Since these expressions are equivalent to assignments
     [C:6.5.3.1/2] [C:6.5.3.1/3],
     the type of the result must be the type of the operand.
     We do not perform array-to-pointer or function-to-pointer conversions,
     because those result in pointers, not lvalues as required [C:6.5.3.1/1].")
   (xdoc::p
    "The @('++') post-increment and @('--') post-decrement operators
     require a real or pointer operand [C:6.5.2.4/1].
     The type of the result is the same as the operand
     [C:6.5.2.4/2] [C:6.5.2.4/3].
     We do not perform array-to-pointer or function-to-pointer conversions,
     because those result in pointers, not lvalues as required [C:6.5.2.4/1]."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       (msg (msg "In the unary expression ~x0, ~
                  the sub-expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg))))
    (case (unop-kind op)
      (:address (retok (type-pointer)))
      (:indir (b* ((type (type-fpconvert (type-apconvert type-arg)))
                   ((unless (type-case type :pointer))
                    (reterr msg)))
                (retok (type-unknown))))
      ((:plus :minus) (b* (((unless (type-arithmeticp type-arg))
                            (reterr msg)))
                        (retok (type-promote type-arg ienv))))
      (:bitnot (b* (((unless (type-integerp type-arg))
                     (reterr msg)))
                 (retok (type-promote type-arg ienv))))
      (:lognot (b* ((type (type-fpconvert (type-apconvert type-arg)))
                    ((unless (type-scalarp type))
                     (reterr msg)))
                 (retok (type-sint))))
      ((:preinc :predec :postinc :postdec)
       (b* (((unless (or (type-realp type-arg)
                         (type-case type-arg :pointer)))
             (reterr msg)))
         (retok (type-fix type-arg))))
      (:sizeof (b* (((when (type-case type-arg :function))
                     (reterr msg)))
                 (retok (type-unknown))))
      (t (prog2$ (impossible) (reterr t)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-binary ((expr exprp)
                      (op binopp)
                      (type-arg1 typep)
                      (type-arg2 typep)
                      (ienv ienvp))
  :guard (expr-case expr :binary)
  :returns (mv erp (type typep))
  :short "Validate a binary expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('*') binary and @('/') operators
     require arithmetic operands [C:6.5.5/2].
     The result is the common type according to
     the usual arithmetic conversions [C:6.5.5/3].
     There is no need for array-to-pointer or function-to-pointer conversions
     because those never produce arithmetic types.")
   (xdoc::p
    "The @('%') operator requires integer operands [C:6.5.5/2].
     The result is from the usual arithmetic conversions [C:6.5.5/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('+') binary operator requires
     either two arithmetic operands
     or an integer and a pointer operand
     [C:6.5.6/2].
     In the first case, the result is from the usual arithmetic conversions
     [C:6.5.6/4].
     In the second case, the result is the pointer type [C:6.5.6/8].
     Because of that second case, which involves pointers,
     we perform array-to-pointer conversion.
     We not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to complete object type is required.")
   (xdoc::p
    "The @('-') binary operator requires
     either two arithmetic operands,
     or two pointer operands,
     or a pointer first operand and an integer second operand
     [C:6.5.6/3].
     In the first case, the result is from the usual arithmetic conversions
     [C:6.5.6/4].
     In the second case, the result has type @('ptrdiff_t') [C:6.5.6/9],
     which has an implementation-specific definition,
     and so we return the unknown type in this case.
     In the third case, the result has the pointer type [C:6.5.6/8].
     Because of the second and third cases, which involve pointers,
     we perform array-to-pointer conversion.
     We not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to complete object type is required.")
   (xdoc::p
    "The @('<<') and @('>>') operators require integer operands [C:6.5.7/2].
     The type of the result is the type of the promoted left operand
     [C:6.5.7/3].
     There is no need for
     array-to-pointer or function-to-pointer conversions.")
   (xdoc::p
    "The @('<'), @('>'), @('<='), and @('>=') operators
     require real types or pointer types [C:6.5.8/2].
     The result is always @('signed int') [C:6.5.8/6].
     Since pointers may be involved,
     we perform array-to-pointer conversion.
     We not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to object type is required.")
   (xdoc::p
    "The @('==') and @('!=') operators require
     arithmetic types or pointer types [C:6.5.9/2];
     since we currently have just one type for pointers,
     the distinctions between the three cases involving pointers
     reduce to just the simple case of two pointers for us for now.
     The result is always @('signed int') [C:6.5.9/3].
     Since pointers may be involved,
     we perform array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('&'), @('^'), and @('|') operators require integer operands
     [C:6.5.10/2] [C:6.5.11/2] [C:6.5.12/2].
     The result has the type from the usual arithmetic conversions
     [C:6.5.10/3] [C:6.5.11/3] [C:6.5.12/3].
     No array-to-pointer or function-to-pointer conversion is needed.")
   (xdoc::p
    "The @('&&') and @('||') operators require scalar types
     [C:6.5.13/2] [C:6.5.14/2].
     The result has type @('signed int') [C:6.5.13/3] [C:6.5.14/3].
     Since pointers may be involved, we need to perform
     array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('=') simple assignment operator requires
     an lvalue as left operand [C:6.5.16/2],
     but currently we do not check that.
     In our currently approximate type system,
     the requirements in [C:6.5.16.1/1] reduce to the two operands having
     both arithmetic types,
     or both the structure type,
     or both the union type,
     or both pointer types.
     We do not perform array-to-pointer or function-to-pointer conversion
     on the left operand, because the result would not be an lvalue.
     The type of the result is the type of the left operand [C:6.5.16/3].")
   (xdoc::p
    "The @('*=') and @('/=') operators require arithmetic operands
     [C:6.5.16.2/2],
     and the result has the type of the first operand [C:6.5.16/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('%=') operator requires integer operands [C:6.5.16.2/2],
     and the result has the type of the first operand [C:6.5.16/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('+=') and @('-=') operands require
     either arithmetic operands
     or a first pointer operand and a second integer operand
     [C:6.5.16.2/1].
     The result has the type of the first operand [C:6.5.16/3].
     Since pointers may be involved,
     we perform array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('<<='), @('>>='), @('&='), @('^='), and @('|=') operators
     require integer operands [C:6.5.13.2/2].
     The result has the type of the first operand [C:6.5.13/3].
     No array-to-pointer or function-to-pointer conversions are needed."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok (type-unknown)))
       (msg (msg "In the binary expression ~x0, ~
                  the sub-expressiona have types ~x1 and ~x2."
                 (expr-fix expr) (type-fix type-arg1) (type-fix type-arg2))))
    (case (binop-kind op)
      ((:mul :div) (b* (((unless (and (type-arithmeticp type-arg1)
                                      (type-arithmeticp type-arg2)))
                         (reterr msg)))
                     (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      (:rem (b* (((unless (and (type-arithmeticp type-arg1)
                               (type-arithmeticp type-arg2)))
                  (reterr msg)))
              (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      (:add (b* ((type1 (type-apconvert type-arg1))
                 (type2 (type-apconvert type-arg2)))
              (cond
               ((and (type-arithmeticp type1)
                     (type-arithmeticp type2))
                (retok (type-uaconvert type1 type2 ienv)))
               ((or (and (type-integerp type1)
                         (type-case type2 :pointer))
                    (and (type-case type1 :pointer)
                         (type-integerp type2)))
                (retok (type-pointer)))
               (t (reterr msg)))))
      (:sub (b* ((type1 (type-apconvert type-arg1))
                 (type2 (type-apconvert type-arg2)))
              (cond
               ((and (type-arithmeticp type1)
                     (type-arithmeticp type2))
                (retok (type-uaconvert type1 type2 ienv)))
               ((and (type-case type1 :pointer)
                     (type-case type2 :pointer))
                (retok (type-unknown)))
               ((and (type-case type1 :pointer)
                     (type-integerp type2))
                (retok (type-pointer)))
               (t (reterr msg)))))
      ((:shl :shr) (b* (((unless (and (type-integerp type-arg1)
                                      (type-integerp type-arg2)))
                         (reterr msg)))
                     (retok (type-promote type-arg1 ienv))))
      ((:lt :gt :le :ge)
       (b* ((type1 (type-apconvert type-arg1))
            (type2 (type-apconvert type-arg2))
            ((unless (or (and (type-realp type1)
                              (type-realp type2))
                         (and (type-case type1 :pointer)
                              (type-case type2 :pointer))))
             (reterr msg)))
         (retok (type-sint))))
      ((:eq :ne) (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
                      (type2 (type-fpconvert (type-apconvert type-arg2)))
                      ((unless (or (and (type-arithmeticp type1)
                                        (type-arithmeticp type2))
                                   (and (type-case type1 :pointer)
                                        (type-case type2 :pointer))))
                       (reterr msg)))
                   (retok (type-sint))))
      ((:bitand :bitxor :bitior)
       (b* (((unless (and (type-integerp type-arg1)
                          (type-integerp type-arg2)))
             (reterr msg)))
         (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      ((:logand :logor)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (and (type-scalarp type1)
                          (type-scalarp type2)))
             (reterr msg)))
         (retok (type-sint))))
      (:asg (b* ((type1 type-arg1)
                 (type2 (type-fpconvert (type-apconvert type-arg2)))
                 ((unless (or (and (type-arithmeticp type1)
                                   (type-arithmeticp type2))
                              (and (type-case type1 :struct)
                                   (type-case type2 :struct))
                              (and (type-case type1 :union)
                                   (type-case type2 :union))
                              (and (or (type-case type1 :pointer)
                                       (type-case type1 :bool))
                                   (type-case type2 :pointer))))
                  (reterr msg)))
              (retok (type-fix type-arg1))))
      ((:asg-mul :asg-div)
       (b* (((unless (and (type-arithmeticp type-arg1)
                          (type-arithmeticp type-arg2)))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      (:asg-rem (b* (((unless (and (type-integerp type-arg1)
                                   (type-integerp type-arg2)))
                      (reterr msg)))
                  (retok (type-fix type-arg1))))
      ((:asg-add :asg-sub)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (or (and (type-arithmeticp type1)
                              (type-arithmeticp type2))
                         (and (type-case type1 :pointer)
                              (type-integerp type2))))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      ((:asg-shl :asg-shr :asg-and :asg-xor :asg-ior)
       (b* (((unless (and (type-integerp type-arg1)
                          (type-integerp type-arg2)))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      (t (prog2$ (impossible) (reterr t)))))
  :guard-hints (("Goal" :in-theory (disable (:e tau-system))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-sizeof/alignof ((expr exprp) (type typep))
  :guard (or (expr-case expr :sizeof)
             (expr-case expr :alignof))
  :returns (mv erp (type1 typep))
  :short "Validate a @('sizeof') operator applied to a type name,
          or an @('alignof') operator,
          given the type denoted by the argument type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('sizeof') operator applied to an type name
     requires a non-function complete type [C:6.5.3.4/1].
     In our current approximate type system,
     we just exclude function types,
     but we do not have a notion of complete types yet.
     The result has type @('size_t') [C:6.5.3.4/5],
     whose definition is implementation-defined,
     so for now we just return the unknown type;
     we will need to extend implementation environments
     with information about the definition of @('size_t')."))
  (b* (((reterr) (irr-type))
       ((when (type-case type :function))
        (reterr (msg "In the ~s0 type expression ~x1, ~
                      the argument ~x2 is a function type."
                     (case (expr-kind expr)
                       (:sizeof "sizeof")
                       (:alignof "_Alignof")
                       (t (impossible)))
                     (expr-fix expr)
                     (type-fix type)))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cast ((expr exprp) (type-cast typep) (type-arg typep))
  :guard (expr-case expr :cast)
  :returns (mv erp (type1 typep))
  :short "Validate a cast expression,
          given the type denoted by the type name
          and the type of the argument expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type name must denote the void type or a scalar type [C:6.5.4/2].
     The expression must have scalar type [C:6.5.4/2].
     Since scalar types involve pointers,
     we perform array-to-pointer and function-to-pointer conversions.
     The result is the type denoted by the type name."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-cast :unknown)
                  (type-case type-arg :unknown)))
        (retok (type-unknown)))
       (type1-arg (type-fpconvert (type-apconvert type-cast)))
       ((unless (or (type-case type-cast :void)
                    (type-scalarp type-cast)))
        (reterr (msg "In the cast expression ~x0, ~
                      the cast type is ~x1."
                     (expr-fix expr) (type-fix type-cast))))
       ((unless (type-scalarp type1-arg))
        (reterr (msg "In the cast expression ~x0, ~
                      the argument expression has type ~x1."
                     (expr-fix expr) (type-fix type-arg)))))
    (retok (type-fix type-cast)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cond ((expr exprp)
                    (type-test typep)
                    (type-then typep)
                    (type-else typep)
                    (ienv ienvp))
  :guard (expr-case expr :cond)
  :returns (mv erp (type typep))
  :short "Validate a conditional expression,
          given types for its operands."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first operand must have scalar type [C:6.5.15/2].
     In our currently approximate type system,
     the other two operands must have
     both arithmetic type,
     or both the structure type,
     or both the union type,
     or both the void type,
     or both the pointer type
     [C:6.5.15/3].
     The type of the result is
     the one from the usual arithmetic converions
     in the first case,
     and the common type in the other cases
     [C:6.5.15/5].
     Since pointers may be involved, we need to perform
     array-to-pointer and function-to-pointer conversions."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-test :unknown)
                  (type-case type-then :unknown)
                  (type-case type-else :unknown)))
        (retok (type-unknown)))
       (type1 (type-fpconvert (type-apconvert type-test)))
       (type2 (type-fpconvert (type-apconvert type-then)))
       (type3 (type-fpconvert (type-apconvert type-else)))
       ((unless (type-scalarp type1))
        (reterr (msg "In the conditional expression ~x0, ~
                      the first operand has type ~x1."
                     (expr-fix expr) (type-fix type-test))))
       ((when (and (type-arithmeticp type2)
                   (type-arithmeticp type3)))
        (retok (type-uaconvert type2 type3 ienv)))
       ((when (and (type-case type2 :struct)
                   (type-case type3 :struct)))
        (retok (type-struct)))
       ((when (and (type-case type2 :union)
                   (type-case type3 :union)))
        (retok (type-union)))
       ((when (and (type-case type2 :pointer)
                   (type-case type3 :pointer)))
        (retok (type-pointer))))
    (reterr (msg "In the conditional expression ~x0, ~
                  the second operand has type ~x1 ~
                  and the third operand has type ~x2."
                 (expr-fix expr) (type-fix type-then) (type-fix type-else))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-type-spec-list-residual ((tyspecs type-spec-listp))
  :guard (and (type-spec-list-unambp tyspecs)
              (consp tyspecs))
  :returns (mv erp (type typep))
  :short "Validate a residual list of type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type specifiers occur as elements of
     declaration specifiers
     (see grammar rule @('declaration-specifiers'))
     and specifier and qualifier lists
     (see grammar rule @('specifier-qualifier-list')).
     As we validate those two kinds of lists,
     when we encounter type specifiers that, like for example @('void'),
     uniquely determine a type,
     and must be the only type specifier occurring in the list,
     we perform all the necessary checks on type specifiers
     as part of validating those lists.")
   (xdoc::p
    "But when instead we encounter type specifiers that
     do not uniquely and solely determine a type,
     such as @('unsigned') and @('char'),
     we collect all of them and then we call this validation function
     to validate whether this residual sequence of type specifier
     determines a unique type or not.
     If it does not, it is an error,
     because every type specifier sub-sequence
     of a sequence of declaration specifiers
     or of a sequence of specifiers and qualifiers
     must denote a type.
     Here, `residual' refers not to the list of type specifiers,
     which are in fact all the ones occurring as sub-sequence,
     but to the fact that we perform the ``residual'' validation.")
   (xdoc::p
    "Here we accept all the lists of type specifiers in [C:6.7.2/2]
     except for those that are singletons determining a type
     and that may not be part of longer sequences."))
  (b* (((reterr) (irr-type)))
    (cond
     ((type-spec-list-char-p tyspecs)
      (retok (type-char)))
     ((type-spec-list-signed-char-p tyspecs)
      (retok (type-schar)))
     ((type-spec-list-unsigned-char-p tyspecs)
      (retok (type-uchar)))
     ((or (type-spec-list-short-p tyspecs)
          (type-spec-list-signed-short-p tyspecs)
          (type-spec-list-short-int-p tyspecs)
          (type-spec-list-signed-short-int-p tyspecs))
      (retok (type-sshort)))
     ((or (type-spec-list-unsigned-short-p tyspecs)
          (type-spec-list-unsigned-short-int-p tyspecs))
      (retok (type-ushort)))
     ((or (type-spec-list-int-p tyspecs)
          (type-spec-list-signed-p tyspecs)
          (type-spec-list-signed-int-p tyspecs))
      (retok (type-sint)))
     ((or (type-spec-list-unsigned-p tyspecs)
          (type-spec-list-unsigned-int-p tyspecs))
      (retok (type-uint)))
     ((or (type-spec-list-long-p tyspecs)
          (type-spec-list-signed-long-p tyspecs)
          (type-spec-list-long-int-p tyspecs)
          (type-spec-list-signed-long-int-p tyspecs))
      (retok (type-slong)))
     ((or (type-spec-list-unsigned-long-p tyspecs)
          (type-spec-list-unsigned-long-int-p tyspecs))
      (retok (type-ulong)))
     ((or (type-spec-list-long-long-p tyspecs)
          (type-spec-list-signed-long-long-p tyspecs)
          (type-spec-list-long-long-int-p tyspecs)
          (type-spec-list-signed-long-long-int-p tyspecs))
      (retok (type-sllong)))
     ((or (type-spec-list-unsigned-long-long-p tyspecs)
          (type-spec-list-unsigned-long-long-int-p tyspecs))
      (retok (type-ullong)))
     ((type-spec-list-float-p tyspecs)
      (retok (type-float)))
     ((type-spec-list-double-p tyspecs)
      (retok (type-double)))
     ((type-spec-list-long-double-p tyspecs)
      (retok (type-ldouble)))
     ((type-spec-list-float-complex-p tyspecs)
      (retok (type-floatc)))
     ((type-spec-list-double-complex-p tyspecs)
      (retok (type-doublec)))
     ((type-spec-list-long-double-complex-p tyspecs)
      (retok (type-ldoublec)))
     (t (reterr (msg "The type specifier sequence ~x0 is invalid."
                     (type-spec-list-fix tyspecs))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stor-spec-list ((storspecs stor-spec-listp)
                              (ident identp)
                              (type typep)
                              (fundefp booleanp)
                              (table valid-tablep))
  :returns (mv erp
               (typedefp booleanp)
               (linkage linkagep)
               (lifetime? lifetime-optionp))
  :short "Validate a list of storage class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is called on the sub-list of storage class specifiers
     of a list of declaration specifiers,
     after determining the identifier being declared and its type,
     which are both passed as input to this function,
     along with the current validation table..")
   (xdoc::p
    "Only a few sequences of storage class specifiers are allowed [C:6.7.1/2],
     also depending on whether the declaration is in a block or file scope
     [C:6.7.1/3],
     which we can see from the validation table.
     Each allowed sequence of storage class specifiers may determine
     that a @('typedef') name is being declared,
     or that an object or function is being declared,
     with a certain linkage and lifetime.
     So we return as results
     a flag saying that a @('typedef') name is being declared,
     a linkage,
     and an optional lifetime.
     We explain all the possibilities below,
     for each allowed sequence of storage class specifiers.")
   (xdoc::p
    "If the storage class specifier sequence is @('typedef'),
     a @('typedef') name is being declared,
     so we return @('t') as the @('typedef') flag result.
     This is the only case in which this result is @('t');
     in all other cases, that result is @('nil'),
     because in all other cases we are not declaring a @('typedef') name.
     A @('typedef') name (which is an identifier) has no linkage
     [C:6.2.2/1] [C:6.2.2/6].
     Since lifetime (i.e. storage duration) only applies to objects [C:6.2.4/1],
     we return @('nil') as lifetime, i.e. no lifetime.")
   (xdoc::p
    "If the storage class specifier sequence is @('extern'),
     linkage may be external or not,
     based on whether there is already
     a declaration of the same identifiers in scope or not
     and whether that previous declaration specifies a linkage or not
     [C:6.2.2/4].
     So we look up the identifier in the validation table.
     If nothing is found, then the linkage is external.
     If an object or function is found with external or internal linkage,
     then the linkage of the new declaration
     is the one of that object or function;
     the two declarations must refer to the same object or function,
     but we check elsewhere that the two declarations
     are consistent with each other.
     If an object or function is found with no linkage,
     or a @('typedef') is found (which has no linkage [C:6.2.2/6]),
     or an enumeration constant is found (which has no linkage [C:6.2.2/6]),
     then the linkage of the new declaration is external;
     the two declarations must refer to different entities.
     In any case, the linkage is always either internal or external.
     If the type is that of a function,
     there is no lifetime, which only applies to objects [C:6.2.4/1].
     If the type is that of an object,
     the lifetime is static [C:6.2.4/3],
     because as mentioned above the linkage is always internal or external.")
   (xdoc::p
    "If the storage class specifier sequence is
     @('extern _Thread_local') or @('_Thread_local extern'),
     then the type must not be that of a function [C:6.7.1/4].
     The lifetime is thread [C:6.2.4/4],
     while the linkage is determined as in the @('extern') case above.")
   (xdoc::p
    "If the storage class specifier sequence is @('static'),
     things differ whether the identifier is declared
     in the file scope or in a block scope.
     If we are in the file scope, the linkage is internal [C:6.2.2/3].
     If we are in a block scope, it depends on whether
     we are declaring an object or a function.
     If it is an object, it has no linkage [C:6.2.2/6],
     because it does not have @('extern').
     If it is a function it is an error [C:6.7.1/7].
     The lifetime is absent (i.e. @('nil')) for a function,
     since lifetimes only apply to objects [C:6.2.4/1];
     it is static otherwise [C:6.2.4/3].")
   (xdoc::p
    "If the storage class specifier sequence is
     @('static _Thread_local') or @('_Thread_local static'),
     then the type must not be that of a function [C:6.7.1/4].
     Linkage is determined as in the previous case.
     The lifetime is thread.")
   (xdoc::p
    "If the storage class specifier sequence is @('_Thread_local'),
     the type must not be one of a function [C:6.7.1/4].
     Since we must have an object, the lifetime is thread.
     If we are in a block scope, it is an error,
     because in that case there must also be @('extern') or @('static')
     [C:6.7.1/3].
     Since we cannot be in a block scope, we must be in the file scope.
     [C:6.2.2] does not seem to specify the linkage for this case,
     perhaps because @('_Thread_local') was added at some point,
     but [C:6.2.2] was not updated accordingly:
     [C:6.2.2/5] specifies external linkage
     for the case of an object in a file scope without storage class specifiers,
     but this should be probably interpreted as
     including the @('_Thread_local') case,
     which makes sense, and is consistent with some clearer wording
     in the newly released C23 standard.")
   (xdoc::p
    "If the storage class specifier sequence is @('auto') or @('register'),
     we must not be in a file scope [C:6.9/2];
     so we must be in a block scope.
     The type must not be one of a function.
     Thus, it has no linkage [C:6.2.2/6].
     The lifetime is automatic [C:6.2.4/5].")
   (xdoc::p
    "If there are no storage class specifiers (i.e. the sequence is empty),
     things differ based on
     whether the identifier declares an object or a function,
     and whether we are in the file scope or a block scope.
     If the type is that of a function,
     linkage is determined as if it had the @('extern') specifier [C:6.2.2/5];
     in this case, there is no lifetime.
     For an object with file scope,
     the linkage is external [C:6.2.2/5],
     and thus the lifetime is static [C:6.2.4/3].
     For an object block scope, there is no linkage [C:6.2.2/6],
     and the lifetime is automatic [C:6.2.4/5].")
   (xdoc::p
    "We prove that if @('typedefp') is @('t')
     then @('lifetime?') is @('nil') and there is no linkage.
     We prove that if a function is being declared,
     then the linkage is always external or internal,
     and that the only possible sequences of storage class specifiers
     are @('extern'), @('static'), and nothing.")
   (xdoc::p
    "The @('fundefp') input is @('t') when this function is called on
     the storage class specifiers of a function definition.
     The reason is that, when this function is called in that situation,
     the validation table contains a block scope for the function body,
     but the storage class specifiers checked here are in the file scope:
     so checking the validation table to determine,
     for the purpose of validating the storage class specifiers,
     whether we are in a block or file scope,
     would give an incorrect result.
     So we use the @('fundefp') flag to adjust the check.
     This flag is @('nil') in all other situations."))
  (b* (((reterr) nil (irr-linkage) nil))
    (cond
     ((stor-spec-list-typedef-p storspecs)
      (retok t (linkage-none) nil))
     ((stor-spec-list-extern-p storspecs)
      (b* ((linkage
            (b* (((mv info? &) (valid-lookup-ord ident table))
                 ((unless info?)
                  (linkage-external))
                 ((unless (valid-ord-info-case info? :objfun))
                  (linkage-external))
                 (previous-linkage (valid-ord-info-objfun->linkage info?)))
              (if (linkage-case previous-linkage :none)
                  (linkage-external)
                previous-linkage)))
           (lifetime? (if (type-case type :function)
                          nil
                        (lifetime-static))))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-extern-threadloc-p storspecs)
      (b* (((when (type-case type :function))
            (reterr (msg "The storage class specifier '_Thread_local' ~
                          cannot be used in the declaration of
                          the function ~x0."
                         (ident-fix ident))))
           (linkage
            (b* (((mv info? &) (valid-lookup-ord ident table))
                 ((unless info?)
                  (linkage-external))
                 ((unless (valid-ord-info-case info? :objfun))
                  (linkage-external))
                 (previous-linkage (valid-ord-info-objfun->linkage info?)))
              (if (linkage-case previous-linkage :none)
                  (linkage-external)
                previous-linkage))))
        (retok nil linkage (lifetime-thread))))
     ((stor-spec-list-static-p storspecs)
      (b* ((block-scope-p (and (> (valid-table-num-scopes table) 1)
                               (not fundefp)))
           ((when (and block-scope-p
                       (type-case type :function)))
            (reterr (msg "The storage class specifier 'static' ~
                          cannot be used in the declaration of ~
                          the function ~x0."
                         (ident-fix ident))))
           (linkage (if block-scope-p
                        (linkage-none)
                      (linkage-internal)))
           (lifetime? (if (type-case type :function)
                          nil
                        (lifetime-static))))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-static-threadloc-p storspecs)
      (b* (((when (type-case type :function))
            (reterr (msg "The storage class specifier '_Thread_local' ~
                          cannot be used in the declaration of
                          the function ~x0."
                         (ident-fix ident))))
           (block-scope-p (and (> (valid-table-num-scopes table) 1)
                               (not fundefp)))
           (linkage (if block-scope-p
                        (linkage-none)
                      (linkage-internal)))
           (lifetime? (lifetime-thread)))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-threadloc-p storspecs)
      (b* (((when (type-case type :function))
            (reterr (msg "The storage class specifier '_Thread_local' ~
                          cannot be used in the declaration of
                          the function ~x0."
                         (ident-fix ident))))
           ((when (and (> (valid-table-num-scopes table) 1)
                       (not fundefp)))
            (reterr (msg "The storage class specifier '_Thread_local' ~
                          cannot be used in a block scope ~
                          without 'extern' or 'static', ~
                          for the declaration of the object ~x0."
                         (ident-fix ident)))))
        (retok nil (linkage-external) (lifetime-thread))))
     ((or (stor-spec-list-auto-p storspecs)
          (stor-spec-list-register-p storspecs))
      (b* (((when (type-case type :function))
            (reterr (msg "The storage class specifier '~s0' ~
                          cannot be used in the declaration of
                          the function ~x1."
                         (if (stor-spec-list-auto-p storspecs)
                             "auto"
                           "register")
                         (ident-fix ident))))
           ((unless (and (> (valid-table-num-scopes table) 1)
                         (not fundefp)))
            (reterr (msg "The storage class specifier '~s0' ~
                          cannot be used in the file scope, ~
                          for identifier ~x1."
                         (if (stor-spec-list-auto-p storspecs)
                             "auto"
                           "register")
                         (ident-fix ident)))))
        (retok nil (linkage-none) (lifetime-auto))))
     ((endp storspecs)
      (if (type-case type :function)
          (b* (((mv info? &) (valid-lookup-ord ident table))
               ((unless info?)
                (retok nil (linkage-external) nil))
               ((unless (valid-ord-info-case info? :objfun))
                (retok nil (linkage-external) nil))
               (previous-linkage (valid-ord-info-objfun->linkage info?)))
            (if (linkage-case previous-linkage :none)
                (retok nil (linkage-external) nil)
              (retok nil previous-linkage nil)))
        (if (and (> (valid-table-num-scopes table) 1)
                 (not fundefp))
            (retok nil (linkage-none) (lifetime-auto))
          (retok nil (linkage-external) (lifetime-static)))))
     (t (reterr (msg "The storage class specifier sequence ~x0 is invalid."
                     (stor-spec-list-fix storspecs))))))
  :hooks (:fix)

  ///

  (defret no-lifetime-of-valid-stor-spec-list-when-typedef
    (implies typedefp
             (not lifetime?)))

  (defret no-linkage-of-valid-stor-spec-list-when-typedef
    (implies typedefp
             (equal (linkage-kind linkage) :none)))

  (defret ext/int-linkage-of-valid-stor-spec-when-function
    (implies (and (not erp)
                  (not typedefp)
                  (type-case type :function))
             (not (equal (linkage-kind linkage)
                         :none))))

  (defret lifetime-of-valid-stor-spec-when-object
    (implies (and (not erp)
                  (not typedefp)
                  (not (type-case type :function)))
             lifetime?))

  (defret extern/static/none-when-valid-stor-spec-list-function
    (implies (and (not erp)
                  (not typedefp)
                  (type-case type :function))
             (or (stor-spec-list-extern-p storspecs)
                 (stor-spec-list-static-p storspecs)
                 (endp storspecs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines valid-exprs/decls/stmts
  :short "Validate expressions, declarations, statements,
          and related artifacts."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since we currently have an approximate model of types,
     with the `unknown type' among them (see @(tsee type)),
     wherever a certain kind of type is required (e.g. an integer type),
     we also need to allow the unknown type,
     because that could the required kind of type.
     Our currently approximate validator must not reject valid programs,
     because it needs to deal with any practical programs we encounter.
     Eventually, when we refine our validator and our model of types
     to no longer be approximate and include the unknown type,
     we will rescind this extra allowance for the unknown type."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr ((expr exprp) (table valid-tablep) (ienv ienvp))
    :guard (expr-unambp expr)
    :returns (mv erp
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful,
       we return the type of the expression,
       the set of types returned by @('return') statements in the expression,
       and a possibly updated validation table.
       The reason for the set of @('return') types
       is that, as a GCC extension, an expression may consist of a statement,
       and the validation of statements involves sets of @('return') types:
       see @(tsee valid-stmt).")
     (xdoc::p
      "For now we do not distinguish lvalues [C:6.3.2.1/1].
       To do that, we will introduce a richer notion of expression type
       that includes a type and also
       an indication of whether the expression is an lvalue;
       we will also perform lvalue conversion where needed.
       This is already done in @(see c::static-semantics),
       for the subset of C that is formalized.")
     (xdoc::p
      "We use separate functions to validate the various kinds of expressions,
       to minimize case splits in the mutually recursive clique of functions.
       But we need to calculate types for sub-expressions recursively here,
       and pass the types to those separate functions.")
     (xdoc::p
      "Expressions without subexpressions return
       the empty set of @('return') types.
       Other expressions return the union of the sets
       obtained from validating the sub-constructs.")
     (xdoc::p
      "To validate a compound literal, first we validate the type name,
       obtaining a type if that validation is successful.
       Then we validate the initializers with optional designations,
       passing the type because in general their validation depends on that;
       however, in our currently approximate type system,
       all the information we need back from
       the validation of the initializers with optional designations
       is the possibly updated validation table.
       The type of the compound literal is the one denoted by the type name.
       We also need to pass an indication of
       the storage duration (i.e. lifetime) of the object,
       which is either static or automatic,
       based on whether the compound literal occurs
       outside or inside the body of a function [C:6.5.2.5/5],
       which we can see based on whether
       the number of scopes in the validation table is 1 or not
       (recall that this number is never 0).")
     (xdoc::p
      "In a conditional expression, the second operand may be absent;
       this is a GCC extension.
       However, for validation, we normalize the situation
       by replicating the type of the first operand for the second operand,
       when there is no second operand,
       according to the semantics of the absence of the second operand.")
     (xdoc::p
      "For the comma operator, we validate both sub-expressions,
       and the resulting type is the one of the second sub-expression
       [C:6.5.17/2].")
     (xdoc::p
      "For a statement expression, we validate the block items.
       If a type is returned, that is the type of the expression.
       Otherwise, the expression has type @('void'),
       as described in the GCC documentation of statement expressions.")
     (xdoc::p
      "The GCC extension @('__builtin_types_compatible_p')
       is validated by validating its argument type names.
       The result is @('signed int'), according to the GCC manual.")
     (xdoc::p
      "For the GCC extension @('__builtin_offsetof'),
       for now we just validate
       its component type names and expressions (if any),
       but without checking that the member designators are valid;
       for that, we need a more refined type system.
       The result has type @('size_t') [C:7.19],
       whose definition is implementation-dependent,
       and thus for now we return the unknown type."))
    (b* (((reterr) (irr-type) nil (irr-valid-table)))
      (expr-case
       expr
       :ident (b* (((erp type) (valid-var expr.ident table)))
                (retok type nil (valid-table-fix table)))
       :const (b* (((erp type) (valid-const expr.const table ienv)))
                (retok type nil (valid-table-fix table)))
       :string (b* (((erp type) (valid-stringlit-list expr.strings)))
                 (retok type nil (valid-table-fix table)))
       :paren (valid-expr expr.inner table ienv)
       :gensel (b* (((erp type-control types-control table)
                     (valid-expr expr.control table ienv))
                    ((erp type-alist types-assoc table)
                     (valid-genassoc-list expr.assocs table ienv))
                    ((erp type) (valid-gensel expr type-control type-alist)))
                 (retok type (set::union types-control types-assoc) table))
       :arrsub (b* (((erp type-arg1 types-arg1 table)
                     (valid-expr expr.arg1 table ienv))
                    ((erp type-arg2 types-arg2 table)
                     (valid-expr expr.arg2 table ienv))
                    ((erp type) (valid-arrsub expr type-arg1 type-arg2)))
                 (retok type (set::union types-arg1 types-arg2) table))
       :funcall (b* (((erp type-fun types-fun table)
                      (valid-expr expr.fun table ienv))
                     ((erp types-arg rtypes-arg table)
                      (valid-expr-list expr.args table ienv))
                     ((erp type) (valid-funcall expr type-fun types-arg)))
                  (retok type (set::union types-fun rtypes-arg) table))
       :member (b* (((erp type-arg types-arg table)
                     (valid-expr expr.arg table ienv))
                    ((erp type) (valid-member expr type-arg)))
                 (retok type types-arg table))
       :memberp (b* (((erp type-arg types-arg table)
                      (valid-expr expr.arg table ienv))
                     ((erp type) (valid-memberp expr type-arg)))
                  (retok type types-arg table))
       :complit (b* (((erp type types-type table)
                      (valid-tyname expr.type table ienv))
                     ((when (type-case type :function))
                      (reterr (msg "The type of the compound literal ~x0 ~
                                    is a function type."
                                   (expr-fix expr))))
                     ((when (type-case type :void))
                      (reterr (msg "The type of the compound literal ~x0 ~
                                    is void."
                                   (expr-fix expr))))
                     (lifetime (if (> (valid-table-num-scopes table) 1)
                                   (lifetime-auto)
                                 (lifetime-static)))
                     ((erp types-elems table)
                      (valid-desiniter-list
                       expr.elems type lifetime table ienv)))
                  (retok type (set::union types-type types-elems) table))
       :unary (b* (((erp type-arg types-arg table)
                    (valid-expr expr.arg table ienv))
                   ((erp type) (valid-unary expr expr.op type-arg ienv)))
                (retok type types-arg table))
       :sizeof (b* (((erp type types table)
                     (valid-tyname expr.type table ienv))
                    ((erp type1) (valid-sizeof/alignof expr type)))
                 (retok type1 types table))
       :alignof (b* (((erp type types table)
                      (valid-tyname expr.type table ienv))
                     ((erp type1) (valid-sizeof/alignof expr type)))
                  (retok type1 types table))
       :cast (b* (((erp type-cast types-cast table)
                   (valid-tyname expr.type table ienv))
                  ((erp type-arg types-arg table)
                   (valid-expr expr.arg table ienv))
                  ((erp type) (valid-cast expr type-cast type-arg)))
               (retok type (set::union types-cast types-arg) table))
       :binary (b* (((erp type-arg1 types-arg1 table)
                     (valid-expr expr.arg1 table ienv))
                    ((erp type-arg2 types-arg2 table)
                     (valid-expr expr.arg2 table ienv))
                    ((erp type)
                     (valid-binary expr expr.op type-arg1 type-arg2 ienv)))
                 (retok type (set::union types-arg1 types-arg2) table))
       :cond (b* (((erp type-test types-test table)
                   (valid-expr expr.test table ienv))
                  ((erp type-then? types-then table)
                   (valid-expr-option expr.then table ienv))
                  (type-then (or type-then? type-test))
                  ((erp type-else types-else table)
                   (valid-expr expr.else table ienv))
                  ((erp type)
                   (valid-cond expr type-test type-then type-else ienv)))
               (retok type
                      (set::union types-test (set::union types-then types-else))
                      table))
       :comma (b* (((erp & types1 table) (valid-expr expr.first table ienv))
                   ((erp type types2 table) (valid-expr expr.next table ienv)))
                (retok type (set::union types1 types2) table))
       :stmt (b* (((erp types type? table)
                   (valid-block-item-list expr.items table ienv))
                  (type (or type? (type-void))))
               (retok type types table))
       :tycompat (b* (((erp & types1 table)
                       (valid-tyname expr.type1 table ienv))
                      ((erp & types2 table)
                       (valid-tyname expr.type2 table ienv)))
                   (retok (type-sint) (set::union types1 types2) table))
       :offsetof (b* (((erp & types table) (valid-tyname expr.type table ienv))
                      ((erp more-types table)
                       (valid-member-designor expr.member table ienv)))
                   (retok (type-unknown) (set::union types more-types) table))
       :va-arg (b* (((erp & list-types table)
                     (valid-expr expr.list table ienv))
                    ((erp & type-types table)
                     (valid-tyname expr.type table ienv)))
                 (retok (type-unknown)
                        (set::union list-types type-types)
                        table))
       :extension (valid-expr expr.expr table ienv)
       :otherwise (prog2$ (impossible) (reterr t))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-list ((exprs expr-listp) (table valid-tablep) (ienv ienvp))
    :guard (expr-list-unambp exprs)
    :returns (mv erp
                 (types type-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate all the expressions, one after the other,
       and we return the resulting types, in the same order.
       We also return the union of all the @('return') types.
       We also return a possibly updated validation table."))
    (b* (((reterr) nil nil (irr-valid-table))
         ((when (endp exprs)) (retok nil nil (valid-table-fix table)))
         ((erp type return-types table)
          (valid-expr (car exprs) table ienv))
         ((erp types more-return-types table)
          (valid-expr-list (cdr exprs) table ienv)))
      (retok (cons type types)
             (set::union return-types more-return-types)
             table))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-option ((expr? expr-optionp)
                             (table valid-tablep)
                             (ienv ienvp))
    :guard (expr-option-unambp expr?)
    :returns (mv erp
                 (type? type-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no expression,
       we return @('nil') as the optional type,
       we return the empty set of @('return') types,
       and the validation table unchanged."))
    (b* (((reterr) nil nil (irr-valid-table)))
      (expr-option-case
       expr?
       :some (valid-expr expr?.val table ienv)
       :none (retok nil nil (valid-table-fix table))))
    :measure (expr-option-count expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr ((cexpr const-exprp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (const-expr-unambp cexpr)
    :returns (mv erp
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "Besides being valid expressions,
       constant expression must satisfy other requirements [C:6.6].
       Fow now we do not check these requirements,
       but when we do we may need to extend this validation function
       to return not only a type but also a value,
       namely the value of the constant expression."))
    (b* (((reterr) (irr-type) nil (irr-valid-table)))
      (valid-expr (const-expr->expr cexpr) table ienv))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr-option ((cexpr? const-expr-optionp)
                                   (table valid-tablep)
                                   (ienv ienvp))
    :guard (const-expr-option-unambp cexpr?)
    :returns (mv erp
                 (type? type-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no constant expression,
       we return @('nil') as the optional type,
       we return the empty set of @('return') types,
       and the validation table unchanged."))
    (b* (((reterr) nil nil (irr-valid-table)))
      (const-expr-option-case
       cexpr?
       :some (valid-const-expr cexpr?.val table ienv)
       :none (retok nil nil (valid-table-fix table))))
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc ((genassoc genassocp)
                          (table valid-tablep)
                          (ienv ienvp))
    :guard (genassoc-unambp genassoc)
    :returns (mv erp
                 (tyname-type type-optionp)
                 (expr-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a generic association."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the generic association has a type name,
       we validate it and return the type that it denotes.
       If the generic association has @('default'),
       we return @('nil') as the @('tyname-type') result.
       Either way, we validate the expression, and return its type."))
    (b* (((reterr) nil (irr-type) nil (irr-valid-table)))
      (genassoc-case
       genassoc
       :type (b* (((erp tyname-type tyname-types table)
                   (valid-tyname genassoc.type table ienv))
                  ((erp expr-type expr-types table)
                   (valid-expr genassoc.expr table ienv)))
               (retok tyname-type
                      expr-type
                      (set::union tyname-types expr-types)
                      table))
       :default (b* (((erp expr-type expr-types table)
                      (valid-expr genassoc.expr table ienv)))
                  (retok nil expr-type expr-types table))))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc-list ((genassocs genassoc-listp)
                               (table valid-tablep)
                               (ienv ienvp))
    :guard (genassoc-list-unambp genassocs)
    :returns (mv erp
                 (type-alist type-option-type-alistp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of generic associations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each generic association, one after the other.
       We put the calculated types (and optional types) into an alist,
       which we return.
       There may be repeated keys in the alist: it is a feature,
       so we can separately check their uniqueness."))
    (b* (((reterr) nil nil (irr-valid-table))
         ((when (endp genassocs)) (retok nil nil (valid-table-fix table)))
         ((erp tyname-type? expr-type types table)
          (valid-genassoc (car genassocs) table ienv))
         ((erp type-alist more-types table)
          (valid-genassoc-list (cdr genassocs) table ienv)))
      (retok (acons tyname-type? expr-type type-alist)
             (set::union types more-types)
             table))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-member-designor ((memdesign member-designorp)
                                 (table valid-tablep)
                                 (ienv ienvp))
    :guard (member-designor-unambp memdesign)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a member designator."
    (b* (((reterr) nil (irr-valid-table)))
      (member-designor-case
       memdesign
       :ident (retok nil (valid-table-fix table))
       :dot (valid-member-designor memdesign.member table ienv)
       :sub (b* (((erp types table)
                  (valid-member-designor memdesign.member table ienv))
                 ((erp & more-types table)
                  (valid-expr memdesign.index table ienv)))
              (retok (set::union types more-types) table))))
    :measure (member-designor-count memdesign))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-type-spec ((tyspec type-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (and (type-spec-unambp tyspec)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv erp
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "Type specifiers are used to specify types, as described in [C:6.7.2/2].
       Certain type specifiers individually specify a type,
       and there cannot be other type specifiers;
       an example is @('void').
       Other type specifiers may individually specify a type,
       but they may be also combined with other type specifiers
       to specify a different type;
       an example is @('signed').
       The type specifier @('_Complex') does not individually specify any type,
       and must be always combined with other type specifiers.")
     (xdoc::p
      "Given these possibilities,
       our approach is to validate type specifiers in order,
       while going through the declaration specifiers,
       or the specifier and qualifier lists,
       where they occur.
       As we go through them, we thread through two pieces of information:
       an optional type,
       non-@('nil') when a type has been definitely determined,
       and a list of type specifiers encountered so far.
       These two cannot be non-@('nil') at the same time, as the guard requires:
       if a type has been determined,
       there is no need to keep track of the type specifiers so far;
       and if we are keeping track of the type specifiers so far,
       we must not have determined a type yet.")
     (xdoc::p
      "Initially,
       the optional type and the list of type specifiers are both @('nil'),
       because we neither have encountered any type specifiers
       nor determined a type.
       If we encounter a type specifier like @('void')
       that individually denotes a type,
       we ensure that no other type specifiers were encountered before,
       and we determine the type.
       Once a type is determined, any type specifier will cause an error.
       We may get at the end without a determined type yet,
       but we will have the list of all the type specifiers,
       which is used, in another validation function,
       to determined the type if any.")
     (xdoc::p
      "Our current type system does not model atomic types,
       so for an atomic type we validate the type name
       and we regard the atomic type as denoting the same type.")
     (xdoc::p
      "For a structure or union or enumeration type specifier,
       we recursively validate their sub-structures,
       and the type is determined in all cases.")
     (xdoc::p
      "Since our currently approximate type system
       does not handle @('typedef') types,
       we just regard it as denoting an unknown type.")
     (xdoc::p
      "For now, for simplicity, we regard
       all the type specifiers that are GCC extensions
       to determine the unknown type;
       except for an empty structure type specifier,
       which determines the structure type."))
    (b* (((reterr) nil nil nil (irr-valid-table))
         ((when type?)
          (reterr (msg "Since the type ~x0 has been determined, ~
                        there must be no more type specifiers, ~
                        but ~x1 follows instead."
                       (type-option-fix type?) (type-spec-fix tyspec))))
         (same-table (valid-table-fix table))
         (ext-tyspecs (rcons (type-spec-fix tyspec)
                             (type-spec-list-fix tyspecs)))
         (msg-bad-preceding (msg "The type specifier ~x0 ~
                                  must not be preceded by ~x1."
                                 (type-spec-fix tyspec)
                                 (type-spec-list-fix tyspecs))))
      (type-spec-case
       tyspec
       :void (if (endp tyspecs)
                 (retok (type-void) nil nil same-table)
               (reterr msg-bad-preceding))
       :char (retok nil ext-tyspecs nil same-table)
       :short (retok nil ext-tyspecs nil same-table)
       :int (retok nil ext-tyspecs nil same-table)
       :long (retok nil ext-tyspecs nil same-table)
       :float (retok nil ext-tyspecs nil same-table)
       :double (retok nil ext-tyspecs nil same-table)
       :signed (retok nil ext-tyspecs nil same-table)
       :unsigned (retok nil ext-tyspecs nil same-table)
       :bool (if (endp tyspecs)
                 (retok (type-bool) nil nil same-table)
               (reterr msg-bad-preceding))
       :complex (retok nil ext-tyspecs nil same-table)
       :atomic (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                    ((erp type types table)
                     (valid-tyname tyspec.type table ienv)))
                 (retok type nil types table))
       :struct (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                    ((erp types table)
                     (valid-strunispec tyspec.spec table ienv)))
                 (retok (type-struct) nil types table))
       :union (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                   ((erp types table)
                    (valid-strunispec tyspec.spec table ienv)))
                (retok (type-union) nil types table))
       :enum (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                  ((erp types table)
                   (valid-enumspec tyspec.spec table ienv)))
               (retok (type-enum) nil types table))
       :typedef (if (endp tyspecs)
                    (retok (type-unknown) nil nil same-table)
                  (reterr msg-bad-preceding))
       :int128 (if (endp tyspecs)
                   (retok (type-unknown) nil nil same-table)
                 (reterr msg-bad-preceding))
       :float32 (if (endp tyspecs)
                    (retok (type-unknown) nil nil same-table)
                  (reterr msg-bad-preceding))
       :float32x (if (endp tyspecs)
                     (retok (type-unknown) nil nil same-table)
                   (reterr msg-bad-preceding))
       :float64 (if (endp tyspecs)
                    (retok (type-unknown) nil nil same-table)
                  (reterr msg-bad-preceding))
       :float64x (if (endp tyspecs)
                     (retok (type-unknown) nil nil same-table)
                   (reterr msg-bad-preceding))
       :float128 (if (endp tyspecs)
                     (retok (type-unknown) nil nil same-table)
                   (reterr msg-bad-preceding))
       :float128x (if (endp tyspecs)
                      (retok (type-unknown) nil nil same-table)
                    (reterr msg-bad-preceding))
       :builtin-va-list (if (endp tyspecs)
                            (retok (type-unknown) nil nil same-table)
                          (reterr msg-bad-preceding))
       :struct-empty (if (endp tyspecs)
                         (retok (type-struct) nil nil same-table)
                       (reterr msg-bad-preceding))
       :typeof-expr (if (endp tyspecs)
                        (retok (type-unknown) nil nil same-table)
                      (reterr msg-bad-preceding))
       :typeof-type (if (endp tyspecs)
                        (retok (type-unknown) nil nil same-table)
                      (reterr msg-bad-preceding))
       :auto-type (if (endp tyspecs)
                      (retok (type-unknown) nil nil same-table)
                    (reterr msg-bad-preceding))
       :otherwise (prog2$ (impossible) (reterr t))))
    :measure (type-spec-count tyspec)

    ///

    (defret type-spec-list-unambp-of-valid-type-spec
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal" :expand (valid-type-spec tyspec type? tyspecs table ienv))))

    (defret not-type-and-type-specs-of-valid-type-spec
      (not (and new-type? new-tyspecs))
      :hints
      (("Goal"
        :expand (valid-type-spec tyspec type? tyspecs table ienv)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-spec/qual ((specqual spec/qual-p)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (and (spec/qual-unambp specqual)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv erp
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a specifier or qualifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we ignore type qualifiers [C:6.7.3],
       as they do not have any impact on our approximate type system.
       We validate alignment specifiers (in a separate validation function),
       but make no use of them in our approximate type system.
       Thus, the validation of a specifier or qualifier
       returns the same results as
       the validation of a type specifier (see @(tsee valid-type-spec)).
       For now we also skip over attributes completely;
       see the ABNF grammar for @('specifier-qualifier-list')."))
    (b* (((reterr) nil nil nil (irr-valid-table)))
      (spec/qual-case
       specqual
       :typespec (valid-type-spec specqual.spec type? tyspecs table ienv)
       :typequal (retok (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        nil
                        (valid-table-fix table))
       :align (b* (((erp types table)
                    (valid-align-spec specqual.spec table ienv)))
                (retok (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       types
                       table))
       :attrib (retok (type-option-fix type?)
                      (type-spec-list-fix tyspecs)
                      nil
                      (valid-table-fix table))))
    :measure (spec/qual-count specqual)

    ///

    (defret type-spec-list-unambp-of-valid-spec/qual
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal" :expand (valid-spec/qual specqual type? tyspecs table ienv))))

    (defret not-type-and-type-specs-of-valid-spec/qual
      (not (and new-type? new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints
      (("Goal"
        :expand ((valid-spec/qual specqual nil tyspecs table ienv)
                 (valid-spec/qual specqual type? nil table ienv)))))

    (defret not-type-specs-of-valid-spec/qual-when-type
      (implies new-type?
               (not new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints (("Goal" :use not-type-and-type-specs-of-valid-spec/qual))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-spec/qual-list ((specquals spec/qual-listp)
                                (type? type-optionp)
                                (tyspecs type-spec-listp)
                                (table valid-tablep)
                                (ienv ienvp))
    :guard (and (spec/qual-list-unambp specquals)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv erp
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of specifiers and qualifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful,
       we return the type determined by
       the type specifiers in the sequence.")
     (xdoc::p
      "We validate specifiers and qualifiers from left to right,
       threading the partial results through.
       When we reach the end, if the type has not been determined yet,
       we look at the collected type specifiers and determine the type,
       via a separate validation function.
       If there are no type specifiers, but no type has been determined,
       it means that there were no type specifiers at all [C:6.7.2/2]."))
    (b* (((reterr) (irr-type) nil (irr-valid-table))
         ((when (endp specquals))
          (cond
           (type? (retok (type-option-fix type?) nil (valid-table-fix table)))
           ((consp tyspecs)
            (b* (((erp type) (valid-type-spec-list-residual tyspecs)))
              (retok type nil (valid-table-fix table))))
           (t (reterr (msg "The specifier and qualifier list ~x0 ~
                            contains no type specifiers."
                           (spec/qual-list-fix specquals))))))
         ((erp type? tyspecs types table)
          (valid-spec/qual (car specquals) type? tyspecs table ienv))
         ((erp type more-types table)
          (valid-spec/qual-list (cdr specquals) type? tyspecs table ienv)))
      (retok type (set::union types more-types) table))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-align-spec ((align align-specp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (align-spec-unambp align)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an alignment specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we just validate the type name or expression,
       possibly extending the validation table,
       but we do not check whether the alignment specifier
       is appropriate for the place where it occurs [C:6.7.5].")
     (xdoc::p
      "In the version with the expression,
       the latter must have integer type [C:6.7.5/3].
       The version with the type name
       is equivalent to @('_Alignas(_Alignof(typename))'),
       and thus we perform the same checks as in
       the @(':alignof') case of @(tsee valid-expr),
       including @(tsee valid-sizeof/alignof)."))
    (b* (((reterr) nil (irr-valid-table)))
      (align-spec-case
       align
       :alignas-type
       (b* (((erp type types table) (valid-tyname align.type table ienv))
            ((when (type-case type :function))
             (reterr (msg "In the alignment specifier ~x0, ~
                           the argument ~x2 is a function type."
                          (align-spec-fix align) type))))
         (retok types table))
       :alignas-expr
       (b* (((erp type types table) (valid-const-expr align.expr table ienv))
            ((unless (or (type-integerp type)
                         (type-case type :unknown)))
             (reterr (msg "In the alignment specifier ~x0, ~
                           the argument has type ~x1."
                          (align-spec-fix align) type))))
         (retok types table))
       :alignas-ambig (prog2$ (impossible) (reterr t))))
    :measure (align-spec-count align))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-spec ((declspec decl-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (storspecs stor-spec-listp)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (and (decl-spec-unambp declspec)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv erp
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (new-storspecs stor-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declaration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we ignore
       type qualifiers,
       function specifiers,
       and attributes.
       We validate alignment specifiers but we do not make any use of them
       in our currently approximate type system.
       We handle type specifiers similarly to @(tsee valid-spec/qual).
       In addition, we collect all the storage class specifiers
       encountered as we go through the declaration specifiers."))
    (b* (((reterr) nil nil nil nil (irr-valid-table)))
      (decl-spec-case
       declspec
       :stoclass (retok (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (rcons declspec.spec (stor-spec-list-fix storspecs))
                        nil
                        (valid-table-fix table))
       :typespec (b* (((erp type? tyspecs types table)
                       (valid-type-spec
                        declspec.spec type? tyspecs table ienv)))
                   (retok type?
                          tyspecs
                          (stor-spec-list-fix storspecs)
                          types
                          table))
       :typequal (retok (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (valid-table-fix table))
       :function (retok (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (valid-table-fix table))
       :align (b* (((erp types table)
                    (valid-align-spec declspec.spec table ienv)))
                (retok (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       (stor-spec-list-fix storspecs)
                       types
                       table))
       :attrib (retok (type-option-fix type?)
                      (type-spec-list-fix tyspecs)
                      (stor-spec-list-fix storspecs)
                      nil
                      (valid-table-fix table))
       :stdcall (retok (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       (stor-spec-list-fix storspecs)
                       nil
                       (valid-table-fix table))
       :declspec (retok (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (valid-table-fix table))))
    :measure (decl-spec-count declspec)

    ///

    (defret type-spec-list-unambp-of-valid-decl-spec
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal"
        :expand (valid-decl-spec declspec type? tyspecs storspecs table ienv))))

    (defret not-type-and-type-specs-of-valid-decl-spec
      (not (and new-type? new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints
      (("Goal"
        :expand ((valid-decl-spec declspec nil tyspecs storspecs table ienv)
                 (valid-decl-spec declspec type? nil storspecs table ienv)))))

    (defret not-type-specs-of-valid-decl-spec-when-type
      (implies new-type?
               (not new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints (("Goal" :use not-type-and-type-specs-of-valid-decl-spec))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-spec-list ((declspecs decl-spec-listp)
                                (type? type-optionp)
                                (tyspecs type-spec-listp)
                                (storspecs stor-spec-listp)
                                (table valid-tablep)
                                (ienv ienvp))
    :guard (and (decl-spec-list-unambp declspecs)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv erp
                 (type typep)
                 (all-storspecs stor-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of declaration specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return
       the type determined by the type specifiers,
       and the list of storage class specifiers
       extracted from the declaration specifiers.")
     (xdoc::p
      "We go through each element of the list,
       threading the partial results through.
       When we reach the end of the list,
       if a type has been determined, we return it.
       Otherwise, we use a separate function to attempt to determine it
       from the collected type specifiers."))
    (b* (((reterr) (irr-type) nil nil (irr-valid-table))
         ((when (endp declspecs))
          (cond
           (type? (retok (type-option-fix type?)
                         (stor-spec-list-fix storspecs)
                         nil
                         (valid-table-fix table)))
           ((consp tyspecs)
            (b* (((erp type) (valid-type-spec-list-residual tyspecs)))
              (retok type
                     (stor-spec-list-fix storspecs)
                     nil
                     (valid-table-fix table))))
           (t (reterr (msg "The declaration specifiers ~x0 ~
                            contain no type specifiers."
                           (decl-spec-list-fix declspecs))))))
         ((erp type? tyspecs storspecs types table)
          (valid-decl-spec (car declspecs) type? tyspecs storspecs table ienv))
         ((erp type storspecs more-types table)
          (valid-decl-spec-list
           (cdr declspecs) type? tyspecs storspecs table ienv)))
      (retok type storspecs (set::union types more-types) table))
    :measure (decl-spec-list-count declspecs)

    ///

    (more-returns
     (all-storspecs true-listp :rule-classes :type-prescription)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer ((initer initerp)
                        (target-type typep)
                        (lifetime lifetimep)
                        (table valid-tablep)
                        (ienv ienvp))
    :guard (and (initer-unambp initer)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as input is
       the type of the object being initialized,
       which must not be a function or void type [C:6.7.9/3].
       The lifetime kind passed as input is
       the one of the object being initialized.")
     (xdoc::p
      "If the target type is a scalar,
       the initializer must be either a single expression,
       or a singleton initializer list without designators
       [C:6.7.9/11].
       The latter is an expression enclosed in braces;
       experiments show that the final comma is allowed.
       The same constraints as in assignments apply here
       [C:6.7.9/11] [C:6.5.16.1/1].
       We perform array-to-pointer and function-to-pointer conversions
       on the expression, as pointers may be required.")
     (xdoc::p
      "If the target type is the structure or union type,
       the initializer is a single expression,
       and the object has automatic storage duration,
       that expression must also have the structure or union type
       [C:6.7.9/13].")
     (xdoc::p
      "If the target type is an array of characters (of various types),
       the initializer may be a single string literal,
       subject to some constraints [C:6.7.9/14] [C:6.7.9/15].
       In our currently approximated type system,
       we must allow any kind of string literal with any array target type.")
     (xdoc::p
      "If the target type is an aggregate or union type,
       and the initializer is a brace-enclosed list,
       then we process the elements of the list,
       via a separate validation function
       [C:6.7.9/16] [C:6.7.9/17] [C:6.7.9/18].")
     (xdoc::p
      "If none of the case above holds, validation fails."))
    (b* (((reterr) nil (irr-valid-table)))
      (cond
       ((type-case target-type :unknown)
        (initer-case
         initer
         :single (b* (((erp & types table) (valid-expr initer.expr table ienv)))
                   (retok types table))
         :list (valid-desiniter-list
                initer.elems (type-unknown) lifetime table ienv)))
       ((type-scalarp target-type)
        (b* (((erp expr)
              (b* (((reterr) (irr-expr)))
                (initer-case
                 initer
                 :single (mv nil initer.expr)
                 :list (b* (((unless (and (consp initer.elems)
                                          (endp (cdr initer.elems))))
                             (mv (msg "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is not a singleton."
                                      (initer-fix initer)
                                      (type-fix target-type))
                                 (irr-expr)))
                            ((desiniter desiniter) (car initer.elems))
                            ((unless (endp desiniter.designors))
                             (mv (msg "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is a singleton ~
                                       but it has designators."
                                      (initer-fix initer)
                                      (type-fix target-type))
                                 (irr-expr)))
                            ((unless (initer-case desiniter.initer :single))
                             (mv (msg "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is a singleton without designators ~
                                       but the inner initializer ~
                                       is not a single expression."
                                      (initer-fix initer)
                                      (type-fix target-type))
                                 (irr-expr))))
                         (mv nil (initer-single->expr desiniter.initer))))))
             ((erp init-type types table) (valid-expr expr table ienv))
             (type (type-fpconvert (type-apconvert init-type)))
             ((unless (or (and (or (type-arithmeticp target-type)
                                   (type-case target-type :unknown))
                               (or (type-arithmeticp type)
                                   (type-case type :unknown)))
                          (and (or (type-case target-type :pointer)
                                   (type-case target-type :bool)
                                   (type-case target-type :unknown))
                               (or (type-case type :pointer)
                                   (type-case type :unknown)))))
              (reterr (msg "The initializer ~x0 ~
                            for the target type ~x1 ~
                            has type ~x2."
                           (initer-fix initer)
                           (type-fix target-type)
                           init-type))))
          (retok types table)))
       ((and (or (type-case target-type :struct)
                 (type-case target-type :union))
             (initer-case initer :single)
             (lifetime-case lifetime :auto))
        (b* (((erp type types table)
              (valid-expr (initer-single->expr initer) table ienv))
             ((unless (type-equiv type target-type))
              (reterr (msg "The initializer ~x0 ~
                            for the target type ~x1 ~
                            of an object in automatic storage ~
                            has type ~x2."
                           (initer-fix initer)
                           (type-fix target-type)
                           type))))
          (retok types table)))
       ((and (type-case target-type :array)
             (initer-case initer :single)
             (expr-case (initer-single->expr initer) :string))
        (b* (((erp &) (valid-stringlit-list
                       (expr-string->strings (initer-single->expr initer)))))
          (retok nil (valid-table-fix table))))
       ((and (or (type-aggregatep target-type)
                 (type-case target-type :union))
             (initer-case initer :list))
        (valid-desiniter-list
         (initer-list->elems initer) (type-unknown) lifetime table ienv))
       (t (reterr (msg "The initializer ~x0 ~
                        for the target type ~x1 ~
                        is disallowed."
                       (initer-fix initer) (type-fix target-type))))))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer-option ((initer? initer-optionp)
                               (target-type typep)
                               (lifetime? lifetime-optionp)
                               (table valid-tablep)
                               (ienv ienvp))
    :guard (and (initer-option-unambp initer?)
                (or (not initer?)
                    lifetime?)
                (or (not initer?)
                    (not (type-case target-type :function)))
                (or (not initer?)
                    (not (type-case target-type :void))))
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no initializer, validation succeeds.
       Otherwise, we validate the initializer.")
     (xdoc::p
      "The guard on the target type is weakened,
       compared to @(tsee valid-initer):
       if there is no initializer, the type can be anything,
       because the restriction applies only to initializers [C:6.7.9/3]."))
    (b* (((reterr) nil (irr-valid-table)))
      (initer-option-case
       initer?
       :some (valid-initer initer?.val
                           target-type
                           (lifetime-option-fix lifetime?)
                           table
                           ienv)
       :none (retok nil (valid-table-fix table))))
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter ((desiniter desiniterp)
                           (target-type typep)
                           (lifetime lifetimep)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (and (desiniter-unambp desiniter)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer with optional designation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the type
       that the list of designators must be applicable to."))
    (b* (((reterr) nil (irr-valid-table))
         ((desiniter desiniter) desiniter)
         ((erp & types table)
          (valid-designor-list desiniter.designors target-type table ienv))
         ((erp more-types table)
          (valid-initer desiniter.initer target-type lifetime table ienv)))
      (retok (set::union types more-types) table))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter-list ((desiniters desiniter-listp)
                                (target-type typep)
                                (lifetime lifetimep)
                                (table valid-tablep)
                                (ienv ienvp))
    :guard (and (desiniter-list-unambp desiniters)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more
            initializers with optional designations."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the type
       that each list of designators must be applicable to."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp desiniters)) (retok nil (valid-table-fix table)))
         ((erp types table)
          (valid-desiniter (car desiniters) target-type lifetime table ienv))
         ((erp more-types table)
          (valid-desiniter-list
           (cdr desiniters) target-type lifetime table ienv)))
      (retok (set::union types more-types) table))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor ((designor designorp)
                          (target-type typep)
                          (table valid-tablep)
                          (ienv ienvp))
    :guard (and (designor-unambp designor)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp
                 (new-target-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as input is
       the one that the designator must apply to;
       the target type returned as result is
       the one that results from applying the designator to it.
       The target type is the type of the current object [C:6.7.9/17].
       A subscript designator requires an array target type,
       and must have an integer expression [C:6.7.9/6];
       the result is the unknown type,
       because currently we have just one array type
       without information about the element type.
       A dotted designator requires a struct or union type [C:6.7.9/7];
       the result is the unknown type,
       because currently we do not have information about the members."))
    (b* (((reterr) (irr-type) nil (irr-valid-table)))
      (designor-case
       designor
       :sub (b* (((erp index-type index-types table)
                  (valid-const-expr designor.index table ienv))
                 ((unless (or (type-integerp index-type)
                              (type-case index-type :unknown)))
                  (reterr (msg "The index of the designator ~x0 has type ~x1."
                               (designor-fix designor)
                               index-type)))
                 ((unless (or (type-case target-type :array)
                              (type-case target-type :unknown)))
                  (reterr (msg "The target type of the designator ~x0 is ~x1."
                               (designor-fix designor)
                               (type-fix target-type)))))
              (retok (type-unknown) index-types table))
       :dot (b* (((unless (or (type-case target-type :struct)
                              (type-case target-type :union)
                              (type-case target-type :unknown)))
                  (reterr (msg "The target type of the designator ~x0 is ~x1."
                               (designor-fix designor)
                               (type-fix target-type)))))
              (retok (type-unknown) nil (valid-table-fix table)))))
    :measure (designor-count designor)

    ///

    (defret valid-designor.new-target-type-not-function
      (implies (not erp)
               (not (equal (type-kind new-target-type)
                           :function)))
      :hints
      (("Goal" :expand (valid-designor designor target-type table ienv))))

    (defret valid-designor.new-target-type-not-void
      (implies (not erp)
               (not (equal (type-kind new-target-type)
                           :void)))
      :hints
      (("Goal" :expand (valid-designor designor target-type table ienv)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor-list ((designors designor-listp)
                               (target-type typep)
                               (table valid-tablep)
                               (ienv ienvp))
    :guard (and (designor-list-unambp designors)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp
                 (new-target-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the current type
       that the designators must be applicable to.
       The target type returned as result is the type
       resulting from the application of the designators."))
    (b* (((reterr) (irr-type) nil (irr-valid-table))
         ((when (endp designors))
          (retok (type-fix target-type) nil (valid-table-fix table)))
         ((erp target-type types table)
          (valid-designor (car designors) target-type table ienv))
         ((erp target-type more-types table)
          (valid-designor-list (cdr designors) target-type table ienv)))
      (retok target-type (set::union types more-types) table))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declor ((declor declorp)
                        (fundef-params-p booleanp)
                        (type typep)
                        (table valid-tablep)
                        (ienv ienvp))
    :guard (declor-unambp declor)
    :returns (mv erp
                 (new-fundef-params-p booleanp)
                 (new-type typep)
                 (ident identp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function is called after validating
       a list of declaration specifiers,
       or a list of specifiers and qualifiers:
       if the validation of those lists is successful,
       they determine a type, which the declarator can further refine:
       we pass that type as input to this validation function,
       which returns the possibly refined type,
       along with the identifier being declared.
       This function is also called recursively,
       since declarators and direct declarators are mutually recursive.")
     (xdoc::p
      "The @('fundef-params-p') flag is @('t')
       when this function is called
       to validate the declarator of a function definition,
       and only when the parameters of the function have not been validated yet.
       Its new value @('fundef-params-p'), returned as result,
       stays @('t') if the parameters of the function
       have still not been validated yet,
       because they are not found in this declarator;
       otherwise, its new value is @('nil').
       If the input @('fundef-params-p') is @('nil'),
       then @('new-fundef-params-p') is @('nil') as well.
       The exact handling of this flag,
       and the exact treatment of the parameters of function declarations,
       are explained in the code that actually makes use of the flag.")
     (xdoc::p
      "In our currently approximate type system,
       we do not validate type qualifiers, or attributes.
       So the only role of the @('pointers') component of @(tsee declor)
       is to refine the type passed as input into the pointer type
       [C:6.7.6.1/1].
       This resulting type is then passed to
       the function to validate the direct declarator that follows.")
     (xdoc::p
      "We also pass the @('fundef-params-p') flag to @(tsee valid-dirdeclor),
       and relay the @('new-fundef-params-p') output.
       The reason is that, after peeling off the pointers,
       which refine the return result of the function,
       the direct declarator is still expected to be for a function,
       and we have not validated the parameters yet."))
    (b* (((reterr) nil (irr-type) (irr-ident) nil (irr-valid-table))
         ((declor declor) declor)
         (type (if (consp declor.pointers)
                   (type-pointer)
                 type)))
      (valid-dirdeclor declor.direct fundef-params-p type table ienv))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declor-option ((declor? declor-optionp)
                               (type typep)
                               (table valid-tablep)
                               (ienv ienvp))
    :guard (declor-option-unambp declor?)
    :returns (mv erp
                 (new-type typep)
                 (ident? ident-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no declarator,
       we return the type and validation table unchanged,
       and no identifer.
       Otherwise, we validate the declarator,
       using a separate validation function.")
     (xdoc::p
      "This function does not take a return a @('fundef-params-p') flag
       because optional declarators are not used in function parameters."))
    (b* (((reterr) (irr-type) nil nil (irr-valid-table)))
      (declor-option-case
       declor?
       :none (retok (type-fix type) nil nil (valid-table-fix table))
       :some (b* (((erp & type ident types table)
                   (valid-declor declor?.val nil type table ienv)))
               (retok type ident types table))))
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirdeclor ((dirdeclor dirdeclorp)
                           (fundef-params-p booleanp)
                           (type typep)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (dirdeclor-unambp dirdeclor)
    :returns (mv erp
                 (new-fundef-params-p booleanp)
                 (new-type typep)
                 (ident identp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type passed as input is the one resulting from the validation of
       the list of declaration specifiers
       or the list of specifiers and qualifiers
       that precedes the declarator of which the direct declarator is part.
       This type is refined according to the direct declarator,
       and we return the refined type,
       along with the declared identifier.")
     (xdoc::p
      "The meaning of the @('fundef-params-p') flag passed as input is
       the same as in @(tsee valid-declor): see that function's documentation.")
     (xdoc::p
      "If the direct declarator is just an identifier,
       the type is not further refined by this direct declarator.")
     (xdoc::p
      "If the direct declarator is a parenthesized declarator,
       we recursively validate the declarator.")
     (xdoc::p
      "If the direct declarator is one of the array kinds,
       we refine the type to the array type [C:6.7.6.2/3]
       (so in our currently approximate type system
       the input type is effectively ignored),
       and we recursively validate the enclosed direct declarator.
       Then we validate the index expression (if present),
       ensuring that it has integer type.
       For now we do not check that, if these expressions are constant,
       their values are greater than 0 [C:6.7.6.2/1].
       Currently we do not need to do anything
       with type qualifiers and attributes.
       The @('fundef-params-p') flag is threaded through.")
     (xdoc::p
      "If the direct declarator is one of the function kinds,
       we ensure that the input type, which is the function return type,
       is not a function or array type [C:6.7.6.3/1].
       We refine the input type to a function type
       (which in our current type system means we override it),
       and we validate the declarator.
       Then things differ between the kinds of function declarators.")
     (xdoc::p
      "In a function declarator with a parameter type list,
       we push a new scope for the parameters,
       and we validate the parameters (which adds them to the new scope),
       passing the @('fundef-params-p') resulting from
       the recursive validation of the enclosed direct declarator.
       This resulting flag is @('t') if
       the parameters of the function being defined
       have not been validated yet,
       which means that the parameters of the current direct declarator
       are in fact the ones of the function.
       So we return @('nil') as the @('new-fundef-params-p') result,
       so that any outer function declarator
       is not treated as the one
       whose parameters are for the function definition,
       if we are validating one.
       To make things clearer, consider a function definition")
     (xdoc::codeblock
      "void (*f(int x, int y))(int z) { ... }")
     (xdoc::p
      "which defines a function @('f') with parameters @('x') and @('y'),
       which returns a pointer to a function
       that has a parameter @('z') and returns @('void').
       When we validate the full declarator of this function definition,
       @('fundef-params-p') is @('t').
       When we encounter the outer function declarator,
       first we recursively process the inner function declarator,
       whose input @('fundef-params-p') is still @('t'),
       and whose output @('new-fundef-params-p') is @('nil').
       That way, when we continue validating the outer function declarator,
       we do not treat @('z') as a parameter of the function definition.
       In any case, when the current function declarator
       is the one whose parameters are for the function definition,
       i.e. when @('fundef-params-p') is @('t'),
       after validating the parameters, which pushes a new scope with them,
       we return the validation table as such,
       so that when we later validate the function body,
       we already have the top-level scope for the body.
       If instead @('fundef-params-p') is @('nil'),
       the parameters form a function prototype scope [C:6.2.1/4],
       which is therefore popped.")
     (xdoc::p
      "For the function declarator with a parameter type list,
       we handle the special case of a single @('void') [C:6.7.6.3/10]
       before calling a separate function to validate the parameters.")
     (xdoc::p
      "A function declarator with a non-empty name list can only occur
       as the parameters of a function being defined [C:6.7.6.3/3]
       Thus, unless the list is empty,
       we raise an error unless @('fundef-params-p') is @('t'),
       i.e. unless we are validating the parameters of a defined function.
       Note that the value of @('fundef-params-p') is the one
       after validating the inner direct declarator.
       If we are not validating the declarator of a function definition
       (i.e. if @('fundef-params-p') is @('nil')),
       in which case as just mentioned the list must be empty,
       there is nothing left to do, and we return;
       note that there is no function prototype scope here.
       Otherwise, we ensure that the names have no duplicates,
       and we push a new scope for the parameters and the function body,
       but we do not add the parameters to the new scope,
       because their types are specified by the declarations
       that must occur between the end of the whole function declarator
       and the beginning of the defined function's body."))
    (b* (((reterr) nil (irr-type) (irr-ident) nil (irr-valid-table)))
      (dirdeclor-case
       dirdeclor
       :ident
       (retok (bool-fix fundef-params-p)
              (type-fix type)
              dirdeclor.unwrap
              nil
              (valid-table-fix table))
       :paren
       (valid-declor dirdeclor.unwrap fundef-params-p type table ienv)
       :array
       (b* ((type (type-array))
            ((erp fundef-params-p type ident types table)
             (valid-dirdeclor dirdeclor.decl fundef-params-p type table ienv))
            ((erp index-type? more-types table)
             (valid-expr-option dirdeclor.expr? table ienv))
            ((when (and index-type?
                        (not (type-integerp index-type?))
                        (not (type-case index-type? :unknown))))
             (reterr (msg "The index expression ~
                           of the direct declarator ~x0 ~
                           has type ~x1."
                          (dirdeclor-fix dirdeclor)
                          index-type?))))
         (retok fundef-params-p type ident (set::union types more-types) table))
       :array-static1
       (b* ((type (type-array))
            ((erp fundef-params-p type ident types table)
             (valid-dirdeclor dirdeclor.decl fundef-params-p type table ienv))
            ((erp index-type more-types table)
             (valid-expr dirdeclor.expr table ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (reterr (msg "The index expression ~
                           of the direct declarator ~x0 ~
                           has type ~x1."
                          (dirdeclor-fix dirdeclor)
                          index-type))))
         (retok fundef-params-p type ident (set::union types more-types) table))
       :array-static2
       (b* ((type (type-array))
            ((erp fundef-params-p type ident types table)
             (valid-dirdeclor dirdeclor.decl fundef-params-p type table ienv))
            ((erp index-type more-types table)
             (valid-expr dirdeclor.expr table ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (reterr (msg "The index expression ~
                           of the direct declarator ~x0 ~
                           has type ~x1."
                          (dirdeclor-fix dirdeclor)
                          index-type))))
         (retok fundef-params-p type ident (set::union types more-types) table))
       :array-star
       (b* ((type (type-array))
            ((erp fundef-params-p type ident types table)
             (valid-dirdeclor dirdeclor.decl fundef-params-p type table ienv)))
         (retok fundef-params-p type ident types table))
       :function-params
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (reterr (msg "The direct declarator ~x0 ~
                           has type ~x1."
                          (dirdeclor-fix dirdeclor)
                          (type-fix type))))
            (type (type-function))
            ((erp fundef-params-p type ident types table)
             (valid-dirdeclor dirdeclor.decl fundef-params-p type table ienv))
            (table (valid-push-scope table))
            ((erp more-types table)
             (if (equal dirdeclor.params
                        (list (make-paramdecl
                               :spec (list (decl-spec-typespec (type-spec-void)))
                               :decl (paramdeclor-none))))
                 (retok nil table)
               (valid-paramdecl-list
                dirdeclor.params fundef-params-p table ienv)))
            (table (if fundef-params-p
                       table
                     (valid-pop-scope table))))
         (retok nil type ident (set::union types more-types) table))
       :function-names
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (reterr (msg "The direct declarator ~x0 ~
                           has type ~x1."
                          (dirdeclor-fix dirdeclor)
                          (type-fix type))))
            (type (type-function))
            ((erp fundef-params-p type ident types table)
             (valid-dirdeclor dirdeclor.decl fundef-params-p type table ienv))
            ((when (and (consp dirdeclor.names)
                        (not fundef-params-p)))
             (reterr (msg "A non-empty list of parameter names ~
                           occurs in a function declarator ~x0 ~
                           that is not part of a function definition."
                          (dirdeclor-fix dirdeclor))))
            ((when (not fundef-params-p))
             (retok nil type ident types table))
            ((unless (no-duplicatesp-equal dirdeclor.names))
             (reterr (msg "The list of parameter names ~
                           in the function declarator ~x0 ~
                           has duplicates."
                          (dirdeclor-fix dirdeclor))))
            (table (valid-push-scope table)))
         (retok nil type ident types table))))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-absdeclor ((absdeclor absdeclorp)
                           (type typep)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (absdeclor-unambp absdeclor)
    :returns (mv erp
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is fairly similar to @(tsee valid-declor)
       (see that function's documentation),
       but since the declarator is abstract,
       there is no identifier being declared to return.
       Furthermore, there is no flag for function definitions,
       since a function definition uses a declarator,
       not an abstract declarator."))
    (b* (((reterr) (irr-type) nil (irr-valid-table))
         ((absdeclor absdeclor) absdeclor)
         (type (if (consp absdeclor.pointers)
                   (type-pointer)
                 type)))
      (valid-dirabsdeclor-option absdeclor.decl? type table ienv))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-absdeclor-option ((absdeclor? absdeclor-optionp)
                                  (type typep)
                                  (table valid-tablep)
                                  (ienv ienvp))
    :guard (absdeclor-option-unambp absdeclor?)
    :returns (mv erp
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no abstract declarator,
       we return the type and validation table unchanged.
       Otherwise, we validate the abstract declarator,
       using a separate validation function."))
    (b* (((reterr) (irr-type) nil (irr-valid-table)))
      (absdeclor-option-case
       absdeclor?
       :none (retok (type-fix type) nil (valid-table-fix table))
       :some (valid-absdeclor absdeclor?.val type table ienv)))
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirabsdeclor ((dirabsdeclor dirabsdeclorp)
                              (type typep)
                              (table valid-tablep)
                              (ienv ienvp))
    :guard (dirabsdeclor-unambp dirabsdeclor)
    :returns (mv erp
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is fairly similar to @(tsee valid-dirdeclor)
       (see that function's documentation),
       but since the direct declarator is abstract,
       there is no identifier being declared to return.
       Furthermore, there is no flag for function definitions,
       since a function definition uses a (direct) declarator,
       not an (direct) abstract declarator."))
    (b* (((reterr) (irr-type) nil (irr-valid-table)))
      (dirabsdeclor-case
       dirabsdeclor
       :paren
       (valid-absdeclor dirabsdeclor.unwrap type table ienv)
       :array
       (b* ((type (type-array))
            ((erp type types table)
             (valid-dirabsdeclor-option dirabsdeclor.decl? type table ienv))
            ((erp index-type? more-types table)
             (valid-expr-option dirabsdeclor.expr? table ienv))
            ((when (and index-type?
                        (not (type-integerp index-type?))
                        (not (type-case index-type? :unknown))))
             (reterr (msg "The index expression ~
                           of the direct abstract declarator ~x0 ~
                           has type ~x1."
                          (dirabsdeclor-fix dirabsdeclor)
                          index-type?))))
         (retok type (set::union types more-types) table))
       :array-static1
       (b* ((type (type-array))
            ((erp type types table)
             (valid-dirabsdeclor-option dirabsdeclor.decl? type table ienv))
            ((erp index-type more-types table)
             (valid-expr dirabsdeclor.expr table ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (reterr (msg "The index expression ~
                           of the direct abstract declarator ~x0 ~
                           has type ~x1."
                          (dirabsdeclor-fix dirabsdeclor)
                          index-type))))
         (retok type (set::union types more-types) table))
       :array-static2
       (b* ((type (type-array))
            ((erp type types table)
             (valid-dirabsdeclor-option dirabsdeclor.decl? type table ienv))
            ((erp index-type more-types table)
             (valid-expr dirabsdeclor.expr table ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (reterr (msg "The index expression ~
                           of the direct abstract declarator ~x0 ~
                           has type ~x1."
                          (dirabsdeclor-fix dirabsdeclor)
                          index-type))))
         (retok type (set::union types more-types) table))
       :array-star
       (b* ((type (type-array))
            ((erp type types table)
             (valid-dirabsdeclor-option dirabsdeclor.decl? type table ienv)))
         (retok type types table))
       :function
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (reterr (msg "The direct abstract declarator ~x0 ~
                           has type ~x1."
                          (dirabsdeclor-fix dirabsdeclor)
                          (type-fix type))))
            (type (type-function))
            ((erp type types table)
             (valid-dirabsdeclor-option dirabsdeclor.decl? type table ienv))
            (table (valid-push-scope table))
            ((erp more-types table)
             (if (equal dirabsdeclor.params
                        (list (make-paramdecl
                               :spec (list (decl-spec-typespec (type-spec-void)))
                               :decl (paramdeclor-none))))
                 (retok nil table)
               (valid-paramdecl-list dirabsdeclor.params nil table ienv)))
            (table (valid-pop-scope table)))
         (retok type (set::union types more-types) table))
       :dummy-base
       (prog2$ (impossible) (reterr t))))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                     (type typep)
                                     (table valid-tablep)
                                     (ienv ienvp))
    :guard (dirabsdeclor-option-unambp dirabsdeclor?)
    :returns (mv erp
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no direct abstract declarator,
       we return the type and validation table unchanged.
       Otherwise, we validate the direct abstract declarator,
       using a separate validation function."))
    (b* (((reterr) (irr-type) nil (irr-valid-table)))
      (dirabsdeclor-option-case
       dirabsdeclor?
       :none (retok (type-fix type) nil (valid-table-fix table))
       :some (valid-dirabsdeclor dirabsdeclor?.val type table ienv)))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-paramdecl ((paramdecl paramdeclp)
                           (fundef-params-p booleanp)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (paramdecl-unambp paramdecl)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('fundef-params-p') input is @('t') iff
       we are validating the parameter of a function definition.")
     (xdoc::p
      "We validate the declaration specifiers,
       which results in a type,
       a list of storage class specifiers,
       and a possibly updated table.
       We ensure that the list of storage class specifiers
       is either empty or the singleton @('register') [C:6.7.6.3/2].")
     (xdoc::p
      "We validate the parameter declarator,
       ensuring that it has an identifier if @('fundef-params-p') is @('t')
       [C:6.9.1/5].
       We adjust the type if necessary [C:6.7.6.3/7] [C:6.7.6.3/8].
       If the parameter declarator has an identifier,
       we extend the validation table with it,
       unless there is already an ordinary identifier
       with the same name in the same (i.e. current) scope;
       since parameters have no linkage [C:6.2.2/6],
       they can be only declared once in the same scope [C:6.7/3].
       Parameters of function declarations have no linkage [C:6.2.2/6].
       Since storage is allocated for them when the function is called,
       they are considered defined [C:6.7/5]."))
    (b* (((reterr) nil (irr-valid-table))
         ((paramdecl paramdecl) paramdecl)
         ((erp type storspecs types table)
          (valid-decl-spec-list paramdecl.spec nil nil nil table ienv))
         ((unless (or (endp storspecs)
                      (stor-spec-list-register-p storspecs)))
          (reterr (msg "The parameter declaration ~x0 ~
                        has storage class specifiers ~x1."
                       (paramdecl-fix paramdecl)
                       (stor-spec-list-fix storspecs))))
         ((erp type ident? more-types table)
          (valid-paramdeclor paramdecl.decl type table ienv))
         ((when (and fundef-params-p
                     (not ident?)))
          (reterr (msg "The parameter declaration ~x0 ~
                        is for a function definition but has no identifier."
                       (paramdecl-fix paramdecl))))
         (type (if (type-case type :array)
                   (type-pointer)
                 type))
         (type (if (type-case type :function)
                   (type-pointer)
                 type))
         ((when (not ident?))
          (retok (set::union types more-types) table))
         (ord-info (make-valid-ord-info-objfun
                    :type type
                    :linkage (linkage-none)
                    :defstatus (valid-defstatus-defined)))
         ((mv info? currentp) (valid-lookup-ord ident? table))
         ((when (and info? currentp))
          (reterr (msg "The parameter declared in ~x0 ~
                        in already declared in the current scope ~
                        with associated information ~x1."
                       (paramdecl-fix paramdecl) info?)))
         (table (valid-add-ord ident? ord-info table)))
      (retok (set::union types more-types) table))
    :measure (paramdecl-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-paramdecl-list ((paramdecls paramdecl-listp)
                                (fundef-params-p booleanp)
                                (table valid-tablep)
                                (ienv ienvp))
    :guard (paramdecl-list-unambp paramdecls)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "IWe validate each parameter in turn,
       threading the validation table through,
       using a separate validation function."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp paramdecls)) (retok nil (valid-table-fix table)))
         ((erp types table)
          (valid-paramdecl (car paramdecls) fundef-params-p table ienv))
         ((erp more-types table)
          (valid-paramdecl-list (cdr paramdecls) fundef-params-p table ienv)))
      (retok (set::union types more-types) table))
    :measure (paramdecl-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-paramdeclor ((paramdeclor paramdeclorp)
                             (type typep)
                             (table valid-tablep)
                             (ienv ienvp))
    :guard (paramdeclor-unambp paramdeclor)
    :returns (mv erp
                 (new-type typep)
                 (ident? ident-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a parameter declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The input type is the one resulting from
       the declaration specifiers of the parameter declaration
       of which the parameter declarator is part of.
       If validation is successful,
       we return a possibly refined type,
       and an optional identifier.")
     (xdoc::p
      "If the parameter declarator is a (non-abstract) declarator,
       we return the possibly refined type and the identifier.
       If the parameter declarator is an abstract declarator,
       we return the possibly refined type but no identifier.
       If the parameter declarator is absent,
       we return the type unchanged and no identifer."))
    (b* (((reterr) (irr-type) (irr-ident) nil (irr-valid-table)))
      (paramdeclor-case
       paramdeclor
       :declor
       (b* (((erp & type ident types table)
             (valid-declor paramdeclor.unwrap nil type table ienv)))
         (retok type ident types table))
       :absdeclor
       (b* (((erp type types table)
             (valid-absdeclor paramdeclor.unwrap type table ienv)))
         (retok type nil types table))
       :none
       (retok (type-fix type) nil nil (valid-table-fix table))
       :ambig
       (prog2$ (impossible) (reterr t))))
    :measure (paramdeclor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-tyname ((tyname tynamep) (table valid-tablep) (ienv ienvp))
    :guard (tyname-unambp tyname)
    :returns (mv erp
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "A valid type name denotes a type,
       so we return a type if validation is successful.")
     (xdoc::p
      "First we validate the list of specifiers and qualifiers,
       which returns a type if successful.
       Then we validate the optional abstract declarator,
       which returns a possibly refined type.
       We return the latter type."))
    (b* (((reterr) (irr-type) nil (irr-valid-table))
         ((tyname tyname) tyname)
         ((erp type types table)
          (valid-spec/qual-list tyname.specqual nil nil table ienv))
         ((erp type more-types table)
          (valid-absdeclor-option tyname.decl? type table ienv)))
      (retok type (set::union types more-types) table))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-strunispec ((strunispec strunispecp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (strunispec-unambp strunispec)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure or union specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check that there is at least a name or a list of members
       [C:6.7.2.1/2].")
     (xdoc::p
      "For now our validation tables include
       no information about structure and union tags,
       so we do not extend the validation table,
       if the structure or union specifier has a name.
       However, we validate the members, if present."))
    (b* (((reterr) nil (irr-valid-table))
         ((strunispec strunispec) strunispec)
         ((when (and (not strunispec.name)
                     (endp strunispec.members)))
          (reterr (msg "The structure or union specifier ~x0 ~
                        has no name and no members."
                       (strunispec-fix strunispec)))))
      (valid-structdecl-list strunispec.members nil table ienv))
    :measure (strunispec-count strunispec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdecl ((structdecl structdeclp)
                            (previous ident-listp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (structdecl-unambp structdecl)
    :returns (mv erp
                 (new-previous ident-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input consists of
       the names of the members that precede this structure declaration
       in the structure or union specifier being validated.
       The @('new-previous') output consists of
       the extension of @('previous') with
       the names of the members declared by this structure declaration.")
     (xdoc::p
      "If the structure declaration declares members,
       first we validate the list of specifiers and qualifiers,
       obtaining a type if the validation is successful.
       Then we use a separate validation function for the structure declarators,
       which also returns a possibly extended list of member names.")
     (xdoc::p
      "If the structure declaration consists of a static assertion declaration,
       we validate it using a separate validation function.
       The list of member names is unchanged.")
     (xdoc::p
      "If the structure declaration is empty (i.e. a semicolon),
       which is a GCC extension,
       the list of member names and the validation table are unchanged."))
    (b* (((reterr) nil nil (irr-valid-table)))
      (structdecl-case
       structdecl
       :member
       (b* (((erp type types table)
             (valid-spec/qual-list structdecl.specqual nil nil table ienv))
            ((erp previous more-types table)
             (valid-structdeclor-list
              structdecl.declor previous type table ienv)))
         (retok previous (set::union types more-types) table))
       :statassert
       (b* (((erp types table) (valid-statassert structdecl.unwrap table ienv)))
         (retok (ident-list-fix previous) types table))
       :empty
       (retok (ident-list-fix previous) nil (valid-table-fix table))))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdecl-list ((structdecls structdecl-listp)
                                 (previous ident-listp)
                                 (table valid-tablep)
                                 (ienv ienvp))
    :guard (structdecl-list-unambp structdecls)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input consists of
       the names of the members that precede these structure declarations
       (which declare more members)
       in the structure or union specifier being validated.
       This list is used to ensure uniqueness of member names."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp structdecls)) (retok nil (valid-table-fix table)))
         ((erp previous types table)
          (valid-structdecl (car structdecls) previous table ienv))
         ((erp more-types table)
          (valid-structdecl-list (cdr structdecls) previous table ienv)))
      (retok (set::union types more-types) table))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdeclor ((structdeclor structdeclorp)
                              (previous ident-listp)
                              (type typep)
                              (table valid-tablep)
                              (ienv ienvp))
    :guard (structdeclor-unambp structdeclor)
    :returns (mv erp
                 (new-previous ident-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input and @('new-previous') output
       have the same meaning as in @(tsee valid-structdecl).")
     (xdoc::p
      "The @('type') input comes from the list of specifiers and qualifiers
       that precedes the list of structure declarators
       of which this structure declarator is an element.
       We ensure that there is either a declarator or a constant expression
       (this is actually a syntactic constraint,
       but it is currently not captured in the abstract syntax,
       so we check it here).
       If there is a declarator, we validate it,
       and we add the declared identifier to the list member names,
       after ensuring that it is not already there.
       If there is a constant expression, we validate it,
       but for now we do not perform any checks related to its value
       [C:6.7.2.1/4];
       we also do not constrain the types of bit fields [C:6.7.2.1/5],
       but we ensure that the constant expression, if present, is integer."))
    (b* (((reterr) nil nil (irr-valid-table))
         ((structdeclor structdeclor) structdeclor)
         ((when (and (not structdeclor.declor?)
                     (not structdeclor.expr?)))
          (reterr (msg "The structure declarator ~x0 is empty."
                       (structdeclor-fix structdeclor))))
         ((erp & ident? types table)
          (valid-declor-option structdeclor.declor? type table ienv))
         (previous (ident-list-fix previous))
         ((when (and ident?
                     (member-equal ident? previous)))
          (reterr (msg "The structure declarator ~x0 ~
                        duplicates the member name."
                       (structdeclor-fix structdeclor))))
         (previous (if ident?
                       (rcons ident? previous)
                     previous))
         ((erp width-type? more-types table)
          (valid-const-expr-option structdeclor.expr? table ienv))
         ((when (and width-type?
                     (not (type-integerp width-type?))
                     (not (type-case width-type? :unknown))))
          (reterr (msg "The structure declarator ~x0 ~
                        has a width of type ~x1."
                       (structdeclor-fix structdeclor)
                       width-type?))))
      (retok previous (set::union types more-types) table))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdeclor-list ((structdeclors structdeclor-listp)
                                   (previous ident-listp)
                                   (type typep)
                                   (table valid-tablep)
                                   (ienv ienvp))
    :guard (structdeclor-list-unambp structdeclors)
    :returns (mv erp
                 (new-previous ident-listp)
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each structure declarator in turn,
       threading the data through.
       Note that the same type
       (coming from the list of specifiers and qualifiers)
       is passed to the validation function for each structure declarator,
       since that type applied to all them
       (possibly refined, possibly differently, by the structure declarators."))
    (b* (((reterr) nil nil (irr-valid-table))
         ((when (endp structdeclors))
          (retok (ident-list-fix previous) nil (valid-table-fix table)))
         ((erp previous types table)
          (valid-structdeclor (car structdeclors) previous type table ienv))
         ((erp previous more-types table)
          (valid-structdeclor-list
           (cdr structdeclors) previous type table ienv)))
      (retok previous (set::union types more-types) table))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumspec ((enumspec enumspecp)
                          (table valid-tablep)
                          (ienv ienvp))
    :guard (enumspec-unambp enumspec)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an enumeration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check that there is at least a name of a list of enumerators;
       although this is a syntactic constraint,
       it is currently not captured in our abstract syntax,
       so we double-check it here.")
     (xdoc::p
      "For now our validation tabled include
       no information about enumeration tags,
       so we do not extend the validation table,
       if the enumeration specifier has a name.
       However, we validate the enumerators, if present."))
    (b* (((reterr) nil (irr-valid-table))
         ((enumspec enumspec) enumspec)
         ((when (and (not enumspec.name)
                     (endp enumspec.list)))
          (reterr (msg "The enumeration specifier ~x0 ~
                        has no name and no enumerators."
                       (enumspec-fix enumspec)))))
      (valid-enumer-list enumspec.list table ienv))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumer ((enumer enumerp) (table valid-tablep) (ienv ienvp))
    :guard (enumer-unambp enumer)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an enumerator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The enumeration constant is added to the validation table [C:6.2.1/7],
       unless there is already an ordinary identifier
       with the same name and in the same (i.e. current) scope;
       since enumeration constants have no linkage [C:6.2.2/6],
       they can be only declared once in the same scope [C:6.7/3].
       If there is a constant expression,
       we validate it and check that it has integer type,
       but for now we do not check that the value
       is representable as @('int') [C:6.7.2.2/2]."))
    (b* (((reterr) nil (irr-valid-table))
         ((enumer enumer) enumer)
         ((mv info? currentp) (valid-lookup-ord enumer.name table))
         ((when (and info? currentp))
          (reterr (msg "The enumerator declared in ~x0 ~
                        in already declared in the current scope ~
                        with associated information ~x1."
                       (enumer-fix enumer) info?)))
         (table (valid-add-ord enumer.name (valid-ord-info-enumconst) table))
         ((erp type? types table)
          (valid-const-expr-option enumer.value table ienv))
         ((when (and type?
                     (not (type-integerp type?))
                     (not (type-case type? :unknown))))
          (reterr (msg "The value of the numerator ~x0 has type ~x1."
                       (enumer-fix enumer) type?))))
      (retok types table))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumer-list ((enumers enumer-listp)
                             (table valid-tablep)
                             (ienv ienvp))
    :guard (enumer-list-unambp enumers)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of enumerators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through each enumerator in order,
       extending the validation table with each."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp enumers)) (retok nil (valid-table-fix table)))
         ((erp types table) (valid-enumer (car enumers) table ienv))
         ((erp more-types table)
          (valid-enumer-list (cdr enumers) table ienv)))
      (retok (set::union types more-types) table))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-statassert ((statassert statassertp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (statassert-unambp statassert)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a static assertion declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate the constant expression, which must be integer [C:6.7.10/3],
       and we validate the string literal(s)."))
    (b* (((reterr) nil (irr-valid-table))
         ((statassert statassert) statassert)
         ((erp type types table)
          (valid-const-expr statassert.test table ienv))
         ((unless (or (type-integerp type)
                      (type-case type :unknown)))
          (reterr (msg "The expression in the static assertion declaration ~x0 ~
                        has type ~x1."
                       (statassert-fix statassert)
                       type)))
         ((erp &) (valid-stringlit-list statassert.message)))
      (retok types table))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initdeclor ((initdeclor initdeclorp)
                            (type typep)
                            (storspecs stor-spec-listp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (initdeclor-unambp initdeclor)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializer declarators [C:6.7/1]
       appear in declarations, after declaration specifiers.
       The latter determine a type, passed as input,
       which an initializer declarator may refine.
       We also pass as input the storage class specifiers
       extracted from the declaration specifiers.")
     (xdoc::p
      "We validate the declarator,
       which returns the identifier and the possibly refined type.
       Here the @('fundef-params-p') flag is always @('nil'),
       because we are not in a function definition.")
     (xdoc::p
      "Then we validate the storage class specifiers,
       which together with the identifier and final type
       determine whether we are declaring a @('typedef'),
       and what the linkage and lifetime are.")
     (xdoc::p
      "If the @('typedef') flag is @('t'),
       there must be no initializer,
       because we are not declaring an object.
       In this case, we add the @('typedef') to the validation table.
       The same @('typedef') is allowed in the same scope [C:6.7/3],
       under certain conditions that are inexpressible
       in our current approximate type system,
       but since our validation tables currently carry limited information
       about @('typedef') names (i.e. just that they are @('typedef')s),
       we allow the identifier to be present, as a @('typedef'),
       in the same (i.e. current) scope,
       to avoid rejecting valid code.")
     (xdoc::p
      "If the @('typedef') flag is @('nil'),
       the identifier may denote a function or an object.
       The initializer may be present only if
       the type is not that of a function,
       because initializers only apply to objects,
       and the type is not void,
       because the type must be complete [C:6.7.9/3].
       We validate the initializer if present;
       we pass the type of the identifier,
       so the initializer is checked against that.")
     (xdoc::p
      "We calculate the definition status for the declaration.
       If we are declaring a function, the status is undefined,
       because we do not have a function body here.
       Otherwise, we are declaring an object.
       If we are in a block scope,
       the status is undefined if the object has external linkage
       (because it refers to some external entity from the block),
       while it is defined otherwise
       (because the declaration allocates storage for the object).
       If we are in a file scope, we follow [C:6.9.2/1] and [C:6.9.2/2]:
       an initializer makes the status defined;
       otherwise, the presence of @('extern') makes the status undefined
       and its absence makes the status defined.
       This is slightly different from what [C:6.9.2/2] says,
       which mentions no storage class specifier or @('static'),
       but it seems clear that this neglects to consider @('_Thread_local');
       in fact, the wording in the newly released C23 standard is clearer.")
     (xdoc::p
      "We look up the identifier in the validation table.
       If no information is found in the validation table,
       we add the identifier to the table.
       If the current declaration has no linkage,
       or if the information in the table has no linkage
       (which includes the case of the information in the table
       being for a @('typedef') or an enumeration constant),
       the two must denote different entities,
       and thus we ensure that the one in the table
       is not in the same (i.e. current) scope [C:6.2.1/4] [C:6.7/3];
       if the checks pass, we add the identifier to the table.
       If instead both have internal or external linkage,
       they must refer to the same entity,
       and so we ensure that the types are the same.
       We also need to check that the linkages are the same,
       in which case we still add the identifier to the table,
       to record that it is also declared in the current scope;
       in this case, it is not clear whether we should suitable combine
       the old and new definition statuses,
       but for now we just use the newest.
       It is an error if the current linkage is internal
       while the one in the table is external.
       The situation where the current one is external
       while the one in the table is internal cannot happen,
       because as defined in @(tsee valid-stor-spec-list),
       the current one would ``inherit''
       the internal linkage from the previous one.")
     (xdoc::p
      "For now we ignore the optional assembler name specifier,
       as well as any attribute specifiers."))
    (b* (((reterr) nil (irr-valid-table))
         ((initdeclor initdeclor) initdeclor)
         ((erp & type ident types table)
          (valid-declor initdeclor.declor nil type table ienv))
         ((erp typedefp linkage lifetime?)
          (valid-stor-spec-list storspecs ident type nil table))
         ((when typedefp)
          (b* (((when initdeclor.init?)
                (reterr (msg "The typedef name ~x0 ~
                              has an initializer ~x1."
                             ident initdeclor.init?)))
               ((mv info? currentp) (valid-lookup-ord ident table))
               ((when (and info?
                           currentp
                           (not (valid-ord-info-case info? :typedef))))
                (reterr (msg "The typedef name ~x0 ~
                              is already declared in the current scope ~
                              with associated information ~x1."
                             ident info?)))
               (table (valid-add-ord ident (valid-ord-info-typedef) table)))
            (retok types table)))
         ((when (and initdeclor.init?
                     (or (type-case type :function)
                         (type-case type :void))))
          (reterr (msg "The identifier ~x0 has type ~x1, ~
                        which disallows the initializer, ~
                        but the initializer ~x2 is present."
                       ident type initdeclor.init?)))
         ((erp more-types table)
          (valid-initer-option initdeclor.init? type lifetime? table ienv))
         (defstatus (if (type-case type :function)
                        (valid-defstatus-undefined)
                      (if (> (valid-table-num-scopes table) 1)
                          (if (linkage-case linkage :external)
                              (valid-defstatus-undefined)
                            (valid-defstatus-defined))
                        (if initdeclor.init?
                            (valid-defstatus-defined)
                          (if (member-equal (stor-spec-extern)
                                            (stor-spec-list-fix storspecs))
                              (valid-defstatus-undefined)
                            (valid-defstatus-tentative))))))
         ((mv info? currentp) (valid-lookup-ord ident table))
         ((when (not info?))
          (b* ((new-info (make-valid-ord-info-objfun
                          :type type
                          :linkage linkage
                          :defstatus defstatus))
               (table (valid-add-ord ident new-info table)))
            (retok (set::union types more-types) table)))
         ((when (or (valid-ord-info-case info? :typedef)
                    (valid-ord-info-case info? :enumconst)))
          (if currentp
              (reterr (msg "The identifier ~x0 ~
                            is already declared in the current scope ~
                            with associated information ~x1."
                           ident info?))
            (b* ((new-info (make-valid-ord-info-objfun
                            :type type
                            :linkage linkage
                            :defstatus defstatus))
                 (table (valid-add-ord ident new-info table)))
              (retok (set::union types more-types) table))))
         ((valid-ord-info-objfun info) info?)
         ((when (or (linkage-case linkage :none)
                    (linkage-case info.linkage :none)))
          (if currentp
              (reterr (msg "The identifier ~x0 ~
                            is already declared in the current scope ~
                            with associated information ~x1."
                           ident info?))
            (b* ((new-info (make-valid-ord-info-objfun
                            :type type
                            :linkage linkage
                            :defstatus defstatus))
                 (table (valid-add-ord ident new-info table)))
              (retok (set::union types more-types) table))))
         ((unless (equal type info.type))
          (reterr (msg "The identifier ~x0 ~
                        is declared with type ~x1 ~
                        after being declared with type ~x2."
                       ident type info.type)))
         ((when (and (linkage-case linkage :internal)
                     (linkage-case info.linkage :external)))
          (reterr (msg "The identifier ~x0 ~
                        is declared with internal linkage ~
                        after being declared with external linkage."
                       ident)))
         ((when (and (linkage-case linkage :external)
                     (linkage-case info.linkage :internal)))
          (raise "Internal error: ~ the identifier ~x0 ~
                  is declared with external linkage ~
                  after being declared with internal linkage."
                 ident)
          (reterr t))
         (new-info (make-valid-ord-info-objfun
                    :type type
                    :linkage linkage
                    :defstatus defstatus))
         (table (valid-add-ord ident new-info table)))
      (retok (set::union types more-types) table))
    :measure (initdeclor-count initdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initdeclor-list ((initdeclors initdeclor-listp)
                                 (type typep)
                                 (storspecs stor-spec-listp)
                                 (table valid-tablep)
                                 (ienv ienvp))
    :guard (initdeclor-list-unambp initdeclors)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type and storage class specifiers come from
       the declaration specifiers that precede the initializer declarators.
       We validate each in turn."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp initdeclors)) (retok nil (valid-table-fix table)))
         ((erp types table)
          (valid-initdeclor (car initdeclors) type storspecs table ienv))
         ((erp more-types table)
          (valid-initdeclor-list (cdr initdeclors) type storspecs table ienv)))
      (retok (set::union types more-types) table))
    :measure (initdeclor-list-count initdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl ((decl declp) (table valid-tablep) (ienv ienvp))
    :guard (decl-unambp decl)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "If it is a static assertion declaration,
       we validate it using a separate validation function.
       Otherwise, we first validate the declaration specifiers
       and then the list of initializer declarators,
       passing information from the former to the latter.
       We ensure that the list of initializer declarators is not empty
       (i.e. there is at least a declarator),
       or the declaration specifiers declare a tag,
       as required in [C:6.7/2].
       We ignore the GCC extension for now."))
    (b* (((reterr) nil (irr-valid-table)))
      (decl-case
       decl
       :decl
       (b* (((erp type storspecs types table)
             (valid-decl-spec-list decl.specs nil nil nil table ienv))
            ((when (and (endp decl.init)
                        (not (type-case type :struct))
                        (not (type-case type :union))
                        (not (type-case type :enum))))
             (reterr (msg "The declaration ~x0 declares ~
                           neither a declarator nor a tag."
                          (decl-fix decl))))
            ((erp more-types table)
             (valid-initdeclor-list decl.init type storspecs table ienv)))
         (retok (set::union types more-types) table))
       :statassert
       (valid-statassert decl.unwrap table ienv)))
    :measure (decl-count decl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-list ((decls decl-listp) (table valid-tablep) (ienv ienvp))
    :guard (decl-list-unambp decls)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each one in turn."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp decls)) (retok nil (valid-table-fix table)))
         ((erp types table) (valid-decl (car decls) table ienv))
         ((erp more-types table) (valid-decl-list (cdr decls) table ienv)))
      (retok (set::union types more-types) table))
    :measure (decl-list-count decls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-label ((label labelp) (table valid-tablep) (ienv ienvp))
    :guard (label-unambp label)
    :returns (mv erp
                 (return-types type-setp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a label."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now this just amounts to validating the constant expression(s),
       for the case of a @('case') label,
       and ensuring it/they has/have integer type [C:6.8.4.2/3];
       in the future, we should collect labels in the validation table
       so that we can check that referenced labels are in scope.
       Also, for now we do not check that @('case') and @('default') labels
       only appear in @('switch') statements [C:6.8.1/2]."))
    (b* (((reterr) nil (irr-valid-table)))
      (label-case
       label
       :name
       (retok nil (valid-table-fix table))
       :casexpr
       (b* (((erp type types table)
             (valid-const-expr label.expr table ienv))
            ((unless (or (type-integerp type)
                         (type-case type :unknown)))
             (reterr (msg "The first or only 'case' expression ~
                           in the label ~x0 has type ~x1."
                          (label-fix label) type)))
            ((erp type? more-types table)
             (valid-const-expr-option label.range? table ienv))
            ((when (and type?
                        (not (type-integerp type?))
                        (not (type-case type? :unknown))))
             (reterr (msg "The second 'case' expression~
                           in the label ~x0 has type ~x1."
                          (label-fix label) type?))))
         (retok (set::union types more-types) table))
       :default
       (retok nil (valid-table-fix table))))
    :measure (label-count label))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-stmt ((stmt stmtp) (table valid-tablep) (ienv ienvp))
    :guard (stmt-unambp stmt)
    :returns (mv erp
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return,
       besides an updated validation table,
       also two pieces of type information.")
     (xdoc::p
      "The first piece is the set of types returned by the statement,
       via @('return') statements, with or without expressions.
       This is a set because a statement may contain
       multiple @('return') sub-statements.
       A @('return') statement with an expression
       contributes the type of the expression to the set;
       a @('return') statement without an expression
       contributes the type @('void') to the set.")
     (xdoc::p
      "The second piece of information is as follows.
       If the statement is either a (possibly labeled) expression statement,
       or is a (possibly labeled) compound one
       whose last block item is an expression statement,
       the second piece of information is the type of that expression.
       If the statement is not an expression or compound,
       or it is compound but does not end in an expression statement
       (including the case in which the compound statement has no block items),
       the second piece of information is @('nil').
       The reason for having this second piece of information
       is to support the validation of "
      (xdoc::ahref "GCC statement expressions"
                   "https://gcc.gnu.org/onlinedocs/gcc/Statement-Exprs.html")
      ".")
     (xdoc::p
      "To validate a labeled statement,
       we validate its label, and then the enclosed statement.
       We return the union of the return types,
       and the optional type from the statement.
       For now we do not check the requirements in
       [C:6.8.1/2] and [C:6.8.1/3].")
     (xdoc::p
      "To validate a compound statement,
       we push a new scope for the block,
       and we validate the list of block items.
       We pop the scope and we return the same results
       coming from the validation of the block items.")
     (xdoc::p
      "To validate an expression statement,
       we validate the expression if present,
       and return its type as the second result;
       this is @('nil') if there is no expression.
       The return types are the same as the ones of the expression.")
     (xdoc::p
      "A selection statement and its sub-statements are blocks [C:6.8.4/3],
       so we push and pop scopes accordingly.
       We check that the test of @('if') has scalar type [C:6.8.4.1/1]
       and that the target of @('switch') has integer type [C:6.8.4.2/1].
       No type is returned as the @('last-expr-type?') result,
       because a selection statement is not an expression statement
       (see criterion above for that result of this validation function).")
     (xdoc::p
      "An iteration statement and its sub-statements are blocks [C:6.8.5/5],
       so we push and pop scopes accordingly.
       We check that the test expression has scalar type.
       No type is returned as the @('last-expr-type?') result,
       because an iteraion statement is not an expression statement
       (see criterion above for that result of this validation function).
       For now we do not enforce that the declaration in a @('for')
       only uses the storage class specifiers @('auto') and @('register').")
     (xdoc::p
      "For now we do not check constraints on
       the label of a @('goto') [C:6.8.6.1/1],
       the occurrence of @('continue') [C:6.8.6.2/2],
       and the occurrence of @('break') [C:6.8.6.3/1].")
     (xdoc::p
      "A @('return') statement explicitly adds a type to the return types,
       either the type of the expression,
       or @('void') is there is no expression.
       We check the constraints on occurrences [C:6.8.6.4/1]
       in the validation function for function definitions.")
     (xdoc::p
      "For now we do not check any constraints on assembler statements."))
    (b* (((reterr) nil nil (irr-valid-table)))
      (stmt-case
       stmt
       :labeled
       (b* (((erp types table) (valid-label stmt.label table ienv))
            ((erp more-types type? table) (valid-stmt stmt.stmt table ienv)))
         (retok (set::union types more-types) type? table))
       :compound
       (b* ((table (valid-push-scope table))
            ((erp types type? table)
             (valid-block-item-list stmt.items table ienv))
            (table (valid-pop-scope table)))
         (retok types type? table))
       :expr
       (b* (((erp type? types table) (valid-expr-option stmt.expr? table ienv)))
         (retok types type? table))
       :if
       (b* ((table (valid-push-scope table))
            ((erp test-type test-types table) (valid-expr stmt.test table ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (reterr (msg "The test of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) test-type)))
            (table (valid-push-scope table))
            ((erp then-types & table) (valid-stmt stmt.then table ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (set::union test-types then-types) nil table))
       :ifelse
       (b* ((table (valid-push-scope table))
            ((erp test-type test-types table) (valid-expr stmt.test table ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (reterr (msg "The test of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) test-type)))
            (table (valid-push-scope table))
            ((erp then-types & table) (valid-stmt stmt.then table ienv))
            (table (valid-pop-scope table))
            (table (valid-push-scope table))
            ((erp else-types & table) (valid-stmt stmt.else table ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (set::union test-types (set::union then-types else-types))
                nil
                table))
       :switch
       (b* ((table (valid-push-scope table))
            ((erp target-type target-types table)
             (valid-expr stmt.target table ienv))
            ((unless (or (type-integerp target-type)
                         (type-case target-type :unknown)))
             (reterr (msg "The target of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) target-type)))
            (table (valid-push-scope table))
            ((erp body-types & table) (valid-stmt stmt.body table ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (set::union target-types body-types) nil table))
       :while
       (b* ((table (valid-push-scope table))
            ((erp test-type test-types table) (valid-expr stmt.test table ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (reterr (msg "The test of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) test-type)))
            (table (valid-push-scope table))
            ((erp body-types & table) (valid-stmt stmt.body table ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table))
            (types (set::union test-types body-types)))
         (retok types nil table))
       :dowhile
       (b* ((table (valid-push-scope table))
            (table (valid-push-scope table))
            ((erp body-types & table) (valid-stmt stmt.body table ienv))
            (table (valid-pop-scope table))
            ((erp test-type test-types table) (valid-expr stmt.test table ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (reterr (msg "The test of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) test-type)))
            (table (valid-pop-scope table)))
         (retok (set::union test-types body-types) nil table))
       :for-expr
       (b* ((table (valid-push-scope table))
            ((erp & init-types table)
             (valid-expr-option stmt.init table ienv))
            ((erp test-type? test-types table)
             (valid-expr-option stmt.test table ienv))
            ((when (and test-type?
                        (not (type-scalarp test-type?))
                        (not (type-case test-type? :unknown))))
             (reterr (msg "The test of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) test-type?)))
            ((erp & next-types table)
             (valid-expr-option stmt.next table ienv))
            (table (valid-push-scope table))
            ((erp body-types & table) (valid-stmt stmt.body table ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (set::union init-types
                            (set::union test-types
                                        (set::union next-types
                                                    body-types)))
                nil
                table))
       :for-decl
       (b* ((table (valid-push-scope table))
            ((erp init-types table) (valid-decl stmt.init table ienv))
            ((erp test-type? test-types table)
             (valid-expr-option stmt.test table ienv))
            ((when (and test-type?
                        (not (type-scalarp test-type?))
                        (not (type-case test-type? :unknown))))
             (reterr (msg "The test of the statement ~x0 has type ~x1."
                          (stmt-fix stmt) test-type?)))
            ((erp & next-types table)
             (valid-expr-option stmt.next table ienv))
            (table (valid-push-scope table))
            ((erp body-types & table) (valid-stmt stmt.body table ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (set::union init-types
                            (set::union test-types
                                        (set::union next-types
                                                    body-types)))
                nil
                table))
       :for-ambig
       (prog2$ (impossible) (reterr t))
       :goto
       (retok nil nil (valid-table-fix table))
       :continue
       (retok nil nil (valid-table-fix table))
       :break
       (retok nil nil (valid-table-fix table))
       :return
       (b* (((erp type? types table) (valid-expr-option stmt.expr? table ienv))
            (return-type (or type? (type-void))))
         (retok (set::insert return-type types) nil table))
       :asm
       (retok nil nil (valid-table-fix table))))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-block-item ((item block-itemp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (block-item-unambp item)
    :returns (mv erp
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the slight modification that
       the @('last-expr-type?') result is a type exactly when
       the block item is a compound statement
       whose last block item is an expression statement,
       in which case the @('last-expr-type?') result is
       the type of that expression.")
     (xdoc::p
      "If the block item is a declaration,
       the @('last-expr-type?') result is @('nil'),
       because the block item is not a statement of the kind
       described in @(tsee valid-stmt)."))
    (b* (((reterr) nil nil (irr-valid-table)))
      (block-item-case
       item
       :decl (b* (((erp types table) (valid-decl item.unwrap table ienv)))
               (retok types nil table))
       :stmt (valid-stmt item.unwrap table ienv)
       :ambig (prog2$ (impossible) (reterr t))))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-block-item-list ((items block-item-listp)
                                 (table valid-tablep)
                                 (ienv ienvp))
    :guard (block-item-list-unambp items)
    :returns (mv erp
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the modification that
       the @('last-expr-type?') result is a type exactly when
       the list of block items is not empty
       and the validation of the last block item
       returns a type as that result."))
    (b* (((reterr) nil nil (irr-valid-table))
         ((when (endp items)) (retok nil nil (valid-table-fix table)))
         ((erp types last-expr-type? table)
          (valid-block-item (car items) table ienv))
         ((when (endp (cdr items)))
          (retok types last-expr-type? table)))
      (valid-block-item-list (cdr items) table ienv))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below

  :prepwork ((local (in-theory (enable acons))))

  ///

  (verify-guards valid-expr)

  (fty::deffixequiv-mutual valid-exprs/decls/stmts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-fundef ((fundef fundefp) (table valid-tablep) (ienv ienvp))
  :guard (fundef-unambp fundef)
  :returns (mv erp (new-table valid-tablep))
  :short "Validate a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we ignore all the GCC extensions.
     We validate the declaration specifiers, then the declarator.
     It is an error if the validation of the declarator
     returns a non-empty set of types,
     because it means that there are statement expressions
     with return statements in them,
     which can only happen inside a function's body.
     We validate the storage class specifiers.
     It is an error if the declaration is for a @('typedef').
     We also ensure that the type is the function type [C:6.9.1/2].")
   (xdoc::p
    "As with declarations, the scope of the function name
     starts just after its declarator;
     it must be added to the file scope of the validation table.
     However, recall that the validation of the declarator
     pushes a new scope for the outermost block of the function definition.
     Thus, instead of using @(tsee valid-add-ord) to add the function,
     we use @(tsee valid-add-ord-file-scope).
     But before adding it, we need to look it up,
     and again in the file scope, not the block scope
     (it is in fact legal for a function parameter
     to have the same name as the function:
     its scope is the block, and it hides the function name there);
     so we use @(tsee valid-lookup-ord-file-scope)
     instead of the usual @(tsee valid-lookup-ord).")
   (xdoc::p
    "If the name of the function is not found in the file scope,
     we add it to the file scope, with the appropriate information.
     Note that the definition status is defined,
     since we are validating a function definition.
     If the name is found already, and does not denote a function,
     it is an error;
     it is also an error if the linkages do not match.
     And it is an error if the function is alread defined.
     If all the checks pass, we add the function to the table,
     which overwrites the previous entry,
     but the only information actually overwritten
     is the definition status, from undefined to defiend,
     which is appropriate.")
   (xdoc::p
    "The declarations between declarator and body should be present
     if and only if the function declarator has a list of identifiers,
     and there should be exactly one declaration per identifier
     [C:6.9.1/5] [C:6.9.1/6].
     For now we do not check those constraints,
     but we validate any declarations
     (ensuring they return no types),
     which will add entries to the block scope in the validation table.")
   (xdoc::p
    "We ensure that the body is a compound statement,
     and we validate directly the block items;
     this way, we do not push an extra scope,
     because the outer scope must include the parameters.
     In our approximate type system,
     the function type alone does not give us enough information
     to check the types returned by the body
     against the return type of the function,
     to enforce the constraints in [C:6.8.6.4/1];
     so for now we discard the set of return types
     obtained by validating the body.")
   (xdoc::p
    "Finally we pop the scope of the function body.
     Recall that the function itself stays in the validation table,
     because we have added it to the file scope."))
  (b* (((reterr) (irr-valid-table))
       ((fundef fundef) fundef)
       ((erp type storspecs types table)
        (valid-decl-spec-list fundef.spec nil nil nil table ienv))
       ((erp & type ident more-types table)
        (valid-declor fundef.declor t type table ienv))
       ((unless (and (set::emptyp types)
                     (set::emptyp more-types)))
        (reterr (msg "The declarator of the function definition ~x0 ~
                      contains return statements."
                     (fundef-fix fundef))))
       ((erp typedefp linkage &)
        (valid-stor-spec-list storspecs ident type t table))
       ((when typedefp)
        (reterr (msg "The function definition ~x0 ~
                      declares a 'typedef' name instead of a function."
                     (fundef-fix fundef))))
       ((unless (type-case type :function))
        (reterr (msg "The function definition ~x0 has type ~x1."
                     (fundef-fix fundef) type)))
       (info? (valid-lookup-ord-file-scope ident table))
       ((erp table)
        (b* (((when (not info?))
              (retok
               (valid-add-ord-file-scope ident
                                         (make-valid-ord-info-objfun
                                          :type (type-function)
                                          :linkage linkage
                                          :defstatus (valid-defstatus-defined))
                                         table)))
             (info info?)
             ((unless (valid-ord-info-case info :objfun))
              (reterr (msg "The name of the function definition ~x0 ~
                            is already in the file scope, ~
                            but is not a function; ~
                            its associated information is ~x1."
                           (fundef-fix fundef) info)))
             ((valid-ord-info-objfun info) info)
             ((unless (type-case info.type :function))
              (reterr (msg "The name of the function definition ~x0 ~
                            is already in the file scope, ~
                            but it has type ~x1."
                           (fundef-fix fundef) info.type)))
             ((unless (equal linkage info.linkage))
              (reterr (msg "The function definition ~x0 has linkage ~s1, ~
                            which is inconsistent with the linkage ~s2 ~
                            already present in the validation table."
                           (fundef-fix fundef)
                           (if (linkage-case linkage :external)
                               "external"
                             "internal")
                           (if (linkage-case info.linkage :external)
                               "external"
                             "internal"))))
             ((when (valid-defstatus-case info.defstatus :defined))
              (reterr (msg "The function definition ~x0 ~
                            is a redefinition of the function."
                           (fundef-fix fundef)))))
          (retok
           (valid-add-ord-file-scope ident
                                     (make-valid-ord-info-objfun
                                      :type (type-function)
                                      :linkage linkage
                                      :defstatus (valid-defstatus-defined))
                                     table))))
       ((erp types table) (valid-decl-list fundef.decls table ienv))
       ((unless (set::emptyp types))
        (reterr (msg "The declarations of the function definition ~x0 ~
                      contain return statements."
                     (fundef-fix fundef))))
       ((unless (stmt-case fundef.body :compound))
        (reterr (msg "The function definition ~x0 ~
                      does not have a compound statement as body."
                     (fundef-fix fundef))))
       (items (stmt-compound->items fundef.body))
       ((erp & & table) (valid-block-item-list items table ienv))
       (table (valid-pop-scope table)))
    (retok table))
  :guard-hints (("Goal" :in-theory (disable (:e tau-system)))) ; for speed
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-extdecl ((edecl extdeclp) (table valid-tablep) (ienv ienvp))
  :guard (extdecl-unambp edecl)
  :returns (mv erp (new-table valid-tablep))
  :short "Validate an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not do anything with assembler statements.
     The empty external declaration is always valid.
     We check that declarations contain no return statements."))
  (b* (((reterr) (irr-valid-table)))
    (extdecl-case
     edecl
     :fundef (valid-fundef edecl.unwrap table ienv)
     :decl (b* (((erp types table)
                 (valid-decl edecl.unwrap table ienv))
                ((unless (set::emptyp types))
                 (reterr (msg "The top-level declaration ~x0 ~
                               contains return statements."
                              edecl.unwrap))))
             (retok table))
     :empty (retok (valid-table-fix table))
     :asm (retok (valid-table-fix table))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-extdecl-list ((edecls extdecl-listp)
                            (table valid-tablep)
                            (ienv ienvp))
  :guard (extdecl-list-unambp edecls)
  :returns (mv erp (new-table valid-tablep))
  :short "Validate a list of external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We validate them in order, threading the validation table through."))
  (b* (((reterr) (irr-valid-table))
       ((when (endp edecls)) (retok (valid-table-fix table)))
       ((erp table) (valid-extdecl (car edecls) table ienv)))
    (valid-extdecl-list (cdr edecls) table ienv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-transunit ((tunit transunitp) (gcc booleanp) (ienv ienvp))
  :guard (transunit-unambp tunit)
  :returns (mv erp (table valid-tablep))
  :short "Validate a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "If GCC extensions are not enabled,
     the initial validation table is the one
     returned by @(tsee valid-init-table).
     If GCC extensions are enabled,
     we add a number of objects and functions
     that we have encountered in practical code;
     we should eventually have a comprehensive list here.")
   (xdoc::p
    "Starting with the validation table as just described,
     we validate all the external declarations in the translation unit.
     Since these are translation units after preprocesing,
     all the referenced names must be declared in the translation unit,
     so it is appropriate to start with the initial validation table.")
   (xdoc::p
    "If validation is successful, we return the final validation table.
     For now we do no make any use of the returned table,
     but in the future we should use it to validate
     the externally linked identifiers across
     different translation units of a translation unit ensemble.
     In fact, we should probably extend this validation function
     to trim the returned validation table
     so it only has entries for identifiers with external linkage.")
   (xdoc::p
    "For each GCC function, the associated information consists of
     the function type, external linkage, and defined status.
     The latter two seem reasonable, given that these identifiers
     are visible and have the same meaning in every translation unit,
     and have their own (built-in) definitions.
     For each GCC object, the associated information consists of
     the unknown type, external linkage, and defined status;
     the rationale for the latter two is the same as for functions."))
  (b* (((reterr) (irr-valid-table))
       (table (valid-init-table))
       (table
         (if gcc
             (b* ((finfo (make-valid-ord-info-objfun
                          :type (type-function)
                          :linkage (linkage-external)
                          :defstatus (valid-defstatus-defined)))
                  (oinfo (make-valid-ord-info-objfun
                          :type (type-unknown)
                          :linkage (linkage-external)
                          :defstatus (valid-defstatus-defined)))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__atomic_signal_fence") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_add_overflow") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_bswap16") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_bswap32") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_bswap64") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_choose_expr") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_clz") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_clzl") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_clzll") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_constant_p") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_ctzl") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_dynamic_object_size") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_expect") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_memchr") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_memcmp") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_memcpy") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_memset") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_mul_overflow") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_object_size") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_return_address") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_strcpy") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_strlen") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_strncat") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_strncpy") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_sub_overflow") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_unreachable") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_va_end") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__builtin_va_start") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__eax") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__ebx") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__ecx") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__edx") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__esi") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__edi") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__ebp") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__esp") oinfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_add_and_fetch") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_and_and_fetch") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_bool_compare_and_swap") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_fetch_and_add") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_fetch_and_and") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_fetch_and_nand") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_fetch_and_or") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_fetch_and_sub") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_fetch_and_xor") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_lock_release") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_lock_test_and_set") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_nand_and_fetch") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_or_and_fetch") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_sub_and_fetch") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_synchronize") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_val_compare_and_swap") finfo table))
                  (table
                    (valid-add-ord-file-scope
                     (ident "__sync_xor_and_fetch") finfo table)))
               table)
           table)))
    (valid-extdecl-list (transunit->decls tunit) table ienv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-transunit-ensemble ((tunits transunit-ensemblep)
                                  (gcc booleanp)
                                  (ienv ienvp))
  :guard (transunit-ensemble-unambp tunits)
  :returns erp
  :short "Validate a translation unit ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "We validate each translation unit.
     As mentioned in @(tsee valid-transunit),
     for now we discard the result validation tables,
     but in the future we should cross-check them.")
   (xdoc::p
    "If validation is successful, we return no information (@('nil')).
     Otherwise, we return an error message,
     which a caller can show to the user in an event macro."))
  (valid-transunit-ensemble-loop (transunit-ensemble->unwrap tunits) gcc ienv)
  :prepwork
  ((define valid-transunit-ensemble-loop ((map filepath-transunit-mapp)
                                          (gcc booleanp)
                                          (ienv ienvp))
     :guard (transunit-ensemble-unambp-loop map)
     :returns erp
     :parents nil
     (b* (((reterr))
          ((when (omap::emptyp map)) (retok))
          ((erp &) (valid-transunit (omap::head-val map) gcc ienv))
          ((erp) (valid-transunit-ensemble-loop (omap::tail map) gcc ienv)))
       (retok))
     ///
     (fty::deffixequiv valid-transunit-ensemble-loop
       :args ((gcc booleanp) (ienv ienvp)))))
  :hooks (:fix))
