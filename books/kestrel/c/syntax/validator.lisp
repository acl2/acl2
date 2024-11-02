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

(define type-spec-list-signed-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('signed')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :signed))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('unsigned')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :unsigned))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('int')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :int))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('short')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :short))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('long')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :long))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('float')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :float))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-double-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('double')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :double))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Complex')."
  (and (= (len tyspecs) 1)
       (type-spec-case (nth 0 tyspecs) :complex))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed int') or @('int signed')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :signed)
                (type-spec-case (nth 1 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :signed))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned int') or @('int unsigned')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :unsigned)
                (type-spec-case (nth 1 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :unsigned))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed short') or @('short signed')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :signed)
                (type-spec-case (nth 1 tyspecs) :short))
           (and (type-spec-case (nth 0 tyspecs) :short)
                (type-spec-case (nth 1 tyspecs) :signed))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned short') or @('short unsigned')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :unsigned)
                (type-spec-case (nth 1 tyspecs) :short))
           (and (type-spec-case (nth 0 tyspecs) :short)
                (type-spec-case (nth 1 tyspecs) :unsigned))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long') or @('long signed')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :signed)
                (type-spec-case (nth 1 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :signed))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long') or @('long unsigned')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :unsigned)
                (type-spec-case (nth 1 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :unsigned))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long long')
          or @('long signed long')
          or @('long long signed')."
  (and (= (len tyspecs) 3)
       (or (and (type-spec-case (nth 0 tyspecs) :signed)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :signed)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :signed))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long long')
          or @('long unsigned long')
          or @('long long unsigned')."
  (and (= (len tyspecs) 3)
       (or (and (type-spec-case (nth 0 tyspecs) :unsigned)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :unsigned)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :unsigned))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long int')
          or @('int signed long')
          or @('long int signed')."
  (and (= (len tyspecs) 3)
       (or (and (type-spec-case (nth 0 tyspecs) :signed)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :signed)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :int)
                (type-spec-case (nth 2 tyspecs) :signed))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long int')
          or @('int unsigned long')
          or @('long int unsigned')."
  (and (= (len tyspecs) 3)
       (or (and (type-spec-case (nth 0 tyspecs) :unsigned)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :unsigned)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :int)
                (type-spec-case (nth 2 tyspecs) :unsigned))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('short int') or @('int short')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :short)
                (type-spec-case (nth 1 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :short))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long int') or @('int long')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long long int')
          or @('int long long')
          or @('long int long')."
  (and (= (len tyspecs) 3)
       (or (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :int))
           (and (type-spec-case (nth 0 tyspecs) :int)
                (type-spec-case (nth 1 tyspecs) :long)
                (type-spec-case (nth 2 tyspecs) :long))
           (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :int)
                (type-spec-case (nth 2 tyspecs) :long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-double-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('double _Complex') or @('_Complex double')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :double)
                (type-spec-case (nth 1 tyspecs) :complex))
           (and (type-spec-case (nth 0 tyspecs) :complex)
                (type-spec-case (nth 1 tyspecs) :double))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long _Complex') or @('_Complex long')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :complex))
           (and (type-spec-case (nth 0 tyspecs) :complex)
                (type-spec-case (nth 1 tyspecs) :long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-double-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long double') or @('double long')."
  (and (= (len tyspecs) 2)
       (or (and (type-spec-case (nth 0 tyspecs) :long)
                (type-spec-case (nth 1 tyspecs) :double))
           (and (type-spec-case (nth 0 tyspecs) :double)
                (type-spec-case (nth 1 tyspecs) :long))))
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
     that information also includes the linkage [C:6.2.2].
     For enumeration constants and for @('typedef') names,
     for now we only track that they are
     enumeration constants and @('typedef') names.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)))
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
  :guard (> (valid-table-num-scopes table) 0)
  :returns (new-table valid-tablep)
  :short "Pop a scope from the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard requires that there are is at least one scope.")
   (xdoc::p
    "The popped scope is discarded."))
  (b* ((scopes (valid-table->scopes table))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-add-ord ((ident identp)
                       (info valid-ord-infop)
                       (table valid-tablep))
  :guard (> (valid-table-num-scopes table) 0)
  :returns (new-table valid-tablep)
  :short "Add an ordinary identifier to the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the information to associate to the identifier.")
   (xdoc::p
    "The identifier is always added to
     the first (i.e. innermost, i.e. current) scope.
     The guard requires the existence of at least one scope;
     recall that there must be always a file scope.")
   (xdoc::p
    "If the identifier is already present in the current scope,
     its information is overwritten,
     but we only call this function after checking that
     this overwriting is acceptable,
     i.e. when it ``refines'' the validation information for the identifier.
     We could consider adding a guard to this function
     that characterizes the acceptable overwriting."))
  (b* ((scopes (valid-table->scopes table))
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
     mentioned in [C:6.4.4.4/4]."))
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
   :v 11)
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

(define valid-stor-spec ((storspec stor-specp)
                         (storspecs stor-spec-listp))
  :returns (mv erp
               (typedefp booleanp)
               (linkage? linkage-optionp)
               (lifetime? lifetime-optionp)
               (new-storspecs stor-spec-listp))
  :short "Validate a storage class specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Storage class specifiers [C:6.7.1]
     appear as declaration specifiers,
     which appear in declarations.
     Declaration specifiers indicate the linkage and storage duration
     of the declared identifiers [C:6.7/6];
     more precisely, it is storage class specifiers that indicate that.
     But storage class specifiers also include @('typedef'),
     mainly for syntactic convenience [C:6.7.1/5],
     which does not determine any linkage or storage duration,
     but indicates that a @('typedef') name is being declared.
     Thus, storage class specifiers may indicate various kinds of information,
     which we return as results,
     along with the list of preceding storage class specifiers.")
   (xdoc::p
    "A @('typedef') must be preceded by no storage class specifier [C:6.7.1/2].
     A @('typedef') specifies that a @('typedef') name is being declared,
     so we return @('t') as the @('typedef') flag result.
     A @('typedef') name is not an object or function,
     and thus it has no linkage [C:6.2.2/6]:
     so we return that as the linkage result.
     Since a @('typedef') name is not an object,
     it does not have a storage duration [C:6.2.4/1],
     so we return @('nil') as the liftetime result.")
   (xdoc::p
    "An @('extern') may be only preceded by @('_Thread_local') [C:6.7.1/2].
     An @('extern') does not specify a @('typedef') name,
     so we return @('nil') as the @('typedef') flag result.
     An @('extern') normally specifies external linkage
     if it is in the first or only declaration of the identifier [C:6.2.2/4],
     so we return external linkage as result;
     this may be overridden (in other validation code)
     if the declaration is not the first or only one [C:6.2.2/4].
     If there is a preceding @('_Thread_local'),
     the storage duration is thread [C:6.2.4/4]
     (in this case the input @('lifetime?') would be already that,
     although we do not explicate this invariant).
     If there is no preceding @('_Thread_local'),
     we return the static storage duration [C:6.2.4/3],
     but this will be changed to thread if a @('_Thread_local') follows.")
   (xdoc::p
    "A @('static') is treated similarly to an @('extern'),
     except that the linkage is internal [C:6.2.2/3].")
   (xdoc::p
    "A @('_Thread_local') may be preceded
     only by an @('extern') or a @('static')
     [C:6.7.1/2].
     If nothing precedes it,
     we only determine the storage duration as thread,
     without determining the linkage.
     If it is preceded by @('extern') or @('static'),
     we also determine the linkage, as external or internal,
     in analogy with the situations, discussed above,
     in which the order of the two storage class specifiers is swapped.")
   (xdoc::p
    "An @('auto') or @('register') may not be preceded by anything [C:6.7.1/2].
     These two give the same results:
     no linkage, and automatic storage duration."))
  (b* (((reterr) nil nil nil nil)
       (msg-bad-preceding (msg "The storage class specifier ~x0 ~
                                must not be preceded by ~x1."
                               (stor-spec-fix storspec)
                               (stor-spec-list-fix storspecs)))
       (ext-storspecs (rcons (stor-spec-fix storspec)
                             (stor-spec-list-fix storspecs))))
    (stor-spec-case
     storspec
     :typedef (cond
               ((endp storspecs) ; typedef
                (retok t
                       (linkage-none)
                       nil
                       ext-storspecs))
               (t ; other typedef
                (reterr msg-bad-preceding)))
     :extern (cond
              ((endp storspecs) ; extern
               (retok nil
                      (linkage-external)
                      (lifetime-static)
                      ext-storspecs))
              ((and (consp storspecs)
                    (endp (cdr storspecs))
                    (stor-spec-case (car storspecs)
                                    :threadloc)) ; _Thread_local extern
               (retok nil
                      (linkage-external)
                      (lifetime-thread)
                      ext-storspecs))
              (t ; other extern
               (reterr msg-bad-preceding)))
     :static (cond
              ((endp storspecs) ; static
               (retok nil
                      (linkage-internal)
                      (lifetime-static)
                      ext-storspecs))
              ((and (consp storspecs)
                    (endp (cdr storspecs))
                    (stor-spec-case (car storspecs)
                                    :threadloc)) ; _Thread_local static
               (retok nil
                      (linkage-internal)
                      (lifetime-thread)
                      ext-storspecs))
              (t ; other static
               (reterr msg-bad-preceding)))
     :threadloc (cond
                 ((endp storspecs) ; _Thread_local
                  (retok nil
                         nil
                         (lifetime-thread)
                         ext-storspecs))
                 ((and (consp storspecs)
                       (endp (cdr storspecs))
                       (stor-spec-case (car storspecs)
                                       :extern)) ; extern _Thread_local
                  (retok nil
                         (linkage-external)
                         (lifetime-thread)
                         ext-storspecs))
                 ((and (consp storspecs)
                       (endp (cdr storspecs))
                       (stor-spec-case (car storspecs)
                                       :static)) ; static _Thread_local
                  (retok nil
                         (linkage-internal)
                         (lifetime-thread)
                         ext-storspecs))
                 (t ; other _Thread_local
                  (reterr msg-bad-preceding)))
     :auto (cond
            ((endp storspecs) ; auto
             (retok nil
                    (linkage-none)
                    (lifetime-auto)
                    ext-storspecs))
            (t ; other auto
             (reterr msg-bad-preceding)))
     :register (cond
                ((endp storspecs) ; register
                 (retok nil
                        (linkage-none)
                        (lifetime-auto)
                        ext-storspecs))
                (t ; other register
                 (reterr msg-bad-preceding)))))
  :hooks (:fix))

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
    :returns (mv erp (type typep) (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the type of the expression,
       along with a possibly updated validation table.
       For now we do not distinguish lvalues [C:6.3.2.1/1].
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
    (b* (((reterr) (irr-type) (irr-valid-table)))
      (expr-case
       expr
       :ident (b* (((erp type) (valid-var expr.ident table)))
                (retok type (valid-table-fix table)))
       :const (b* (((erp type) (valid-const expr.const table ienv)))
                (retok type (valid-table-fix table)))
       :string (b* (((erp type) (valid-stringlit-list expr.literals)))
                 (retok type (valid-table-fix table)))
       :paren (valid-expr expr.unwrap table ienv)
       :gensel (b* (((erp type table) (valid-expr expr.control table ienv))
                    ((erp type-alist table)
                     (valid-genassoc-list expr.assocs table ienv))
                    ((erp type) (valid-gensel expr type type-alist)))
                 (retok type table))
       :arrsub (b* (((erp type-arg1 table) (valid-expr expr.arg1 table ienv))
                    ((erp type-arg2 table) (valid-expr expr.arg2 table ienv))
                    ((erp type) (valid-arrsub expr type-arg1 type-arg2)))
                 (retok type table))
       :funcall (b* (((erp type-fun table) (valid-expr expr.fun table ienv))
                     ((erp types-arg table) (valid-expr-list expr.args
                                                             table
                                                             ienv))
                     ((erp type) (valid-funcall expr type-fun types-arg)))
                  (retok type table))
       :member (b* (((erp type-arg table) (valid-expr expr.arg table ienv))
                    ((erp type) (valid-member expr type-arg)))
                 (retok type table))
       :memberp (b* (((erp type-arg table) (valid-expr expr.arg table ienv))
                     ((erp type) (valid-memberp expr type-arg)))
                  (retok type table))
       :complit (b* (((erp type table) (valid-tyname expr.type table ienv))
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
                     ((erp table)
                      (valid-desiniter-list
                       expr.elems type lifetime table ienv)))
                  (retok type table))
       :unary (b* (((erp type-arg table) (valid-expr expr.arg table ienv))
                   ((erp type) (valid-unary expr expr.op type-arg ienv)))
                (retok type table))
       :sizeof (b* (((erp type table) (valid-tyname expr.type table ienv))
                    ((erp type1) (valid-sizeof/alignof expr type)))
                 (retok type1 table))
       :alignof (b* (((erp type table) (valid-tyname expr.type table ienv))
                     ((erp type1) (valid-sizeof/alignof expr type)))
                  (retok type1 table))
       :cast (b* (((erp type-cast table) (valid-tyname expr.type table ienv))
                  ((erp type-arg table) (valid-expr expr.arg table ienv))
                  ((erp type) (valid-cast expr type-cast type-arg)))
               (retok type table))
       :binary (b* (((erp type-arg1 table) (valid-expr expr.arg1 table ienv))
                    ((erp type-arg2 table) (valid-expr expr.arg2 table ienv))
                    ((erp type)
                     (valid-binary expr expr.op type-arg1 type-arg2 ienv)))
                 (retok type table))
       :cond (b* (((erp type-test table) (valid-expr expr.test table ienv))
                  ((erp type-then? table) (valid-expr-option expr.then
                                                             table
                                                             ienv))
                  (type-then (or type-then? type-test))
                  ((erp type-else table) (valid-expr expr.else table ienv))
                  ((erp type)
                   (valid-cond expr type-test type-then type-else ienv)))
               (retok type table))
       :comma (b* (((erp & table) (valid-expr expr.first table ienv))
                   ((erp type table) (valid-expr expr.next table ienv)))
                (retok type table))
       :stmt (reterr :todo)
       :tycompat (b* (((erp & table) (valid-tyname expr.type1 table ienv))
                      ((erp & table) (valid-tyname expr.type2 table ienv)))
                   (retok (type-sint) table))
       :offsetof (b* (((erp & table) (valid-tyname expr.type table ienv))
                      ((erp table)
                       (valid-member-designor expr.member table ienv)))
                   (retok (type-unknown) table))
       :otherwise (prog2$ (impossible) (reterr t))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-list ((exprs expr-listp) (table valid-tablep) (ienv ienvp))
    :guard (expr-list-unambp exprs)
    :returns (mv erp (types type-listp) (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate all the expressions, one after the other,
       and we return the resulting types, in the same order.
       We also return a possibly updated validation table."))
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp exprs)) (retok nil (valid-table-fix table)))
         ((erp type table) (valid-expr (car exprs) table ienv))
         ((erp types table) (valid-expr-list (cdr exprs) table ienv)))
      (retok (cons type types) table))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-option ((expr? expr-optionp)
                             (table valid-tablep)
                             (ienv ienvp))
    :guard (expr-option-unambp expr?)
    :returns (mv erp (type? type-optionp) (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no expression,
       we return @('nil') as the optional type,
       and the validation table unchanged."))
    (b* (((reterr) nil (irr-valid-table)))
      (expr-option-case
       expr?
       :some (valid-expr expr?.val table ienv)
       :none (retok nil (valid-table-fix table))))
    :measure (expr-option-count expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr ((cexpr const-exprp)
                            (table valid-tablep)
                            (ienv ienvp))
    :guard (const-expr-unambp cexpr)
    :returns (mv erp (type typep) (new-table valid-tablep))
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
    (b* (((reterr) (irr-type) (irr-valid-table)))
      (valid-expr (const-expr->unwrap cexpr) table ienv))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc ((genassoc genassocp)
                          (table valid-tablep)
                          (ienv ienvp))
    :guard (genassoc-unambp genassoc)
    :returns (mv erp
                 (tyname-type type-optionp)
                 (expr-type typep)
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
    (b* (((reterr) nil (irr-type) (irr-valid-table)))
      (genassoc-case
       genassoc
       :type (b* (((erp tyname-type table)
                   (valid-tyname genassoc.type table ienv))
                  ((erp expr-type table)
                   (valid-expr genassoc.expr table ienv)))
               (retok tyname-type expr-type table))
       :default (b* (((erp expr-type table)
                      (valid-expr genassoc.expr table ienv)))
                  (retok nil expr-type table))))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc-list ((genassocs genassoc-listp)
                               (table valid-tablep)
                               (ienv ienvp))
    :guard (genassoc-list-unambp genassocs)
    :returns (mv erp
                 (type-alist type-option-type-alistp)
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
    (b* (((reterr) nil (irr-valid-table))
         ((when (endp genassocs)) (retok nil (valid-table-fix table)))
         ((erp tyname-type? expr-type table)
          (valid-genassoc (car genassocs) table ienv))
         ((erp type-alist table)
          (valid-genassoc-list (cdr genassocs) table ienv)))
      (retok (acons tyname-type? expr-type type-alist) table))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-member-designor ((memdesign member-designorp)
                                 (table valid-tablep)
                                 (ienv ienvp))
    :guard (member-designor-unambp memdesign)
    :returns (mv erp (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a member designator."
    (b* (((reterr) (irr-valid-table)))
      (member-designor-case
       memdesign
       :ident (retok (valid-table-fix table))
       :dot (valid-member-designor memdesign.member table ienv)
       :sub (b* (((erp table) (valid-member-designor
                               memdesign.member table ienv))
                 ((erp & table) (valid-expr memdesign.index table ienv)))
              (retok table))))
    :measure (member-designor-count memdesign))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-type-spec ((tyspec type-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (and (type-spec-unambp tyspec)
                (not (and type? tyspecs)))
    :returns (mv erp
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
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
       threading though information about
       either a definitely determined type (e.g. the void type),
       or type specifiers that may (or not) already specifiy a type
       but that would specify a different type if additional ones are found.
       This information consists of the @('type?') and @('tyspecs') inputs,
       which the guard requires to be not both non-@('nil'):
       if we have determined a type,
       we do not need to track preceding type specifiers;
       and if we are tracking preceding type specifiers,
       we have not determined a type yet.
       Initially they are both @('nil').")
     (xdoc::p
      "After going through all the type specifiers,
       we will either have a type or a list of type specifiers:
       the latter may or may not denote a type,
       and our validation will check that.
       But that is done elsewhere:
       this validation function operates on a single type specifier.")
     (xdoc::p
      "Although we do not explicate that in the guard,
       the @('tyspecs') list always satisfies certain invariants,
       such as the fact that it does not contain
       both @('signed') and @('unsigned'),
       because validation would have failed before reaching this point.
       But our code in this validation function relies on these invariants.")
     (xdoc::p
      "When this function is called with a non-@('nil') @('type?'),
       it means that the type has been determined,
       and no more type specifiers can follow.
       So we return an error in this case.")
     (xdoc::p
      "A @('void') or @('_Bool') type specifier
       determines a type,
       and cannot be preceded by any other type specifier.")
     (xdoc::p
      "A @('char') type specifier can be only preceded by
       a single @('signed') or @('unsigned') type specifier,
       in which case they together specify a type.
       If there is no preceding type specifier,
       @('char') alone does not specify a definite type,
       because it may be followed by @('signed') or @('unsigned').")
     (xdoc::p
      "A @('short') type specifier may be preceded
       by @('signed') and @('int') (in any order),
       or by @('unsigned') and @('int') (in any order),
       in which cases the type is determined
       and no more type specifiers are allowed.
       If @('short') is preceded only by @('signed') or @('unsigned'),
       the type is also determined,
       but @('int') may be allowed after that,
       so we delay the determination of the type in this case,
       otherwise we could not check for duplicate @('int')s.
       If @('short') is preceded by @('int'),
       the type is not determined yet,
       because an @('unsigned') may follow or not.
       If @('short') is not preceded by anything,
       the type is not determined yet either,
       because an @('unsigned') may follow or not.
       Any other preceding type specifiers are disallowed.")
     (xdoc::p
      "An @('int') type specifier may be preceded
       by @('signed') and @('short') (in any order),
       or by @('unsigned') and @('short') (in any order),
       or by @('signed') and @('long') and @('long') (in any order),
       or by @('unsigned') and @('long') and @('long') (in any order),
       in which cases the type is determined
       and no more type specifiers are allowed.
       If @('int') is preceded only
       by @('signed') or @('unsigned') or @('long') or @('short'),
       or by @('signed') and @('long') (in any order),
       or by @('unsigned') and @('long') (in any order),
       the type is not determined, so we add the type specifier to the list.
       If @('int') is not preceded by anything,
       the type is not determined yet either,
       because an @('unsigned') or a @('short') or a @('long') or two @('long')s
       may follow or not.
       Any other preceding type specifiers are disallowed.")
     (xdoc::p
      "A @('long') type specifier may be preceded
       by @('signed') and @('long') and @('int') (in any order),
       or by @('unsigned') and @('long') and @('int') (in any order),
       or by @('double') and @('_Complex') (in any order),
       in which cases the type is determined
       and no more type specifiers are allowed.
       If @('long') is preceded only
       by @('signed') or @('unsigned')
       or @('int') or @('long')
       or @('double') or @('_Complex'),
       or by @('signed') and @('int') (in any order),
       or by @('unsigned') and @('int') (in any order),
       or by @('signed') and @('short') (in any order),
       or by @('unsigned') and @('short') (in any order),
       or by @('signed') and @('long') (in any order),
       or by @('unsigned') and @('long') (in any order),
       the type is not determined, so we add the type specifier to the list.
       If @('long') is preceded only
       by @('signed') and @('long') (in any order)
       or by @('unsigned') and @('long') (in any order),
       the type is determined, but we delay its determination so that
       we can allow an @('int') to follow
       while enforcing that there are no duplicate @('int')s.
       If @('long') is not preceded by anything,
       the type is not determined yet either,
       because an @('unsigned') or another @('long') may follow.
       Any other preceding type specifiers are disallowed.")
     (xdoc::p
      "A @('float') type specifier
       may be preceded by a @('_Complex') type specifier,
       in which case the type is determined.
       If the @('float') is not preceded by anything,
       the type is not determined yet, because @('_Complex') may follow.
       Nothing else can precede @('float').")
     (xdoc::p
      "A @('double') type specifier may be preceded
       by @('long') and @('_Complex') (in any order),
       in which case the type is determined.
       If @('double') is preceded only by @('long') or @('_Complex'),
       the type is not determined.
       Nothing else can precede @('double').")
     (xdoc::p
      "A @('signed') or @('unsigned') type specifier may be preceded
       by @('short') and @('int') (in any order)
       or by @('long') and @('long') and @('int') (in any order),
       in which cases the type is determined.
       If it is preceded only by subsequences of those,
       including the empty subsequence,
       the type is not determined,
       or it is but there may be an additional type specifier
       to allow without duplicates.")
     (xdoc::p
      "A @('_Complex') type specifier may be preceded
       by @('long') and @('double') (in any order),
       in which case the type is determined.
       If it is preceded by any subsequence of those,
       the type is not determined yet.")
     (xdoc::p
      "Our current type system does not model atomic types,
       so for an atomic type we validate the type name
       and we regard the atomic type as denoting the same type.
       No type specifier may precede an atomic type.")
     (xdoc::p
      "For a structure or union or enumeration type specifier,
       we recursively validate their sub-structures,
       and the type is determined in all cases.
       No type specifier may precede this one.")
     (xdoc::p
      "Since our currently approximate type system
       does not handle @('typedef') types,
       we just regard it as denoting an unknown type.
       No type specifier may precede this one.")
     (xdoc::p
      "For now, for simplicity, we regard
       all the type specifiers that are GCC extensions
       to determine the unknown type;
       except for an empty structure type specifier,
       which determines the structure type.
       None of them may be preceded by other type specifiers,
       so we check that."))
    (b* (((reterr) nil nil (irr-valid-table))
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
       :void (cond ((endp tyspecs) ; void
                    (retok (type-void) nil same-table))
                   (t ; other void
                    (reterr msg-bad-preceding)))
       :char (cond ((endp tyspecs) ; char
                    (retok nil (list (type-spec-fix tyspec)) same-table))
                   ((type-spec-list-signed-p tyspecs) ; signed char
                    (retok (type-schar) nil same-table))
                   ((type-spec-list-unsigned-p tyspecs) ; unsigned char
                    (retok (type-uchar) nil same-table))
                   (t ; other char
                    (reterr msg-bad-preceding)))
       :short (cond
               ((endp tyspecs) ; short
                (retok nil ext-tyspecs same-table))
               ((or (type-spec-list-signed-p tyspecs) ; signed short
                    (type-spec-list-unsigned-p tyspecs) ; unsigned short
                    (type-spec-list-int-p tyspecs)) ; int short
                (retok nil ext-tyspecs same-table))
               ((type-spec-list-signed-int-p tyspecs) ; signed int short
                (retok (type-sshort) nil same-table))
               ((type-spec-list-unsigned-int-p tyspecs) ; unsigned int short
                (retok (type-ushort) nil same-table))
               (t ; other short
                (reterr msg-bad-preceding)))
       :int (cond
             ((endp tyspecs) ; short
              (retok nil ext-tyspecs same-table))
             ((or (type-spec-list-signed-p tyspecs) ; signed int
                  (type-spec-list-unsigned-p tyspecs) ; unsigned int
                  (type-spec-list-short-p tyspecs) ; short int
                  (type-spec-list-long-p tyspecs)) ; long int
              (retok nil ext-tyspecs same-table))
             ((type-spec-list-signed-short-p tyspecs) ; signed short int
              (retok (type-sshort) nil same-table))
             ((type-spec-list-unsigned-short-p tyspecs) ; unsigned short int
              (retok (type-ushort) nil same-table))
             ((or (type-spec-list-signed-long-p tyspecs) ; signed long int
                  (type-spec-list-unsigned-long-p tyspecs)) ; unsigned long int
              (retok nil ext-tyspecs same-table))
             ((type-spec-list-signed-long-long-p ; signed long long int
               tyspecs)
              (retok (type-sllong) nil same-table))
             ((type-spec-list-unsigned-long-long-p ; unsigned long long int
               tyspecs)
              (retok (type-ullong) nil same-table))
             (t ; other int
              (reterr msg-bad-preceding)))
       :long (cond
              ((endp tyspecs) ; long
               (retok nil ext-tyspecs same-table))
              ((or (type-spec-list-signed-p tyspecs) ; signed long
                   (type-spec-list-unsigned-p tyspecs) ; unsigned long
                   (type-spec-list-int-p tyspecs) ; int long
                   (type-spec-list-long-p tyspecs) ; long long
                   (type-spec-list-double-p tyspecs) ; double long
                   (type-spec-list-complex-p tyspecs)) ; _Complex long
               (retok nil ext-tyspecs same-table))
              ((or (type-spec-list-signed-int-p ; signed int long
                    tyspecs)
                   (type-spec-list-unsigned-int-p ; unsigned int long
                    tyspecs)
                   (type-spec-list-signed-long-p ; signed long long
                    tyspecs)
                   (type-spec-list-unsigned-long-p ; unsigned long long
                    tyspecs))
               (retok nil ext-tyspecs same-table))
              ((type-spec-list-signed-long-int-p ; signed long int long
                tyspecs)
               (retok (type-sllong) nil same-table))
              ((type-spec-list-unsigned-long-int-p ; unsigned long int long
                tyspecs)
               (retok (type-ullong) nil same-table))
              ((type-spec-list-double-complex-p tyspecs) ; double _Complex long
               (retok (type-doublec) nil same-table))
              (t ; other long
               (reterr msg-bad-preceding)))
       :float (cond
               ((endp tyspecs) ; float
                (retok nil ext-tyspecs same-table))
               ((type-spec-list-complex-p tyspecs) ; _Complex float
                (retok (type-floatc) nil same-table))
               (t ; other float
                (reterr msg-bad-preceding)))
       :double (cond
                ((endp tyspecs) ; double
                 (retok nil ext-tyspecs same-table))
                ((or (type-spec-list-long-p tyspecs) ; long double
                     (type-spec-list-complex-p tyspecs)) ; _Complex double
                 (retok nil ext-tyspecs same-table))
                ((type-spec-list-long-complex-p tyspecs) ; long _Complex double
                 (retok (type-ldoublec) nil same-table))
                (t ; other double
                 (reterr msg-bad-preceding)))
       :signed (cond
                ((endp tyspecs) ; signed
                 (retok nil ext-tyspecs same-table))
                ((or (type-spec-list-int-p tyspecs) ; int signed
                     (type-spec-list-short-p tyspecs) ; short signed
                     (type-spec-list-long-p tyspecs)) ; long signed
                 (retok nil ext-tyspecs same-table))
                ((type-spec-list-short-int-p tyspecs) ; short int signed
                 (retok (type-sshort) nil same-table))
                ((type-spec-list-long-int-p tyspecs) ; long int signed
                 (retok nil ext-tyspecs same-table))
                ((type-spec-list-long-long-int-p tyspecs) ; long long int signed
                 (retok (type-sllong) nil same-table))
                (t ; other signed
                 (reterr msg-bad-preceding)))
       :unsigned (cond
                  ((endp tyspecs) ; unsigned
                   (retok nil ext-tyspecs same-table))
                  ((or (type-spec-list-int-p tyspecs) ; int unsigned
                       (type-spec-list-short-p tyspecs) ; short unsigned
                       (type-spec-list-long-p tyspecs)) ; long unsigned
                   (retok nil ext-tyspecs same-table))
                  ((type-spec-list-short-int-p tyspecs) ; short int unsigned
                   (retok (type-ushort) nil same-table))
                  ((type-spec-list-long-int-p tyspecs) ; long int unsigned
                   (retok nil ext-tyspecs same-table))
                  ((type-spec-list-long-long-int-p ; long long int unsigned
                    tyspecs)
                   (retok (type-ullong) nil same-table))
                  (t ; other unsigned
                   (reterr msg-bad-preceding)))
       :bool (cond ((endp tyspecs) ; _Bool
                    (retok (type-bool) nil same-table))
                   (t ; other _Bool
                    (reterr msg-bad-preceding)))
       :complex (cond
                 ((endp tyspecs) ; _Complex
                  (retok nil ext-tyspecs same-table))
                 ((or (type-spec-list-double-p tyspecs) ; double _Complex
                      (type-spec-list-long-p tyspecs)) ; long _Complex
                  (retok nil ext-tyspecs same-table))
                 ((type-spec-list-long-double-p tyspecs) ; long double _Complex
                  (retok (type-ldoublec) nil same-table))
                 (t ; other _Complex
                  (reterr msg-bad-preceding)))
       :atomic (b* (((erp type table)
                     (valid-tyname tyspec.type table ienv))
                    ((unless (endp tyspecs)) (reterr msg-bad-preceding)))
                 (retok type nil table))
       :struct (cond ((endp tyspecs) ; struct...
                      (b* (((erp table) (mv :todo-strunispec same-table)))
                        (retok (type-struct) nil table)))
                     (t ; other struct...
                      (reterr msg-bad-preceding)))
       :union (cond ((endp tyspecs) ; union...
                     (b* (((erp table) (mv :todo-strunispec same-table)))
                       (retok (type-union) nil table)))
                    (t ; other union...
                     (reterr msg-bad-preceding)))
       :enum (cond ((endp tyspecs) ; enum...
                    (b* (((erp table) (mv :todo-enumspec same-table)))
                      (retok (type-enum) nil table)))
                   (t ; other enum...
                    (reterr msg-bad-preceding)))
       :typedef (cond ((endp tyspecs) ; typedef...
                       (retok (type-unknown) nil same-table))
                      (t ; other typedef...
                       (reterr msg-bad-preceding)))
       :int128 (cond ((endp tyspecs) ; __int128
                      (retok (type-unknown) nil same-table))
                     (t ; other __int128
                      (reterr msg-bad-preceding)))
       :float128 (cond ((endp tyspecs) ; _Float128
                        (retok (type-unknown) nil same-table))
                       (t ; other _Float128
                        (reterr msg-bad-preceding)))
       :builtin-va-list (cond ((endp tyspecs) ; __buildin_va_list
                               (retok (type-unknown) nil same-table))
                              (t ; other __buildin_va_list
                               (reterr msg-bad-preceding)))
       :struct-empty (cond ((endp tyspecs) ; struct... {}
                            (retok (type-struct) nil same-table))
                           (t ; other struct... {}
                            (reterr msg-bad-preceding)))
       :typeof-expr (cond ((endp tyspecs) ; typeof...
                           (retok (type-unknown) nil same-table))
                          (t ; other typeof...
                           (reterr msg-bad-preceding)))
       :typeof-type (cond ((endp tyspecs) ; typeof...
                           (retok (type-unknown) nil same-table))
                          (t ; other typeof...
                           (reterr msg-bad-preceding)))
       :auto-type (cond ((endp tyspecs) ; __auto_type
                         (retok (type-unknown) nil same-table))
                        (t ; other __auto_type
                         (reterr msg-bad-preceding)))
       :otherwise (prog2$ (impossible) (reterr t))))
    :measure (type-spec-count tyspec)

    ///

    (defret not-type-and-type-spec-list-of-valid-type-spec
      (not (and new-type? new-tyspecs))
      :hints
      (("Goal"
        :expand (valid-type-spec tyspec type? tyspecs table ienv)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer ((initer initerp)
                        (target-type typep)
                        (lifetime lifetimep)
                        (table valid-tablep)
                        (ienv ienvp))
    :guard (and (initer-unambp initer)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp (new-table valid-tablep))
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
    (b* (((reterr) (irr-valid-table)))
      (cond
       ((type-case target-type :unknown)
        (initer-case
         initer
         :single (b* (((erp & table) (valid-expr initer.expr table ienv)))
                   (retok table))
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
                            ((unless (endp desiniter.design))
                             (mv (msg "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is a singleton ~
                                       but it has designators."
                                      (initer-fix initer)
                                      (type-fix target-type))
                                 (irr-expr)))
                            ((unless (initer-case desiniter.init :single))
                             (mv (msg "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is a singleton without designators ~
                                       but the inner initializer ~
                                       is not a single expression."
                                      (initer-fix initer)
                                      (type-fix target-type))
                                 (irr-expr))))
                         (mv nil (initer-single->expr desiniter.init))))))
             ((erp init-type table) (valid-expr expr table ienv))
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
          (retok table)))
       ((and (or (type-case target-type :struct)
                 (type-case target-type :union))
             (initer-case initer :single)
             (lifetime-case lifetime :auto))
        (b* (((erp type table)
              (valid-expr (initer-single->expr initer) table ienv))
             ((unless (type-equiv type target-type))
              (reterr (msg "The initializer ~x0 ~
                            for the target type ~x1 ~
                            of an object in automatic storage ~
                            has type ~x2."
                           (initer-fix initer)
                           (type-fix target-type)
                           type))))
          (retok table)))
       ((and (type-case target-type :array)
             (initer-case initer :single)
             (expr-case (initer-single->expr initer) :string))
        (b* (((erp &) (valid-stringlit-list
                       (expr-string->literals (initer-single->expr initer)))))
          (retok (valid-table-fix table))))
       ((and (or (type-aggregatep target-type)
                 (type-case target-type :union))
             (initer-case initer :list))
        (valid-desiniter-list
         (initer-list->elems initer) target-type lifetime table ienv))
       (t (reterr (msg "The initializer ~x0 ~
                        for the target type ~x1 ~
                        is disallowed."
                       (initer-fix initer) (type-fix target-type))))))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter ((desiniter desiniterp)
                           (target-type typep)
                           (lifetime lifetimep)
                           (table valid-tablep)
                           (ienv ienvp))
    :guard (and (desiniter-unambp desiniter)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer with optional designation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the type
       that the list of designators must be applicable to."))
    (b* (((reterr) (irr-valid-table))
         ((desiniter desiniter) desiniter)
         ((erp & table) (valid-designor-list
                         desiniter.design target-type table ienv))
         ((erp table)
          (valid-initer desiniter.init target-type lifetime table ienv)))
      (retok table))
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
    :returns (mv erp (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more
            initializers with optional designations."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the type
       that each list of designators must be applicable to."))
    (b* (((reterr) (irr-valid-table))
         ((when (endp desiniters)) (retok (valid-table-fix table)))
         ((erp table) (valid-desiniter
                       (car desiniters) target-type lifetime table ienv))
         ((erp table) (valid-desiniter-list
                       (cdr desiniters) target-type lifetime table ienv)))
      (retok table))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor ((designor designorp)
                          (target-type typep)
                          (table valid-tablep)
                          (ienv ienvp))
    :guard (and (designor-unambp designor)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv erp (new-target-type typep) (new-table valid-tablep))
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
    (b* (((reterr) (irr-type) (irr-valid-table)))
      (designor-case
       designor
       :sub (b* (((erp index-type table)
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
              (retok (type-unknown) table))
       :dot (b* (((unless (or (type-case target-type :struct)
                              (type-case target-type :union)
                              (type-case target-type :unknown)))
                  (reterr (msg "The target type of the designator ~x0 is ~x1."
                               (designor-fix designor)
                               (type-fix target-type)))))
              (retok (type-unknown) (valid-table-fix table)))))
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
    :returns (mv erp (new-target-type typep) (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the current type
       that the designators must be applicable to.
       The target type returned as result is the type
       resulting from the application of the designators."))
    (b* (((reterr) (irr-type) (irr-valid-table))
         ((when (endp designors))
          (retok (type-fix target-type) (valid-table-fix table)))
         ((erp target-type table)
          (valid-designor (car designors) target-type table ienv)))
      (valid-designor-list (cdr designors) target-type table ienv))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-tyname ((tyname tynamep) (table valid-tablep) (ienv ienvp))
    :guard (tyname-unambp tyname)
    :returns (mv erp (type typep) (new-table valid-tablep))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "A valid type name denotes a type,
       so we return a type if validation is successful."))
    (declare (ignore tyname table ienv))
    (b* (((reterr) (irr-type) (irr-valid-table)))
      (reterr :todo))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below

  :prepwork ((set-bogus-mutual-recursion-ok t) ; TODO: remove eventually
             (local (in-theory (enable acons))))

  ///

  (verify-guards valid-expr)

  (fty::deffixequiv-mutual valid-exprs/decls/stmts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
