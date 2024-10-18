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
    "The types of the two sub-expressions are
     calculated (recursively) by @(tsee valid-expr).")
   (xdoc::p
    "After converting array types to pointer types [C:6.3.2.1/3],
     one sub-expression must have pointer type,
     and the other sub-expression must have integer type
     [C:6.5.2.1/1].
     The expression should have the type referenced by the pointer type,
     but since for now we model just one pointer type,
     the type of the expression is unknown."))
  (b* (((reterr) (irr-type))
       (type1 (type-apconvert type-arg1))
       (type2 (type-apconvert type-arg2))
       ((unless (or (and (or (type-case type1 :pointer)
                             (type-case type1 :unknown))
                         (or (type-integerp type2)
                             (type-case type2 :unknown)))
                    (and (or (type-integerp type1)
                             (type-case type1 :unknown))
                         (or (type-case type2 :pointer)
                             (type-case type2 :unknown)))))
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
    "The types of the two sub-expressions are
     calculated (recursively) by @(tsee valid-expr).")
   (xdoc::p
    "After converting function types to pointer types,
     the first sub-expression must have pointer type [C:6.5.2.2/1];
     since we currently have just one pointer type,
     we cannot check that it is a pointer to a function.
     For the same reason,
     we do not check the argument types against the function type [C:6.5.2.2/2].
     Also for the same reason,
     we return the unknown type,
     because we do not have information about the result type."))
  (declare (ignore types-arg))
  (b* (((reterr) (irr-type))
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
    "The type of the sub-expression is
     calculated (recursively) by @(tsee valid-expr).")
   (xdoc::p
    "The argument type must be a structure or union type [C:6.5.2.3/1].
     Since a pointer type is not allowed here,
     there is no need to convert arrays to pointers [C:6.3.2.1/3].")
   (xdoc::p
    "For now we only have one type for structures and one type for unions.
     We cannot look up the member type, so we return the unknown type."))
  (b* (((reterr) (irr-type))
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
     we will refine this when we refine our type system.")
   (xdoc::p
    "Since we cannot yet look up members in structure and union types,
     we return the unknown type."))
  (b* (((reterr) (irr-type))
       (type (type-apconvert type-arg))
       ((unless (type-case type :pointer))
        (reterr (msg "In the member pointer expression ~x0, ~
                      the sub-expression has type ~x1."
                     (expr-fix expr) (type-fix type-arg)))))
    (retok (type-unknown)))
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
       and pass the types to those separate functions."))
    (b* (((reterr) (irr-type) (irr-valid-table)))
      (expr-case
       expr
       :ident (b* (((erp type) (valid-var expr.unwrap table)))
                (retok type (valid-table-fix table)))
       :const (b* (((erp type) (valid-const expr.unwrap table ienv)))
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
       :complit (reterr :todo)
       :unary (reterr :todo)
       :sizeof (reterr :todo)
       :alignof (reterr :todo)
       :cast (reterr :todo)
       :binary (reterr :todo)
       :cond (reterr :todo)
       :comma (reterr :todo)
       :stmt (reterr :todo)
       :tycompat (reterr :todo)
       :offsetof (reterr :todo)
       :otherwise (prog2$ (impossible) (reterr t))))
    :measure (expr-count expr))

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

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below

  :prepwork ((set-bogus-mutual-recursion-ok t) ; TODO: remove eventually
             (local (in-theory (enable acons))))

  ///

  (verify-guards valid-expr)

  (fty::deffixequiv-mutual valid-exprs/decls/stmts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
