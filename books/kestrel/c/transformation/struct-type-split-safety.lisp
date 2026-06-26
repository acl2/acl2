; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../syntax/validation-annotations")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* c$::abstract-syntax-annop-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-type-split-safety
  :parents (transformation-tools)
  :short "Safety checks for the @(tsee struct-type-split) transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "That transformation is work in progress,
     as are the safety checks provided here.
     The two will be connected once the safety checks are practical
     (currently they are very preliminary and conservative).")
   (xdoc::p
    "The STS (= Struct Type Split) transformation is safe,
     in the sense that it suitably preserves code functionality,
     only provided that the struct type is not used in certain ways.
     For instance, if a pointer to the struct type is cast to @('void*'),
     the resulting pointer may manipulate the bytes that form the struct
     in ways that break the abstraction of the struct,
     making it unsafe to split the struct type.")
   (xdoc::p
    "Here we provide checkers that
     code uses (values of) the struct type being split
     only in safe ways with respect to the STS transformation.
     These checkers operate on ASTs annotated by validation.")
   (xdoc::p
    "It is possible that these checkers may be useful
     for other kinds of transformations as well,
     e.g. to add or remove struct members.
     If that turns out to be the case,
     we will suitably generalize their naming and role.")
   (xdoc::p
    "The STS transformation operates on a translation ensemble.
     The struct type to split is specified as
     the tag (name) of a file-scope struct declaration
     in one of the translation units of the ensemble.
     But the transformation also splits
     all the compatible file-scope struct types in other translation units.
     More explicitly, each translation unit in the ensemble
     either has or does not have a file-scope struct type
     with the tag specified to the STS transformation.
     The translation units that do not have it undergo no transformation.
     For each translation unit that has it,
     it either is compatible with the one to split or it is not;
     in the latter case, the translation unit undergoes no transformation.
     So only the translation units with
     either exactly the struct type, or one compatible with it,
     undergo transformation.
     This is orchestrated by the STS transformation,
     which will call these checking tools on
     each translation unit being transformed,
     to ensure that the transformation is applicable."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod sts-struct-spec
  :short "Fixtype of specifications of the struct type to split."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see struct-type-split-safety),
     the safety checks are applied to each translation unit
     that needs transformation.
     This translation unit contains, at the file scope,
     either the exact struct type specified to the STS transformation
     (as the tag name and optionally the translation unit file path,
     where the latter defaults to the first translation unit),
     or one compatible with it.
     Compatibility means that [C17:6.2.7/1]
     the struct types have the same tag, members with compatible types, etc.
     Since struct tags have no linkage [C17:6.2.2/6],
     struct types with the same tag in different translation units
     have different UIDs.")
   (xdoc::p
    "Here we define a data structure that specifies
     the struct type being split in a given translation unit.
     This will be created by the STS transformation for each translation unit.
     Our checking tools take it and use it to check the translation unit.")
   (xdoc::p
    "This data structure consists of the UID, the tag, and the members.
     Although this is more than needed to identify the struct type,
     we use all this information to check that
     there are no other similar struct declarations (e.g. in a block scope)."))
  ((uid uid)
   (tag ident)
   (members type-struni-member-list))
  :pred sts-struct-specp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-type-is-struct-spec-p ((uid uidp)
                                      (tunit? filepath-optionp)
                                      (tag/members type-struni-tag/members-p)
                                      (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a struct type is the one being split."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first three inputs of this function are
     the fields of the @(':struct') summand of @(tsee type).
     The last input of this function specifies the struct type being split.
     We check whether the struct type consisting of the three fields
     is a tagged one with the same tag and UID as the struct being split."))
  (declare (ignore tunit?))
  (b* (((sts-struct-spec spec)))
    (and (type-struni-tag/members-case tag/members :tagged)
         (b* ((tag (type-struni-tag/members-tagged->tag tag/members)))
           (and (equal tag spec.tag)
                (equal (uid-fix uid) spec.uid))))))

;;;;;;;;;;;;;;;;;;;;

(define type-is-struct-spec-p ((type typep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type is the struct type being split."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is true if the type is a struct type,
     and @(tsee struct-type-is-struct-spec-p) holds:
     see the documentation of that function."))
  (and (type-case type :struct)
       (struct-type-is-struct-spec-p (type-struct->uid type)
                                     (type-struct->tunit? type)
                                     (type-struct->tag/members type)
                                     spec)))

;;;;;;;;;;;;;;;;;;;;

(define type-may-be-struct-spec-p ((type typep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type may be the struct type being split."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when @(tsee type-is-struct-spec-p) holds,
     or when the type is unknown,
     because it could be the struct type being split.
     The unknown scalar and unknown arithmetic types cannot be struct types.
     We assume that the struct that we split is not a built-in one,
     which is why we do not include the unknown built-in type here."))
  (or (type-is-struct-spec-p type spec)
      (type-case type :unknown)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-sts-safep
  :short "Check that types are safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the struct type being split
     is not nested in array, union, or (other) struct types."))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-sts-safep ((type typep)
                          (nested booleanp)
                          (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that a type is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('nested') input indicates whether the @('type') input
       is nested under some array or union or struct type.")
     (xdoc::p
      "Most types are safe because they do not contain other types.
       When we reach a struct type, we compare it with the one being split:
       if they are the same, and we are nested under some type,
       the safety check fails, otherwise it succeeds.
       We use separate functions to check the content of struct and union types.
       For array types, we check the element type,
       setting the @('nested') flag to @('t') since the element type is nested.
       For pointer types, we leave the @('nested') flag as is;
       although the struct type being split cannot be nested as such in them,
       we also disallow nesting of pointers to the struct type being split.
       For function types,
       we disallow the struct anywhere in the return type,
       passing @('t') as the nested flag for the return type;
       but we pass the nested flag as is for parameters.
       We regard an unknown type as unsafe, because it could be anything.
       The same goes for an unknown scalar type,
       because it could be a pointer to an unsafe type
       (e.g. structs that contain the struct being split).
       An unknown arithmetic type is safe,
       because it can never contain the struct being split."))
    (type-case
     type
     :void t
     :char t
     :schar t
     :uchar t
     :sshort t
     :ushort t
     :sint t
     :uint t
     :slong t
     :ulong t
     :sllong t
     :ullong t
     :float t
     :double t
     :ldouble t
     :floatc t
     :doublec t
     :ldoublec t
     :bool t
     :struct (if (and nested
                      (struct-type-is-struct-spec-p type.uid
                                                    type.tunit?
                                                    type.tag/members
                                                    spec))
                 nil
               (type-struni-tag/members-sts-safep type.tag/members spec))
     :union (type-struni-tag/members-sts-safep type.tag/members spec)
     :enum t
     :array (type-sts-safep type.of t spec)
     :pointer (type-sts-safep type.to nested spec)
     :function (and (type-sts-safep type.ret t spec)
                    (type-params-sts-safep type.params nested spec))
     :unknown nil
     :unknown-builtin t
     :unknown-scalar nil
     :unknown-arithmetic t)
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-list-sts-safep ((types type-listp)
                               (nested booleanp)
                               (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that a list of types are safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check every type in turn."))
    (or (endp types)
        (and (type-sts-safep (car types) nested spec)
             (type-list-sts-safep (cdr types) nested spec)))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-tag/members-sts-safep ((tystr-tag/mems
                                              type-struni-tag/members-p)
                                             (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that the portion of a struct/union type
            that corresponds to the tag and members
            is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function takes no nested flag because
       structure or union members are always implicitly nested.
       I.e. it is as if the flag were implicitly @('t').")
     (xdoc::p
      "A tag alone is safe, because it does not contain types;
       checks on the definition of the type referred to by the tag
       are performed elsewhere.
       Otherwise, we descend into the members."))
    (type-struni-tag/members-case
     tystr-tag/mems
     :tagged t
     :untagged (type-struni-member-list-sts-safep tystr-tag/mems.members
                                                  spec))
    :measure (type-struni-tag/members-count tystr-tag/mems))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-member-sts-safep ((mem type-struni-member-p)
                                        (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that a struct/union member
            is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function takes no nested flag because
       structure or union members are always implicitly nested.
       I.e. it is as if the flag were implicitly @('t').
       This is why we pass @('t') as the nested flag
       to @(tsee type-sts-safep)."))
    (type-sts-safep (type-struni-member->type mem) t spec)
    :measure (type-struni-member-count mem))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-member-list-sts-safep ((mems type-struni-member-listp)
                                             (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that a list of struct/union members
            are safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check every member in turn."))
    (or (endp mems)
        (and (type-struni-member-sts-safep (car mems) spec)
             (type-struni-member-list-sts-safep (cdr mems) spec)))
    :measure (type-struni-member-list-count mems))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-params-sts-safep ((params type-params-p)
                                 (nested booleanp)
                                 (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that the portion of a function type
            pertaining to the function parameters
            is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check all the types."))
    (type-params-case
     params
     :prototype (type-list-sts-safep params.params nested spec)
     :old-style (type-list-sts-safep params.params nested spec)
     :unspecified t)
    :measure (type-params-count params))

  ;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual type/type-list-sts-safep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define top-type-sts-safep ((type typep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check that a top-level type is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the nested flag to @('nil'), since we are at the top level."))
  (type-sts-safep type nil spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-unamb/anno-p ((expr exprp))
  :returns (yes/no booleanp)
  :short "Check that an expression
          is unambiguous and has validation annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Throw an error, but logically just return @('nil'), if not.
     This is enabled because we use it as an abbreviation,
     until @(tsee fty::deffold-map) supports fold guards."))
  (and (or (expr-unambp expr)
           (raise "Internal error: ~x0 is ambiguous." (expr-fix expr)))
       (or (expr-annop expr)
           (raise "Internal error: ~x0 is not validated." (expr-fix expr))))
  :no-function nil
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-unamb/anno-p ((tyname tynamep))
  :returns (yes/no booleanp)
  :short "Check that a type name
          is unambiguous and has validation annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Throw an error, but logically just return @('nil'), if not.
     This is enabled because we use it as an abbreviation,
     until @(tsee fty::deffold-map) supports fold guards."))
  (and (or (tyname-unambp tyname)
           (raise "Internal error: ~x0 is ambiguous." (tyname-fix tyname)))
       (or (tyname-annop tyname)
           (raise "Internal error: ~x0 is not validated." (tyname-fix tyname))))
  :no-function nil
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-unary-sts-safep ((op unopp) (arg exprp) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a unary expression is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most unary operators are always safe:
     some never operate on structs;
     others may perform arithmetic on struct pointers, which is safe;
     taking the address of, or dereferencing, a struct of the type being split
     is also safe, it does not break the struct abstraction.
     The only operators that may be unsafe are @('sizeof') and @('alignof'),
     but only if the type of the argument expression
     may be the struct type being split;
     they expose the size and alignment, which may change under splitting.")
   (xdoc::p
    "We may need to refine these checks to prohibit
     taking the address of a member of the struct being split,
     i.e. @('&s.m') where @('s') is the struct and @('m') the members.
     Once that pointer is taken, its type is the one of @('m'),
     and it has lost its connection to the type of @('s')."))
  (or (not (unop-case op '(:sizeof :alignof)))
      (and (expr-unamb/anno-p arg)
           (not (type-may-be-struct-spec-p (expr-type arg) spec)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-sizeof/alignof-sts-safep ((tyname tynamep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a @('sizeof') or @('alignof') expression on a type name
          is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case exactly when the type denoted by the type name
     may not be the struct type being split.
     The reason is that same as explained in @(tsee expr-unary-sts-safep)."))
  (and (tyname-unamb/anno-p tyname)
       (not (type-may-be-struct-spec-p (type-vinfo->type (tyname->info tyname))
                                       spec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-cast-sts-safep ((tyname tynamep)
                             (arg exprp)
                             (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a cast expression is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case exactly when
     neither the source nor the destination type
     is the struct being split or a pointer type to it."))
  (and (tyname-unamb/anno-p tyname)
       (expr-unamb/anno-p arg)
       (b* ((src-type (expr-type arg))
            (dst-type (type-vinfo->type (tyname->info tyname))))
         (and (not (type-may-be-struct-spec-p src-type spec))
              (not (and (type-case src-type :pointer)
                        (type-may-be-struct-spec-p (type-pointer->to src-type)
                                                   spec)))
              (not (type-may-be-struct-spec-p dst-type spec))
              (not (and (type-case dst-type :pointer)
                        (type-may-be-struct-spec-p (type-pointer->to dst-type)
                                                   spec)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce sts-safep
  :short "Check that ASTs are safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a family of predicates on ASTs,
     using @(tsee fty::deffold-reduce).
     The ASTs must satisfy the @(tsee c$::abstract-syntax-annop) predicates,
     i.e. they must include validation annotations,
     but currently @(tsee fty::deffold-reduce) does not support
     the use of another @(tsee fty::deffold-reduce) as guards
     (we plan to add that feature soon).")
   (xdoc::p
    "The @('spec') extra argument specifies the struct type being split.
     These predicates check that the ASTs use that struct type
     (and its values, and pointers to its values)
     only in ways that are safe for the STS transformation.")
   (xdoc::p
    "The predicates should start at the @(tsee exprs/decls/stmts) clique.
     It is not hard to see that
     all the ASTs in @(see c$::abstract-syntax-trees) before that clique
     do not contain anything directly related to structs.
     As a simple example, an identifier,
     although it could be a struct name,
     or the name of a variable that contains a struct,
     in isolation it cannot be deemed unsafe;
     it is only when used in a larger context (e.g. an expression)
     that we can detect unsafety.
     More concretely,
     all the ASTs that precede the @(tsee exprs/decls/stmts) clique
     should be deemed safe when taken in isolation,
     and thus we do not need to define any predicates on them.")
   (xdoc::p
    "However, above we said `should' because, for now,
     we are including the @(tsee stor-spec) and @(tsee type-qual) fixtypes,
     so that we can exclude
     the @('_Atomic') type qualifier
     and the @('auto') storage specifier.
     In general, for now we want to reject code
     where the struct type is qualified as being atomic,
     because it is not clear how that interacts with
     transformations such as splitting the struct;
     so we just forbid that type qualifier.
     The reason for excluding the @('auto') storage specifier
     is that, in C23, it does type inference,
     which might resolve to the struct type being split,
     and so we exclude that for now.")
   (xdoc::p
    "The predicates end at the @(tsee trans-unit) type,
     because these checks operate on one translation unit at a time.")
   (xdoc::p
    "Our initial definition of these safety predicates is very conservative.
     We will relax it gradually.")
   (xdoc::p
    "The default value of these predicates is @('t'),
     which means that, for example, an expression that is a constant
     is accepted, because it is a leaf in the types for these predicates.
     Indeed, such an expression is safe, because it does not involve structs
     (note that this is an @(tsee expr) of the @(':const') kind,
     not a constant expression as defined in [C17] and [C23],
     which is a separate notion).")
   (xdoc::p
    "Although it may seem better to use @('nil') as default to be conservative,
     that would not play well (it generally does not, for predicates).
     The reason is that @('t') is the identity of @(tsee and),
     which is obviously the right combination operator for this fold.
     Thus empty lists and absent sub-constructs would be deemed unsafe,
     if we used @('nil') as the default instead of @('t').")
   (xdoc::p
    "Since we operate on validated (and thus disambiguated) ASTs,
     the ambiguous constructs do not occur,
     so for now we do not handle them specially.")
   (xdoc::p
    "Option and list AST types are safe iff their components are.
     This is the default generated definition of the predicates.")
   (xdoc::p
    "AST types that merely wrap other AST types,
     like @(tsee const-expr) and @(tsee spec/qual),
     are allowed iff their wrapped ASTs are,
     which is the default definition.")
   (xdoc::p
    "Consider expressions:")
   (xdoc::ul
    (xdoc::li
     "Identifiers, constants, and strings are safe leaves.
      Although an identifier may be a variable of struct type,
      this is safe in isolation;
      unsafety can only come from a larger construct containing the variable.
      So we keep the default for these.")
    (xdoc::li
     "A parenthesized expression is safe iff its inner expression is,
      which is what the default does.")
    (xdoc::li
     "We reject generic selections out of caution.
      The controlling expression may have struct type;
      we need to think of the safety.")
    (xdoc::li
     "We allow subscripting expressions.
      Subscripting is equivalent to pointer addition and dereferencing,
      which are safe operations with respect to struct splitting.
      Note that pointer addition takes the size of the struct into account
      (if the pointer is one to a struct),
      but so long as the resulting pointer is not cast to an integer or similar,
      it does not expose the exact size of the struct.
      However, note also that currently @(tsee type-sts-safep) prohibits
      arrays of the struct type being split (or nested in general),
      so normally we would not encounter array subscripting
      involving the struct being split
      (unless one writes @('s[0]') instead of @('*s')).")
    (xdoc::li
     "We reject function calls for now,
      because we need to make sure that those are safe too,
      and that may include some built-in functions
      which need to be examined case by case.")
    (xdoc::li
     "We allow member access, by value or by pointer.
      This is the normal safe way to access structs.
      Note that the nesting of the struct type being split
      in other structs or in unions is excluded via @(tsee type-sts-safep).")
    (xdoc::li
     "We reject compound literals out of initial caution.
      We need to think through them.")
    (xdoc::li
     "We use a dedicated ACL2 function for unary expressions.")
    (xdoc::li
     "We use a dedicated ACL2 function for
      @('sizeof') and @('alignof') applied to type names.")
    (xdoc::li
     "Taking the address of a label (a GCC/Clang extension) is safe;
      it does not involve structs.")
    (xdoc::li
     "We use a dedicated ACL2 function for cast expressions.")
    (xdoc::li
     "We accept all binary expressions.
      The only binary operator that may operate on struct values
      is plain assignment @('='),
      but it involves no automatic conversion that may break abstraction,
      so this should be always safe,
      even when it assigns a struct being split to a variable,
      which must have the same type.
      But we plan to do some experiments to confirm this;
      we might compare the type of the left and right sides to be sure.
      Pointers to the structs being split may be involved in arithmetic,
      but this is always safe according to the standard;
      although the exact values may vary with the size of the struct,
      this is handled automatically,
      e.g. adding 1 to a pointer to the struct
      actually adds the size of the struct to the pointer;
      but the only way to see the difference is
      to cast the resulting pointer to an integer,
      which would trigger a safety violation.")
    (xdoc::li
     "Ternary expressions are safe iff their components are,
      which is the default definition of the predicate.")
    (xdoc::li
     "A statement expression (GCC/Clang extension)
      is safe iff the compound statement is,
      which is the default definition of the predicate.")
    (xdoc::li
     "We reject
      @('__builtin_types_compatible_p'),
      @('__builtin_offsetof'), and
      @('__builtin_va_arg')
      out of caution for now.")
    (xdoc::li
     "An expression preceded by @('__extension__') is safe iff
      the expression itself is,
      so we leave it as default."))
   (xdoc::p
    "We do not need to override @(tsee genassoc)
     because it is only reachable from @(':genassoc') expressions,
     which we currently reject.")
   (xdoc::p
    "We do not need to override @(tsee member-designor)
     because it is only reachable from
     @(':genassoc') and @(':offsetof') expressions,
     which we currently reject.")
   (xdoc::p
    "We allow most type specifiers, except the following:")
   (xdoc::ul
    (xdoc::li
     "@('_Atomic'), for the same reason as the homonymous type qualifier,
      as explained earlier.")
    (xdoc::li
     "@('typedef'), since it could be the struct type being split.
      Clearly we should relax this.")
    (xdoc::li
     "@('typeof') and spelling variants,
      in C23 or in GCC/Clang-extended C17.
      This is because the type may denote the struct type being split,
      without that being immediately syntactically apparent.")
    (xdoc::li
     "@('__auto_type') is excluded for the same reason as
      the storage specifier @('auto') explained earlier."))
   (xdoc::p
    "Since @('struct') specifiers are allowed,
     we need to reject constructs that nest
     the struct being split in other aggregate data types.")
   (xdoc::p
    "We reject all alignment specifiers,
     because they may apply to the struct being split.")
   (xdoc::p
    "Certain GCC/Clang attributes might need to be rejected,
     but we need to examine them in more detail.")
   (xdoc::p
    "We reject the @('__stdcall') and @('__declspec') declaration specifiers,
     out of caution.")
   (xdoc::p
    "We reject list initializers for now,
     because they may affect the struct being split.")
   (xdoc::p
    "Initializers with optional designations are only reachable
     from list initializers, which are excluded (see above).")
   (xdoc::p
    "We exclude declarators and abstract declarators,
     because in combination with type specifiers
     they may give rise to arrays of the struct being split.
     We may need to look at types added by the validator
     to make this kind of checks more easily.")
   (xdoc::p
    "The exclusion of declarators and abstract declarators
     implies the exclusion of many constructs,
     e.g. most parameter and structure declarations;
     the latter prevent the nesting of the struct being split.")
   (xdoc::p
    "We exclude assembly, because we do not know what it does exactly."))
  :types (stor-spec
          type-qual
          exprs/decls/stmts
          fundef
          ext-declon
          trans-items
          trans-unit)
  :result booleanp
  :default t
  :combine and
  :extra-args ((spec sts-struct-specp))
  :override
  ((stor-spec :auto nil)
   (type-qual :atomic nil)
   (expr :gensel nil)
   (expr :funcall nil)
   (expr :complit nil)
   (expr :unary (and (expr-sts-safep expr.arg spec)
                     (expr-unary-sts-safep expr.op expr.arg spec)))
   (expr :sizeof (and (tyname-sts-safep expr.type spec)
                      (expr-sizeof/alignof-sts-safep expr.type spec)))
   (expr :alignof (and (tyname-sts-safep expr.type spec)
                       (expr-sizeof/alignof-sts-safep expr.type spec)))
   (expr :cast (and (tyname-sts-safep expr.type spec)
                    (expr-sts-safep expr.arg spec)
                    (expr-cast-sts-safep expr.type expr.arg spec)))
   (expr :tycompat nil)
   (expr :offsetof nil)
   (expr :va-arg nil)
   (type-spec :atomic nil)
   (type-spec :typedef nil)
   (type-spec :typeof-expr nil)
   (type-spec :typeof-type nil)
   (type-spec :auto-type nil)
   (align-spec nil)
   (decl-spec :stdcall nil)
   (decl-spec :declspec nil)
   (initer :list nil)
   (declor nil)
   (absdeclor nil)
   (asm-stmt nil))
  :name abstract-syntax-sts-safep)
