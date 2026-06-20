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

(defxdoc+ struct-type-split-safety
  :parents (transformation-tools)
  :short "Safety checks for the @(tsee struct-type-split) transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "That transformation is work in progress,
     as are the safety checks provided here.
     The two will be connected once the safety checks are practical
     (currently they are just very preliminary and conservative).")
   (xdoc::p
    "The STS (= Struct Type Split) transformation is safe,
     in the sense that it suitabley preserves code functionality,
     only provided that the struct type is not used in certain ways.
     For instance, if a pointer to the struct type is cast to @('void*'),
     the resulting pointer may manipulate the bytes that form the struct
     in ways that break the abstraction of the struct,
     making it unsafe to split the struct type.")
   (xdoc::p
    "Here we provide checkers that
     code uses (values of) a given struct type
     only in safe ways with respect to the STS transformation.
     These checkers operate on ASTs annotated by validation.")
   (xdoc::p
    "It is possible that these checkers may be useful
     for other kinds of transformationa as well,
     e.g. to add or remove struct members.
     If that turns out to be the case,
     we will suitably generalize their naming and role."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-type-is-the-struct-p ((uid uidp)
                                     (tunit? filepath-optionp)
                                     (tag/members type-struni-tag/members-p)
                                     (the-struct identp))
  :returns (yes/no booleanp)
  :short "Check if a struct type is the one to split."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first three inputs of this function are
     the fields of the @(':struct') summand of @(tsee type).
     The last input of this function is the tag of the struct being split.
     We check whether the struct type consisting of the three fields
     is a tagged one with the same tag as the struct of interest.
     We will need to elaborate this check,
     because in general a tag alone may not uniquely identify a struct type,
     and we may also need to take into account type compatibility."))
  (declare (ignore uid tunit?))
  (and (type-struni-tag/members-case tag/members :tagged)
       (b* ((tag (type-struni-tag/members-tagged->tag tag/members)))
         (equal tag (ident-fix the-struct)))))

;;;;;;;;;;;;;;;;;;;;

(define type-is-the-struct-p ((type typep) (the-struct identp))
  :returns (yes/no booleanp)
  :short "Check if a type is the struct type to split."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is true if the type is a struct type,
     and @(tsee struct-type-is-the-struct-p) holds:
     see the documentation of that function."))
  (and (type-case type :struct)
       (struct-type-is-the-struct-p (type-struct->uid type)
                                    (type-struct->tunit? type)
                                    (type-struct->tag/members type)
                                    the-struct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-sts-safep
  :short "Check that types are safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the struct type of interest
     is not nested in array, union, or (other) struct types."))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-sts-safep ((type typep) (nested booleanp) (struct identp))
    :returns (yes/no booleanp)
    :parents (struct-safety-checks type/type-list-sts-safep)
    :short "Check that a type is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('nested') input indicates whether the @('type') input
       is nested under some array or union or struct type.")
     (xdoc::p
      "Most types are safe because they do not contain other types.
       When we reach a struct type, we compare it with the one of interest:
       if they are the same, and we are nested under some type,
       the safety check fails, otherwise it succeeds.
       We use separate functions to check the content of struct and union types.
       For array types, we check the element type,
       setting the @('nested') flag to @('t') since the element type is nested.
       For pointer and function types, we leave the @('nested') flag as is;
       although the struct type of interest cannot be nested as such in them,
       we also disallow nesting of pointers to the struct type of interest,
       at least for now.
       We regard an unknown type as unsafe, because it could be anything.
       The same goes for an unknown scalar type,
       because it could be a pointer to an unsafe type
       (e.g. structs that contain the struct of interest).
       An unknown arithmetic type is safe,
       because it can never contain the struct of interest."))
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
                      (struct-type-is-the-struct-p type.uid
                                                   type.tunit?
                                                   type.tag/members
                                                   struct))
                 nil
               (type-struni-tag/members-sts-safep type.tag/members struct))
     :union (type-struni-tag/members-sts-safep type.tag/members struct)
     :enum t
     :array (type-sts-safep type.of t struct)
     :pointer (type-sts-safep type.to nested struct)
     :function (and (type-sts-safep type.ret nested struct)
                    (type-params-sts-safep type.params nested struct))
     :unknown nil
     :unknown-scalar nil
     :unknown-arithmetic t)
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-list-sts-safep ((types type-listp) (nested booleanp) (struct identp))
    :returns (yes/no booleanp)
    :parents (struct-safety-checks type/type-list-sts-safep)
    :short "Check that a list of types are safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check every type in turn."))
    (or (endp types)
        (and (type-sts-safep (car types) nested struct)
             (type-list-sts-safep (cdr types) nested struct)))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-tag/members-sts-safep ((tystr-tag/mems
                                              type-struni-tag/members-p)
                                             (struct identp))
    :returns (yes/no booleanp)
    :parents (struct-safety-checks type/type-list-sts-safep)
    :short "Check that the portion of a struct/union type
            that corresponds to the tag and members
            is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "A tag alone is safe, because it does not contain types;
       checks on the definition of the type referred to by the tag
       are performed elsewhere.
       Otherwise, we descend into the members."))
    (type-struni-tag/members-case
     tystr-tag/mems
     :tagged t
     :untagged (type-struni-member-list-sts-safep tystr-tag/mems.members struct))
    :measure (type-struni-tag/members-count tystr-tag/mems))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-member-sts-safep ((mem type-struni-member-p)
                                        (struct identp))
    :returns (yes/no booleanp)
    :parents (struct-safety-checks type/type-list-sts-safep)
    :short "Check that a struct/union member
            is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the type, passing @('t') as the @('nested') flag,
       because we arrived here from a struct or union type,
       so we are in a nested situation."))
    (type-sts-safep (type-struni-member->type mem) t struct)
    :measure (type-struni-member-count mem))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-member-list-sts-safep ((mems type-struni-member-listp)
                                             (struct identp))
    :returns (yes/no booleanp)
    :parents (struct-safety-checks type/type-list-sts-safep)
    :short "Check that a list of struct/union members
            are safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check every member in turn."))
    (or (endp mems)
        (and (type-struni-member-sts-safep (car mems) struct)
             (type-struni-member-list-sts-safep (cdr mems) struct)))
    :measure (type-struni-member-list-count mems))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-params-sts-safep ((params type-params-p)
                                 (nested booleanp)
                                 (struct identp))
    :returns (yes/no booleanp)
    :parents (struct-safety-checks type/type-list-sts-safep)
    :short "Check that the portion of a function type
            pertaining to the function parameters
            is safe for the STS transformation."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check all the types."))
    (type-params-case
     params
     :prototype (type-list-sts-safep params.params nested struct)
     :old-style (type-list-sts-safep params.params nested struct)
     :unspecified t)
    :measure (type-params-count params))

  ;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual type/type-list-sts-safep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define top-type-sts-safep ((type typep) (struct identp))
  :returns (yes/no booleanp)
  :short "Check that a top-level type is safe for the STS transformation."
  (type-sts-safep type nil struct))

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
    "The @('struct') extra argument is the tag of the struct type of interest.
     This may need to evolve into something richer,
     as the name alone may not uniquely identify a struct type,
     but we start with this for simplicity.
     There is also the issue of compatible struct types,
     but we leave these elaborations for later as well.")
   (xdoc::p
    "These predicates check that the ASTs use that struct type
     (and its values, and pointers to its values)
     only in ways that are safe for transformations
     that operate on the struct type, e.g. that split it.")
   (xdoc::p
    "The predicates should start at the @(tsee exprs/decls/stmts) clique.
     It is not hard to see that
     all the ASTs in @(see c$::abstract-syntax-trees) before that clique
     do not contain anything directly related to structs.
     As a simple example, an identifier,
     although it could a struct name,
     or the name of a variable that contains a struct,
     in isolation it cannot be deemed unsafe;
     it is only when used in a larger context (e.g. an expression)
     that we can detect unsafety.
     More concretely,
     all the ASTs that precede the @(tsee exprs/decls/stmts) clique
     have to deemed safe when taken in isolation,
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
     which might resolve to the struct type of interest,
     and so we exlude that for now.")
   (xdoc::p
    "The predicates end at the @(tsee trans-ensemble) type.
     We could extend this to @(tsee code-ensemble) if needed.")
   (xdoc::p
    "Aside from the above-mentioned approximations about
     the designation of the struct type of interest,
     our initial definition of these safety predicates is very conservative.
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
     Thus empty lists and absent sub-constructs would be deemed safe.")
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
     "We reject array subscripting for now.
      This should be safe for structs,
      in the sense that it does not break their abstraction;
      it is, after all, just pointer addition and dereferencing.
      But a transformation may not handle arrays of structs yet.
      These checks should be refined to look at the type of the array,
      and also to make checks on declarations for types.")
    (xdoc::li
     "Although member access is safe for structs,
      for now we want to reject access to possibly nested structs,
      or structs inside union,
      in the same spirit as the rejection of array subscripting,
      as explained just above.")
    (xdoc::li
     "We reject compound literals out of initial caution.
      We need to think through them.")
    (xdoc::li
     "While some unary operators are safe,
      we reject all unary expressions for now.
      We will refine this soon.")
    (xdoc::li
     "Taking the address of a label (a GCC/Clang extension) is safe;
      it does not involve structs.")
    (xdoc::li
     "We reject all the @('sizeof') and @('alignof') operators on type names.
      This must be refined to only do that for the struct type of interest.")
    (xdoc::li
     "Casts are rejected initially,
      but they should be accepted unless they cast
      a struct of interest, or a pointer to it,
      to some other type that breaks the abstraction.")
    (xdoc::li
     "We accept all binary expressions.
      The only binary operator that may operate on struct values
      is plain assignment @('='),
      but it involves no automatic conversion that may break abstraction,
      so this should be always safe,
      even when it assigns a struct of interest to a variable,
      which must have the same type.
      But we plan to do some experiments to confirm this;
      we might compare the type of the left and right sides to be sure.
      Pointers to the structs of interest may be involved in arithmetic,
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
     "@('typedef'), since it could be the struct type of interest.
      Clearly we should relax this.")
    (xdoc::li
     "@('typeof') and spelling variants,
      in C23 or in GCC/Clang-extended C17.
      This is because the type may denote the struct type of interest,
      without that being immediately syntactically apparent.")
    (xdoc::li
     "@('__auto_type') is excluded for the same reason as
      the storage specifier @('auto') explained earlier."))
   (xdoc::p
    "Since @('struct') specifiers are allowed,
     we need to reject constructs that nest
     the struct of interest in other aggregate data types.")
   (xdoc::p
    "We reject all alignment specifiers,
     because they may apply to the struct of interest.")
   (xdoc::p
    "Certain GCC/Clang attributes might need to be rejected,
     but we need to examine them in more detail.")
   (xdoc::p
    "We reject the @('__stdcall') and @('__declspec') declaration specifiers,
     out of caution.")
   (xdoc::p
    "We reject list initializers for now,
     because they may affect the struct of interest.")
   (xdoc::p
    "Initializers with optional designations are only reachable
     from listt initializers, which are excluded (see above).")
   (xdoc::p
    "We exclude declarators and abstract declarators,
     because in combination with type specifiers
     they may give rise to arrays of the struct of interest.
     We may need to look at types added by the validator
     to make this kind of checks more easily.")
   (xdoc::p
    "The exclusion of declarators and abstract declarators
     implies the exclusion of many constructs,
     e.g. most parameter and structure declarations;
     the latter prevent the nesting of the struct of interest.")
   (xdoc::p
    "We exclude assembly, because we do not know what it does exactly."))
  :types (stor-spec
          type-qual
          exprs/decls/stmts
          fundef
          ext-declon
          trans-items
          trans-unit
          filepath-trans-unit-map
          trans-ensemble)
  :result booleanp
  :default t
  :combine and
  :extra-args ((struct identp))
  :override
  ((stor-spec :auto nil)
   (type-qual :atomic nil)
   (expr :gensel nil)
   (expr :arrsub nil)
   (expr :funcall nil)
   (expr :member nil)
   (expr :memberp nil)
   (expr :complit nil)
   (expr :unary nil)
   (expr :sizeof nil)
   (expr :alignof nil)
   (expr :cast nil)
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
