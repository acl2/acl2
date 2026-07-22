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
    "The STS (= Struct Type Split) transformation is safe,
     in the sense that it suitably preserves code functionality,
     only provided that the struct type is not used in certain ways.
     For instance, if a pointer to the struct type is cast to @('void*'),
     the resulting pointer may manipulate the bytes that form the struct
     in ways that break the abstraction of the struct,
     making it unsafe to split the struct type.")
   (xdoc::p
    "Here we provide checkers that
     code uses the struct type being split
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
     the tag (name) of a file-scope struct declaration,
     or as the name of a file-scope @('typedef') struct declaration,
     in one of the translation units of the ensemble.
     But the transformation also splits
     all the compatible file-scope struct types in other translation units.
     More explicitly, each translation unit in the ensemble
     either has or does not have a file-scope struct type
     (declared just a struct type or as a @('typedef'), as above),
     that is compatible with
     the struct type specified to the STS transformation.
     The translation units that do not have it undergo no transformation.
     While each translation unit that has it undergoes the transformation.
     This is orchestrated by the STS transformation,
     which calls these safety checks on
     each translation unit being transformed,
     to ensure that the transformation is applicable."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ sts-reject (x)
  :short "Reject an entity that does not satisfy the safety checks,
          printing it in the comment window."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our safety checks are predicates that return @('t') or @('nil').
     But when a check fails, just @('nil') does not covery much information,
     when the checks are applied to non-trivial amounts of code.
     This macro is a simple way to provide more information:
     instead of returning @('nil'),
     our checking predicates can return a call of this macro
     on the entity that failed the checks,
     which logically is @('nil'),
     but prints the entity to the comment window as a side effect."))
  `(cw "STS safety failure: ~x0~%" ,x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod sts-struct-spec
  :short "Fixtype of specifications of the struct type being split."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see struct-type-split-safety),
     the safety checks are applied to each translation unit
     that needs transformation.
     This translation unit contains, at the file scope,
     either the exact struct type specified to the STS transformation,
     or one compatible with it.
     The struct type may be declared directly, or via a @('typedef').
     Either way, it is identified by a UID,
     which the STS transformation passes to these safety checks.")
   (xdoc::p
    "Here we define a data structure that specifies
     the struct type being split in a given translation unit.
     The specification consists of a UID,
     but we wrap it into a data structure for future extensibility.
     This data structure is an input to the STS safety checks."))
  ((uid uid))
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
     has the same UID as the struct type being split.
     The other two inputs are unused,
     but kept here for future extensibility."))
  (declare (ignore tag/members tunit?))
  (equal (sts-struct-spec->uid spec)
         (uid-fix uid)))

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

(define type-is-pointer-to-struct-spec-p ((type typep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type is a pointer to the struct type being split."
  (and (type-case type :pointer)
       (type-is-struct-spec-p (type-pointer->to type) spec)))

;;;;;;;;;;;;;;;;;;;;

(define type-is-*pointer-to-struct-spec-p ((type typep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type is
          the struct type being split,
          or a pointer to it,
          or a pointer to a pointer to it,
          etc."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('*') in the name of this function conveys the idea of `0 or more'."))
  (or (type-is-struct-spec-p type spec)
      (and (type-case type :pointer)
           (type-is-*pointer-to-struct-spec-p (type-pointer->to type) spec)))
  :measure (type-count type))

;;;;;;;;;;;;;;;;;;;;

(defines types-may-refer-to-struct-spec-p
  :short "Check if types may refer to the struct type being split,
          directly or indirectly."

  ;;;;;;;;;;

  (define type-may-refer-to-struct-spec-p ((type typep) (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety types-with-struct-spec-p)
    :short "Check if a type may refer to the struct type being split,
            directly or indirectly."
    :long
    (xdoc::topstring
     (xdoc::p
      "Most types fail the check because
       they are not, and do not contain, struct types.")
     (xdoc::p
      "The check passes if we encounter the struct type being split.
       For other struct types, we recursively check them,
       via a separate ACL2 function,
       the same used for union types.")
     (xdoc::p
      "For array, pointer, and function types,
       we recursively check their constituents.")
     (xdoc::p
      "Unknown and unknown scalar types pass the check,
       because they could be pointers to the struct type being split,
       among other possibilities.
       But unknown arithmetic and unknowno built-in types fail the check,
       because they cannot be or refer to the struct type."))
    (type-case
     type
     :void nil
     :char nil
     :schar nil
     :uchar nil
     :sshort nil
     :ushort nil
     :sint nil
     :uint nil
     :slong nil
     :ulong nil
     :sllong nil
     :ullong nil
     :float nil
     :double nil
     :ldouble nil
     :floatc nil
     :doublec nil
     :ldoublec nil
     :bool nil
     :struct (or (struct-type-is-struct-spec-p type.uid
                                               type.tunit?
                                               type.tag/members
                                               spec)
                 (type-struni-tag/members-may-refer-to-struct-spec-p
                  type.tag/members spec))
     :union (type-struni-tag/members-may-refer-to-struct-spec-p
             type.tag/members spec)
     :enum nil
     :array (type-may-refer-to-struct-spec-p type.of spec)
     :pointer (type-may-refer-to-struct-spec-p type.to spec)
     :function (or (type-may-refer-to-struct-spec-p type.ret spec)
                   (type-params-may-refer-to-struct-spec-p type.params spec))
     :unknown t
     :unknown-builtin nil
     :unknown-scalar t
     :unknown-arithmetic nil)
    :measure (type-count type))

  ;;;;;;;;;;

  (define type-list-may-refer-to-struct-spec-p ((types type-listp)
                                                (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety types-with-struct-spec-p)
    :short "Check if (any element of) a list of types
            may refer to the struct type being split, directly or indirectly."
    (and (not (endp types))
         (or (type-may-refer-to-struct-spec-p (car types) spec)
             (type-list-may-refer-to-struct-spec-p (cdr types) spec)))
    :measure (type-list-count types))

  ;;;;;;;;;;

  (define type-struni-tag/members-may-refer-to-struct-spec-p
    ((tystr-tag/mems type-struni-tag/members-p) (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety types-with-struct-spec-p)
    :short "Check if the portion of struct/union types
            corresponding to the tag and members
            may refer to the struct type being split, directly or indirectly."
    :long
    (xdoc::topstring
     (xdoc::p
      "If we just have a tag,
       we should look it up in the validation information,
       so we can recursively check the struct type found there.
       For now we just conservatively return @('t'),
       but we plan to refine that.")
     (xdoc::p
      "If instead we have members, we recursively check them."))
    (type-struni-tag/members-case
     tystr-tag/mems
     :tagged t ; TODO: refine
     :untagged (type-struni-member-list-may-refer-to-struct-spec-p
                tystr-tag/mems.members spec))
    :measure (type-struni-tag/members-count tystr-tag/mems))

  ;;;;;;;;;;

  (define type-struni-member-may-refer-to-struct-spec-p
    ((mem type-struni-member-p) (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety types-with-struct-spec-p)
    :short "Check if a struct or union member
            may refer to the struct type being split, directly or indirectly."
    (type-may-refer-to-struct-spec-p (type-struni-member->type mem) spec)
    :measure (type-struni-member-count mem))

  ;;;;;;;;;;

  (define type-struni-member-list-may-refer-to-struct-spec-p
    ((mems type-struni-member-listp) (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety types-with-struct-spec-p)
    :short "Check if (any element of) a list of struct or union members
            may refer to the struct type being split, directly or indirectly."
    (and (not (endp mems))
         (or (type-struni-member-may-refer-to-struct-spec-p (car mems) spec)
             (type-struni-member-list-may-refer-to-struct-spec-p (cdr mems)
                                                                 spec)))
    :measure (type-struni-member-list-count mems))

  ;;;;;;;;;;

  (define type-params-may-refer-to-struct-spec-p ((params type-params-p)
                                                  (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety types-with-struct-spec-p)
    :short "Check if a portion of a function type
            pertaining to the function parameters
            may refer to the struct type being split, directly or indirectly."
    (type-params-case
     params
     :prototype (type-list-may-refer-to-struct-spec-p params.params spec)
     :old-style (type-list-may-refer-to-struct-spec-p params.params spec)
     :unspecified nil)
    :measure (type-params-count params))

  ;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual types-may-refer-to-struct-spec-p))

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

;;;;;;;;;;;;;;;;;;;;

(define type-may-be-pointer-to-struct-spec-p ((type typep)
                                              (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type may be a pointer to the struct type being split."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when @(tsee type-is-pointer-to-struct-spec-p) holds,
     or when the type is unknown or an unknown scalar.
     The unknown arithmetic type cannot be a pointer.
     An unknown built-in type may be a pointer (to a built-in type),
     but we assume that the struct type being split is not a built-in one."))
  (or (type-is-pointer-to-struct-spec-p type spec)
      (type-case type :unknown)
      (type-case type :unknown-scalar)))

;;;;;;;;;;;;;;;;;;;;

(define type-may-be-*pointer-to-struct-spec-p ((type typep)
                                               (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type may be
          the struct type being split,
          or a pointer to it,
          or a pointer to a pointer to it,
          etc."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when @(tsee type-is-*pointer-to-struct-spec-p) holds,
     or when the type is unknown or an unknown scalar.
     The unknown arithmetic type cannot be a struct or a pointer.
     An unknown built-in type may be a struct or pointer to a struct,
     but we assume that the struct type being split is not a built-in one."))
  (or (type-is-*pointer-to-struct-spec-p type spec)
      (type-case type :unknown)
      (type-case type :unknown-scalar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-sts-safep
  :short "Check that types are safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the struct type being split
     is not nested in array or union types.
     Nesting under other struct types is fine,
     i.e. properly handled by the STS transformation."))

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
       is nested under some type where
       the struct type being split should not be nested
       because the STS transformation does not support that nesting.")
     (xdoc::p
      "Most types are safe because they do not contain other types.")
     (xdoc::p
      "When we reach a struct type, we compare it with the one being split:
       if they are the same, and the @('nested') flag is @('t'),
       the safety check fails, otherwise it succeeds.")
     (xdoc::p
      "We use a separate function to check
       the content of struct and union types.
       The @('nested') flag passed to that function is
       set to @('t') under a union,
       and to @('nil') under a struct,
       because we support nesting under structs but not under unions.")
     (xdoc::p
      "For array types, we check the element type,
       setting the @('nested') flag to @('t')
       since we do not support nesting under arrays.")
     (xdoc::p
      "For pointer types, we leave the @('nested') flag as is;
       although the struct type being split cannot be nested as such in them,
       we also disallow nesting of pointers to the struct type being split.")
     (xdoc::p
      "For function types,
       we disallow the struct anywhere in the return type,
       passing @('t') as the nested flag for the return type;
       but we pass the nested flag as is for parameters.")
     (xdoc::p
      "We regard an unknown type as unsafe, because it could be anything.
       The same goes for an unknown scalar type,
       because it could be a pointer to an unsafe type
       (e.g. structs that contain the struct being split).
       But an unknown arithmetic type is safe,
       because it can never be or contain the struct being split."))
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
                 (sts-reject `(:nested ,(type-fix type)))
               (type-struni-tag/members-sts-safep type.tag/members nil spec))
     :union (type-struni-tag/members-sts-safep type.tag/members t spec)
     :enum t
     :array (type-sts-safep type.of t spec)
     :pointer (type-sts-safep type.to nested spec)
     :function (and (type-sts-safep type.ret t spec)
                    (type-params-sts-safep type.params nested spec))
     :unknown (sts-reject (type-fix type))
     :unknown-builtin t
     :unknown-scalar (sts-reject (type-fix type))
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
                                             (nested booleanp)
                                             (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
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
     :untagged (type-struni-member-list-sts-safep tystr-tag/mems.members
                                                  nested
                                                  spec))
    :measure (type-struni-tag/members-count tystr-tag/mems))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-member-sts-safep ((mem type-struni-member-p)
                                        (nested booleanp)
                                        (spec sts-struct-specp))
    :returns (yes/no booleanp)
    :parents (struct-type-split-safety type/type-list-sts-safep)
    :short "Check that a struct/union member
            is safe for the STS transformation."
    (type-sts-safep (type-struni-member->type mem) nested spec)
    :measure (type-struni-member-count mem))

  ;;;;;;;;;;;;;;;;;;;;

  (define type-struni-member-list-sts-safep ((mems type-struni-member-listp)
                                             (nested booleanp)
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
        (and (type-struni-member-sts-safep (car mems) nested spec)
             (type-struni-member-list-sts-safep (cdr mems) nested spec)))
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
  (or (type-sts-safep type nil spec)
      (sts-reject (type-fix type))))

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

(define expr-unary-sts-safep ((op unopp)
                              (arg exprp)
                              info
                              (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a unary expression is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most unary operators are always safe:
     some never operate on structs;
     others may perform arithmetic on struct pointers, which is safe;
     taking the address of, or dereferencing, a struct of the type being split
     is also safe, it does not break the struct abstraction,
     with the exception described below.")
   (xdoc::p
    "The @('sizeof') and @('alignof') operators may be unsafe,
     but only if the type of the argument expression
     may be the struct type being split.
     They expose the size and alignment, which may change under splitting.")
   (xdoc::p
    "Another potentially unsafe case is taking
     the address of a member of the struct whose type is being split,
     because for example it could be involved in some pointer arithmetic,
     but we would lose information that the pointer came
     from the struct whose type is being split
     (more elaborate analyses are needed to retain that information)."))
  (case (unop-kind op)
    ((:sizeof :alignof)
     (or (and (expr-unamb/anno-p arg)
              (not (type-may-be-struct-spec-p (expr-type arg) spec)))
         (sts-reject (expr-unary op arg info))))
    (:address
     (expr-case
      arg
      :member (b* ((base (expr-member->arg arg)))
                (and (expr-unamb/anno-p base)
                     (or (not (type-may-be-struct-spec-p (expr-type base) spec))
                         (sts-reject (expr-unary op arg info)))))
      :memberp (b* ((base (expr-memberp->arg arg)))
                 (and (expr-unamb/anno-p base)
                      (or (not (type-may-be-pointer-to-struct-spec-p
                                (expr-type base) spec))
                          (sts-reject (expr-unary op arg info)))))
      :otherwise t))
    (t t)))

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

;;;;;;;;;;;;;;;;;;;;

(define expr-sizeof-sts-safep ((tyname tynamep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a @('sizeof') expression on a type name
          is safe for the STS transformation."
  (or (expr-sizeof/alignof-sts-safep tyname spec)
      (sts-reject (expr-sizeof tyname))))

;;;;;;;;;;;;;;;;;;;;

(define expr-alignof-sts-safep ((tyname tynamep)
                                (uscores keyword-uscores-p)
                                (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if an @('alignof') expression on a type name
          is safe for the STS transformation."
  (or (expr-sizeof/alignof-sts-safep tyname spec)
      (sts-reject (expr-alignof tyname uscores))))

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
     may refer to the struct type being split, directly or indirectly."))
  (or (and (tyname-unamb/anno-p tyname)
           (expr-unamb/anno-p arg)
           (b* ((src-type (expr-type arg))
                (dst-type (type-vinfo->type (tyname->info tyname))))
             (and (not (type-may-refer-to-struct-spec-p src-type spec))
                  (not (type-may-refer-to-struct-spec-p dst-type spec)))))
      (sts-reject (expr-cast tyname arg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-binary-sts-safep ((op binopp)
                               (arg1 exprp)
                               (arg2 exprp)
                               info
                               (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a binary expression is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most binary operators are safe.
     Only plain assignment can operates directly on struct types,
     but it needs a cast to break the abstraction.
     Several operators can operate on pointers to structs;
     arithmetic is safe, but assignments need to be checked.
     [C17] and [C23] allow automatic conversions with @('void *'),
     but experiments with Clang show that other pointer types
     may only generate warnings.
     Thus, we check that there are no possible automatic conversions
     between pointers to the struct being split
     and pointers to any other types."))
  (or
   (and (binop-case op '(:mul :div :rem :add :sub :shl :shr
                         :lt :gt :le :ge :eq :ne
                         :bitand :bitxor :bitior
                         :logand :logor))
        t)
   (and (expr-unamb/anno-p arg1)
        (expr-unamb/anno-p arg2)
        (b* ((type1 (expr-type arg1))
             (type2 (expr-type arg2)))
          (or (and (type-is-struct-spec-p type1 spec)
                   (type-is-struct-spec-p type2 spec))
              (and (type-is-pointer-to-struct-spec-p type1 spec)
                   (type-is-pointer-to-struct-spec-p type2 spec))
              (and (not (type-may-be-struct-spec-p type1 spec))
                   (not (type-may-be-struct-spec-p type2 spec))
                   (not (type-may-be-pointer-to-struct-spec-p type1 spec))
                   (not (type-may-be-pointer-to-struct-spec-p type2 spec))))))
   (sts-reject (expr-binary op arg1 arg2 info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-atomic-sts-safep ((tyname tynamep) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if an atomic type specifier is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is rejected when the type denoted by the type name
     is the struct type being split,
     because it is not clear how atomicity interacts with splitting.
     It is instead fine for a pointer to the struct type to be atomic."))
  (and (tyname-unamb/anno-p tyname)
       (or (not (type-may-be-struct-spec-p
                 (type-vinfo->type (tyname->info tyname))
                 spec))
           (sts-reject (type-spec-atomic tyname)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declor-nonabstract-sts-safep ((declor declorp)
                                            info
                                            (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a non-abstract parameter declarator
          is safe for the STS transformation."
  (and (or (type+uid-vinfop info)
           (raise "Internal error: malformed ~x0." info))
       (or (top-type-sts-safep (type+uid-vinfo->type info) spec)
           (sts-reject (param-declor-nonabstract declor info))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declor-abstract-sts-safep ((declor absdeclorp)
                                         info
                                         (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if an abstract parameter declarator
          is safe for the STS transformation."
  (and (or (type-vinfop info)
           (raise "Internal error: malformed ~x0." info))
       (or (top-type-sts-safep (type-vinfo->type info) spec)
           (sts-reject (param-declor-abstract declor info))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-info-sts-safep ((tyname tynamep)
                               (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a type name
          is safe for the STS transformation."
  (b* ((info (tyname->info tyname)))
    (and (or (type-vinfop info)
             (raise "Internal error: malformed ~x0." info))
         (or (top-type-sts-safep (type-vinfo->type info) spec)
             (sts-reject (tyname-fix tyname)))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-declor-info-sts-safep ((sdeclor struct-declorp)
                                      (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if a structure declarator
          is safe for the STS transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this is a member of a structure,
     we are not at the top level,
     so we call @(tsee type-sts-safep) with @('nested') set to @('t'),
     instead of @(tsee top-type-sts-safep)."))
  (b* ((info (struct-declor->info sdeclor)))
    (and (or (type-vinfop info)
             (raise "Internal error: malformed ~x0." info))
         (or (type-sts-safep (type-vinfo->type info) t spec)
             (sts-reject (struct-declor-fix sdeclor)))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-declor-info-sts-safep ((ideclor init-declorp)
                                    (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if the type in
          the validation annotation of an initializer declarator
          is safe for the STS transformation."
  (b* ((info (init-declor->info ideclor)))
    (and (or (init-declor-vinfop info)
             (raise "Internal error: malformed ~x0." info))
         (or (top-type-sts-safep (init-declor-vinfo->type info) spec)
             (sts-reject (init-declor-fix ideclor)))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-info-sts-safep ((fundef fundefp) (spec sts-struct-specp))
  :returns (yes/no booleanp)
  :short "Check if the type in
          the validation annotation of a function definition
          is safe for the STS transformation."
  (b* ((info (fundef->info fundef)))
    (and (or (type+uid-vinfop info)
             (raise "Internal error: malformed ~x0." info))
         (or (top-type-sts-safep (type+uid-vinfo->type info) spec)
             (sts-reject (fundef-fix fundef)))))
  :no-function nil)

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
    "The predicates start at the @(tsee exprs/decls/stmts) clique.
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
     so for now we just ignore them,
     i.e. we let them be treated in the default way
     by @(tsee fty::deffold-reduce).")
   (xdoc::p
    "Option and list AST types are safe iff their components are.
     This is the default generated definition of the predicates.")
   (xdoc::p
    "AST types that merely wrap other AST types,
     like @(tsee const-expr) and @(tsee spec/qual),
     are allowed iff their wrapped ASTs are,
     which is the default definition.")
   (xdoc::p
    "Some constructs are handled via separate ACL2 functions,
     whose documentation explains the rationale.
     See those functions for details,
     which we do not repeat here.
     Here we only discuss the rationale for the constructs
     handled directly in the @(tsee fty::deffold-reduce).")
   (xdoc::p
    "Identifiers, constants, and strings are safe leaves.
     Although an identifier may be a variable of struct type,
     this is safe in isolation;
     unsafety can only come from a larger construct containing the variable.
     So we keep the default for these.")
   (xdoc::p
    "A parenthesized expression is safe iff its inner expression is,
     which is what the default does.")
   (xdoc::p
    "We reject generic selections out of caution.
     The controlling expression may have struct type;
     we need to think of the safety.")
   (xdoc::p
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
   (xdoc::p
    "Function calls are allowed
     (so long as the arguments satisfy the safety checks),
     but this relies on the assumption that
     we are safety-checking all the called functions.
     We plan to do this as a complementary safety check.")
   (xdoc::p
    "We allow member access, by value or by pointer.
     This is the normal safe way to access structs.
     Note that the nesting of the struct type being split
     in other structs or in unions is excluded via @(tsee type-sts-safep).")
   (xdoc::p
    "Taking the address of a label (a GCC/Clang extension) is safe;
     it does not involve structs.")
   (xdoc::p
    "Ternary expressions are safe iff their components are,
     which is the default definition of the predicate.")
   (xdoc::p
    "A statement expression (GCC/Clang extension)
     is safe iff the compound statement is,
     which is the default definition of the predicate.")
   (xdoc::p
    "We reject
     @('__builtin_types_compatible_p'),
     @('__builtin_offsetof'), and
     @('__builtin_va_arg')
     out of caution for now.")
   (xdoc::p
    "An expression preceded by @('__extension__') is safe iff
     the expression itself is,
     so we leave it as default.")
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
    "We allow all the type specifiers that do not contain other types.")
   (xdoc::p
    "We allow all @('struct') type specifiers.
     We expect there to be at least one in the translation unit,
     the one for the struct type being split,
     as explained in @(see struct-type-split-safety).
     There may be others.
     The validator annotates all of them with their struct type,
     which has either a tag without members or no tag with members.
     Whether that is the same struct type being split,
     can be seen from the UID, but we do not seem to need any check here.
     If it is the same UID, then presumably the validator has checked
     that the tag is the same and the members are compatible.
     The non-nesting of the struct type being split in other struct
     is checked elsewhere, via @(tsee type-sts-safep).")
   (xdoc::p
    "We allow all @('union') type specifiers.
     The non-nesting of the struct being split
     is checked elsewhere, via @(tsee type-sts-safep).")
   (xdoc::p
    "We allow all @('typedef') type specifiers.
     They may stand for the struct type being split,
     but that in itself is harmless.
     In fact, the validator expands all @('typedef')s;
     @(tsee type) does not have a summand for @('typedef')s.")
   (xdoc::p
    "We reject @('typeof') and spelling variants,
     in C23 or in GCC/Clang-extended C17.
     This is because the type may denote the struct type being split,
     without that being immediately syntactically apparent.")
   (xdoc::p
    "@('__auto_type') is excluded because it does type inference,
     and so we need to think of this more carefully.
     In C23, the @('auto') storage class specifier also does type inference,
     and so it should be treated the same way (excluded for now).
     However, for now the STS transformation is expressly limited to C17
     (the transformation checks that explicitly),
     and so we can accept the @('auto') storage class specifier for now.")
   (xdoc::p
    "We allow all alignment specifiers,
     because they do not seem related to the struct type being split.")
   (xdoc::p
    "For now we accept all attributes without examining them,
     because attributes may contain expressions
     but those are not yet annotated by the validator,
     and the STS transformation does not transform attributes.
     All of this will need to be handled properly eventually.")
   (xdoc::p
    "For the same reason as attributes,
     for now we accept all the assembler input and output operands.")
   (xdoc::p
    "We reject the @('__stdcall') and @('__declspec') declaration specifiers,
     out of caution.")
   (xdoc::p
    "We reject initializers with optional designations for now,
     because they may affect the struct type being split.")
   (xdoc::p
    "Declarators (@(tsee declor) ASTs) are checked indirectly,
     via the types of the ASTs where declarators may appear:
     function definitions,
     initializer declarators,
     and non-abstract parameter declarators.")
   (xdoc::p
    "Abstract declarators (@(tsee absdeclor) ASTs) are checked indirectly,
     via the types of the ASTs where abstract declarators may appear:
     abstract parameter declarators,
     and type names.")
   (xdoc::p
    "Declarations are checked indirectly.
     If a declaration has initializer declarators,
     we check (the types of) all its initializer declarators.
     If a declaration does not have initializer declarators,
     it must be a structure or union or enumeration declaration
     (see @(tsee c$::valid-declon));
     these are checked by checking their structure declarators,
     which are the only cases in which the struct type being split
     might be nested inside other structure or union types.
     Declarations may also be static assertion declarations,
     which are checked independently.")
   (xdoc::p
    "We exclude assembly, because we do not know what it does exactly.")
   (xdoc::p
    "We reject translation items that are
     preprocessing constructs preserved by our preprocessor.
     We do not have transformations working on those yet.")
   (xdoc::p
    "Like we exclude the @('_Atomic') type specifier
     applied to the struct type being split,
     we should also exclude the @('_Atomic') type qualifier
     applied to the struct type being split.
     Currently this is a bit cumbersome to check because
     that type qualifier may not be immediately before the struct type.
     We should extend our model of types with an atomic flag,
     which is more generally useful,
     and then we should be able to check atomic type
     without looking directly at specifiers and qualifiers."))
  :types (exprs/decls/stmts
          fundef
          ext-declon
          trans-items
          trans-unit)
  :result booleanp
  :default t
  :combine and
  :extra-args ((spec sts-struct-specp))
  :override
  ((expr :gensel (sts-reject (expr-fix expr)))
   (expr :complit (and (tyname-sts-safep expr.type spec)
                       (desiniter-list-sts-safep expr.elems spec)
                       (tyname-info-sts-safep expr.type spec)))
   (expr :unary (and (expr-sts-safep expr.arg spec)
                     (expr-unary-sts-safep expr.op expr.arg expr.info spec)))
   (expr :sizeof (and (tyname-sts-safep expr.type spec)
                      (expr-sizeof-sts-safep expr.type spec)))
   (expr :alignof (and (tyname-sts-safep expr.type spec)
                       (expr-alignof-sts-safep expr.type expr.uscores spec)))
   (expr :cast (and (tyname-sts-safep expr.type spec)
                    (expr-sts-safep expr.arg spec)
                    (expr-cast-sts-safep expr.type expr.arg spec)))
   (expr :binary (and (expr-sts-safep expr.arg1 spec)
                      (expr-sts-safep expr.arg2 spec)
                      (expr-binary-sts-safep
                       expr.op expr.arg1 expr.arg2 expr.info spec)))
   (expr :tycompat (sts-reject (expr-fix expr)))
   (expr :offsetof (sts-reject (expr-fix expr)))
   (expr :va-arg (sts-reject (expr-fix expr)))
   (type-spec :atomic (and (tyname-sts-safep type-spec.type spec)
                           (type-spec-atomic-sts-safep type-spec.type spec)))
   (type-spec :typeof-expr (sts-reject (type-spec-fix type-spec)))
   (type-spec :typeof-type (sts-reject (type-spec-fix type-spec)))
   (type-spec :auto-type (sts-reject (type-spec-fix type-spec)))
   (decl-spec :stdcall (sts-reject (decl-spec-fix decl-spec)))
   (decl-spec :declspec (sts-reject (decl-spec-fix decl-spec)))
   (desiniter (sts-reject (desiniter-fix desiniter)))
   (param-declor :nonabstract (and (declor-sts-safep param-declor.declor spec)
                                   (param-declor-nonabstract-sts-safep
                                    param-declor.declor
                                    param-declor.info
                                    spec)))
   (param-declor :abstract (and (absdeclor-sts-safep param-declor.declor spec)
                                (param-declor-abstract-sts-safep
                                 param-declor.declor
                                 param-declor.info
                                 spec)))
   (tyname (b* (((tyname tyname)))
             (and (spec/qual-list-sts-safep tyname.specquals spec)
                  (absdeclor-option-sts-safep tyname.declor? spec)
                  (tyname-info-sts-safep tyname spec))))
   (struct-declor (b* (((struct-declor struct-declor)))
                    (and (declor-option-sts-safep struct-declor.declor? spec)
                         (const-expr-option-sts-safep struct-declor.expr? spec)
                         (struct-declor-info-sts-safep struct-declor spec))))
   (attrib t)
   (init-declor (b* (((init-declor init-declor)))
                  (and (declor-sts-safep init-declor.declor spec)
                       (attrib-spec-list-sts-safep init-declor.attribs spec)
                       (initer-option-sts-safep init-declor.initer? spec)
                       (init-declor-info-sts-safep init-declor spec))))
   (asm-output t)
   (asm-input t)
   (asm-stmt (sts-reject (asm-stmt-fix asm-stmt)))
   (fundef (b* (((fundef fundef)))
             (and (decl-spec-list-sts-safep fundef.specs spec)
                  (declor-sts-safep fundef.declor spec)
                  (attrib-spec-list-sts-safep fundef.attribs spec)
                  (declon-list-sts-safep fundef.declons spec)
                  (comp-stmt-sts-safep fundef.body spec)
                  (fundef-info-sts-safep fundef spec))))
   (trans-item :include (sts-reject (trans-item-fix trans-item)))
   (trans-item :define (sts-reject (trans-item-fix trans-item)))
   (trans-item :undef (sts-reject (trans-item-fix trans-item)))
   (trans-item :cond (sts-reject (trans-item-fix trans-item))))
  :name abstract-syntax-sts-safep)
