; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")
(include-book "implementation-environments")
(include-book "uid")
(include-book "file-paths")

(include-book "../language/types")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(include-book "kestrel/abstract-domains/many-valued-logics/3vl-defs" :dir :system)

(acl2::controlled-configuration)

(local (include-book "std/basic/inductions" :dir :system))

(local (include-book "kestrel/abstract-domains/many-valued-logics/3vl" :dir :system))

(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions.

(defrulel equal-of-nfix-and-0
  (equal (equal (nfix x) 0)
         (not (posp x)))
  :enable nfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (validation)
  :short "C types used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a model of C types,
     along with some operations over those types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-array-kind
  :parents (type)
  :short "Fixtype classifying C array types by completeness and length form."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(':const-len') case represents array types whose size specifier
     is an integer constant expression
     or whose length is inferred from an initializer.
     The @('len') field allows a @('nil') value
     to represent an unknown length.
     This occurs as a result of imprecise analysis.
     In particular, the validator currently classifies
     an array completed by its initializer as @(':const-len'),
     but does not yet derive its numerical length from that initializer,
     so its @('len') field is @('nil').
     We use a positive integer instead of a natural
     because arrays are not empty [C17:6.2.5/20] [C23:6.2.5/25],
     and so a determined constant length must not be 0
     (but we can revise this if we discover that
     array types may need to track a 0 length).")
   (xdoc::p
    "The @(':nonconst-len') case represents complete array types
     whose size specifier is not an integer constant expression,
     including an unspecified size written as @('*').
     We do not yet store any information in this case.
     Eventually, we may wish to distinguish
     a size specified by a nonconstant expression
     from an unspecified size (written as @('*')),
     and to store the size expression if there is one.")
   (xdoc::p
    "The @(':unknown-complete') case represents a complete array type
     for which we do not have enough information to classify as either
     @(':const-len') or @(':nonconst-len').")
   (xdoc::p
    "The @(':incomplete') case represents an incomplete array type.")
   (xdoc::p
    "Note that these type cases do not capture
     whether the array type is a variable-length array (VLA).
     VLA status depends on more than just the array length;
     it also depends on whether the array element type has known constant size
     [C17:6.7.6.2/4] [C23:6.7.7.3/4].
     Therefore, a @(':nonconst-len') array is known to be a VLA,
     but a @(':const-len') array may or may not be a VLA.")
   (xdoc::p
    "Finally, we clarify some terminology.
     The standard typically uses ``size''
     to refer to the number of array elements.
     However, it also uses ``size'' to refer
     to the overall size of the array type,
     i.e. the value returned by @('sizeof').
     To disambiguate these two concepts, we generally use ``length''
     to refer to the number of array elements.
     We still use ``size'' when referring to a named piece of syntax,
     i.e. a size specifier or size expression."))
  (:const-len ((len pos-option)))
  (:nonconst-len ())
  (:unknown-complete ())
  (:incomplete ())
  :pred type-array-kindp
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes type/type-list
  (fty::deftagsum type
    :short "Fixtype of C types [C17:6.2.5]."
    :long
    (xdoc::topstring
     (xdoc::p
      "Currently we do not model all the C types in detail,
       but only an approximate version of them,
       which still lets us perform some validation.
       We plan to refine the types, and the rest of the validator,
       to cover exactly all the validity checks prescribed by C17
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
       "Structure types [C17:6.2.5/20].
        Structure types contain a @(see UID), translation unit name,
        and information about the tag and members
        (see @(tsee type-struni-tag/members)).
        The UID allows disambiguation of otherwise identical structs
        which occur in different scopes.
        The translation unit name identifies the translation unit in which
        the struct type was declared.
        This is necessary to weaken the compatibility rules
        when comparing structs across translation units.")
      (xdoc::li
       "Union types [C17:6.2.5/20].
        Union types contain the same information as structure types.")
      (xdoc::li
       "A collective type for all enumeration types [C17:6.2.5/20].
        This is an approximation,
        because there are different enumeration types.")
      (xdoc::li
       "An array type [C17:6.2.5/20],
        derived from the ``element type''
        and an array kind.
        See @(tsee type-array-kind).")
      (xdoc::li
       "A pointer type [C17:6.2.5/20],
        derived from the ``referenced type.''")
      (xdoc::li
       "A function type [C17:6.2.5/20],
        which contains the return type and parameter information
        (see @(tsee type-params)).")
      (xdoc::li
       "An ``unknown'' type that we need due to our current approximation.
        Our validator must not reject valid code.
        But due to our approximate treatment of types,
        and incomplete @(see implementation-environments),
        we cannot always calculate a type.
        E.g., a character constant with the @('L') prefix
        should have the type represented by @('wchar_t') [C17:6.4.4.4/9],
        but we do not yet indicate in the implementation environment
        what primitive type is equivalent to @('wchar_t').
        Therefore, we give such character constants the unknown type,
        which is always acceptable.")
      (xdoc::li
       "An ``unknown builtin'' type that restricts
        the previously described unknown type to only involve built-in types.
        I.e., the type cannot involve a user-defined
        structure, union, or enumeration.")
      (xdoc::li
       "An ``unknown scalar'' type that restricts
        the previously described unknown type to be at least scalar.")
      (xdoc::li
       "An ``unknown arithmetic'' type that restricts
        the previously described unknown type to be at least arithmetic."))
     (xdoc::p
      "The unknown built-in, scalar, and arithmetic types
       are useful to improve the precision of our validation.")
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
    (:struct ((uid uid)
              (tunit? filepath-option)
              (tag/members type-struni-tag/members)))
    (:union ((uid uid)
             (tunit? filepath-option)
             (tag/members type-struni-tag/members)))
    (:enum ())
    (:array ((of type)
             (kind type-array-kind)))
    (:pointer ((to type)))
    (:function ((ret type) (params type-params)))
    (:unknown ())
    (:unknown-builtin ())
    (:unknown-scalar ())
    (:unknown-arithmetic ())
    :pred typep
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum type-struni-tag/members
    :short "Fixtype of the portion of struct/union types corresponding to the
            tag and members."
    :long
    (xdoc::topstring
     (xdoc::p
      "We store the member information directly
       for untagged structs and unions.
       Untagged structs and unions are always complete
       and therefore this information is always available.
       Furthermore, untagged structs and unions cannot be self-referential,
       so the members will always be finite.")
     (xdoc::p
      "We do not store the member information directly
       for tagged structs and unions.
       Instead, member information is stored in an external environment
       and associated to the struct @(see UID).
       See @(tsee type-completions)."))
    (:tagged ((tag ident)))
    (:untagged ((members type-struni-member-list)))
    :pred type-struni-tag/members-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod type-struni-member
    :short "Fixtype of struct/union members."
    :long
    (xdoc::topstring
     (xdoc::p
      "If a member does not have a name,
       it must be either an anonymous struct/union
       or a bit-field [C17:6.7.2.1/1-2]."))
    ((name? ident-option)
     (type type))
    :pred type-struni-member-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist type-struni-member-list
    :short "Fixtype of lists of struct/union members."
    :long
    (xdoc::topstring
     (xdoc::p
      "Struct/union members are defined in @(tsee type-struni-member)."))
    :elt-type type-struni-member
    :true-listp t
    :elementp-of-nil nil
    :pred type-struni-member-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum type-params
    :short "Fixtype of the portion of function types pertaining to the function
            parameters."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @(':prototype') case corresponds to function prototypes
       [C17:6.2.1/2], [C17:6.2.7/3].
       It also includes the special case in which the parameter list is
       comprised of just one unnamed parameter of type @('void')
       [C17:6.7.6.3/10].
       This is represented by an empty type list in the @('params') field.
       If the @('params') field is empty, an ellipsis must not be present.
       (A parameter list is grammatically nonempty [C17:6.7.6/1],
       and the special @('void') case requires no other items
       in the parameter type list [C17:6.7.6.3/10].)")
     (xdoc::p
      "The @(':old-style') case represents functions declared with
       identifier lists instead of parameter lists,
       and which are associated with a definition.
       A function declaration with an identifier list
       can only exist as part of a function definition,
       unless the identifier list is empty [6.7.6.3/3].
       This case of a function declaration with empty identifier list
       not associated with a definition
       is represented by the @(':unspecified') case.
       An identifier list only names the parameters,
       it does not assign them a type.
       The type list in the @('params') field
       come from the declarations in a function definition
       which follows the function declarator and precedes the function body.")
     (xdoc::p
      "The @(':unspecified') case corresponds to a function declarator
       with an empty identifier list not associated with a definition.
       It indicates that the number of parameters
       and the types of those parameter is unspecified [C17:6.7.6.3/14].")
     (xdoc::p
      "For both the @(':prototype') and @(':old-style') cases,
       the @('params') field represents the parameter types after adjustments
       [C17:6.7.6.3/7-8]."))
    (:prototype ((params type-list) (ellipsis bool)))
    (:old-style ((params type-list)))
    (:unspecified ())
    :pred type-params-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 0))

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
    :measure (two-nats-measure (acl2-count x) 0)

    ///

    (defruled cdr-of-type-list-fix
      (equal (cdr (type-list-fix x))
             (type-list-fix (cdr x)))
      :enable type-list-fix))

  ///

  (defrule type-struni-member-list-count-of-append
    (equal (type-struni-member-list-count (append x y))
           (+ (type-struni-member-list-count x)
              (type-struni-member-list-count y)
              -1))
    :induct (acl2::cdr-induct x)
    :enable type-struni-member-list-count))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-type
  :short "An irrelevant type."
  :type typep
  :body (type-void))

(defirrelevant irr-type-struni-member
  :short "An irrelevant @(tsee type-struni-member)."
  :type type-struni-member-p
  :body (make-type-struni-member :name? nil :type (irr-type)))

(defirrelevant irr-type-params
  :short "An irrelevant @(tsee type-params)."
  :type type-params-p
  :body (type-params-unspecified))

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

(define type-struct->tag? ((type typep))
  :guard (type-case type :struct)
  :returns (tag? ident-optionp)
  (let ((tag/members (type-struct->tag/members type)))
    (type-struni-tag/members-case
      tag/members
      :tagged tag/members.tag
      :untagged nil)))

(define type-union->tag? ((type typep))
  :guard (type-case type :union)
  :returns (tag? ident-optionp)
  (let ((tag/members (type-union->tag/members type)))
    (type-struni-tag/members-case
      tag/members
      :tagged tag/members.tag
      :untagged nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-struni-member-list-lookup ((ident identp)
                                        (members type-struni-member-listp))
  :returns (type? type-optionp)
  :short "Lookup a @(tsee type-struni-member) by name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Members of anonymous struct/union members
     are considered members of the containing struct/union [C17:6.7.2.1/13].
     Therefore, this function recurses into such members."))
  (b* (((when (endp members))
        nil)
       ((type-struni-member member) (first members)))
    (if member.name?
        (if (ident-equal ident member.name?)
            member.type
          (type-struni-member-list-lookup ident (rest members)))
      (or (type-case
            member.type
            :struct (type-struni-tag/members-case
                      member.type.tag/members
                      :tagged nil
                      :untagged (type-struni-member-list-lookup
                                  ident
                                  member.type.tag/members.members))
            :union (type-struni-tag/members-case
                     member.type.tag/members
                     :tagged nil
                     :untagged (type-struni-member-list-lookup
                                 ident
                                 member.type.tag/members.members))
            :otherwise nil)
          (type-struni-member-list-lookup ident (rest members)))))
  :measure (type-struni-member-list-count members)
  :hooks ((:fix :hints (("Goal" :induct t)))))

;;;;;;;;;;;;;;;;;;;;

(defrule type-struni-member-list-lookup-when-not-consp-of-arg2-type-prescription
  (implies (not (consp members))
           (equal (type-struni-member-list-lookup ident members)
                  nil))
  :rule-classes :type-prescription
  :enable type-struni-member-list-lookup)

(defrule type-struni-member-list-lookup-of-append
  (equal (type-struni-member-list-lookup ident (append x y))
         (or (type-struni-member-list-lookup ident x)
             (type-struni-member-list-lookup ident y)))
  :induct t
  :enable type-struni-member-list-lookup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce well-formed-p
  :short "Definition of predicates to check whether a type is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "These predicates are currently over-approximate.
     That is, if @('(not (well-formedp type))') holds,
     the type represented by @('type') is certainly ill-formed.
     But, when @('(well-formedp type)'), it is not necessarily the case that
     @('type') is truly well-formed.")
   (xdoc::p
    "Currently, we check the following conditions:")
   (xdoc::ul
    (xdoc::li
     "The return type of a function is neither an array nor a function
      [C17:6.7.6.3/1].")
    (xdoc::li
     "If a member of a struct or union does not have a name
      and the member type is a struct,
      the struct type of the member must be untagged [C17:6.7.2.1/2].")
    (xdoc::li
     "If a member of a struct or union does not have a name
      and the member type is a union,
      the union type of the member must be untagged [C17:6.7.2.1/2]."))
   (xdoc::p
    "The following is a likely incomplete list
     of all the conditions we do not yet check:")
   (xdoc::ul
    (xdoc::li
     "The type of a function parameter is neither an array nor a function
      (after adjustment) [C17:6.7.6.3/8].")
    (xdoc::li
     "If a member of a struct or union type does not have a name
      and the member type is neither a struct nor a union,
      the member must be a bit-field [C17:6.7.2.1/2].")
    (xdoc::li
     "The names of all members of a struct/union must be distinct,
      including those which occur in anonymous struct/union members.")
    (xdoc::li
     "Two struct/union types with the same UID should be identical.")
    (xdoc::li
     "If a struct/union is defined in translation unit @('\"foo.c\"'),
      the types of the members of the struct/union type
      should not include references to any other translation unit
      besides @('\"foo.c\"').
      (It is impossible for a struct/union type
      defined in one translation unit
      to be visible in another,
      and the creation of a type composite will not
      introduce a translation unit.)")))
  :types (type/type-list)
  :result booleanp
  :default t
  :combine and
  :override
  ((type
     :function (and (not (type-case type.ret :array))
                    (not (type-case type.ret :function))
                    (type-params-well-formed-p type.params)))
   (type-struni-member
     (b* (((type-struni-member type-struni-member) type-struni-member))
       (if type-struni-member.name?
           t
         (type-case
           type-struni-member.type
           :struct (type-struni-tag/members-case
                     type-struni-member.type.tag/members
                     :untagged)
           :union (type-struni-tag/members-case
                    type-struni-member.type.tag/members
                    :untagged)
           :otherwise t)))))
  :name abstract-syntax-well-formed-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap type-completions
  :short "A map from @(see UID)s to struct/union members."
  :long
  (xdoc::topstring
   (xdoc::p
    "We cannot store the @(tsee type-struni-member-list)
     of a tagged struct/union type directly,
     because the type might be self-referential.
     Instead, we maintain a ``completions'' map
     which associates the struct/union type @(see UID)
     to its @(tsee type-struni-member-list)."))
  :key-type uid
  :val-type type-struni-member-list
  :pred type-completions-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-struni-tag/members->members
  ((tag/members type-struni-tag/members-p)
   (uid uidp)
   (completions type-completions-p))
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (members type-struni-member-listp))
  :short "Get the members list from a @(tsee type-struni-tag/members)."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the @(tsee type-struni-tag/members) object is untagged,
     we can get the members directly.
     Otherwise, we lookup the @(see UID) in the @(see type-completions) map."))
  (type-struni-tag/members-case
    tag/members
    :tagged (b* ((uid (uid-fix uid))
                 (completions (type-completions-fix completions))
                 ((mv foundp members) (treemap::lookup? uid completions)))
              (if foundp
                  (mv nil members)
                (mv t nil)))
    :untagged (mv nil tag/members.members))

  ///
  (more-returns
   (members true-listp
            :rule-classes :type-prescription
            :hints (("Goal" :use type-struni-member-listp-of-type-struni-tag/members->members.members
                            :in-theory (disable type-struni-member-listp-of-type-struni-tag/members->members.members))))))

(define type-struni-tag/members->lookup
  ((tag/members type-struni-tag/members-p)
   (ident identp)
   (uid uidp)
   (completions type-completions-p))
  :returns (type? type-optionp)
  :short "Get the members list and lookup a @(tsee type-struni-member)."
  (b* (((mv erp members)
        (type-struni-tag/members->members tag/members uid completions))
       ((when erp)
        nil))
    (type-struni-member-list-lookup ident members)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-some-unknownp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is one of the unknown types."
  (or (type-case type :unknown)
      (type-case type :unknown-builtin)
      (type-case type :unknown-scalar)
      (type-case type :unknown-arithmetic)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-has-some-unknownp
  (define type-has-some-unknownp ((type typep))
    :returns (yes/no booleanp)
    :short "Check if a type is or is derived from one of the unknown types."
    :long
    (xdoc::topstring
     (xdoc::p
      "This does not check for unknown types in completions."))
    (type-case
     type
     :array (type-has-some-unknownp type.of)
     :struct (type-struni-tag/members-case
              type.tag/members
              :tagged t
              :untagged (type-struni-member-list-has-some-unknownp
                         type.tag/members.members))
     :union (type-struni-tag/members-case
              type.tag/members
              :tagged t
              :untagged (type-struni-member-list-has-some-unknownp
                         type.tag/members.members))
     :function (or (type-has-some-unknownp type.ret)
                   (type-params-case
                    type.params
                    :prototype (type-list-has-some-unknownp type.params.params)
                    :old-style (type-list-has-some-unknownp type.params.params)
                    :unspecified nil))
     :otherwise (type-some-unknownp type))
    :measure (type-count type))

  (define type-struni-member-list-has-some-unknownp ((members
                                                      type-struni-member-listp))
    (and (not (endp members))
         (or (type-has-some-unknownp (type-struni-member->type (first members)))
             (type-struni-member-list-has-some-unknownp (rest members))))
    :measure (type-struni-member-list-count members))

  (define type-list-has-some-unknownp ((types type-listp))
    (and (not (endp types))
         (or (type-has-some-unknownp (first types))
             (type-list-has-some-unknownp (rest types))))
    :measure (type-list-count types)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-derived-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if the type is a derived type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The standard defines a <emph>derived type</emph>
     as an array, structure, union, function, pointer, or atomic type
     [C17:6.2.5/20].
     Since we do not currently have a representation of atomic types,
     atomicity is not considered.
     The result is a "
    (xdoc::seetopic "acl2::3vl" "three-valued generalized boolean")
    " in order to reflect uncertainty around certain of the unknown types."))
  (type-case
   type
   :array t
   :struct t
   :union t
   :function t
   :pointer t
   :unknown :unknown
   :unknown-builtin :unknown
   :unknown-scalar :unknown
   :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-signed-integer-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a standard signed integer type [C17:6.2.5/4]."
  (cond ((member-eq (type-kind type)
                    '(:schar :sshort :sint :slong :sllong))
         t)
        ((member-eq (type-kind type)
                    '(:unknown
                      :unknown-builtin
                      :unknown-scalar
                      :unknown-arithmetic))
         :unknown)
        (t nil))

  ///

  (defrule type-standard-signed-integer-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-standard-signed-integer-3p type)
                    (cond ((member-equal
                             kind
                             '(:schar :sshort :sint :slong :sllong))
                           t)
                          ((member-equal kind '(:unknown
                                                :unknown-builtin
                                                :unknown-scalar
                                                :unknown-arithmetic))
                           :unknown)
                          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-signed-integer-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a signed integer type [C17:6.2.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not model any extended signed integer types,
     so the signed integer types coincide with
     the standard signed integer types."))
  (type-standard-signed-integer-3p type)

  ///

  (defrule type-signed-integer-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-signed-integer-3p type)
                    (type-standard-signed-integer-3p type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-unsigned-integer-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a standard unsigned integer type
          [C17:6.2.5/6]."
  (cond ((member-eq (type-kind type)
                    '(:bool :uchar :ushort :uint :ulong :ullong))
         t)
        ((member-eq (type-kind type)
                    '(:unknown
                      :unknown-builtin
                      :unknown-scalar
                      :unknown-arithmetic))
         :unknown)
        (t nil))

  ///

  (defrule type-standard-unsigned-integer-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-standard-unsigned-integer-3p type)
                    (cond ((member-equal
                             kind
                             '(:bool :uchar :ushort :uint :ulong :ullong))
                           t)
                          ((member-equal kind '(:unknown
                                                :unknown-builtin
                                                :unknown-scalar
                                                :unknown-arithmetic))
                           :unknown)
                          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-unsigned-integer-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is an unsigned integer type [C17:6.2.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not model any extended unsigned integer types,
     so the unsigned integer types coincide with
     the standard unsigned integer types."))
  (type-standard-unsigned-integer-3p type)

  ///

  (defrule type-unsigned-integer-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-unsigned-integer-3p type)
                    (type-standard-unsigned-integer-3p type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-standard-integer-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a standard integer type [C17:6.2.5/7]."
  (3or (type-standard-signed-integer-3p type)
       (type-standard-unsigned-integer-3p type))

  ///

  (defrule type-standard-integer-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-standard-integer-3p type)
                    (3or (type-standard-signed-integer-3p type)
                         (type-standard-unsigned-integer-3p type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-real-floating-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a real floating type [C17:6.2.5/10]."
  (cond ((member-eq (type-kind type)  '(:float :double :ldouble))
         t)
        ((member-eq (type-kind type)
                    '(:unknown
                      :unknown-builtin
                      :unknown-scalar
                      :unknown-arithmetic))
         :unknown)
        (t nil))

  ///

  (defrule type-real-floating-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-real-floating-3p type)
                    (cond ((member-equal kind '(:float :double :ldouble))
                           t)
                          ((member-equal kind '(:unknown
                                                :unknown-builtin
                                                :unknown-scalar
                                                :unknown-arithmetic))
                           :unknown)
                          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-complex-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a complex type [C17:6.2.5/11]."
  (cond ((member-eq (type-kind type)  '(:floatc :doublec :ldoublec))
         t)
        ((member-eq (type-kind type)
                    '(:unknown
                      :unknown-builtin
                      :unknown-scalar
                      :unknown-arithmetic))
         :unknown)
        (t nil))

  ///

  (defrule type-complex-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-complex-3p type)
                    (cond ((member-equal kind '(:floatc :doublec :ldoublec))
                           t)
                          ((member-equal kind '(:unknown
                                                :unknown-builtin
                                                :unknown-scalar
                                                :unknown-arithmetic))
                           :unknown)
                          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-floating-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a floating type [C17:6.2.5/11]."
  (3or (type-real-floating-3p type)
       (type-complex-3p type))

  ///

  (defrule type-floating-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-floating-3p type)
                    (3or (type-real-floating-3p type)
                         (type-complex-3p type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-basic-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a basic type [C17:6.2.5/14]."
  (3or (type-case type :char)
       (type-signed-integer-3p type)
       (type-unsigned-integer-3p type)
       (type-floating-3p type))

  ///

  (defrule type-basic-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-basic-3p type)
                    (3or (equal kind :char)
                         (type-signed-integer-3p type)
                         (type-unsigned-integer-3p type)
                         (type-floating-3p type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-character-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a character type [C17:6.2.5/15]."
  (cond ((member-eq (type-kind type)  '(:char :schar :uchar))
         t)
        ((member-eq (type-kind type)
                    '(:unknown
                      :unknown-builtin
                      :unknown-scalar
                      :unknown-arithmetic))
         :unknown)
        (t nil))

  ///

  (defrule type-character-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-character-3p type)
                    (cond ((member-equal kind '(:char :schar :uchar))
                           t)
                          ((member-equal kind '(:unknown
                                                :unknown-builtin
                                                :unknown-scalar
                                                :unknown-arithmetic))
                           :unknown)
                          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integer-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is an integer type [C17:6.2.5/17]."
  (3or (type-case type :char)
       (type-signed-integer-3p type)
       (type-unsigned-integer-3p type)
       (type-case type :enum))

  ///

  (defrule type-integer-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-integer-3p type)
                    (3or (equal kind :char)
                         (type-signed-integer-3p type)
                         (type-unsigned-integer-3p type)
                         (equal kind :enum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-real-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a real type [C17:6.2.5/17]."
  (3or (type-integer-3p type)
       (type-real-floating-3p type))

  ///

  (defrule type-real-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-real-3p type)
                    (3or (type-integer-3p type)
                         (type-real-floating-3p type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-arithmetic-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is an arithmetic type [C17:6.2.5/18]."
  (3or (type-integer-3p type)
       (type-floating-3p type)
       (type-case type :unknown-arithmetic))

  ///

  (defrule type-arithmetic-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-arithmetic-3p type)
                    (3or (type-integer-3p type)
                         (type-floating-3p type)
                         (equal kind :unknown-arithmetic)))))

  (defrule type-arithmetic-3p-when-type-integer-3p
    (implies (3definitely (type-integer-3p type))
             (3definitely (type-arithmetic-3p type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalar-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is a scalar type [C17:6.2.5/21]."
  (3or (type-arithmetic-3p type)
       (type-case type :pointer)
       (type-case type :unknown-scalar))

  ///

  (defrule type-scalar-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-scalar-3p type)
                    (3or (type-arithmetic-3p type)
                         (equal kind :pointer)
                         (equal kind :unknown-scalar))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-aggregate-3p ((type typep))
  :returns (3vl 3p)
  :short "Check if a type is an aggregate type [C17:6.2.5/21]."
  (cond ((or (type-case type :array)
             (type-case type :struct))
         t)
        ((or (type-case type :unknown)
             (type-case type :unknown-builtin))
         :unknown)
        (t nil))

  ///

  (defrule type-aggregate-3p-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-aggregate-3p type)
                    (cond ((member-equal kind '(:array :struct))
                           t)
                          ((member-equal kind '(:unknown :unknown-builtin))
                           :unknown)
                          (t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-array-kind-equal-3p ((x type-array-kindp)
                                  (y type-array-kindp))
  :returns (3vl 3p)
  :short "Check whether two array kinds are equal."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is equality of array kinds,
     accommodating the imprecision of the representation.
     Two constant lengths are equal if both are known and equal;
     if either is unknown, we cannot tell.
     Two nonconstant lengths may or may not be equal,
     since we do not track their size expressions.
     A kind that is complete but otherwise unknown
     may be equal to any complete kind.
     Two incomplete kinds are equal, and any other combination differs."))
  (type-array-kind-case
    x
    :const-len
    (type-array-kind-case
      y
      :const-len (if (and x.len y.len)
                     (equal x.len y.len)
                   :unknown)
      :unknown-complete :unknown
      :otherwise nil)
    :nonconst-len
    (type-array-kind-case
      y
      :nonconst-len :unknown
      :unknown-complete :unknown
      :otherwise nil)
    :unknown-complete
    (type-array-kind-case
      y
      :incomplete nil
      :otherwise :unknown)
    :incomplete
    (type-array-kind-case y :incomplete)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-equal-3p
  (define type-equal-3p ((x typep)
                         (y typep))
    :returns (3vl 3p)
    :short "Check whether two types are equal."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is equality of types,
       accommodating the imprecision of the representation")
     (xdoc::p
      "If either type is one of the unknown types,
       the types may be equal if the other type
       may be of the kind that the unknown type stands for.
       Otherwise, two types of different kinds are different.
       Two types of the same kind are equal if their components are.
       Structure and union types are equal if they have the same UID.
       Two enumerated types may or may not be equal,
       since we do not currently distinguish different enumerations.
       The remaining types are equal
       if they are represented identically."))
    (cond ((or (type-case x :unknown)
               (type-case x :unknown-builtin)
               (type-case y :unknown)
               (type-case y :unknown-builtin))
           :unknown)
          ((type-case x :unknown-scalar)
           (3and (type-scalar-3p y) :unknown))
          ((type-case y :unknown-scalar)
           (3and (type-scalar-3p x) :unknown))
          ((type-case x :unknown-arithmetic)
           (3and (type-arithmetic-3p y) :unknown))
          ((type-case y :unknown-arithmetic)
           (3and (type-arithmetic-3p x) :unknown))
          (t (type-case
               x
               :array
               (type-case
                 y
                 :array (3and$ (type-array-kind-equal-3p x.kind y.kind)
                               (type-equal-3p x.of y.of))
                 :otherwise nil)
               :pointer
               (type-case
                 y
                 :pointer (type-equal-3p x.to y.to)
                 :otherwise nil)
               :function
               (type-case
                 y
                 :function (3and$ (type-equal-3p x.ret y.ret)
                                  (type-params-equal-3p
                                   x.params y.params))
                 :otherwise nil)
               :struct
               (type-case
                 y
                 :struct (uid-equal x.uid y.uid)
                 :otherwise nil)
               :union
               (type-case
                 y
                 :union (uid-equal x.uid y.uid)
                 :otherwise nil)
               :enum
               (type-case
                 y
                 :enum :unknown
                 :otherwise nil)
               :otherwise
               (type-equiv x y))))
    :measure (+ (type-count x)
                (type-count y)))

  (define type-params-equal-3p ((x type-params-p)
                                (y type-params-p))
    :returns (3vl 3p)
    :short "Check whether the parameter portions of two function types
            are equal."
    (type-params-case
      x
      :prototype
      (type-params-case
        y
        :prototype (if (equal x.ellipsis y.ellipsis)
                       (type-list-equal-3p x.params y.params)
                     nil)
        :otherwise nil)
      :old-style
      (type-params-case
        y
        :old-style (type-list-equal-3p x.params y.params)
        :otherwise nil)
      :unspecified (type-params-case y :unspecified))
    :measure (+ (type-params-count x)
                (type-params-count y)))

  (define type-list-equal-3p ((x type-listp)
                              (y type-listp))
    :returns (3vl 3p)
    :short "Check whether two lists of types are equal."
    (b* (((when (endp x))
          (endp y))
         ((when (endp y))
          nil))
      (3and$ (type-equal-3p (first x) (first y))
             (type-list-equal-3p (rest x) (rest y))))
    :measure (+ (type-list-count x)
                (type-list-count y)))

  :flag-local nil
  :verify-guards :after-returns
  ///

  (fty::deffixequiv-mutual type/type-list-equal-3p
    :hints (("Goal" :in-theory (disable type-fix-when-enum)))))

;;;;;;;;;;;;;;;;;;;;

(define type-struni-member-list-equal-3p ((x type-struni-member-listp)
                                          (y type-struni-member-listp))
  :returns (3vl 3p)
  :short "Check whether two lists of structure or union members are equal."
  :long
  (xdoc::topstring
   (xdoc::p
    "The names must be the same, in the same order,
     and the types must be equal in the sense of @(tsee type-equal-3p)."))
  (b* (((when (endp x))
        (endp y))
       ((when (endp y))
        nil)
       ((type-struni-member member-x) (first x))
       ((type-struni-member member-y) (first y))
       ((unless (equal member-x.name? member-y.name?))
        nil))
    (3and$ (type-equal-3p member-x.type member-y.type)
           (type-struni-member-list-equal-3p (rest x) (rest y))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule type-array-kind-equal-3p-under-iff-when-same
  (iff (type-array-kind-equal-3p x x)
       t)
  :enable type-array-kind-equal-3p)

(defrule 3possibly-type-array-kind-equal-3p-when-same
  (3possibly (type-array-kind-equal-3p x x))
  :enable type-array-kind-equal-3p)

(defrule type-array-kind-equal-3p-symmetric
  (equal (type-array-kind-equal-3p y x)
         (type-array-kind-equal-3p x y))
  :enable type-array-kind-equal-3p)

(encapsulate ()
  (local
    (defthm-type/type-list-equal-3p-flag
      (defthm type-equal-3p-when-same-lemma
        (implies (equal x y)
                 (iff (type-equal-3p x y)
                      t))
        :flag type-equal-3p)
      (defthm type-params-equal-3p-when-same-lemma
        (implies (equal x y)
                 (iff (type-params-equal-3p x y)
                      t))
        :flag type-params-equal-3p)
      (defthm type-list-equal-3p-when-same-lemma
        (implies (equal x y)
                 (iff (type-list-equal-3p x y)
                      t))
        :flag type-list-equal-3p)
      :hints (("Goal"
               :in-theory (enable 3and
                                  type-equal-3p
                                  type-params-equal-3p
                                  type-list-equal-3p
                                  (:i type/type-list-equal-3p-flag))))))

  (defrule type-equal-3p-under-iff-when-same
    (iff (type-equal-3p x x)
         t))

  (defrule type-params-equal-3p-under-iff-when-same
    (iff (type-params-equal-3p x x)
         t))

  (defrule type-list-equal-3p-under-iff-when-same
    (iff (type-list-equal-3p x x)
         t)))

(defrule 3possibly-type-equal-3p-when-same
  (3possibly (type-equal-3p x x))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-params-equal-3p-when-same
  (3possibly (type-params-equal-3p x x))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-list-equal-3p-when-same
  (3possibly (type-list-equal-3p x x))
  :enable (3possibly 3equiv))

(defthm-type/type-list-equal-3p-flag
  (defthm type-equal-3p-symmetric
    (equal (type-equal-3p y x)
           (type-equal-3p x y))
    :flag type-equal-3p)
  (defthm type-params-equal-3p-symmetric
    (equal (type-params-equal-3p y x)
           (type-params-equal-3p x y))
    :flag type-params-equal-3p)
  (defthm type-list-equal-3p-symmetric
    (equal (type-list-equal-3p y x)
           (type-list-equal-3p x y))
    :flag type-list-equal-3p)
  :hints (("Goal"
           :in-theory (enable type-equal-3p
                              type-params-equal-3p
                              type-list-equal-3p
                              uid-equal
                              (:i type/type-list-equal-3p-flag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integer-promotedp ((type typep))
  :guard (3definitely (type-arithmetic-3p type))
  :returns (yes/no booleanp)
  :short "Check if an arithmetic type is a promoted one."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if it is a possible result of @(tsee type-integer-promote).
     This holds for all types except
     the integer ones with rank below @('int')."))
  (not (member-eq (type-kind type)
                  '(:bool :char :schar :uchar :sshort :ushort :enum)))

  ///

  (defrule type-integer-promotedp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-integer-promotedp type)
                    (not (member-equal kind
                                       '(:bool :char :schar :uchar :sshort
                                         :ushort :enum)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-default-arg-promotedp ((type typep))
  :guard (3definitely (type-arithmetic-3p type))
  :returns (yes/no booleanp)
  :short "Check if type is a default argument promoted type."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if it is a possible result of
     @(tsee type-default-arg-promote).
     This holds for all types except @('float') and
     integer types with rank below @('int')."))
  (not (member-eq (type-kind type)
                  '(:bool :char :schar :uchar :sshort :ushort :enum :float)))

  ///

  (defrule type-default-arg-promotedp-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-default-arg-promotedp type)
                    (not (member-equal kind
                                       '(:bool :char :schar :uchar :sshort
                                         :ushort :enum :float)))))))

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
    :otherwise (type-fix type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-fpconvert ((type typep))
  :returns (new-type typep)
  :short "Convert function types to pointer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This performs the conversion in [C17:6.3.2.1/4].
     It leaves non-function types unchanged."))
  (if (type-case type :function)
      (make-type-pointer :to (type-fix type))
    (type-fix type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integer-promote ((type typep) (ienv ienvp))
  :guard (3definitely (type-arithmetic-3p type))
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
     Thus, for now we promote the (one) enumerated type to unknown scalar."))
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
   :enum (type-unknown-arithmetic)
   :otherwise (type-fix type))

  ///

  (more-returns
   (new-type type-integer-promotedp
             :hints (("Goal" :in-theory (enable type-integer-promotedp)))))

  (defrule type-count-of-type-integer-promote
    (equal (type-count (type-integer-promote type ienv))
           (type-count type))
    :enable type-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-signed ((type1 typep) (type2 typep))
  :guard (and (3definitely (type-signed-integer-3p type1))
              (3definitely (type-signed-integer-3p type2))
              (type-integer-promotedp type1)
              (type-integer-promotedp type2))
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
  :guard-hints (("Goal" :in-theory (enable type-arithmetic-3p
                                           type-integer-3p))))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-unsigned ((type1 typep) (type2 typep))
  :guard (and (3definitely (type-unsigned-integer-3p type1))
              (3definitely (type-unsigned-integer-3p type2))
              (type-integer-promotedp type1)
              (type-integer-promotedp type2))
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
  :guard-hints (("Goal" :in-theory (enable type-arithmetic-3p
                                           type-integer-3p))))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-signed-unsigned ((type1 typep)
                                        (type2 typep)
                                        (ienv ienvp))
  :guard (and (3definitely (type-signed-integer-3p type1))
              (3definitely (type-unsigned-integer-3p type2))
              (type-integer-promotedp type1)
              (type-integer-promotedp type2))
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
  :guard-hints
  (("Goal" :in-theory (enable type-arithmetic-3p
                              type-integer-3p
                              type-integer-promotedp
                              type-unsigned-integer-3p
                              type-signed-integer-3p
                              type-standard-unsigned-integer-3p
                              type-standard-signed-integer-3p))))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert ((type1 typep) (type2 typep) (ienv ienvp))
  :guard (and (3definitely (type-arithmetic-3p type1))
              (3definitely (type-arithmetic-3p type2)))
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
    "If either type is unknown, the result is the unknown arithmetic type;
     we know that it must be at least arithmetic.
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
     via separate functions (see their documentation).
     Note that currently enum types are promoted to the unknown arithmetic type,
     so we need to handle that case after the integer promotions."))
  (cond
   ((or (type-some-unknownp type1)
        (type-some-unknownp type2))
    (type-unknown-arithmetic))
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
   (t (b* ((type1 (type-integer-promote type1 ienv))
           (type2 (type-integer-promote type2 ienv)))
        (cond
         ((equal type1 type2)
          type1)
         ((or (type-case type1 :unknown-arithmetic)
              (type-case type2 :unknown-arithmetic))
          (type-unknown-arithmetic))
         ((and (3definitely (type-signed-integer-3p type1))
               (3definitely (type-signed-integer-3p type2)))
          (type-uaconvert-signed type1 type2))
         ((and (3definitely (type-unsigned-integer-3p type1))
               (3definitely (type-unsigned-integer-3p type2)))
          (type-uaconvert-unsigned type1 type2))
         ((and (3definitely (type-signed-integer-3p type1))
               (3definitely (type-unsigned-integer-3p type2)))
          (type-uaconvert-signed-unsigned type1 type2 ienv))
         ((and (3definitely (type-unsigned-integer-3p type1))
               (3definitely (type-signed-integer-3p type2)))
          (type-uaconvert-signed-unsigned type2 type1 ienv))
         (t (prog2$ (impossible) (irr-type)))))))
  :guard-hints (("Goal"
                 :do-not '(preprocess)
                 :in-theory (e/d (type-some-unknownp
                                  type-arithmetic-3p
                                  type-integer-3p
                                  type-unsigned-integer-3p
                                  type-signed-integer-3p
                                  type-standard-unsigned-integer-3p
                                  type-standard-signed-integer-3p
                                  type-integer-promote
                                  type-integer-promotedp
                                  type-floating-3p
                                  type-real-floating-3p
                                  type-complex-3p)
                                 ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-default-arg-promote ((type typep) (ienv ienvp))
  :returns (new-type typep)
  :short "Perform default argument promotion on a type [C17:6.5.2.2/6]."
  (type-case
   type
   :float (type-double)
   :otherwise (if (3definitely (type-arithmetic-3p type))
                  (type-integer-promote type ienv)
                (type-fix type)))

  ///

  (more-returns
   (new-type type-default-arg-promotedp
             :hints (("Goal" :in-theory (enable type-default-arg-promotedp
                                                type-integer-promote)))))

  (defrule type-count-of-type-default-arg-promote
    (equal (type-count (type-default-arg-promote type ienv))
           (type-count type))
    :enable type-count))

;;;;;;;;;;;;;;;;;;;;

(define type-list-default-arg-promote ((types type-listp) (ienv ienvp))
  :returns (new-types type-listp)
  :short "Perform default argument promotion on each type in a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a map of the @(tsee type-default-arg-promote) function
     over a list."))
  (if (endp types)
      nil
    (cons (type-default-arg-promote (first types) ienv)
          (type-list-default-arg-promote (rest types) ienv)))

  ///

  (defrule len-of-type-list-default-arg-promote
    (equal (len (type-list-default-arg-promote types ienv))
           (len (type-list-fix types)))
    :induct t
    :enable len)

  (defrule type-list-count-of-type-list-default-arg-promote
    (equal (type-list-count (type-list-default-arg-promote types ienv))
           (type-list-count types))
    :induct t
    :enable type-list-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-size-exact ((type typep) (ienv ienvp))
  :returns (size? acl2::maybe-natp)
  :short "Get the exact size of a type in bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "If we do not have sufficient information to calculate the size,
     we return @('nil') instead.")
   (xdoc::p
    "These values largely come directly from the implementation environment.
     The size of the complex floating types is given by [C17:6.2.5/13].")
   (xdoc::p
    "The size of an array type is known when its kind is @(':const-len'),
     its length is known,
     and the size of its element type is known."))
  (b* (((ienv ienv) ienv))
    (type-case
      type
      :void nil
      :char 1
      :schar 1
      :uchar 1
      :sshort ienv.short-bytes
      :ushort ienv.short-bytes
      :sint ienv.int-bytes
      :uint ienv.int-bytes
      :slong ienv.long-bytes
      :ulong ienv.long-bytes
      :sllong ienv.llong-bytes
      :ullong ienv.llong-bytes
      :float ienv.float-bytes
      :double ienv.double-bytes
      :ldouble ienv.ldouble-bytes
      :floatc (* 2 ienv.float-bytes)
      :doublec (* 2 ienv.double-bytes)
      :ldoublec (* 2 ienv.ldouble-bytes)
      :bool ienv.bool-bytes
      :struct nil
      :union nil
      :enum nil
      :array (type-array-kind-case
               type.kind
               :const-len
               (b* ((elem-size (type-size-exact type.of ienv))
                    (array-len
                      (type-array-kind-const-len->len type.kind)))
                 (if (and elem-size array-len)
                     (* elem-size array-len)
                   nil))
               :otherwise nil)
      :pointer ienv.pointer-bytes
      :function nil
      :unknown nil
      :unknown-builtin nil
      :unknown-scalar nil
      :unknown-arithmetic nil))
  :measure (type-count type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines contributes-named-members-p/any-named-members-p
  (define contributes-named-members-p ((member type-struni-member-p))
    :returns (yes/no booleanp)
    :short "Recognizes named members and anonymous structs/unions which
            contribute named members."
    (b* (((type-struni-member member) member)
         ((when member.name?)
          t))
      (type-case
        member.type
        :struct (type-struni-tag/members-case
                  member.type.tag/members
                  :tagged nil
                  :untagged (any-named-members-p member.type.tag/members.members))
        :union (type-struni-tag/members-case
                 member.type.tag/members
                 :tagged nil
                 :untagged (any-named-members-p member.type.tag/members.members))
        :otherwise nil))
    :measure (type-struni-member-count member))

  (define any-named-members-p ((members type-struni-member-listp))
    :returns (yes/no booleanp)
    :short "Check whether any members in the list contribute named members."
    (and (not (endp members))
         (or (contributes-named-members-p (first members))
             (any-named-members-p (rest members))))
    :measure (type-struni-member-list-count members))

  ///
  (fty::deffixequiv-mutual contributes-named-members-p/any-named-members-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define members-filter-contributors ((members type-struni-member-listp))
  :returns (new-members type-struni-member-listp)
  :parents (contributes-named-members-p)
  :short "Filter out members which do not contribute any named members to the
          struct/union."
  (cond ((endp members)
         nil)
        ((contributes-named-members-p (first members))
         (cons (type-struni-member-fix (first members))
               (members-filter-contributors (rest members))))
        (t (members-filter-contributors (rest members)))))

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
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-array-change-kind-at-depth ((type typep)
                                         (depth natp)
                                         (kind type-array-kindp))
  :returns (new-type typep)
  :short "Change the kind of an array at a derived-type depth."
  :long
  (xdoc::topstring-p
   "At each positive depth, this follows the next type along a
    declarator-derived spine: the element type of an array,
    the target type of a pointer, or the return type of a function.
    The type at depth zero must be an array type.")
  (b* ((type (type-fix type))
       (depth (nfix depth))
       (kind (type-array-kind-fix kind))
       ((when (zp depth))
        (type-case type
          :array (change-type-array type :kind kind)
          :otherwise (prog2$ (raise "Internal error: expected array type ~x0."
                                    type)
                             type)))
       (depth (1- depth)))
    (type-case type
      :array
      (change-type-array
       type
       :of (type-array-change-kind-at-depth type.of depth kind))
      :pointer
      (change-type-pointer
       type
       :to (type-array-change-kind-at-depth type.to depth kind))
      :function
      (change-type-function
       type
       :ret (type-array-change-kind-at-depth type.ret depth kind))
      :otherwise
      (prog2$ (raise "Internal error: expected derived type ~x0." type)
              type)))
  :measure (nfix depth)
  :verify-guards nil
  :no-function nil
  :hooks nil
  ///

  (verify-guards type-array-change-kind-at-depth))
