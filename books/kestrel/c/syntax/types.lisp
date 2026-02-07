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
(include-book "formalized")
(include-book "langdef-mapping")
(include-book "uid")
(include-book "file-paths")

(include-book "../language/types")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/omaps/delete" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable hons-equal hons-get hons-acons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions.

(defrulel sfix-when-not-setp-cheap
  (implies (not (setp x))
           (equal (sfix x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable sfix)

(defrulel cardinality-when-emptyp-cheap
  (implies (emptyp x)
           (equal (cardinality x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruledl equal-cardinality-becomes-equal-sfix-when-subset
  (implies (subset x y)
           (equal (equal (cardinality x) (cardinality y))
                  (equal (sfix x) (sfix y))))
  :enable (sfix
           set::equal-cardinality-subset-is-equality))

(defrulel equal-cardinality-when-subset
  (implies (subset x y)
           (equal (equal (cardinality x) (cardinality y))
                  (subset y x)))
  :enable (equal-cardinality-becomes-equal-sfix-when-subset
           set::double-containment))

(defrulel subset-of-delete-when-subset
  (implies (subset set0 set1)
           (subset (delete x set0)
                   set1))
  :enable set::subset-transitive)

(defrulel in-when-subset-of-difference-and-in-not-in
  (implies (and (subset (difference x y) set)
                (in a x)
                (not (in a set)))
           (in a y))
  :enable set::expensive-rules)

(defruledl proper-subset-cardinality-case-split
  (implies (case-split (and (subset x y)
                            (not (subset y x))))
           (< (cardinality x)
              (cardinality y))))

;;;;;;;;;;;;;;;;;;;;

(defrulel equal-of-nfix-and-0
  (equal (equal (nfix x) 0)
         (not (posp x)))
  :enable nfix)

;;;;;;;;;;;;;;;;;;;;

(defrulel hons-assoc-equal-when-assoc-equal
  (implies (alistp alist)
           (equal (hons-assoc-equal x alist)
                  (assoc-equal x alist)))
  :induct t
  :enable (hons-assoc-equal
           alistp))

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
        derived from the ``element type.''
        This is an approximation,
        because we do not track the size of the array type.")
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
        which is always acceptable."))
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
    (:array ((of type)))
    (:pointer ((to type)))
    (:function ((ret type) (params type-params)))
    (:unknown ())
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
    :measure (two-nats-measure (acl2-count x) 0))

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
           :otherwise t))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist type-completions
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
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  :pred type-completions-p
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;

(defrule alistp-when-type-completions-p-forward-chaining
  (implies (type-completions-p x)
           (alistp x))
  :rule-classes :forward-chaining
  :by alistp-when-type-completions-p-rewrite)

(defrule alistp-of-type-completions-fix
  (alistp (type-completions-fix x))
  :induct t
  :enable (type-completions-fix
           alistp))

(defrule type-struni-member-listp-of-cdr-of-assoc-equal
  (implies (type-completions-p completions)
           (type-struni-member-listp (cdr (assoc-equal key completions))))
  :induct t
  :enable assoc-equal)

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
                 (members? (hons-get uid completions)))
              (if members?
                  (mv nil (cdr members?))
                (mv t nil)))
    :untagged (mv nil tag/members.members)))

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

(define type-standard-signed-integerp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type is a standard signed integer type [C17:6.2.5/4]."
  (and (member-eq (type-kind type) '(:schar :sshort :sint :slong :sllong))
       t)

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

  ///

  (defrule type-aggregatep-when-type-kind-syntaxp
    (implies (and (equal (type-kind type) kind)
                  (syntaxp (quotep kind)))
             (equal (type-aggregatep type)
                    (or (type-case type :array)
                        (type-case type :struct))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-integer-promotedp ((type typep))
  :guard (type-arithmeticp type)
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
  :guard (type-arithmeticp type)
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
  :guard (and (type-signed-integerp type1)
              (type-signed-integerp type2)
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
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-integerp))))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-unsigned ((type1 typep) (type2 typep))
  :guard (and (type-unsigned-integerp type1)
              (type-unsigned-integerp type2)
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
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-integerp))))

;;;;;;;;;;;;;;;;;;;;

(define type-uaconvert-signed-unsigned ((type1 typep)
                                        (type2 typep)
                                        (ienv ienvp))
  :guard (and (type-signed-integerp type1)
              (type-unsigned-integerp type2)
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
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-integerp
                                           type-integer-promotedp
                                           type-unsigned-integerp
                                           type-signed-integerp
                                           type-standard-unsigned-integerp
                                           type-standard-signed-integerp))))

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
   (t (b* ((type1 (type-integer-promote type1 ienv))
           (type2 (type-integer-promote type2 ienv)))
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
                                  type-integer-promote
                                  type-integer-promotedp
                                  type-floatingp
                                  type-real-floatingp
                                  type-complexp)
                                 ((:e tau-system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-default-arg-promote ((type typep) (ienv ienvp))
  :returns (new-type typep)
  :short "Perform default argument promotion on a type [C17:6.5.2.2/6]."
  (type-case
   type
   :float (type-double)
   :otherwise (if (type-arithmeticp type)
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

(defines type/type-list-compatible-p-aux
  (define type-compatible-p-aux ((x typep)
                                 (y typep)
                                 (completions type-completions-p)
                                 (incomplete uid-setp)
                                 (ienv ienvp))
    :returns (yes/no booleanp)
    :short "Auxiliary function for check that two @(see type)s are compatible
            [C17:6.2.7]."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee type-compatible-p) for a description
       of what type compatibility means and how we check it."))
    (or (type-case y :unknown)
        (type-case
          x
          :unknown t
          :struct
          (type-case
            y
            :struct
            (if (and x.tunit? y.tunit? (equal x.tunit? y.tunit?))
                (if (c::version-std-c23p (ienv->version ienv))
                    (type-struni-tag/members-case
                      x.tag/members
                      :tagged
                      (type-struni-tag/members-case
                        y.tag/members
                        :tagged
                        (b* ((completions (type-completions-fix completions))
                             (incomplete (uid-set-fix incomplete))
                             ((when (or (in x.uid incomplete)
                                        (in y.uid incomplete)))
                              t)
                             (x-members? (hons-get x.uid completions))
                             (y-members? (hons-get y.uid completions))
                             ((unless (and (consp x-members?)
                                           (consp y-members?)))
                              t)
                             (incomplete
                               (insert x.uid (insert y.uid incomplete))))
                          (type-struni-member-list-compatible-p-aux
                            (cdr x-members?)
                            (cdr y-members?)
                            completions
                            incomplete
                            ienv))
                        :untagged nil)
                      :untagged (type-struni-tag/members-case
                                  y.tag/members
                                  :tagged nil
                                  :untagged (uid-equal x.uid y.uid)))
                  (uid-equal x.uid y.uid))
              (type-struni-tag/members-case
                x.tag/members
                :tagged
                (type-struni-tag/members-case
                  y.tag/members
                  :tagged
                  (b* ((completions (type-completions-fix completions))
                       (incomplete (uid-set-fix incomplete))
                       ((when (or (in x.uid incomplete)
                                  (in y.uid incomplete)))
                        t)
                       (x-members? (hons-get x.uid completions))
                       (y-members? (hons-get y.uid completions))
                       ((unless (and (consp x-members?)
                                     (consp y-members?)))
                        t)
                       (incomplete (insert x.uid (insert y.uid incomplete))))
                    (type-struni-member-list-compatible-p-aux
                      (cdr x-members?)
                      (cdr y-members?)
                      completions
                      incomplete
                      ienv))
                  :untagged nil)
                :untagged
                (type-struni-tag/members-case
                  y.tag/members
                  :tagged nil
                  :untagged (type-struni-member-list-compatible-p-aux
                              x.tag/members.members
                              y.tag/members.members
                              completions
                              incomplete
                              ienv))))
            :otherwise nil)
          :union
          (type-case
            y
            :union
            (if (and x.tunit? y.tunit? (equal x.tunit? y.tunit?))
                (if (c::version-std-c23p (ienv->version ienv))
                    (type-struni-tag/members-case
                      x.tag/members
                      :tagged (type-struni-tag/members-case
                                y.tag/members
                                :tagged t
                                :untagged nil)
                      :untagged (type-struni-tag/members-case
                                  y.tag/members
                                  :tagged nil
                                  :untagged (uid-equal x.uid y.uid)))
                  (uid-equal x.uid y.uid))
              (type-struni-tag/members-case
                x.tag/members
                :tagged (type-struni-tag/members-case
                          y.tag/members
                          :tagged t
                          :untagged nil)
                :untagged (type-struni-tag/members-case
                            y.tag/members
                            :tagged nil
                            :untagged t)))
            :otherwise nil)
          :array (type-case
                   y
                   :array (type-compatible-p-aux
                            x.of y.of completions incomplete ienv)
                   :otherwise nil)
          :pointer (type-case
                     y
                     :pointer (type-compatible-p-aux
                                x.to y.to completions incomplete ienv)
                     :otherwise nil)
          :function
          (type-case
            y
            :function
            (and (type-compatible-p-aux
                   x.ret y.ret completions incomplete ienv)
                 (type-params-compatible-p-aux
                   x.params y.params completions incomplete ienv))
            :otherwise nil)
          :otherwise (or (equal (type-fix x) (type-fix y))
                         (and (type-integerp x) (type-case y :enum))
                         (and (type-case x :enum) (type-integerp y)))))
    :measure (two-nats-measure
              (cardinality
                (difference
                  (mergesort (strip-cars (type-completions-fix completions)))
                  (uid-set-fix incomplete)))
              (max (type-count x) (type-count y))))

  (define type-struni-member-list-compatible-p-aux
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (completions type-completions-p)
     (incomplete uid-setp)
     (ienv ienvp))
    :returns (yes/no booleanp)
    :short "Check that a list of struct/union members are compatible
            [C17:6.2.7]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This implements the ``correspondence'' check
       described in @(tsee type-compatible-p-aux)."))
    (b* (((when (endp x))
          (endp y))
         ((when (endp y))
          nil)
         ((type-struni-member member-x) (first x))
         ((type-struni-member member-y) (first y)))
      (and (equal member-x.name? member-y.name?)
           (type-compatible-p-aux
             member-x.type member-y.type completions incomplete ienv)
           (type-struni-member-list-compatible-p-aux
             (rest x) (rest y) completions incomplete ienv)))
    :measure (two-nats-measure
              (cardinality
                (difference
                  (mergesort (strip-cars (type-completions-fix completions)))
                  (uid-set-fix incomplete)))
              (max (type-struni-member-list-count x)
                   (type-struni-member-list-count y))))

  (define type-params-compatible-p-aux ((x type-params-p)
                                        (y type-params-p)
                                        (completions type-completions-p)
                                        (incomplete uid-setp)
                                        (ienv ienvp))
    :returns (yes/no booleanp)
    :short "Check that the parameter portions of two function @(see type)s are
            compatible [C17:6.2.7]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the second part of the compatibility check on function types.
       In addition to the earlier check
       that the return types must be compatible,
       the following conditions must also hold."
      (xdoc::ol
       (xdoc::li
        "When both function types correspond to function prototypes,
         both must have the same number of parameters
         and each parameter must have compatible type.
         Furthermore, both must agree on the ellipsis terminator.")
       (xdoc::li
        "When one type corresponds to a function prototype
         and the other is part of an ``old-style'' function definition,
         each type in the parameter type list of the prototype
         must be compatible with the corresponding of the old-style function
         after the latter has gone through default argument promotion.
         Furthermore, the prototype must not feature an ellipsis terminator.")
       (xdoc::li
        "When one type corresponds to a function prototype
         and the other has an empty identifier list
         and is not derived from a function definition,
         the type of each parameter in the function prototype
         must be compatible with itself after default argument promotion.
         Furthermore, the prototype must not feature
         an ellipsis terminator."))
      "Note that no checks are required
       when neither function type includes a function prototype;
       it is sufficient that the two function types
       have the compatible return types.")
     (xdoc::p
      "In the above mention of parameter types,
       we mean the type after adjustment [C17:6.7.6.3/7-8].
       This requires no special consideration here,
       since we always represent function types post-adjustment
       (see @(see type))."))
    (type-params-case
      x
      :prototype
      (type-params-case
        y
        :prototype (and (type-list-compatible-p-aux
                          x.params y.params completions incomplete ienv)
                        (equal x.ellipsis y.ellipsis))
        :old-style (and (not x.ellipsis)
                        (type-list-compatible-p-aux
                          x.params
                          (type-list-default-arg-promote y.params ienv)
                          completions
                          incomplete
                          ienv))
        :unspecified (and (not x.ellipsis)
                          (type-list-compatible-p-aux
                            x.params
                            (type-list-default-arg-promote x.params ienv)
                            completions
                            incomplete
                            ienv)))
      :old-style
      (type-params-case
        y
        :prototype (and (not y.ellipsis)
                        (type-list-compatible-p-aux
                          (type-list-default-arg-promote x.params ienv)
                          y.params
                          completions
                          incomplete
                          ienv))
        :otherwise t)
      :unspecified
      (type-params-case
        y
        :prototype (and (not y.ellipsis)
                        (type-list-compatible-p-aux
                          y.params
                          (type-list-default-arg-promote y.params ienv)
                          completions
                          incomplete
                          ienv))
        :otherwise t))
    :measure (two-nats-measure
              (cardinality
                (difference
                  (mergesort (strip-cars (type-completions-fix completions)))
                  (uid-set-fix incomplete)))
              (max (type-params-count x)
                   (type-params-count y))))

  (define type-list-compatible-p-aux ((x type-listp)
                                      (y type-listp)
                                      (completions type-completions-p)
                                      (incomplete uid-setp)
                                      (ienv ienvp))
    :returns (yes/no booleanp)
    :short "Check that two @(see type-list)s are compatible [C17:6.2.7]."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each corresponding pair of elements from the two lists
       must be compatible.
       The lists must have the same length."))
    (if (endp x)
        (endp y)
      (and (not (endp y))
           (type-compatible-p-aux
             (first x) (first y) completions incomplete ienv)
           (type-list-compatible-p-aux
             (rest x) (rest y) completions incomplete ienv)))
    :measure (two-nats-measure
              (cardinality
                (difference
                  (mergesort (strip-cars (type-completions-fix completions)))
                  (uid-set-fix incomplete)))
              (max (type-list-count x)
                   (type-list-count y))))

  :hints (("Goal" :in-theory (e/d (max
                                   acl2::member-equal-of-strip-cars-iff
                                   proper-subset-cardinality-case-split)
                                  (set::expand-cardinality-of-difference
                                   set::delete-cardinality
                                   set::proper-subset-cardinality))))
  ///

  (fty::deffixequiv-mutual type/type-list-compatible-p-aux)

  (encapsulate ()
    (local
      (defthm-type/type-list-compatible-p-aux-flag
        (defthm type-compatible-p-aux-reflexive-lemma
          (implies (equal x y)
                   (type-compatible-p-aux x y completions incomplete ienv))
          :flag type-compatible-p-aux)
        (defthm type-struni-member-list-compatible-p-aux-reflexive-lemma
          (implies (equal x y)
                   (type-struni-member-list-compatible-p-aux
                     x y completions incomplete ienv))
          :flag type-struni-member-list-compatible-p-aux)
        (defthm type-params-compatible-p-aux-reflexive-lemma
          (implies (equal x y)
                   (type-params-compatible-p-aux
                     x y completions incomplete ienv))
          :flag type-params-compatible-p-aux)
        (defthm type-list-compatible-p-aux-reflexive-lemma
          (implies (equal x y)
                   (type-list-compatible-p-aux
                     x y completions incomplete ienv))
          :flag type-list-compatible-p-aux)))

    (defrule type-compatible-p-aux-reflexive
      (type-compatible-p-aux x x completions incomplete ienv))

    (defrule type-struni-member-list-compatible-p-aux-reflexive
      (type-struni-member-list-compatible-p-aux
        x x completions incomplete ienv))

    (defrule type-params-compatible-p-aux-reflexive
      (type-params-compatible-p-aux x x completions incomplete ienv))

    (defrule type-list-compatible-p-aux-reflexive
      (type-list-compatible-p-aux x x completions incomplete ienv)))

  (defthm-type/type-list-compatible-p-aux-flag
    (defthm type-compatible-p-aux-symmetric
      (equal (type-compatible-p-aux y x completions incomplete ienv)
             (type-compatible-p-aux x y completions incomplete ienv))
      :flag type-compatible-p-aux
      :hints ('(:expand (type-compatible-p-aux y x completions incomplete ienv))))
    (defthm type-struni-member-list-compatible-p-aux-symmetric
      (equal (type-struni-member-list-compatible-p-aux
               y x completions incomplete ienv)
             (type-struni-member-list-compatible-p-aux
               x y completions incomplete ienv))
      :flag type-struni-member-list-compatible-p-aux)
    (defthm type-params-compatible-p-aux-symmetric
      (equal (type-params-compatible-p-aux y x completions incomplete ienv)
             (type-params-compatible-p-aux x y completions incomplete ienv))
      :flag type-params-compatible-p-aux)
    (defthm type-list-compatible-p-aux-symmetric
      (equal (type-list-compatible-p-aux y x completions incomplete ienv)
             (type-list-compatible-p-aux x y completions incomplete ienv))
      :flag type-list-compatible-p-aux)))

(defruled len-when-type-list-compatible-p-aux
  (implies (type-list-compatible-p-aux x y completions incomplete ienv)
           (equal (len y)
                  (len x)))
  :induct (acl2::cdr-cdr-induct x y)
  :enable (type-list-compatible-p-aux
           len))

(defruled consp-when-type-list-compatible-p-aux
  (implies (type-list-compatible-p-aux x y completions incomplete ienv)
           (equal (consp y)
                  (consp x)))
  :expand (type-list-compatible-p-aux x y completions incomplete ienv))

;;;;;;;;;;;;;;;;;;;;

(define type-compatible-p ((x typep)
                           (y typep)
                           (completions type-completions-p)
                           (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check that two @(see type)s are compatible [C17:6.2.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type compatibility is a check that two types are
     in some sense ``consistent''.
     Compatibility affects whether a redeclaration is permissible,
     whether one type may be used when another is expected,
     and whether two declarations referring to
     the same object or function are well-defined.")
   (xdoc::p
    "Because we currently only model an approximation of C types,
     our notion of compatibility is also approximate.
     Specifically, this relation overapproximates true type compatibility.
     Compatible types should always be recognized as such,
     but incompatible types may also be recognized.")
   (xdoc::p
    "Furthermore, we deliberately weaken our notion of compatibility
     when comparing certain types across translation units.
     Specifically, the compatibility rules for @('struct') types
     require knowing whether a type is completed <i>anywhere</i>
     in a translation unit [C17:6.2.7/1].
     To avoid having to delay our compatibility checks,
     we weaken our definition to instead only require that two types
     <i>might</i> be compatible under a future extension
     of the current completions environment.
     This is consistent with our aforementioned goal
     of overapproximating true type compatibility.")
   (xdoc::p
    "Our approximate notion of type compatibility
     is established by the following cases:")
   (xdoc::ul
    (xdoc::li
     "If either type is unknown, the types are compatible.")
    (xdoc::li
     "Structure type compatibility depends on
      whether they are declared in the same translation unit.
      If they are, the only requirement is
      that the UIDs and tags are the same.
      The UID establishes that the structs correspond to
      the same declaration in the same scope [C17:6.7.2.3/4-5].
      Note that it is expected that two struct types
      produced by the validator should always have the same tag
      when they share a UID.
      If the struct types are declared in different translation units,
      the restrictions are weaker.
      We check that the tags are the same and,
      if both types are complete
      with respect to the type completion environment,
      then there is a one-to-one correspondence between struct members.
      For a member of one struct to correspond with a member of the other,
      the names must agree and their types must be compatible.
      We do not yet check member alignment specifiers agree.
      Furthermore, the members of one struct type
      must appear in the same order as
      the corresponding members of the other struct [C17:6.2.7/1].
      Note that, for the purpose compatibility, anonymous structs/unions
      are considered regular members of their containing type.
      (This is not so explicit in C17, but is clarified in [C23:6.2.7/1].)")
    (xdoc::li
     "Union type compatibility mirrors struct compatibility,
      with the exception that
      corresponding members do not need to appear in the same order
      when comparing unions across translation units [C17:6.2.7/1].
      For now, we do not check union members
      when comparing across translation unit,
      and instead conservatively accept any two unions with the same tag.")
    (xdoc::li
     "Due to their approximate representations,
      all enumeration types are considered compatible [C17:6.7.2.2/4].")
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
     "Function types are considered compatible if
      their return types are compatible [C17:6.7.6.3/15]
      and their @(tsee type-params) are compatible
      (see @(tsee type-params-compatible-p-aux)).")
    (xdoc::li
     "For any other case, the types are compatible only if they are equal."))
   (xdoc::p
    "Eventually, we shall refine the notion of compatibility,
     alongside our representation of types,
     in order to reflect true type compatibility.")
   (xdoc::p
    "Finally, we note the perhaps surprising fact that
     type compatibility is intransitive and therefore
     not an equivalence relation.
     For instance, consider the following functions.")
   (xdoc::codeblock
    "int foo();"
    ""
    "int bar(int x);"
    ""
    "int baz(double x);")
   (xdoc::p
    "In this example, the types of @('bar') and @('baz')
     are both compatible with the type of @('foo').
     However, the types of @('bar') and @('baz')
     are not compatible with each other.")
   (xdoc::section
    "C23 Standard"
    (xdoc::p
     "The C23 standard makes various changes to type compatibility,
      of which we only implement some subset.
      When the implementation environment specifies the C23 standard,
      we make the following changes to the C17 type compatibility
      outlined above.")
   (xdoc::ul
    (xdoc::li
     "Two struct types are compared as if
      they were declared in separate translation units [C23:6.2.7/1].")
    (xdoc::li
     "Two union types are compared as if
      they were declared in separate translation units [C23:6.2.7/1]."))))
  (type-compatible-p-aux x y completions nil ienv))

(defrule type-compatible-p-reflexive
  (type-compatible-p x x completions ienv)
  :enable type-compatible-p)

(defrule type-compatible-p-symmetric
  (equal (type-compatible-p y x completions ienv)
         (type-compatible-p x y completions ienv))
  :enable type-compatible-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-composite-aux
  (define type-composite-aux ((x typep)
                              (y typep)
                              (composites uid-uid-mapp)
                              (completions type-completions-p)
                              (next-uid uidp)
                              (ienv ienvp)
                              (count natp))
    :returns (mv (composite typep)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Auxiliary function for constructing a composite @(see type)
            [C17:6.2.7/3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee type-composite) for a description type composites.")
     (xdoc::p
      "The termination argument for this clique is nontrivial.
       A sufficient measure would be the size of the @('completions') map,
       with the @(see UID)s from the @('composites') map removed,
       and restricted to @(see UID)s below @('next-uid').
       For the moment, we simply add a @('count') argument."))
    (if (= (the unsigned-byte (lnfix count)) 0)
        (mv (type-fix x)
            (type-completions-fix completions)
            (uid-fix next-uid))
      (type-case
        x
        :struct
        (type-case
          y
          :struct
          (if (uid-equal x.uid y.uid)
              (mv (type-fix x)
                  (type-completions-fix completions)
                  (uid-fix next-uid))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* ((composites (uid-uid-mfix composites))
                     (completions (type-completions-fix completions))
                     (x-composite? (omap::assoc x.uid composites))
                     (y-composite? (omap::assoc y.uid composites))
                     ((when (and (consp x-composite?)
                                 (consp y-composite?)
                                 (equal (cdr x-composite?) (cdr y-composite?))))
                      (mv (make-type-struct
                            :uid (cdr x-composite?)
                            :tunit? nil
                            :tag/members x.tag/members)
                          completions
                          (uid-fix next-uid)))
                     (x-members? (hons-get x.uid completions))
                     (y-members? (hons-get y.uid completions))
                     ((unless (consp x-members?))
                      (mv (type-fix y)
                          completions
                          (uid-fix next-uid)))
                     ((unless (consp y-members?))
                      (mv (type-fix x)
                          completions
                          (uid-fix next-uid)))
                     (composite-uid (uid-fix next-uid))
                     (next-uid (uid-increment next-uid))
                     (composites
                       (omap::update x.uid
                                     composite-uid
                                     (omap::update y.uid
                                                   composite-uid
                                                   composites)))
                     ((mv members-composite completions next-uid)
                      (type-struni-member-list-composite-aux
                        (cdr x-members?)
                        (cdr y-members?)
                        composites
                        completions
                        next-uid
                        ienv
                        (- (the unsigned-byte count) 1)))
                     (completions (hons-acons composite-uid
                                              members-composite
                                              completions)))
                  (mv (make-type-struct
                        :uid composite-uid
                        :tunit? nil
                        :tag/members x.tag/members)
                      completions
                      next-uid))
                :untagged
                (mv (type-fix x)
                    (type-completions-fix completions)
                    (uid-fix next-uid)))
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (mv (type-fix x)
                    (type-completions-fix completions)
                    (uid-fix next-uid))
                :untagged
                (b* ((composite-uid next-uid)
                     (next-uid (uid-increment next-uid))
                     ((mv members-composite completions next-uid)
                      (type-struni-member-list-composite-aux
                        x.tag/members.members
                        y.tag/members.members
                        composites
                        completions
                        next-uid
                        ienv
                        (- (the unsigned-byte count) 1))))
                  (mv (make-type-struct
                        :uid composite-uid
                        :tunit? nil
                        :tag/members (type-struni-tag/members-untagged
                                       members-composite))
                      completions
                      next-uid)))))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :union (mv (type-fix x)
                   (type-completions-fix completions)
                   (uid-fix next-uid))
        :array
        (type-case
          y
          :array (b* (((mv of-type completions next-uid)
                       (type-composite-aux x.of
                                           y.of
                                           composites
                                           completions
                                           next-uid
                                           ienv
                                           (- (the unsigned-byte count) 1))))
                   (mv (make-type-array :of of-type)
                       completions
                       next-uid))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :pointer
        (type-case
          y
          :pointer (b* (((mv to-type completions next-uid)
                         (type-composite-aux x.to
                                             y.to
                                             composites
                                             completions
                                             next-uid
                                             ienv
                                             (- (the unsigned-byte count) 1))))
                     (mv (make-type-pointer :to to-type)
                         completions
                         next-uid))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :function
        (type-case
          y
          :function
          (b* (((mv ret-type completions next-uid)
                (type-composite-aux x.ret
                                    y.ret
                                    composites
                                    completions
                                    next-uid
                                    ienv
                                    (- (the unsigned-byte count) 1)))
               ((mv params completions next-uid)
                (type-params-composite-aux x.params
                                           y.params
                                           composites
                                           completions
                                           next-uid
                                           ienv
                                           (- (the unsigned-byte count) 1))))
            (mv (make-type-function :ret ret-type :params params)
                completions
                next-uid))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :unknown (mv (type-fix y)
                     (type-completions-fix completions)
                     (uid-fix next-uid))
        :otherwise (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))))
    :measure (nfix count))

    (define type-struni-member-list-composite-aux
      ((x type-struni-member-listp)
       (y type-struni-member-listp)
       (composites uid-uid-mapp)
       (completions type-completions-p)
       (next-uid uidp)
       (ienv ienvp)
       (count natp))
    :returns (mv (composite type-struni-member-listp)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Construct a composite @(tsee type-struni-member-list)."
    (b* (((when (or (endp x) (endp y) (= (the unsigned-byte (lnfix count)) 0)))
          (mv nil (type-completions-fix completions) (uid-fix next-uid)))
         ((mv first-type completions next-uid)
          (type-composite-aux (type-struni-member->type (first x))
                              (type-struni-member->type (first y))
                              composites
                              completions
                              next-uid
                              ienv
                              (- (the unsigned-byte count) 1)))
         (first-member (change-type-struni-member
                         (first x)
                         :type first-type))
         ((mv rest-members completions next-uid)
          (type-struni-member-list-composite-aux
            (rest x)
            (rest y)
            composites
            completions
            next-uid
            ienv
            (- (the unsigned-byte count) 1))))
      (mv (cons first-member rest-members)
          completions
          next-uid))
    :measure (nfix count))

  (define type-params-composite-aux ((x type-params-p)
                                     (y type-params-p)
                                     (composites uid-uid-mapp)
                                     (completions type-completions-p)
                                     (next-uid uidp)
                                     (ienv ienvp)
                                     (count natp))
    :returns (mv (composite type-params-p)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Construct a composite of the @(tsee type-params) portion of a
            function @(see type)."
    :long
    (xdoc::topstring
     (xdoc::p
      "If both function types are prototypes,
       the result is a prototype whose parameter lists consists of
       the composite type of each parameter [C17:6.2.7/3].")
     (xdoc::p
      "If one function type is a prototype and the other is not,
       the composite is a prototype with the prototype function type's
       parameter types [C17:6.2.7/3].")
     (xdoc::p
      "If neither function type is a prototype,
       the composite is unconstrained except by the general restriction
       that it is compatible with both function types.
       In this case,
       we arbitrarily choose the function type with more information
       (i.e. an old-style function type)."))
    (if (= (the unsigned-byte (lnfix count)) 0)
        (mv (type-params-fix x)
            (type-completions-fix completions)
            (uid-fix next-uid))
      (type-params-case
        x
        :prototype
        (type-params-case
          y
          :prototype
          (b* (((mv param-types completions next-uid)
                (type-list-composite-aux x.params
                                         y.params
                                         composites
                                         completions
                                         next-uid
                                         ienv
                                         (- (the unsigned-byte count) 1))))
            (mv (make-type-params-prototype
                  :params param-types
                  :ellipsis x.ellipsis)
                completions
                next-uid))
          :otherwise (mv (type-params-fix x)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :old-style (mv (type-params-case
                         y
                         :prototype (type-params-fix y)
                         ;; TODO: we could consider creating a better composite when
                         ;; both are :old-style which could resolve some unknowns.
                         :otherwise (type-params-fix x))
                       (type-completions-fix completions)
                       (uid-fix next-uid))
        :unspecified (mv (type-params-fix y)
                         (type-completions-fix completions)
                         (uid-fix next-uid))))
    :measure (nfix count))

  (define type-list-composite-aux ((x type-listp)
                                   (y type-listp)
                                   (composites uid-uid-mapp)
                                   (completions type-completions-p)
                                   (next-uid uidp)
                                   (ienv ienvp)
                                   (count natp))
    :returns (mv (composite type-listp)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Construct a composite @(tsee type-list)."
    (b* (((when (or (endp x) (endp y) (= (the unsigned-byte (lnfix count)) 0)))
          (mv nil (type-completions-fix completions) (uid-fix next-uid)))
         ((mv first-type completions next-uid)
          (type-composite-aux (first x)
                              (first y)
                              composites
                              completions
                              next-uid
                              ienv
                              (- (the unsigned-byte count) 1)))
         ((mv rest-types completions next-uid)
          (type-list-composite-aux (rest x)
                                   (rest y)
                                   composites
                                   completions
                                   next-uid
                                   ienv
                                   (- (the unsigned-byte count) 1))))
      (mv (cons first-type rest-types)
          completions
          next-uid))
    :measure (nfix count))

  :verify-guards :after-returns
  :hints (("Goal" :in-theory (enable the-check)))
  ///

  (fty::deffixequiv-mutual type/type-list-composite-aux))

;;;;;;;;;;;;;;;;;;;;

(define type-composite ((x typep)
                        (y typep)
                        (completions type-completions-p)
                        (next-uid uidp)
                        (ienv ienvp))
  :returns (mv (composite typep)
               (new-completions type-completions-p)
               (new-next-uid uidp))
  :short "Construct a composite @(see type) [C17:6.2.7/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our approximate type system,
     a composite type is a type that is compatible with both input types.
     For function types, further constraints apply.
     See @(tsee type-params-composite-aux).")
   (xdoc::p
    "When taking the composite of the unknown type with any other type,
     we take the other type as the composite.
     Our choice to take the more specific of the two compatible types
     is consistent with the general pattern
     of constraints outlined by the standard
     (e.g., when taking the composite of two arrays,
     one with a length, and the other without,
     the composite as an array with the specified length [C17:6.2.7/2])."))
  (type-composite-aux x
                      y
                      nil
                      completions
                      next-uid
                      ienv
                      (the (unsigned-byte 60) (1- (expt 2 60)))))

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
     The size of the complex floating types is given by [C17:6.2.5/13]."))
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
      :array nil
      :pointer ienv.pointer-bytes
      :function nil
      :unknown nil)))

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
           (let ((tag/members (type-struct->tag/members type)))
             (type-struni-tag/members-case
               tag/members
               :tagged (ident-formalp tag/members.tag)
               :untagged nil))))
  :measure (type-count type))

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
                    :none t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-set-formalp ((types type-setp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a set
          are supported in our formal semantics of C."
  (or (set::emptyp (type-set-fix types))
      (and (type-formalp (set::head types))
           (type-set-formalp (set::tail types))))
  :prepwork ((local (in-theory (enable emptyp-of-type-set-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-option-set-formalp ((type?s type-option-setp))
  :returns (yes/no booleanp)
  :short "Check if all the optional types in a set
          are supported in our formal semantics of C."
  (or (set::emptyp (type-option-set-fix type?s))
      (and (type-option-formalp (set::head type?s))
           (type-option-set-formalp (set::tail type?s))))
  :prepwork ((local (in-theory (enable emptyp-of-type-option-set-fix)))))

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
     :struct (let ((tag/members (type-struct->tag/members type)))
               (type-struni-tag/members-case
                 tag/members
                 :tagged (b* (((erp tag) (ldm-ident tag/members.tag)))
                           (retok (c::type-struct tag)))
                 :untagged (reterr (msg "Type ~x0 not supported."
                                        (type-fix type)))))
     :union (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :enum (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :array (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :pointer (b* (((erp refd-type) (ldm-type type.to)))
                (retok (c::make-type-pointer :to refd-type)))
     :function (reterr (msg "Type ~x0 not supported." (type-fix type)))
     :unknown (reterr (msg "Type ~x0 not supported." (type-fix type)))))
  :measure (type-count type)
  :verify-guards :after-returns

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
  :no-function nil)

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
   ;; TODO: we can't really create a struct, unless we wanted to invent a UID
   ;; and tunit. Then, we could perhaps create an incomplete struct type.
   :struct (irr-type)
   :pointer (make-type-pointer :to (ildm-type ctype.to))
   :array (make-type-array :of (ildm-type ctype.of)))
  :measure (c::type-count ctype)
  :verify-guards :after-returns)
