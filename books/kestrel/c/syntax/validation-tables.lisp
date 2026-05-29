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

(include-book "types")
(include-book "macro-tables")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-tables
  :parents (validation)
  :short "Validation tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are symbol tables used by the validator."))
  :order-subtopics t
  :default-parent t)

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
     We use the term `lifetime' because it is just one word,
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
     We also assign a "
    (xdoc::seetopic "uid" "unique identifier")
    ". For enumeration constants names,
     for now we only track that they are enumeration constants.
     For @('typedef') names, we track the type corresponding to its
     definition.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)
            (defstatus valid-defstatus)
            (uid uid)))
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

(fty::deftagsum tag-kind
  :short "Fixtype of the different kinds of tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now, we include cases for just @(':struct') and @(':union').
     We omit @(':enum'), whose tags are not yet being tracked."))
  (:struct ())
  (:union ())
  :pred tag-kindp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-tag-info
  :short "Fixtype of validation information about tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "Tags [C17:6.2.3/1] identify a structure, union, or enumeration type.
     Tags form their own name space,
     disambiguated by the @('struct'), @('union'), or @('enum') keywords.")
   (xdoc::p
    "We store the @(tsee tag-kind)
     and the @(see UID) associated with the tag
     in the current scope.
     The @(see UID) can be used to lookup the completion
     under a separate @(tsee type-completions) map."))
  ((kind tag-kind)
   (uid uid))
  :pred valid-tag-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-tag-info-option
  valid-tag-info
  :short "Fixtype of optional validation information about tags."
  :pred valid-tag-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist valid-tag-scope
  :short "Fixtype of validation scopes of tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "The same tag may refer to different types in different scopes.
     Therefore, we use an alist from identifiers
     to the validation information for tags
     to track the meaning of tags in each scope."))
  :key-type ident
  :val-type valid-tag-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred valid-tag-scopep
  :prepwork ((set-induction-depth-limit 1))
  ///

  (defrule valid-tag-infop-of-cdr-assoc-when-valid-tag-scopep
    (implies (and (valid-tag-scopep scope)
                  (assoc-equal ident scope))
             (valid-tag-infop (cdr (assoc-equal ident scope))))
    :induct t
    :enable (valid-tag-scopep assoc-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-scope
  :short "Fixtype of validation scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     This fixtype contains all the information about a scope,
     which considers the name space of ordinary identifiers
     and the name space of tags."))
  ((ord valid-ord-scope)
   (tag valid-tag-scope))
  :pred valid-scopep
  ///

  (defrule alistp-of-valid-scope->ord
    (alistp (valid-scope->ord x))
    :enable alistp-when-valid-ord-scopep-rewrite)

  (defrule alistp-of-valid-scope->tag
    (alistp (valid-scope->tag x))
    :enable alistp-when-valid-tag-scopep-rewrite))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist valid-scope-list
  :short "Fixtype of lists of validation scopes."
  :elt-type valid-scope
  :true-listp t
  :elementp-of-nil nil
  :pred valid-scope-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-ext-info
  :short "Fixtype of validation information about identifiers with external
          linkage."
  :long
  (xdoc::topstring
   (xdoc::p
    "We store the following information about identifiers
     with external linkage for the purpose of validation
     across unrelated scopes and across different translation units
     (by ``unrelated,'' we mean neither scope is nested within the other).")
   (xdoc::p
    "Each declaration of a given identifier with external linkage
     must agree on the type [C17:6.2.2/2] [C17:6.2.7/2].
     Therefore, we store the type to check type compatibility
     of any declaration after the first.")
   (xdoc::p
    "We also store the set of translation units
     (represented by their @(see filepath)s)
     in which the identifier has been declared.
     This is used to ensure the same identifier has not been declared
     with both internal and external linkage in the same translation unit
     [C17:6.2.2/7].")
   (xdoc::p
    "Finally, we store a "
    (xdoc::seetopic "uid" "unique identifier")
    " for the object.
     All identifiers of the same name with external linkage
     refer to the same object and therefore possess
     the same unique identifier.")
   (xdoc::p
    "Eventually, we may wish to store a boolean flag indicating
     whether the identifier has been externally defined.
     This would be used to ensure
     that externally linked identifiers are defined at most once
     (or exactly once, if the identifier is used in an expression) [C17:6.9/5].
     For now, we conservatively allow any number of definitions."))
  ((type type)
   (declared-in filepath-set)
   (uid uid))
  :pred valid-ext-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-ext-info-option
  valid-ext-info
  :short "Fixtype of optional validation information
          about identifiers with external linkage."
  :pred valid-ext-info-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::defomap valid-externals
  :short "Fixtype of validation information associated with identifiers with
          external linkage."
  :key-type ident
  :val-type valid-ext-info
  :pred valid-externalsp
  ///

  (defrule valid-ext-info-optionp-of-cdr-assoc-when-valid-externalsp
    (implies (valid-externalsp externals)
             (valid-ext-info-optionp (cdr (omap::assoc ident externals))))
    :induct t
    :enable (valid-externalsp omap::assoc valid-ext-info-optionp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-table
  :short "Fixtype of validation tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validation table is a collection of validation information
     for a single translation unit.")
   (xdoc::p
    "The @('filepath') field stores the name of the translation unit.")
   (xdoc::p
    "Scopes are treated in a stack-like manner [C17:6.2.1].
     Thus, a validation table contains a list (i.e. stack) of scopes.
     The stack grows from right to left:
     the leftmost scope is the top, and the rightmost scope is the bottom;
     in other words, in the nesting of scopes in the stack,
     the leftmost scope is the innermost,
     and the rightmost scope is the outermost
     (i.e. the file scope [C17:6.2.1/4].)")
   (xdoc::p
    "The @('macros') field stores the macro table."))
  ((filepath filepath)
   (scopes valid-scope-list)
   (macros macro-table))
  :pred valid-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-valid-table
  :short "An irrelevant validation table."
  :type valid-tablep
  :body (valid-table (irr-filepath) nil (irr-macro-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-table-option
  valid-table
  :short "Fixtype of optional validation tables."
  :pred valid-table-optionp)
