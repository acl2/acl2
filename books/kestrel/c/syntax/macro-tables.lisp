; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-lexemes")

(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ macro-tables
  :parents (preprocessor)
  :short "Tables of macro definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce data structures to keep track of
     the active macro definitions during preprocessing.
     We introduce operations to manipulate these data structures."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum macro-info
  :short "Fixtype of information about a macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not include the name, which we represent separately.")
   (xdoc::p
    "Aside from the name, an object-like macro [C17:6.10.3/9]
     consists of its replacement list,
     which is a sequence of zero or more preprocessing tokens.
     To facilitate comparisons with multiple definitions of the same macro
     [C17:6.10.3/1] [C17:6.10.3/2],
     we also keep track of white space separating tokens,
     in the form of a single space between two tokens.
     The invariant @(tsee plexeme-list-token/space-p) captures
     the fact that we only have tokens and single spaces,
     but does not capture the fact that the single spaces
     only occur between two tokens,
     which should be also an invariant.
     The list of lexemes that forms the replacement list
     excludes the (mandatory [C17:6.10.3/3]) white space
     (and comments, which we keep but must treat as white space)
     between the name and the replacement list,
     as well as the white space (and comments) after the replacement list,
     excluding the closing new line as well
     [C17:6.10.3/7].")
   (xdoc::p
    "For a function-like macro [C17:6.10.3/10],
     besides the replacement list,
     which we model as for object-like macros (see above),
     we have zero or more parameters, which are identifiers,
     an optional ellipsis parameter,
     whose presence or absence we model as a boolean,
     and a subset of the parameters that are, in the replacement list,
     either preceded by @('#') or @('##') or followed by @('##').
     This subset is modeled as a list, but treated as a set.
     If the parameters include an ellipsis,
     we need to count it as the @('__VA_ARGS__') identifier."))
  (:object ((replist plexeme-list
                     :reqfix (if (plexeme-list-token/space-p replist)
                                 replist
                               nil)))
   :require (plexeme-list-token/space-p replist))
  (:function ((params ident-list)
              (ellipsis bool)
              (replist plexeme-list
                       :reqfix (if (plexeme-list-token/space-p replist)
                                   replist
                                 nil))
              (hash-params ident-list
                           :reqfix (if (subsetp-equal
                                        hash-params
                                        (if ellipsis
                                            (cons (ident "__VA_ARGS__") params)
                                          params))
                                       hash-params
                                     nil)))
   :require (and (plexeme-list-token/space-p replist)
                 (subsetp-equal hash-params
                                (if ellipsis
                                    (cons (ident "__VA_ARGS__") params)
                                  params))))
  :pred macro-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption macro-info-option
  macro-info
  :short "Fixtype of optional information about a macro."
  :pred macro-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist macro-scope
  :short "Fixtype of macro scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A file may define some macros, and then include another file.
     When preprocessing the included file,
     which may define its own macros,
     the macros defined in the including file are also in scope.
     If the included file includes a further file,
     the latter sees the macros of
     the two (directly and indirectly) including files.
     This leads to a natural stack-like structure
     for keeping track of the macros in scope,
     where each scope corresponds to a file.
     [C17] does not have a notion of macro scopes,
     but our preprocessor uses this notion to determine
     when included files are @(see self-contained),
     in the precise sense that we define elsewhere.")
   (xdoc::p
    "The values of this fixtype represent a macro scope.
     The keys represent the names of the macros,
     with the values representing the associated information.
     The names are identifiers [C17:6.10.3/9] [C17:6.10.3/10],
     and should be unique according to [C17:6.10.3/2],
     but in practice GCC allows redefinition within a file,
     with the last definition overriding the previous one.
     So we do not necessarily enforce the uniqueness of keys;
     note that, by adding new associations with @(tsee acons)
     and by looking up associations with @(tsee assoc-equal),
     we automatically match GCC's behavior."))
  :key-type ident
  :val-type macro-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred macro-scopep
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled macro-infop-of-cdr-of-assoc-equal-when-macro-scopep
    (implies (and (macro-scopep scope)
                  (assoc-equal name scope))
             (macro-infop (cdr (assoc-equal name scope))))
    :induct t
    :enable macro-scopep))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist macro-scope-list
  :short "Fixtype of lists of macro scopes."
  :elt-type macro-scope
  :true-listp t
  :elementp-of-nil t
  :pred macro-scope-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod macro-table
  :short "Fixtype of macro tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee macro-scope),
     we organize macros in a stack of scopes,
     i.e. a list of scopes corresponding to the files being preprocessed,
     the @(tsee car) being the innermost scope,
     and the list being empty only before any file is being preprocessed.
     We also have a separate scope of predefined macros [C17:6.10.8].")
   (xdoc::p
    "Just like we do not necessarily enforce
     the uniqueness of keys in each scope (see @(tsee macro-scope)),
     we also do not necessarily enforce the disjointness of
     the scopes in a macro table, including the predefined one.
     GCC allows redefinition of predefined macros,
     with the redefinition overriding the predefinition.")
   (xdoc::p
    "We do not actually support the predefined macros yet,
     but we already have a placeholder in the macro table.
     It is not yet clear whether the best way to represent them
     is as a macro scope,
     given that some of them have dynamic definitions
     (e.g. @('__LINE__') [C17:6.10.8.1/1]).
     We may revise this part of the data structure
     when we actually add support for predefined macros."))
  ((predefined macro-scope)
   (scopes macro-scope-list))
  :pred macro-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-macro-table
  :short "An irrelevant macro table."
  :type macro-tablep
  :body (macro-table nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-lookup ((name identp) (table macro-tablep))
  :returns
  (mv (info? macro-info-optionp)
      (innermostp booleanp)
      (predefinedp booleanp))
  :short "Look up a macro in a macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We search from innermost to outermost scope,
     and then the predefined scope if needed.
     This lookup order matches GCC's behavior,
     notes in @(tsee macro-scope) and @(tsee macro-table).")
   (xdoc::p
    "We also return two flags saying whether the macro was found
     in the innermost scope or in the predefined scope.
     At most one such flag can be @('t').
     They are both @('nil') if the macro is not found."))
  (b* (((mv info? innermostp)
        (macro-lookup-in-scopes name t (macro-table->scopes table)))
       ((when info?) (mv info? innermostp nil))
       (name+info
        (assoc-equal (ident-fix name) (macro-table->predefined table)))
       ((when name+info) (mv (cdr name+info) nil t)))
    (mv nil nil nil))

  :prepwork
  ((local (in-theory (enable macro-info-optionp
                             macro-infop-of-cdr-of-assoc-equal-when-macro-scopep
                             alistp-when-macro-scopep-rewrite)))
   (define macro-lookup-in-scopes ((name identp)
                                   (current-innermostp booleanp)
                                   (scopes macro-scope-listp))
     :returns (mv (info? macro-info-optionp)
                  (final-innermostp booleanp))
     :parents nil
     (b* (((when (endp scopes)) (mv nil nil))
          (scope (macro-scope-fix (car scopes)))
          (name+info (assoc-equal (ident-fix name) scope))
          ((when name+info) (mv (cdr name+info) (bool-fix current-innermostp))))
       (macro-lookup-in-scopes name nil (cdr scopes)))))

  ///

  (defret macro-lookup-not-innermostp-and-predefinedp
    (not (and innermostp predefinedp)))

  (in-theory (disable macro-lookup-not-innermostp-and-predefinedp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-table-init ()
  :returns (table macro-tablep)
  :short "Initial macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the table before we preprocess any file, so there are no scopes.
     For now we do not add any predefined macros,
     but we should do that at some point."))
  (make-macro-table :predefined nil ; TODO
                    :scopes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-table-push ((table macro-tablep))
  :returns (new-table macro-tablep)
  :short "Push a scope onto the macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used just before preprocessing a file.
     We add a new empty scope for the new file."))
  (change-macro-table table :scopes (cons nil (macro-table->scopes table)))

  ///

  (defret consp-of-scopes-of-macro-table-push
    (consp (macro-table->scopes new-table))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-add ((name identp) (info macro-infop) (table macro-tablep))
  :returns (mv erp (new-table macro-tablep))
  :short "Add a macro to the macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is added to the innermost scope,
     because it is the scope of the file being currently preprocessed.")
   (xdoc::p
    "If the table already contains a non-predefined macro with the given name,
     the associated information must be the same:
     this enforces the requirement in [C17:6.10.3/2],
     namely that multiple definitions are allowed so long as
     they are of the same kind (both object-like or both function-like),
     they have the same parameters if both function-like,
     and they have identical replacement list.
     The latter notion [C17:6.10.3/1] amounts to equality for us,
     because, as explained in @(tsee macro-info),
     we normalize all white space to single spaces.
     We may need to relax this check at some point,
     based on the C version, because GCC allows redefinition.")
   (xdoc::p
    "If the table already contains a predefined macro with the given name,
     we give an error outright,
     because [C:6.10.8/2] prohibits redefinition of predefined macros.
     We may need to relax this check at some point,
     based on the C version,
     because GCC allows redefinition of predefined macros.")
   (xdoc::p
    "If the above checks pass, we add the macro to the table.
     Note that, even if we eliminate those checks for some C versions,
     the added definition will shadow any existing definition,
     in line with the behavior of GCC."))
  (b* (((reterr) (irr-macro-table))
       ((mv info? & predefinedp) (macro-lookup name table))
       ((erp &)
        (if info?
            (if predefinedp
                (reterr (msg "Redefinition of predefined macro ~x0."
                             (ident-fix name)))
              (if (equal info? (macro-info-fix info))
                  (retok nil)
                (reterr (msg "Duplicate macro ~x0 ~
                              with incompatible definitions ~x1 and ~x2."
                             (ident-fix name)
                             (macro-info-fix info)
                             info?))))
          (retok nil)))
       (scopes (macro-table->scopes table))
       ((unless (consp scopes))
        (raise "Internal error: no macro scopes.")
        (reterr t))
       (scope (car scopes))
       (new-scope (acons (ident-fix name) (macro-info-fix info) scope))
       (new-scopes (cons new-scope (cdr scopes)))
       (new-table (change-macro-table table :scopes new-scopes)))
    (retok new-table))
  :guard-hints (("Goal" :in-theory (enable alistp-when-macro-scopep-rewrite
                                           acons)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-table-extend-top ((scope macro-scopep) (table macro-tablep))
  :returns (new-table macro-tablep)
  :short "Extend the top scope of a macro table with another scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to incorporate,
     into the macro table of a file being preprocessed,
     the macros contributed by a (@(see self-contained)) file
     included by the former file.
     When the included file is self-contained,
     it is not expanded in place,
     but we need to preprocess the rest of the including file
     as if the included file were expanded in place,
     in particular we must add the macro definitions that
     the expanded included file would produce."))
  (b* ((old-scopes (macro-table->scopes table))
       ((unless (consp old-scopes))
        (raise "Internal error: no scopes in macro table.")
        (irr-macro-table))
       (old-scope (car old-scopes))
       (new-scope (append scope old-scope))
       (new-scopes (cons new-scope (cdr old-scopes))))
    (change-macro-table table :scopes new-scopes))
  :no-function nil)
