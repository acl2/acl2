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

(include-book "../language/implementation-environments/versions")

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
    "Both object-like and function-like macros have replacement lists,
     which grammatically are sequences of zero or more preprocessing tokens.
     Although white space and comments between such tokens
     could be ignored if we always operated on tokens,
     our "
    (xdoc::seetopic "preprocessor-printer" "preprocessor printer")
    " could print something incorrect without white space separation:
     for instance, given")
   (xdoc::codeblock
    "#define M A B"
    "M")
   (xdoc::p
    "should result in")
   (xdoc::codeblock
    "A B")
   (xdoc::p
    "and not in")
   (xdoc::codeblock
    "AB")
   (xdoc::p
    "Additionally, [C17:6.10.3/1] suggests that
     the notion of `identical replacement lists'
     involves considerations of white space separation between tokens.")
   (xdoc::p
    "To facilitate comparisons with multiple definitions of the same macro
     [C17:6.10.3/1] [C17:6.10.3/2],
     we normalize the white space between tokens as single spaces
     in our replacement lists, which we thus model as
     lists of tokens and (single) spaces.
     These spaces can only occur between two tokens,
     but we currently do not capture this additional invariant.")
   (xdoc::p
    "Aside from the name, an object-like macro [C17:6.10.3/9]
     consists of its replacement list.")
   (xdoc::p
    "For a function-like macro [C17:6.10.3/10],
     besides the replacement list,
     we have zero or more parameters, which are identifiers,
     an optional ellipsis parameter,
     whose presence or absence we model as a boolean,
     and a subset of the parameters that are, in the replacement list,
     either preceded by @('#') or @('##') or followed by @('##').
     This subset is modeled as a list, but treated as a set.
     If the parameters include an ellipsis,
     we need to count it as the @('__VA_ARGS__') identifier.
     This subset is redundant, but convenient."))
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
     When preprocessing the included file as @(see self-contained),
     the included file may define its own macros,
     while the macros defined in the including file are also in scope.
     If the included file includes a further file,
     which we also try prepreocessing as @(see self-contained),
     the latter sees the macros of
     the two (directly and indirectly) including files.
     This leads to a natural stack-like structure
     for keeping track of the macros in scope,
     where each scope corresponds to a file.
     [C17] does not have a notion of macro scopes,
     but our preprocessor uses this notion to determine
     when included files are @(see self-contained).")
   (xdoc::p
    "The values of this alist fixtype represent a macro scope.
     The keys of the alist represent the names of the macros,
     with the values of the alist representing the associated information.
     The reason why we use an option type for the values of the alist
     is that we use @('nil') to represent a macro undefinition,
     i.e. the effect of a @('#undef') directive.
     This may seem strange, but it motivated by the fact that,
     when we encounter a @('#include') that does not need to be expanded,
     we need to incorporate into the macro table of the including file
     the effect of the macro definitions, and also undefinitions,
     contributed by the included file.
     This amounts to treating a macro undefinition
     like a definition to be ``undefined''.")
   (xdoc::p
    "The names of the macros (keys of the alist)
     are identifiers [C17:6.10.3/9] [C17:6.10.3/10].
     These are not necessarily unique,
     because a macro may be alternatively defined and undefined.
     Multiple undefinitions without intervening definitions are harmless
     [C17:6.10.3.5/2].
     Multiple definitions without intervening undefinitions
     are disallowed unless they are suitably equivalent [C17:6.10.3/2];
     in practice, GCC allows redefinition within a file,
     with the last definition overriding the previous one.
     So our current structure with non-unique alist keys
     is amenable to accommodate this GCC (and probably also Clang) relaxation.
     Definitions and undefinitions are added with @(tsee acons),
     and looked up with @(tsee assoc-equal),
     so the latest one is always found."))
  :key-type ident
  :val-type macro-info-option
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  :pred macro-scopep
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled macro-info-optionp-of-cdr-of-assoc-equal-when-macro-scopep
    (implies (macro-scopep scope)
             (macro-info-optionp (cdr (assoc-equal name scope))))
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
     i.e. a list of scopes corresponding to the files
     being preprocessed as @(see self-contained),
     the @(tsee car) being the innermost scope,
     and the list being empty only before any file is being preprocessed.
     We also have a separate scope of predefined macros [C17:6.10.8].")
   (xdoc::p
    "For the same reason we discuss in @(tsee macro-scope),
     we do not enforce any constraint on keys in different scopes,
     because we keep track of both definitions and undefinitions.
     This can accommodate future extensions in which we may allow
     overriding of definitions (without intervening undefinitions).")
   (xdoc::p
    "The predefined macros can be viewed as being in an outermost scope.
     Their names and definitions depend on the C version,
     and should be initialized accordingly.
     Many predefined macros are adequately modeled
     with the same @(tsee macro-info) data as non-predefined ones.
     A few predefined macros are special,
     such as @('__LINE__') and @('__FILE__') [C17:6.10.10],
     which do not have a fixed value:
     these need to be recognized (by name)
     and handled appropriately;
     we model them as having empty replacement lists,
     and include them in the predefined scope.")
   (xdoc::p
    "The scope of predefined macros only contains definitions, no undefinitions.
     We could use a slightly tighter type for the scope of predefined macros."))
  ((predefined macro-scope)
   (scopes macro-scope-list))
  :pred macro-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-macro-table
  :short "An irrelevant macro table."
  :type macro-tablep
  :body (macro-table nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c17 ()
  :returns (macros macro-scopep)
  :short "Predefined macros for C17 (without GCC or Clang extensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress:
     we start with a few macros,
     but we need to systematically add more."))
  (list (cons (ident "__STDC__")
              (macro-info-object
               (list (plexeme-number (pnumber-digit #\1)))))
        (cons (ident "__STDC_VERSION__")
              (macro-info-object
               (list (plexeme-number
                      (pnumber-number-nondigit
                       (pnumber-number-digit
                        (pnumber-number-digit
                         (pnumber-number-digit
                          (pnumber-number-digit
                           (pnumber-number-digit
                            (pnumber-digit
                             #\2) #\0) #\1) #\7) #\1) #\0) #\L))))))
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c23 ()
  :returns (macros macro-scopep)
  :short "Predefined macros for C17 (without GCC or Clang extensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress:
     we start with a few macros,
     but we need to systematically add more."))
  (list (cons (ident "__STDC__")
              (macro-info-object
               (list (plexeme-number (pnumber-digit #\1)))))
        (cons (ident "__STDC_VERSION__")
              (macro-info-object
               (list (plexeme-number
                      (pnumber-number-nondigit
                       (pnumber-number-digit
                        (pnumber-number-digit
                         (pnumber-number-digit
                          (pnumber-number-digit
                           (pnumber-number-digit
                            (pnumber-digit
                             #\2) #\0) #\2) #\3) #\1) #\1) #\L))))))
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c17+gcc ()
  :returns (macros macro-scopep)
  :short "Predefined macros for C17 with GCC extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress:
     we start with a few macros,
     but we need to systematically add more."))
  (predefined-macros-c17))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c23+gcc ()
  :returns (macros macro-scopep)
  :short "Predefined macros for C23 with GCC extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress:
     we start with a few macros,
     but we need to systematically add more."))
  (predefined-macros-c23))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c17+clang ()
  :returns (macros macro-scopep)
  :short "Predefined macros for C17 with Clang extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress:
     we start with a few macros,
     but we need to systematically add more.")
   (xdoc::p
    "The @('__arm64__') is more specific than Clang,
     so we may want to introduce and use further parameterization;
     but this should work fine on (relatively) new Mac machines."))
  (append (predefined-macros-c17)
          (list (cons (ident "__arm64__")
                      (macro-info-object
                       (list (plexeme-number (pnumber-digit #\1)))))
                (cons (ident "__GNUC__")
                      (macro-info-object
                       (list (plexeme-number (pnumber-digit #\4)))))
                (cons (ident "__GNUC_MINOR__")
                      (macro-info-object
                       (list (plexeme-number (pnumber-digit #\2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c23+clang ()
  :returns (macros macro-scopep)
  :short "Predefined macros for C23 with Clang extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress:
     we start with a few macros,
     but we need to systematically add more.")
   (xdoc::p
    "The @('__arm64__') is more specific than Clang,
     so we may want to introduce and use further parameterization;
     but this should work fine on (relatively) new Mac machines."))
  (append (predefined-macros-c23)
          (list (cons (ident "__arm64__")
                      (macro-info-object
                       (list (plexeme-number (pnumber-digit #\1)))))
                (cons (ident "__GNUC__")
                      (macro-info-object
                       (list (plexeme-number (pnumber-digit #\4)))))
                (cons (ident "__GNUC_MINOR__")
                      (macro-info-object
                       (list (plexeme-number (pnumber-digit #\2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros ((version c::versionp))
  :returns (macros macro-scopep)
  :short "Predefined macros for the given C version."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress.
     We start with some initial macros,
     but we need to systematically add more."))
  (c::version-case
   version
   :c17 (predefined-macros-c17)
   :c23 (predefined-macros-c23)
   :c17+gcc (predefined-macros-c17+gcc)
   :c23+gcc (predefined-macros-c23+gcc)
   :c17+clang (predefined-macros-c17+clang)
   :c23+clang (predefined-macros-c23+clang)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-lookup ((name identp) (table macro-tablep))
  :returns (mv (info? macro-info-optionp)
               (reach integerp :rule-classes (:rewrite :type-prescription)))
  :short "Look up a macro in a macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We search from innermost to outermost scope,
     and then the predefined scope if needed.
     This lookup order matches GCC's behavior,
     notes in @(tsee macro-scope) and @(tsee macro-table).")
   (xdoc::p
    "We also return an integer that we call `reach',
     indicating how far in the macro tables
     we had to look to find the macro, if we found it.
     The reach is 0 if we find the macro in the innermost scope,
     1 if we find it in the scope just before that, and so on.
     If we find it in the predefined scope, the reach is -1.
     If we do not find the macro at all, the reach is -2.
     The rationale for this notion of reach is
     to support the recognition of self-contained files,
     as explained elsewhere.")
   (xdoc::p
    "We return @('nil') if we find the macro name
     in an alist with associated value @('nil'),
     which means that the macro has been undefined via @('#undef');
     see @(tsee macro-scope).
     We also return @('nil') if the macro is not found in any alist."))
  (b* (((mv foundp info? reach)
        (macro-lookup-in-scopes name 0 (macro-table->scopes table)))
       ((when foundp) (mv info? reach))
       (name+info
        (assoc-equal (ident-fix name) (macro-table->predefined table)))
       ((when name+info) (mv (cdr name+info) -1)))
    (mv nil -2))

  :prepwork

  ((local (in-theory (enable alistp-when-macro-scopep-rewrite)))

   (define macro-lookup-in-scopes ((name identp)
                                   (current-reach integerp)
                                   (scopes macro-scope-listp))
     :returns (mv (foundp booleanp)
                  (info? macro-info-optionp)
                  (final-reach integerp))
     :parents nil
     (b* (((when (endp scopes)) (mv nil nil -2))
          (scope (macro-scope-fix (car scopes)))
          (name+info (assoc-equal (ident-fix name) scope))
          ((when name+info) (mv t (cdr name+info) (lifix current-reach))))
       (macro-lookup-in-scopes name (1+ (lifix current-reach)) (cdr scopes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-table-init ((version c::versionp))
  :returns (table macro-tablep)
  :short "Initial macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the table before we preprocess any file, so there are no scopes.
     But we have the predefined macros."))
  (make-macro-table :predefined (predefined-macros version)
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
  :short "Add a macro definition to the macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is added to the innermost scope,
     because it is the scope of the file being currently preprocessed.")
   (xdoc::p
    "If the table already contains a non-predefined macro with the given name,
     that has not been undefined
     (i.e. looking up the macro name finds a definition),
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
    "If the above checks pass, we add the macro to the table,
     at the beginning of the alist for the innermost scope.
     This shadow any other undefinition and definition in that scope,
     as well as in other scopes."))
  (b* (((reterr) (irr-macro-table))
       ((mv info? reach) (macro-lookup name table))
       ((erp &)
        (if info?
            (if (= reach -1)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-remove ((name identp) (table macro-tablep))
  :returns (mv erp (new-table macro-tablep))
  :short "Add a macro undefinition to the macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just add an undefinition to the innermost scope,
     at the start, so that subsequent lookups find this undefinition.")
   (xdoc::p
    "This has no effect on subsequent lookups
     if the macro was already undefined or absent from the table,
     consistently with [C17:6.10.3.5/2].")
   (xdoc::p
    "[C17:6.10.8/2] prohibits the removal of a predefined macro.
     So we return an error if an attempt is made.
     However, Clang allows that, so we may need to optionally relax this."))
  (b* (((reterr) (irr-macro-table))
       ((macro-table table) table)
       ((when (assoc-equal (ident-fix name) table.predefined))
        (reterr (msg "Cannot undefine the predefined macro ~x0."
                     (ident-fix name))))
       (scope (car table.scopes))
       (new-scope (acons (ident-fix name) nil scope))
       (new-scopes (cons new-scope (cdr table.scopes)))
       (new-table (change-macro-table table :scopes new-scopes)))
    (retok new-table))
  :guard-hints (("Goal" :in-theory (enable alistp-when-macro-scopep-rewrite
                                           acons)))
  :no-function nil)
