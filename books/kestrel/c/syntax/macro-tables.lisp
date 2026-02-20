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
     which grammatically are sequences of zero or more preprocessing tokens.")
   (xdoc::p
    "Since [C17:6.10.3/1] suggests that
     the notion of `identical replacement lists'
     involves considerations of white space separation between tokens,
     we more generally use lexemes in replacement lists..")
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

(fty::defalist ident-macro-info-alist
  :short "Fixtype of alists from identifiers to macro information."
  :key-type ident
  :val-type macro-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred ident-macro-info-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled macro-infop-of-cdr-of-assoc-equal-when-ident-macro-info-alistp
    (implies (and (ident-macro-info-alistp macros)
                  (assoc-equal name macros))
             (macro-infop (cdr (assoc-equal name macros))))
    :induct t
    :enable ident-macro-info-alistp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist ident-macro-info-option-alist
  :short "Fixtype of alists from identifiers to optional macro information."
  :key-type ident
  :val-type macro-info-option
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  :pred ident-macro-info-option-alistp
  :prepwork ((set-induction-depth-limit 1))

  ///

  (defruled
    macro-info-optionp-of-cdr-of-assoc-equal-when-macro-info-option-alistp
    (implies (ident-macro-info-option-alistp macros)
             (macro-info-optionp (cdr (assoc-equal name macros))))
    :induct t
    :enable ident-macro-info-option-alistp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod macro-table
  :short "Fixtype of macro tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We represent the predefined macros [C17:6.10.8]
     as an alist from their names to the information about them.
     Some predefined macros, e.g. @('__LINE__') and @('__FILE__'),
     are special in the sense that they do not have a fixed definition
     [C17:6.10.8.1].
     We represent them as having empty replacement list,
     but handle their actual replacement specially in code.
     The exact predefined macros depend on the version:
     see @(tsee predefined-macros).
     The predefined macros never change,
     i.e. that component of the macro table stays constant.")
   (xdoc::p
    "The alist of predefined macros has unique keys.
     We enforce that with an invariant.")
   (xdoc::p
    "The second component of the macro table is dynamic:
     it starts empty, and gets extended
     every time a @('#define') or a @('#undef') is encountered.
     While a @('#define') adds an entry with a @(tsee macro-info),
     a @('#undef') adds an entry with @('nil'):
     this is why we use an alist from names to optional macro information.
     In essence, we treat a macro undefinition
     like a definition to be ``undefined''.")
   (xdoc::p
    "It may seem strange to handle macro undefinition
     by adding an entry with @('nil') to the dynamic alist,
     instead of just removing the entry from the alist.
     But this approach makes it faster
     both to undefine a macro,
     and to find out if a macro was undefined in a lookup.")
   (xdoc::p
    "The dynamic alist of macros does not necessarily have unique keys.
     This is intentional,
     because a macro may be alternatively defined and undefined.
     Multiple undefinitions without intervening definitions are harmless
     [C17:6.10.3.5/2].
     Multiple definitions without intervening undefinitions
     are disallowed unless they are suitably equivalent [C17:6.10.3/2];
     in practice, GCC and Clang allow redefinition within a file,
     with the last definition overriding the previous one.
     So in the future we can (optionallY) accommodate this GCC/Clang extension,
     simply by adding the new definition to the front of the alist.
     Definitions and undefinitions are added with @(tsee acons),
     and looked up with @(tsee assoc-equal),
     so the latest one is always found."))
  ((predefined ident-macro-info-alist
               :reqfix (if (no-duplicatesp-equal (strip-cars predefined))
                           predefined
                         nil))
   (dynamic ident-macro-info-option-alist))
  :require (no-duplicatesp-equal (strip-cars predefined))
  :pred macro-tablep
  :prepwork
  ((local (in-theory (enable alistp-when-ident-macro-info-alistp-rewrite)))))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-macro-table
  :short "An irrelevant macro table."
  :type macro-tablep
  :body (macro-table nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c17 ()
  :returns (macros ident-macro-info-alistp)
  :short "Predefined macros for C17 (without GCC or Clang extensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We start with just a few macros from [C17:6.10.8].
     We should add all of them."))
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
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p)))

  ///

  (defret no-duplicatesp-equal-of-predefined-macros-c17
    (no-duplicatesp-equal (strip-cars macros))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-c23 ()
  :returns (macros ident-macro-info-alistp)
  :short "Predefined macros for C17 (without GCC or Clang extensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are similar to @(tsee predefined-macros-c17).
     See [C23:6.10.10]."))
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
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p)))

  ///

  (defret no-duplicatesp-equal-of-predefined-macros-c23
    (no-duplicatesp-equal (strip-cars macros))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-gcc ()
  :returns (macros ident-macro-info-alistp)
  :short "Predefined macros for GCC extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are in addition to the standard ones.
     We have none for now,
     because we have only tested standard and Clang code for now.
     But we should add them, in a systematic way."))
  nil

  ///

  (defret no-duplicatesp-equal-of-predefined-macros-gcc
    (no-duplicatesp-equal (strip-cars macros))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros-clang ()
  :returns (macros ident-macro-info-alistp)
  :short "Predefined macros for Clang extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are in addition to the standard ones.
     We start with just a few macros that come up in tests,
     and without which we cannot successfully preprocess
     Clang's system headers.
     We should add more, in a systematic way.")
   (xdoc::p
    "The @('__arm64__') macro is more specific than Clang,
     so we may want to introduce and use further parameterization;
     but this should work fine on sufficiently new Mac machines.
     Without this, or one of a few other alternatives,
     @('sys/cdefs.h') fails with an error
     indicating an unsupported architecture.")
   (xdoc::p
    "without a definitino for the @('__GNUC__') macro,
     we get an error when preprocessing the Clang system files.
     We also add the @('__GNUC_MINOR__') macro, since it is related.")
   (xdoc::p
    "The @('__has_feature') macro is actually a function-like macro,
     documented in "
    (xdoc::ahref "https://clang.llvm.org/docs/LanguageExtensions.html" "[CLE]")
    ", for which we need to add proper support.
     For now we define it to be just @('0'),
     consistently with the following code in @('sys/cdefs.h'):")
   (xdoc::codeblock
    "#ifndef __has_feature"
    "#define __has_feature(x) 0"
    "#endif")
   (xdoc::p
    "If this macro is not defined at all,
     the following code in @('sys/_types/_ptrdiff.h'),
     and probably in other files as well,
     fails:")
   (xdoc::codeblock
    "#if defined(__has_feature) && __has_feature(modules)")
   (xdoc::p
    "Although the test looks sensible,
     before it is evaluated,
     it has to be macro-expanded and parsed.
     After the @('&&'), if @('__has_feature') is not defined,
     it gets replaced with @('0') [C17:6.10.1/4],
     which then leaves an extra @('(modules)') after the @('0'),
     which does not form an expression.
     Indeed, both Clang and GCC fail on a line")
   (xdoc::codeblock
    "#if defined(F) && F(...)")
   (xdoc::p
    "when @('F') is not defined.
     The error that both Clang and GCC give is that
     the function-like macro F has no definition,
     which is not unreasonable,
     although [C17] may actually require that,
     if @('F') is not a function-like macro,
     it is left as is, even when an open parenthesis follows.
     Our preprocessor does that, but fails when parsing the expression,
     because of the extra tokens after the @('F'),
     or after the @('__has_feature') before we predefine it here."))
  (list (cons (ident "__arm64__")
              (macro-info-object
               (list (plexeme-number (pnumber-digit #\1)))))
        (cons (ident "__GNUC__")
              (macro-info-object
               (list (plexeme-number (pnumber-digit #\4)))))
        (cons (ident "__GNUC_MINOR__")
              (macro-info-object
               (list (plexeme-number (pnumber-digit #\2)))))
        (cons (ident "__has_feature")
              (make-macro-info-function
               :params (list (ident "x"))
               :ellipsis nil
               :replist (list (plexeme-number (pnumber-digit #\0)))
               :hash-params nil)))

  ///

  (defret no-duplicatesp-equal-of-predefined-macros-clang
    (no-duplicatesp-equal (strip-cars macros))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predefined-macros ((version c::versionp))
  :returns (macros ident-macro-info-alistp)
  :short "Predefined macros for the given C version."
  :long
  (xdoc::topstring
   (xdoc::p
    "We compose the macros according to the version."))
  (c::version-case
   version
   :c17 (predefined-macros-c17)
   :c23 (predefined-macros-c23)
   :c17+gcc (append (predefined-macros-c17)
                    (predefined-macros-gcc))
   :c23+gcc (append (predefined-macros-c23)
                    (predefined-macros-gcc))
   :c17+clang (append (predefined-macros-c17)
                      (predefined-macros-clang))
   :c23+clang (append (predefined-macros-c23)
                      (predefined-macros-clang)))

  ///

  (defret no-duplicatesp-equal-of-predefined-macros
    (no-duplicatesp-equal (strip-cars macros))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-lookup ((name identp) (table macro-tablep))
  :returns
  (info?
   macro-info-optionp
   :hints
   (("Goal"
     :in-theory
     (enable
      macro-info-optionp
      macro-infop-of-cdr-of-assoc-equal-when-ident-macro-info-alistp))))
  :short "Look up a macro in a macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we look in the dynamic alist,
     returning @('nil') if we find an undefinition.
     If we find no definition or undefinition in the dynamic alist,
     we look in the predefined alist:
     if we find it, we return the information,
     otherwise @('nil').
     Either way, @('nil') means that no definition,
     possibly due to undefinition,
     is found."))
  (b* ((name+info? (assoc-equal (ident-fix name)
                                (macro-table->dynamic table)))
       ((when name+info?) (cdr name+info?)))
    (cdr (assoc-equal (ident-fix name) (macro-table->predefined table))))
  :guard-hints
  (("Goal"
    :in-theory (enable alistp-when-ident-macro-info-alistp-rewrite
                       alistp-when-ident-macro-info-option-alistp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-init ((version c::versionp))
  :returns (table macro-tablep)
  :short "Initial macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the table before we preprocess any file,
     so there are no macros int the dynamic alist.
     But we have the predefined macros."))
  (make-macro-table :predefined (predefined-macros version)
                    :dynamic nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-define ((name identp) (info macro-infop) (table macro-tablep))
  :returns (mv erp (new-table macro-tablep))
  :short "Add a macro definition to the macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the table already contains a predefined macro with the given name,
     we give an error outright,
     because [C:6.10.8/2] prohibits redefinition of predefined macros.
     We may need to relax this check at some point,
     based on the C version,
     because GCC allows redefinition of predefined macros.")
   (xdoc::p
    "If the table already contains, in the dynamic alist,
     a macro with the given name,
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
    "If the above checks pass, we add the macro to the table,
     at the beginning of the dynamic alist.
     This shadows any other undefinition and definition."))
  (b* (((reterr) (irr-macro-table))
       ((macro-table table) table)
       ((when (assoc-equal (ident-fix name) table.predefined))
        (reterr (msg "Cannot re-define the predefined macro ~x0."
                     (ident-fix name))))
       (info? (cdr (assoc-equal (ident-fix name) table.dynamic)))
       ((erp &)
        (if info?
            (if (equal info? (macro-info-fix info))
                (retok nil)
              (reterr (msg "Duplicate macro ~x0 ~
                            with incompatible definitions ~x1 and ~x2."
                           (ident-fix name)
                           (macro-info-fix info)
                           info?)))
          (retok nil)))
       (new-dynamic
        (acons (ident-fix name) (macro-info-fix info) table.dynamic)))
    (retok (change-macro-table table :dynamic new-dynamic)))
  :guard-hints
  (("Goal" :in-theory (enable alistp-when-ident-macro-info-alistp-rewrite
                              alistp-when-ident-macro-info-option-alistp-rewrite
                              acons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-undefine ((name identp) (table macro-tablep))
  :returns (mv erp (new-table macro-tablep))
  :short "Add a macro undefinition to the macro table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add an undefinition to the dynamic alist,
     at the start, so that subsequent lookups find this undefinition.")
   (xdoc::p
    "This has no effect on subsequent lookups
     if the macro was already undefined or absent from the table,
     consistently with [C17:6.10.3.5/2].")
   (xdoc::p
    "[C17:6.10.8/2] prohibits the removal of a predefined macro.
     So we return an error if an attempt is made.
     However, GCC and Clang allows that,
     so we may need to optionally relax this."))
  (b* (((reterr) (irr-macro-table))
       ((macro-table table) table)
       ((when (assoc-equal (ident-fix name) table.predefined))
        (reterr (msg "Cannot undefine the predefined macro ~x0."
                     (ident-fix name))))
       (new-dynamic (acons (ident-fix name) nil table.dynamic)))
    (retok (change-macro-table table :dynamic new-dynamic)))
  :guard-hints
  (("Goal" :in-theory (enable alistp-when-ident-macro-info-alistp-rewrite
                              alistp-when-ident-macro-info-option-alistp-rewrite
                              acons))))
