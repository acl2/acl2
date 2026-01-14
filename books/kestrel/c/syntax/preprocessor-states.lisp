; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser-states")
(include-book "implementation-environments")

(include-book "kestrel/fty/byte-list-list" :dir :system)
(include-book "std/strings/letter-uscore-chars" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(acl2::controlled-configuration)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl assoc-equal-iff-member-equal-of-strip-cars
  (implies (alistp alist)
           (iff (assoc-equal key alist)
                (member-equal key (strip-cars alist))))
  :induct t
  :enable (assoc-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl byte-list-listp-of-resize-list
  (implies (and (byte-list-listp bytess)
                (byte-listp default))
           (byte-list-listp (resize-list bytess length default)))
  :induct t
  :enable (byte-list-listp resize-list))

(defruledl byte-list-listp-of-update-nth-strong
  (implies (byte-list-listp bytess)
           (equal (byte-list-listp (update-nth i bytes bytess))
                  (byte-listp bytes)))
  :induct t
  :enable (byte-listp update-nth nfix zp len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-states
  :parents (preprocessor)
  :short "States of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are somewhat analogous to the "
    (xdoc::seetopic "parser-states" "parser states")
    ", but for the preprocessor.")
   (xdoc::p
    "We include the file that defines parser states
     because we reuse some of the definitions here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pnumber
  :short "Fixtype of preprocessing numbers [C17:6.4.8] [C17:A.1.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like an abstract syntax for preprocessing numbers,
     corresponding to the rule for @('pp-number') in the ABNF grammar.
     We need to capture their structure, in order to do preprocessing."))
  (:digit ((digit character
                  :reqfix (if (dec-digit-char-p digit)
                              digit
                            #\0)))
   :require (dec-digit-char-p digit))
  (:dot-digit ((digit character
                      :reqfix (if (dec-digit-char-p digit)
                                  digit
                                #\0)))
   :require (dec-digit-char-p digit))
  (:number-digit ((number pnumber)
                  (digit character
                         :reqfix (if (dec-digit-char-p digit)
                                     digit
                                   #\0)))
   :require (dec-digit-char-p digit))
  (:number-nondigit ((number pnumber)
                     (nondigit character
                               :reqfix (if (str::letter/uscore-char-p nondigit)
                                           nondigit
                                         #\_)))
   :require (str::letter/uscore-char-p nondigit))
  (:number-locase-e-sign ((number pnumber)
                          (sign sign)))
  (:number-upcase-e-sign ((number pnumber)
                          (sign sign)))
  (:number-locase-p-sign ((number pnumber)
                          (sign sign)))
  (:number-upcase-p-sign ((number pnumber)
                          (sign sign)))
  (:number-dot ((number pnumber)))
  :pred pnumberp
  :prepwork ((set-induction-depth-limit 1)
             (local (in-theory (enable fix (:e str::letter/uscore-char-p))))))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pnumber
  :short "An irrelevant preprocessing number."
  :type pnumberp
  :body (pnumber-digit #\0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum newline
  :short "Fixtype of new lines."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the rule @('new-line') in the ABNF grammar.
     Our preprocessor does not collapse them into a single new-line
     because it preserves white space, which includes new lines."))
  (:lf ())
  (:cr ())
  (:crlf ())
  :pred newlinep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-newline
  :short "An irrelevant new line."
  :type newlinep
  :body (newline-lf))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum plexeme
  :short "Fixtype of preprocessing lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of preprocessing tokens [C17:6.4] [C17:A.1.1],
     with the addition of comments and white space:
     these are all the preprocessing lexemes,
     although [C17] does not use the word `lexeme'.")
   (xdoc::p
    "We reuse some of the fixtypes for ASTs here.")
   (xdoc::p
    "The @(':other') summand corresponds to
     the last alternative in the ABNF grammar rule for @('preprocessing-token'),
     as well as the prose description of the rule in [C17].
     It consists of the code of the character.")
   (xdoc::p
    "For (block and line) comments, we include the content,
     consisting of the codes of the characters.
     For block comments, these are all the characters
     from just after the opening @('/*') to just before the closing @('*/').
     For line comments, these are all the characters
     from just after the opening @('//') to just before the closing new line;
     recall that line comments exclude the ending new line [C17:6.4.9/2].")
   (xdoc::p
    "We keep the information about the three possible kinds of new-line,
     and of all other white space characters,
     according to the ABNF grammar rule for @('white-space').
     Since spaces (code 32) often occur in consecutive chunks,
     we represent them more efficiently as chunks, via positive counts."))
  (:header ((name header-name)))
  (:ident ((ident ident)))
  (:number ((number pnumber)))
  (:char ((const cconst)))
  (:string ((literal stringlit)))
  (:punctuator ((punctuator string)))
  (:other ((char nat)))
  (:block-comment ((content nat-list)))
  (:line-comment ((content nat-list)))
  (:newline ((chars newline)))
  (:spaces ((count pos)))
  (:horizontal-tab ())
  (:vertical-tab ())
  (:form-feed ())
  :pred plexemep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-plexeme
  :short "An irrelevant preprocessing lexeme."
  :type plexemep
  :body (plexeme-ident (ident :irrelevant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption plexeme-option
  plexeme
  :short "Fixtype of optional preprocessing lexemes."
  :pred plexeme-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist plexeme-list
  :short "Fixtype of lists of preprocessing lexemes."
  :elt-type plexeme
  :true-listp t
  :elementp-of-nil nil
  :pred plexeme-listp

  ///

  (defruled true-listp-when-plexeme-listp
    (implies (plexeme-listp x)
             (true-listp x))
    :induct t
    :enable plexeme-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-tokenp ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the grammar rule for <i>preprocessing-token</i>
     [C17:6.4] [C17:A.1.1]."))
  (and (member-eq (plexeme-kind lexeme)
                  '(:header
                    :ident
                    :number
                    :char
                    :string
                    :punctuator
                    :other))
       t)

  ///

  (defruled plexeme-tokenp-alt-def
    (equal (plexeme-tokenp lexeme)
           (not (member-eq (plexeme-kind lexeme)
                           '(:block-comment
                             :line-comment
                             :newline
                             :spaces
                             :horizontal-tab
                             :vertical-tab
                             :form-feed))))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-tokenp (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list is a token."
  (plexeme-tokenp x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-tokenp))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-not-tokenp (x)
  :guard (plexeme-listp x)
  :short "Check if no preprocessing lexeme in a list is a token."
  (plexeme-tokenp x)
  :negatedp t
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-not-tokenp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-token/newline-p ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token or a new line."
  :long
  (xdoc::topstring
   (xdoc::p
    "During preprocessing, new-line characters are significant:
     see grammar rules in [C17:6.10/1].
     Preprocessing is largely line-oriented.
     In our preprocessor, new-line characters are captured as new-line lexemes
     (see @(tsee plexeme))."))
  (or (plexeme-tokenp lexeme)
      (plexeme-case lexeme :newline)))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-token/newline-p (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list is a token or new line."
  (plexeme-token/newline-p x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-token/newline-p))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-not-token/newline-p (x)
  :guard (plexeme-listp x)
  :short "Check if no preprocessing lexeme in a list is a token or new line."
  (plexeme-token/newline-p x)
  :negatedp t
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-not-token/newline-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-token/space-p ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token or a (single) space."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to represent, and facilitate comparison of,
     replacement lists of macros, as explained in more detail elsewhere."))
  (or (plexeme-tokenp lexeme)
      (and (plexeme-case lexeme :spaces)
           (equal (plexeme-spaces->count lexeme) 1))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-token/space-p (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list
          is a token or (single) space."
  (plexeme-token/space-p x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-token/space-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-hashp ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a lexeme is a hash @('#')."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the lexeme is the punctuator @('#'),
     or also if the lexeme is the digraph @('%:') [C17:6.4.6/3]."))
  (and (plexeme-case lexeme :punctuator)
       (b* ((string (plexeme-punctuator->punctuator lexeme)))
         (or (equal string "#")
             (equal string "%:")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lexmark
  :short "Fixtype of preprocessing lexemes and markers (`lexmarks')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Along with lexemes,
     it is convenient to handle certain markers.
     We use the term `lexmark' to denote a preprocessing lexeme or marker.")
   (xdoc::p
    "The lexemes are accompanied by spans.")
   (xdoc::p
    "The @(':start') and @(':end') summands are used to mark
     the start and end of an expansion of the macro,
     whose name is the @('macro') field of these two summands,
     in order to inhibit its (direct or indirect) recursive expansion
     [C17:6.10.3.4/2].")
   (xdoc::p
    "The @(':placemarker') summand is used as described in [C17:6.10.3.3],
     to handle the @('##') operator.")
   (xdoc::p
    "Only lexemes have spans associated with them.
     The markers are artifacts, not an actual part of the input files."))
  (:lexeme ((lexeme plexeme)
            (span span)))
  (:start ((macro ident)))
  (:end ((macro ident)))
  (:placemarker ())
  :pred lexmarkp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lexmark
  :short "An irrelevant lexmark."
  :type lexmarkp
  :body (lexmark-lexeme (irr-plexeme) (irr-span)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist lexmark-list
  :short "Fixtype of lists of lexmarks."
  :elt-type lexmark
  :true-listp t
  :elementp-of-nil nil
  :pred lexmark-listp)

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
     The list of lexemes excludes
     the (mandatory [C17:6.10.3/3]) white space
     between the name and the replacement list,
     as well as the white space after the replacement list,
     excluding the closing new line as well
     [C17:6.10.3/7].")
   (xdoc::p
    "For a function-like macro [C17:6.10.3/10],
     besides the replacement list,
     which we model as for object-like macros (see above),
     we have zero or more parameters, which are identifiers,
     and an optional ellipsis parameter,
     whose presence or absence we model as a boolean.
     The list of lexemes excludes any white space between
     the closing parenthesis of the parameters and the replacement list,
     as well as the white space after the replacement list,
     exclusing the closing new line as well
     [C17:6.10.3/7]."))
  (:object ((replace plexeme-list
                     :reqfix (if (plexeme-list-token/space-p replace)
                                 replace
                               nil)))
   :require (plexeme-list-token/space-p replace))
  (:function ((params ident-list)
              (ellipsis bool)
              (replace plexeme-list
                       :reqfix (if (plexeme-list-token/space-p replace)
                                   replace
                                 nil)))
   :require (plexeme-list-token/space-p replace))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ppstate
  :short "Fixtype of preprocessor states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee parstate), but for the preprocessor.")
   (xdoc::p
    "Our preprocessing functions take and return preprocessor states.")
   (xdoc::p
    "The preprocessor state is a stobj, which we turn into a fixtype
     by adding a fixer along with readers and writers
     that fix their inputs and unconditionally return typed outputs.
     The use of a stobj is an optimization for speed:
     conceptually,
     the preprocessor state could be defined as a @(tsee fty::defprod).")
   (xdoc::p
    "Most of the components of the preprocessor state
     are analogous to the ones of the parser state
     (see the documentation of @(tsee parstate) first),
     but there are differences:")
   (xdoc::ul
    (xdoc::li
     "The bytes being read are organized as an array of lists
      (the @('ss') in @('bytess') conveys the ``double plural'').
      Conceptually, it is equivalent to concatenating the lists in order,
      but the nested structure derives from file inclusion via @('#include'),
      and plays a role in the termination argument of the preprocessor.
      When starting to read a top-level file,
      there is just one list with the bytes of the file.
      When a @('#include') directive is encountered,
      unless certain conditions (specific to our preprocessor) are satisfied,
      the contents of the included file must be expanded in place,
      i.e. the @('#include') directive must be replaced
      with the content of the file [C17:6.10.2],
      and preprocessing continues on that content,
      and then eventually with the content of the including file
      after the @('#include') directive;
      this is the normal behavior of C preprocessors, in fact.
      When that happens,
      instead of @(tsee append)ing the bytes of the included file
      in front of the remaining bytes in the stobj,
      we store the bytes of the included file
      into the next element of the array,
      i.e. one more than the current index @('bytess-current'),
      which is also part of the stobj,
      and keeps track of the current byte list being read.
      If the included file's bytes, when parsed/preprocessed,
      contain more @('#include') directives,
      more lists of bytes are added to the array,
      and @('bytess-current') advanced accordingly.
      This is more efficient than @(tsee append)ing to one list of bytes.
      We use an array instead of a list of lists so that
      we can efficiently read and remove bytes:
      @(tsee cdr) on a list is efficient (no memory allocation),
      but if we had a list of lists instead of an array of lists,
      we would have to create a new list of lists
      with the first list resulting from the @(tsee cdr),
      i.e. we would have to execute a @(tsee cons);
      this is avoided with an array, since the lists in it are independent.
      As bytes are read from the current list of the array,
      when that list becomes empty, the @('bytess-current') is decremented:
      that happens when the bytes of the latest included file
      have been completely preprocessed;
      the reduced @('bytess-current') reflects
      the reduced depth of the file inclusion.")
    (xdoc::li
     "Instead of just a C version as in the parser state,
      the preprocessor state has a full implementation environment.
      Probably parser states should have that too.")
    (xdoc::li
     "Instead of an array and two indices that represent
      a sequence of read and unread tokens,
      we have a single list of pending lexmarks.
      This is used like the sequence of unread tokens in the parser state,
      in the sense that the next lexeme is read from the list if non-empty,
      and otherwise it is lexed from the input characters.
      However, lexmarks are added to the pending list
      not only when unreading lexemes,
      which actually happens rarely in our preprocessor,
      but also when expanding macros.
      When a macro is expanded, the expansion is added to the pending list,
      so that preprocessing continues with the expansion,
      thus realizing rescanning and further replacement [C17:6.10.3.4].
      The @(':start') and @(':end') markers are added around that expansion,
      to delimit that the expansion comes from a certain macro,
      so that we can prevent recursive expansion,
      as explained in more detail elsewhere.
      The pending list of lexmarks in the preprocessing state
      actually never contains @(':placemarker') markers;
      we should sharpen the type of this stobj component accordingly.")
    (xdoc::li
     "The preprocessor state also contains
      a macro table that consists of all the macros in scope.")))

  ;; needed for DEFSTOBJ and reader/writer proofs:

  (local (in-theory (enable length)))

  ;; stobj definition:

  (make-event
   `(defstobj ppstate
      (bytess :type (array (satisfies byte-listp) (1))
              :initially nil
              :resizable t)
      (bytess-current :type (integer 0 *)
                      :initially 0)
      (position :type (satisfies positionp)
                :initially ,(irr-position))
      (chars :type (array (satisfies char+position-p) (1))
             :initially ,(make-char+position :char 0
                                             :position (irr-position))
             :resizable t)
      (chars-read :type (integer 0 *)
                  :initially 0)
      (chars-unread :type (integer 0 *)
                    :initially 0)
      (lexmarks :type (satisfies lexmark-listp)
                :initially nil)
      (ienv :type (satisfies ienvp)
            :initially ,(irr-ienv))
      (size :type (integer 0 *)
            :initially 0)
      (macros :type (satisfies macro-tablep)
              :initially ,(macro-table-init))
      :renaming (;; field recognizers:
                 (bytessp raw-ppstate->bytess-p)
                 (bytess-currentp raw-ppstate->bytess-current-p)
                 (positionp raw-ppstate->position-p)
                 (charsp raw-ppstate->chars-p)
                 (chars-readp raw-ppstate->chars-read-p)
                 (chars-unreadp raw-ppstate->chars-unread-p)
                 (lexmarksp raw-ppstate->lexmarks-p)
                 (ienvp raw-ppstate->ienvp)
                 (sizep raw-ppstate->size-p)
                 (macrosp raw-ppstate->macros-p)
                 ;; field readers:
                 (bytess-length raw-ppstate->bytess-length)
                 (bytessi raw-ppstate->bytes)
                 (bytess-current raw-ppstate->bytess-current)
                 (position raw-ppstate->position)
                 (chars-length raw-ppstate->chars-length)
                 (charsi raw-ppstate->char)
                 (chars-read raw-ppstate->chars-read)
                 (chars-unread raw-ppstate->chars-unread)
                 (lexmarks raw-ppstate->lexmarks)
                 (ienv raw-ppstate->ienv)
                 (size raw-ppstate->size)
                 (macros raw-ppstate->macros)
                 ;; field writers:
                 (resize-bytess raw-update-ppstate->bytess-length)
                 (update-bytessi raw-update-ppstate->bytes)
                 (update-bytess-current raw-update-ppstate->bytess-current)
                 (update-position raw-update-ppstate->position)
                 (resize-chars raw-update-ppstate->chars-length)
                 (update-charsi raw-update-ppstate->char)
                 (update-chars-read raw-update-ppstate->chars-read)
                 (update-chars-unread raw-update-ppstate->chars-unread)
                 (update-lexmarks raw-update-ppstate->lexmarks)
                 (update-ienv raw-update-ppstate->ienv)
                 (update-size raw-update-ppstate->size)
                 (update-macros raw-update-ppstate->macros))))

  ;; fixer:

  (define ppstate-fix (ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (if (ppstatep ppstate)
                    ppstate
                  (non-exec (create-ppstate)))
         :exec ppstate)
    ///
    (defrule ppstate-fix-when-ppstatep
      (implies (ppstatep ppstate)
               (equal (ppstate-fix ppstate)
                      ppstate))))

  ;; fixtype:

  (fty::deffixtype ppstate
    :pred ppstatep
    :fix ppstate-fix
    :equiv ppstate-equiv
    :define t
    :executablep nil)

  ;; normalize recognizers:

  (defrule raw-ppstate->bytess-p-becomes-byte-list-listp
    (equal (raw-ppstate->bytess-p x)
           (byte-list-listp x))
    :induct t
    :enable (raw-ppstate->bytess-p
             byte-list-listp))

  (defrule raw-ppstate->chars-p-becomes-char+position-listp
    (equal (raw-ppstate->chars-p x)
           (char+position-listp x))
    :induct t
    :enable (raw-ppstate->chars-p
             char+position-listp))

  (defrule raw-ppstate->lexmarks-p-becomes-lexmark-listp
    (equal (raw-ppstate->lexmarks-p x)
           (lexmark-listp x))
    :induct t
    :enable (raw-ppstate->lexmarks-p
             lexmark-listp))

  ;; needed for subsequent proofs:

  (local (in-theory (enable ppstate-fix
                            nfix
                            update-nth-array
                            byte-list-listp-of-resize-list
                            char+position-listp-of-resize-list
                            byte-list-listp-of-update-nth-strong
                            char+position-listp-of-update-nth-strong)))

  ;; readers:

  (define ppstate->bytess-length (ppstate)
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->bytess-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytess-length ppstate)))

  (define ppstate->bytes ((i natp) ppstate)
    :guard (< i (ppstate->bytess-length ppstate))
    :returns (bytes byte-listp)
    (mbe :logic (non-exec (raw-ppstate->bytes (nfix i) (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytes i ppstate))
    :prepwork ((local (in-theory (enable ppstate->bytess-length)))))

  (define ppstate->bytess-current (ppstate)
    :returns (bytess-current natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->bytess-current (ppstate-fix ppstate)))
         :exec (raw-ppstate->bytess-current ppstate)))

  (define ppstate->position (ppstate)
    :returns (position positionp)
    (mbe :logic (non-exec (raw-ppstate->position (ppstate-fix ppstate)))
         :exec (raw-ppstate->position ppstate)))

  (define ppstate->chars-length (ppstate)
    :returns (length natp)
    (mbe :logic (non-exec (raw-ppstate->chars-length (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-length ppstate)))

  (define ppstate->char ((i natp) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (char+pos char+position-p)
    (char+position-fix
     (mbe :logic (non-exec (raw-ppstate->char (nfix i) (ppstate-fix ppstate)))
          :exec (raw-ppstate->char i ppstate)))
    :prepwork ((local (in-theory (enable ppstate->chars-length)))))

  (define ppstate->chars-read (ppstate)
    :returns (chars-read natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->chars-read (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-read ppstate)))

  (define ppstate->chars-unread (ppstate)
    :returns (chars-unread natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->chars-unread (ppstate-fix ppstate)))
         :exec (raw-ppstate->chars-unread ppstate)))

  (define ppstate->lexmarks (ppstate)
    :returns (lexmarks lexmark-listp)
    (mbe :logic (non-exec (raw-ppstate->lexmarks (ppstate-fix ppstate)))
         :exec (raw-ppstate->lexmarks ppstate)))

  (define ppstate->ienv (ppstate)
    :returns (ienv ienvp)
    (mbe :logic (non-exec (raw-ppstate->ienv (ppstate-fix ppstate)))
         :exec (raw-ppstate->ienv ppstate)))

  (define ppstate->size (ppstate)
    :returns (size natp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (non-exec (raw-ppstate->size (ppstate-fix ppstate)))
         :exec (raw-ppstate->size ppstate)))

  (define ppstate->macros (ppstate)
    :returns (macros macro-tablep)
    (mbe :logic (non-exec (raw-ppstate->macros (ppstate-fix ppstate)))
         :exec (raw-ppstate->macros ppstate)))

  ;; writers:

  (define update-ppstate->bytess-length ((length natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->bytess-length (nfix length)
                                                    (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytess-length length ppstate)))

  (define update-ppstate->bytes ((i natp) (bytes byte-listp) ppstate)
    :guard (< i (ppstate->bytess-length ppstate))
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec (raw-update-ppstate->bytes (nfix i)
                                                     (byte-list-fix bytes)
                                                     (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytes i bytes ppstate))
    :guard-hints (("Goal" :in-theory (enable ppstate->bytess-length))))

  (define update-ppstate->bytess-current ((bytess-current natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->bytess-current (nfix bytess-current)
                                                     (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->bytess-current bytess-current ppstate)))

  (define update-ppstate->position ((position positionp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->position (position-fix position)
                                               (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->position position ppstate)))

  (define update-ppstate->chars-length ((length natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-length (nfix length)
                                                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-length length ppstate)))

  (define update-ppstate->char ((i natp) (char+pos char+position-p) ppstate)
    :guard (< i (ppstate->chars-length ppstate))
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (if (< (nfix i) (ppstate->chars-length ppstate))
                     (raw-update-ppstate->char (nfix i)
                                               (char+position-fix char+pos)
                                               (ppstate-fix ppstate))
                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->char i char+pos ppstate))
    :prepwork ((local (in-theory (enable ppstate->chars-length)))))

  (define update-ppstate->chars-read ((chars-read natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-read (nfix chars-read)
                                                 (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-read chars-read ppstate)))

  (define update-ppstate->chars-unread ((chars-unread natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->chars-unread (nfix chars-unread)
                                                   (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->chars-unread chars-unread ppstate)))

  (define update-ppstate->lexmarks ((lexmarks lexmark-listp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->lexmarks (lexmark-list-fix lexmarks)
                                               (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->lexmarks lexmarks ppstate)))

  (define update-ppstate->ienv ((ienv ienvp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->ienv (ienv-fix ienv)
                                           (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->ienv ienv ppstate)))

  (define update-ppstate->size ((size natp) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->size (nfix size) (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->size size ppstate)))

  (define update-ppstate->macros ((macros macro-tablep) ppstate)
    :returns (ppstate ppstatep)
    (mbe :logic (non-exec
                 (raw-update-ppstate->macros (macro-table-fix macros)
                                             (ppstate-fix ppstate)))
         :exec (raw-update-ppstate->macros macros ppstate)))

  ;; readers over writers:

  (defrule ppstate->bytess-length-of-update-ppstate->bytess-length
    (equal (ppstate->bytess-length
            (update-ppstate->bytess-length length ppstate))
           (lnfix length))
    :enable (ppstate->bytess-length
             update-ppstate->bytess-length))

  (defrule ppstate->bytess-current-of-update-ppstate->bytess-current
    (equal (ppstate->bytess-current
            (update-ppstate->bytess-current bytess-current ppstate))
           (nfix bytess-current))
    :enable (ppstate->bytess-current
             update-ppstate->bytess-current))

  (defrule ppstate->chars-length-of-update-ppstate->bytes
    (equal (ppstate->chars-length (update-ppstate->bytes i bytes ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->chars-length-of-update-ppstate->bytess-current
    (equal (ppstate->chars-length
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->bytess-current))

  (defrule ppstate->chars-length-of-update-ppstate->size
    (equal (ppstate->chars-length (update-ppstate->size size ppstate))
           (ppstate->chars-length ppstate))
    :enable (ppstate->chars-length
             update-ppstate->size))

  (defrule ppstate->chars-read-of-update-ppstate->bytes
    (equal (ppstate->chars-read (update-ppstate->bytes i bytes ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->chars-read-of-update-ppstate->bytess-current
    (equal (ppstate->chars-read
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->bytess-current))

  (defrule ppstate->chars-read-of-update-ppstate->size
    (equal (ppstate->chars-read (update-ppstate->size size ppstate))
           (ppstate->chars-read ppstate))
    :enable (ppstate->chars-read
             update-ppstate->size))

  (defrule ppstate->lexmarks-of-update-ppstate->bytes
    (equal (ppstate->lexmarks (update-ppstate->bytes i bytes ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->lexmarks-of-update-ppstate->bytess-current
    (equal (ppstate->lexmarks
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->bytess-current))

  (defrule ppstate->lexmarks-of-update-ppstate->position
    (equal (ppstate->lexmarks
            (update-ppstate->position position ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->position))

  (defrule ppstate->lexmarks-of-update-ppstate->char
    (equal (ppstate->lexmarks (update-ppstate->char i char ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->char
             ppstate->chars-length))

  (defrule ppstate->lexmarks-of-update-ppstate->chars-read
    (equal (ppstate->lexmarks
            (update-ppstate->chars-read chars-read ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->chars-read))

  (defrule ppstate->lexmarks-of-update-ppstate->chars-unread
    (equal (ppstate->lexmarks
            (update-ppstate->chars-unread chars-unread ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->chars-unread))

  (defrule ppstate->lexmarks-of-update-ppstate->size
    (equal (ppstate->lexmarks (update-ppstate->size size ppstate))
           (ppstate->lexmarks ppstate))
    :enable (ppstate->lexmarks
             update-ppstate->size))

  (defrule ppstate->size-of-update-ppstate->bytes
    (equal (ppstate->size (update-ppstate->bytes i bytes ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->bytes
             ppstate->bytess-length))

  (defrule ppstate->size-of-update-ppstate->bytess-current
    (equal (ppstate->size
            (update-ppstate->bytess-current bytess-current ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->bytess-current))

  (defrule ppstate->size-of-update-ppstate->position
    (equal (ppstate->size (update-ppstate->position position ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->position))

  (defrule ppstate->size-of-update-ppstate->char
    (equal (ppstate->size (update-ppstate->char i char+pos ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->char
             ppstate->chars-length))

  (defrule ppstate->size-of-update-ppstate->chars-read
    (equal (ppstate->size (update-ppstate->chars-read chars-read ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->chars-read))

  (defrule ppstate->size-of-update-ppstate->chars-unread
    (equal (ppstate->size (update-ppstate->chars-unread chars-unread ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->chars-unread))

  (defrule ppstate->size-of-update-ppstate->lexmarks
    (equal (ppstate->size (update-ppstate->lexmarks lexmarks ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->lexmarks))

  (defrule ppstate->size-of-update-ppstate->size
    (equal (ppstate->size (update-ppstate->size size ppstate))
           (lnfix size))
    :enable (ppstate->size
             update-ppstate->size))

  (defrule ppstate->size-of-update-ppstate->macros
    (equal (ppstate->size (update-ppstate->macros macros ppstate))
           (ppstate->size ppstate))
    :enable (ppstate->size
             update-ppstate->macros))

  ;; writers over readers:

  (defrule update-ppstate->chars-read-of-ppstate->chars-read
    (equal (update-ppstate->chars-read
            (ppstate->chars-read ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->chars-read
             ppstate->chars-read))

  (defrule update-ppstate->chars-read-of-ppstate->chars-unread
    (equal (update-ppstate->chars-unread
            (ppstate->chars-unread ppstate) ppstate)
           (ppstate-fix ppstate))
    :enable (update-ppstate->chars-unread
             ppstate->chars-unread))

  ;; keep recognizer disabled:

  (in-theory (disable ppstatep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ppstate->gcc ((ppstate ppstatep))
  :returns (gcc booleanp)
  :short "Flag saying whether GCC extensions are supported or not."
  (c::version-gccp (ienv->version (ppstate->ienv ppstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ppstate ((data byte-listp)
                      (file-recursion-limit posp)
                      (macros macro-tablep)
                      (ienv ienvp)
                      ppstate)
  :returns (ppstate ppstatep)
  :short "Initialize the preprocessor state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the state when we start preprocessing a file.
     It is built from
     (the data of) a file to preprocess,
     a limit on the number of files recursively preprocessed/included,
     the current table of macros in scope,
     and an implementation environment.")
   (xdoc::p
    "The array of byte lists is resized to the file recursion limit,
     which is set by the caller of this function.
     The bytes of the file are stored into the first element of the array,
     to which the current byte list index is set to point.
     The position is the initial one.
     There are no read or unread characters,
     and no lexmarks pending.
     The macro table is obtained by pushing a new scope for the file.
     We also resize the arrays of characters to the number of data bytes,
     which is sufficient because each character takes at least one byte."))
  (b* ((ppstate (update-ppstate->bytess-length (pos-fix file-recursion-limit)
                                               ppstate))
       (ppstate (update-ppstate->bytes 0 (byte-list-fix data) ppstate))
       (ppstate (update-ppstate->bytess-current 0 ppstate))
       (ppstate (update-ppstate->position (position-init) ppstate))
       (ppstate (update-ppstate->chars-length (len data) ppstate))
       (ppstate (update-ppstate->chars-read 0 ppstate))
       (ppstate (update-ppstate->chars-unread 0 ppstate))
       (ppstate (update-ppstate->lexmarks nil ppstate))
       (ppstate (update-ppstate->ienv ienv ppstate))
       (ppstate (update-ppstate->size (len data) ppstate))
       (ppstate (update-ppstate->macros (macro-table-push macros) ppstate)))
    ppstate)
  :guard-hints
  (("Goal"
    :in-theory
    (enable ppstate->bytess-length-of-update-ppstate->bytess-length))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-lexmark ((lexmark lexmarkp) (ppstate ppstatep))
  :returns (new-ppstate ppstatep)
  :short "Push a lexmark onto the pending lexmark list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when unreading a lexeme,
     and also when expaning a macro."))
  (b* ((new-lexmarks (cons lexmark (ppstate->lexmarks ppstate)))
       (new-size (1+ (ppstate->size ppstate)))
       (ppstate (update-ppstate->lexmarks new-lexmarks ppstate))
       (ppstate (update-ppstate->size new-size ppstate)))
    ppstate)

  ///

  (defret ppstate->size-of-push-lexmark
    (equal (ppstate->size new-ppstate)
           (1+ (ppstate->size ppstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ppstate-add-bytes ((bytes byte-listp) (ppstate ppstatep))
  :returns (mv erp (new-ppstate ppstatep :hyp (ppstatep ppstate)))
  :short "Add some input bytes to a preprocessing state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when a file included via a @('#include') directive
     is expanded in place:
     as explained in @(tsee ppstate),
     we put its bytes into the next element of the array of byte lists.
     It is an internal error if there is no next element in the array:
     the file recursion limit has been exceeded."))
  (b* ((ppstate (ppstate-fix ppstate))
       ((reterr) ppstate)
       (bytess-length (ppstate->bytess-length ppstate))
       (bytess-current (ppstate->bytess-current ppstate))
       (size (ppstate->size ppstate))
       (bytess-current (1+ bytess-current))
       ((unless (< bytess-current bytess-length))
        (reterr (msg "Exceeded file recursion limit of ~x0." bytess-length)))
       (ppstate (update-ppstate->bytes bytess-current bytes ppstate))
       (ppstate (update-ppstate->bytess-current bytess-current ppstate))
       (ppstate (update-ppstate->size (+ size (len bytes)) ppstate)))
    (retok ppstate)))
