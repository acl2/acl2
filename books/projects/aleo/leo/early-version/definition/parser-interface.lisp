; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "lexer")
(include-book "tokenizer")
(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-interface
  :parents (lexing-and-parsing)
  :short "API functions for parsing Leo programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This section defines convenient functions
     (whose names start with @('parse-from-'))
     for parsing Leo programs from:")
   (xdoc::ul
    (xdoc::li "a list of Unicode code points")
    (xdoc::li "a list of UTF-8 bytes")
    (xdoc::li "an ACL2 string (in UTF-8)")
    (xdoc::li "a file"))
   (xdoc::p
    "By \"parsing\", we mean lexing, tokenization, and parsing, with
     the result being a CST (concrete syntax tree) for a Leo @('file'),
     and optionally the sequence of lexeme CSTs (see below).")
   (xdoc::p
    "Additionally, we define functions for parsing specific Leo constructs
     from strings: @('file'), @('statement'), @('expression'), and @('token').
     These can be used for the @('<leo>/tests/parser') namespaces
     @('Parse'), @('ParseExpression'), @('ParseStatement'), and @('Token'),
     where @('<leo>') is the GitHub repo of the Leo compiler.
     See @(see parse-fragment-to-CST).  For simply checking if a given
     string can be fully parsed, we define predicates @('xxx-parses?') for
     the same set of supported rulenames.")
   (xdoc::p
    "The API functions whose names end in @('+') also return the full sequence
     of lexemes from the lexer.  This can be valuable for checking correctness,
     for proving theorems, and for locating specific tokens within the
     input."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper functions

;; Helper function, to handle the parsing after lexing and tokenizing,
;; and to support specific grammar rule names.
;;
(define tokens-to-CST ((rule-name stringp) (tokens abnf::tree-listp))
  :returns (tree abnf::tree-resultp)
  :short "Parse list of @('tokens') for a supported grammar rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Supported grammar rule names are @('file'), @('statement'), @('expression'),
     and @('token') (expressed as strings).")
   (xdoc::p
    "Given a list of tokens resulting from lexing and tokenizing,
     this function attempts to parse the tokens into a CST for the
     the given grammar rule name.")
   (xdoc::p
    "In the case of @('rule-name') being @('\"token\"'), the rule names
     at the top of the trees in the @('tokens') argument
     are actually the rule names on the right hand
     side of the rule for @('token'), although that is not checked here.")
   (xdoc::p
    "If the given rule cannot be parsed or if there are tokens left over,
     then a @(see reserr) is returned."))
  (b* (((unless (member-equal rule-name '("file" "statement" "expression" "token")))
        (reserrf (cons :not-yet-supported-top-level-rule-name rule-name)))
       ;; "file" can be empty (zero definitions)
       ;; but "expression" and "statement" and "token" must have at least one token
       ((when (and (null tokens)
                   (not (equal rule-name "file"))))
        (reserrf (cons :not-enough-tokens rule-name)))
       ((mv cst next-token rest-input)
        (cond ((equal rule-name "file") (parse-file tokens))
              ((equal rule-name "statement")
               (parse-statement (first tokens) (rest tokens)))
              ((equal rule-name "expression")
               (parse-expression (first tokens) (rest tokens)))
              ((equal rule-name "token")
               ;; parse-token has a different signature, so we adapt the output
               (b* (((mv tree? rest-tokens) (parse-token tokens))
                    ((unless (abnf::treep tree?))
                     ;; caller expects a reserrp, not a nil
                     (mv (reserrf (cons :no-more-tokens tokens)) nil nil))
                    ((when (null rest-tokens))
                     (mv tree? nil nil)))
                 (mv tree? (car rest-tokens) (cdr rest-tokens))))
              (t
               (mv (reserrf (cons :not-yet-supported-top-level-rule-name rule-name))
                   nil nil))))
       ((when (reserrp cst)) cst)
       ((when (or next-token rest-input))
        (reserrf (list :not-all-tokens-parsed cst next-token rest-input))))
    cst)
  :guard-hints (("Goal" :in-theory (enable parse-token))))

;; Helper function, to handle the tokenizing and parsing after lexing,
;; and to support specific grammar rule names.
;;
(define lexemes-to-CST+ ((rule-name stringp) (lexemes abnf::tree-list-resultp))
  :returns (mv (tree abnf::tree-resultp) (lexemes abnf::tree-listp))
  :short "Tokenize and parse list of @('lexemes') for a supported grammar rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Supported grammar rule names are @('file'), @('statement'), @('expression'),
     and @('token').")
   (xdoc::p
    "Given a list of lexemes resulting from lexing,
     this function tokenizes the lexemes and
     then attempts to parse the tokens into a CST for the
     the given grammar rule name.")
   (xdoc::p
    "If the given rule cannot be parsed or if there are tokens left over,
     then a @(see reserr) is returned."))
  (b* (((when (reserrp lexemes))
        (mv (reserrf (cons :lexing-failed lexemes)) nil))
       (lexemes (abnf::tree-list-fix lexemes))
       (tokens (filter-and-lower-tokens lexemes))
       ((when (reserrp tokens))
        (mv (reserrf (cons :tokenizing-failed tokens)) lexemes))
       (cst (tokens-to-CST rule-name tokens)))
    (mv cst lexemes)))

;; Consider defining lexemes-to-CST  (not returning the lexemes)
;; if it is more convenient for callers.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; API functions that do lexing, tokenization, and parsing
;; for a given grammar rule name.

;; When rule-name is "file", these functions do the same thing as
;; 'parse-from-string+' and 'parse-from-string'.

(define parse-fragment-to-CST+ ((rule-name stringp) (source-code stringp))
  :returns (mv (tree abnf::tree-resultp) (lexemes abnf::tree-listp))
  :short "Parse source string for a supported grammar rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Supported grammar rule names are @('file'), @('statement'), @('expression'),
     and @('token').")
   (xdoc::p
    "If the given rule cannot be parsed or if there are tokens left over,
     then a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('source-code'), when converted to codes, is required to be valid
     UTF-8.")
   (xdoc::p
    "As a second value, returns the full list of lexemes, including comments and
     whitespace.  If the first value is an error, the second value is undefined."))
  (b* ((lexemes-or-err (lexemize-leo-from-string source-code)))
    (lexemes-to-CST+ rule-name lexemes-or-err)))

(define parse-fragment-to-CST ((rule-name stringp) (source-code stringp))
  :returns (tree abnf::tree-resultp)
  :short "Parse source string for a supported grammar rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Supported grammar rule names are @('file'), @('statement'), @('expression'),
     and @('token').")
   (xdoc::p
    "If the given rule cannot be parsed or if there are tokens left over,
     then a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('source-code'), when converted to codes, is required to be valid
     UTF-8."))
  (b* (((mv cst ?lexemes) (parse-fragment-to-CST+ rule-name source-code)))
    cst))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predicates on whether specific constructs can be parsed.
;; Does not return the CST or lexemes.

(define file-parses? ((file-contents stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo file CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Checks that the given string is lexed, tokenized, and parsed successfully
     and checks that the CST from parsing has the root rule name @('file').")
   (xdoc::p
    "Does not check that the lexemes have the same fringe as the given string.
     For that you want @(see file-parses-same-fringe?)."))
  (b* ((tree? (parse-fragment-to-CST "file" file-contents)))
    (and (abnf::treep tree?)
         (abnf-tree-with-root-p tree? "file"))))

(define file-parses-same-fringe? ((file-contents stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo file CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as @(see file-parses?), but this does some additional checks, so
     it is better for testing."))
  (b* (((mv tree? lexemes) (parse-fragment-to-CST+ "file" file-contents)))
    (and (abnf::treep tree?)
         (abnf-tree-with-root-p tree? "file")
         (abnf-tree-list-with-root-p lexemes "lexeme")
         (equal (abnf::tree-list->string lexemes) ; actually a codepoint list
                (acl2::utf8=>ustring (string=>nats file-contents))))))

(define statement-parses? ((statement-string stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo statement CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Checks that the given string is lexed, tokenized, and parsed successfully
     and checks that the CST from parsing has the root rule name @('statement').")
   (xdoc::p
    "Does not check that the lexemes have the same fringe as the given string.
     For that you want @(see statement-parses-same-fringe?)."))
  (b* ((tree? (parse-fragment-to-CST "statement" statement-string)))
    (and (abnf::treep tree?)
         (abnf-tree-with-root-p tree? "statement"))))

(define statement-parses-same-fringe? ((statement-string stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo statement CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as @(see statement-parses?), but this does some additional checks, so
     it is better for testing."))
  (b* (((mv tree? lexemes) (parse-fragment-to-CST+ "statement" statement-string)))
    (and (abnf::treep tree?)
         (abnf-tree-with-root-p tree? "statement")
         (abnf-tree-list-with-root-p lexemes "lexeme")
         (equal (abnf::tree-list->string lexemes)
                (acl2::utf8=>ustring (string=>nats statement-string))))))

(define expression-parses? ((expression-string stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo expression CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Checks that the given string is lexed, tokenized, and parsed successfully
     and checks that the CST from parsing has the root rule name @('expression').")
   (xdoc::p
    "Does not check that the lexemes have the same fringe as the given string.
     For that you want @(see expression-parses-same-fringe?)."))
  (b* ((tree? (parse-fragment-to-CST "expression" expression-string)))
    (and (abnf::treep tree?)
         (abnf-tree-with-root-p tree? "expression"))))

(define expression-parses-same-fringe? ((expression-string stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo expression CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as @(see expression-parses?), but this does some additional checks, so
     it is better for testing."))
  (b* (((mv tree? lexemes) (parse-fragment-to-CST+ "expression" expression-string)))
    (and (abnf::treep tree?)
         (abnf-tree-with-root-p tree? "expression")
         (abnf-tree-list-with-root-p lexemes "lexeme")
         (equal (abnf::tree-list->string lexemes)
                (acl2::utf8=>ustring (string=>nats expression-string))))))

(define token-parses? ((token-string stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo token CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Checks that the given string is lexed, tokenized, and parsed successfully
     and checks that the CST from parsing has the root rule name @('token').")
   (xdoc::p
    "Does not check that the lexemes have the same fringe as the given string.
     For that you want @(see token-parses-same-fringe?)."))
  (b* ((tree? (parse-fragment-to-CST "token" token-string))
       ((unless (abnf::treep tree?))
        nil)
       (rulename (abnf::check-tree-nonleaf? tree?))
       ((unless (stringp rulename))
        nil)
       ;; the following list of token types should be calculated from the grammar
       ((unless (member-equal rulename '("keyword" "identifier" "atomic-literal"
                                         "numeral" "annotation" "symbol")))
        nil))
    ;; this does some more checks that the tree is well formed
    (abnf-tree-with-root-p tree? rulename)))

(define token-parses-same-fringe? ((token-string stringp))
  :returns (yes/no booleanp)
  :short "Checks if the given string can be parsed to a Leo token CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as @(see token-parses?), but this does some additional checks, so
     it is better for testing."))
  (b* (((mv tree? lexemes) (parse-fragment-to-CST+ "token" token-string))
       ((unless (abnf::treep tree?))
        nil)
       (rulename (abnf::check-tree-nonleaf? tree?))
       ((unless (stringp rulename))
        nil)
       ;; the following list of token types should be calculated from the grammar
       ((unless (member-equal rulename '("keyword" "identifier" "atomic-literal"
                                         "numeral" "annotation" "symbol")))
        nil))
    ;; this does some more checks that the tree is well formed
    (and (abnf-tree-with-root-p tree? rulename)
         (abnf-tree-list-with-root-p lexemes "lexeme")
         (equal (abnf::tree-list->string lexemes)
                (acl2::utf8=>ustring (string=>nats token-string))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; API functions that do lexing, tokenization, and parsing
;; of a top-level Leo file, with various input data types.

;; The first set of functions return a CST and the full list of lexemes
;; including comments and whitespace.
;; The list of lexemes is useful for verification purposes.
;; We add "+" to the function name to indicate that the lexemes are also
;; returned.

;; The second set of functions discards the lexemes, and is more
;; convenient for execution.

(define parse-from-codepoints+ ((codepoints nat-listp))
  :returns (mv (tree abnf::tree-resultp) (lexemes abnf::tree-listp))
  :short "Parse Unicode code points into a CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a Leo source file expressed
     as a list of Unicode code points.  Returns a @('file') CST,
     and the full list of lexemes, including comments and whitespace.")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes all the bytes or a @(see reserr) is returned."))
  (b* ((lexemes-or-err (lexemize-leo codepoints)))
    (lexemes-to-CST+ "file" lexemes-or-err)))

(define parse-from-bytes+ ((leo-bytes nat-listp))
  :returns (mv (tree abnf::tree-resultp) (lexemes abnf::tree-listp))
  :short "Parse UTF-8 bytes into a CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a Leo source file expressed
     as a list of UTF-8 bytes.  Returns a @('file') CST,
     and the full list of lexemes, including comments and whitespace.")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes all the bytes or a @(see reserr) is returned."))
  (b* ((lexemes-or-err (lexemize-leo-from-bytes leo-bytes)))
    (lexemes-to-CST+ "file" lexemes-or-err)))

(define parse-from-string+ ((leo-string stringp))
  :returns (mv (tree abnf::tree-resultp) (lexemes abnf::tree-listp))
  :short "Parse UTF-8 ACL2 string into a CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a Leo source file expressed
     as a string of ACL2 characters whose char-codes are UTF-8 bytes.
     Returns a @('file') CST,
     and the full list of lexemes, including comments and whitespace.")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes the entire string or a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('leo-string'), when converted to codes, is required to be valid
     UTF-8."))
  (b* ((lexemes-or-err (lexemize-leo-from-string leo-string)))
    (lexemes-to-CST+ "file" lexemes-or-err)))

(define parse-from-file-at-path+ ((path stringp) state)
  :returns (mv (tree abnf::tree-resultp)
               (lexemes abnf::tree-listp)
               state)
  :short "Parse a Leo file at a path."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function attempts to parse a Leo source file at a given path.
     If parsing is successful, we return an ABNF @('file') tree (and state),
     along with the list of lexemes that the file consists of
     (these cannot be completely derived from the @('file') tree,
     which only contains tokens,
     while the lexemes also include whitespace and comments).
     If parsing is unsuccessful, we return an error value as first result,
     and @('nil') as list of lexemes.")
   (xdoc::p
    "Since Leo files are encoded in UTF-8,
     we use the Unicode library function @('read-utf8')
     to obtain a list of Unicode code points.
     If the reading or UTF-8 decoding fails,
     that function returns an ACL2 string instead of a list of code points:
     we return that string as part of the error value,
     as it may be informative.")
   (xdoc::p
    "If reading and decoding are successful, we call @(tsee parse-from-codepoints+),
     and we inspect its results.
     If there is an error,
     we try to provide an indication of where the error occurs in the file.
     For now we simply return the position in the file by
     turning the lexemes returned into a list of Unicode code points (not bytes)
     and counting such code points.
     While this may not be quite exactly where the error occurs
     (as the parser has not been optimized for error reporting yet),
     it should be at least close enough to significantly narrow the search."))
  (b* (((mv unicodes state) (acl2::read-utf8 (str-fix path) state))
       ((unless (nat-listp unicodes))
        (mv (reserrf unicodes)
            nil
            state))
       ((mv tree lexemes) (parse-from-codepoints+ unicodes))
       ;; Try to indicate where the error is, but that depends on
       ;; whether the lexemes before the error are returned
       ;; from the callee.
       ((when (reserrp tree))
        (b* ((pos (len (abnf::tree-list->string lexemes))))
          (mv (reserrf (list :position pos :error tree)) nil state))))
    (mv tree
        lexemes
        state))
  :hooks (:fix)
  :prepwork ((local (in-theory (disable acl2::read-utf8)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parsing full Leo file from various input types, without returning lexemes.

(define parse-from-codepoints ((codepoints nat-listp))
  :returns (tree abnf::tree-resultp)
  :short "Parse Unicode code points into a CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a Leo source file expressed
     as a list of Unicode code points.  Returns a @('file') CST.")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes all the bytes or a @(see reserr) is returned."))
  (b* (((mv file-cst ?lexemes) (parse-from-codepoints+ codepoints)))
    file-cst))

(define parse-from-bytes ((leo-bytes nat-listp))
  :returns (tree abnf::tree-resultp)
  :short "Parse UTF-8 bytes into a CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a Leo source file expressed
     as a list of UTF-8 bytes.  Returns a @('file') CST.")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes all the bytes or a @(see reserr) is returned."))
  (b* (((mv file-cst ?lexemes) (parse-from-bytes+ leo-bytes)))
    file-cst))

(define parse-from-string ((leo-string stringp))
  :returns (tree abnf::tree-resultp)
  :short "Parse UTF-8 ACL2 string into a CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a Leo source file expressed
     as a string of acl2 characters whose char-codes are UTF-8 bytes.
     Returns a @('file') CST.")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes the entire string or a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('leo-string'), when converted to codes, is required to be valid
     UTF-8."))
  (b* (((mv file-cst ?lexemes) (parse-from-string+ leo-string)))
    file-cst))

(define parse-from-file-at-path ((path stringp) state)
  :returns (mv (tree abnf::tree-resultp)
               state)
  :short "Parse a Leo file at a path."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function attempts to parse a Leo source file at a given path.
     If parsing is successful, we return an ABNF @('file') tree (and state).
     If parsing is unsuccessful, we return an error value as first result.")
   (xdoc::p
    "For more details see @(see parse-from-file-at-path+).  The only difference
     between that function and this one is that this one doesn't bother to
     return the lexemes."))
  (b* (((mv file-cst ?lexemes  state) (parse-from-file-at-path+ path state)))
    (mv file-cst state)))
