; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "spans")
(include-book "keywords")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tokens
  :parents (syntax-for-tools)
  :short "Rust tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce fixtypes for Rust tokens
     ["
    (xdoc::ahref "https://doc.rust-lang.org/1.87.0/reference/tokens.html"
                 "Reference: Tokens; rustc 1.87.0")
    "],
     the output of the lexer and the input of the parser
     (via token trees, introduced separately).
     Since keyword classification is edition-dependent
     (see @(see keywords)),
     and lexing is edition-parameterized anyway,
     keywords are a token kind of their own,
     separate from identifiers;
     weak keywords are lexed as identifiers.")
   (xdoc::p
    "Following rustc's lexer, literal tokens store
     their content as written
     (e.g. digits with any @('_') separators, escapes undecoded)
     together with any suffix;
     decoding and validation happen in later phases.
     This choice preserves the information needed
     to reprint tokens exactly as read.")
   (xdoc::p
    "The delimiters @('( )'), @('[ ]'), and @('{ }')
     are their own token kinds, distinct from punctuation,
     because they are structural in token trees.
     The lone underscore @('_') is a punctuation token
     ["
    (xdoc::ahref
     "https://doc.rust-lang.org/1.87.0/reference/tokens.html#punctuation"
     "Reference: Punctuation")
    "],
     not an identifier.
     Doc comments are tokens
     (they turn into attributes during parsing),
     while non-doc comments and whitespace are trivia:
     they appear only in the lexeme layer,
     which the lexer produces
     and which supports exact reprinting of source text."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *punctuation*
  :short "The punctuation tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the 47 punctuation tokens of
     ["
    (xdoc::ahref
     "https://doc.rust-lang.org/1.87.0/reference/tokens.html#punctuation"
     "Reference: Punctuation")
    "],
     including the lone underscore @('_'),
     and including @('<-') and @('~'),
     which are currently unused by the language but are lexed as tokens.")
   (xdoc::p
    "The value of a @(':punct') token is expected to be
     one of these strings;
     see @(tsee punctuationp).
     Note that the lexer applies maximal munch,
     e.g. @('>>=') lexes as one token,
     and that the parser may later split tokens like @('>>')
     when closing nested generic argument lists."))
  (list "+" "-" "*" "/" "%" "^" "!" "&" "|"
        "&&" "||" "<<" ">>"
        "+=" "-=" "*=" "/=" "%=" "^=" "&=" "|=" "<<=" ">>="
        "=" "==" "!=" ">" "<" ">=" "<="
        "@" "_" "." ".." "..." "..="
        "," ";" ":" "::"
        "->" "=>" "<-"
        "#" "$" "?" "~"))

(assert-event (string-listp *punctuation*))
(assert-event (equal (len *punctuation*) 47))
(assert-event (no-duplicatesp-equal *punctuation*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punctuationp ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if a string is a punctuation token."
  (and (member-equal (str-fix string) *punctuation*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum delim
  :short "Fixtype of delimiters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parentheses, square brackets, and curly braces
     ["
    (xdoc::ahref
     "https://doc.rust-lang.org/1.87.0/reference/tokens.html#delimiters"
     "Reference: Delimiters")
    "].
     A delimiter kind, together with an opening/closing indication,
     forms a delimiter token; see @(tsee token).
     In token trees, a matched pair of delimiter tokens
     becomes a delimited group."))
  (:paren ())
  (:bracket ())
  (:brace ())
  :pred delimp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-delim
  :short "A delimiter witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type delimp
  :body (delim-paren))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum radix
  :short "Fixtype of radixes of integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Decimal (no prefix), binary (@('0b')),
     octal (@('0o')), and hexadecimal (@('0x'))."))
  (:dec ())
  (:bin ())
  (:oct ())
  (:hex ())
  :pred radixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-lit
  :short "Fixtype of integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "An integer literal consists of a radix,
     the digits as written
     (without the radix prefix, and
     possibly containing @('_') separators),
     and a suffix.")
   (xdoc::p
    "The suffix is the identifier-shaped text
     immediately following the digits,
     as written; the empty string means no suffix.
     At the lexical level any such suffix is accepted
     (e.g. @('1px') lexes as the integer 1 with suffix @('\"px\"'));
     only later phases restrict suffixes
     to the standard ones (@('u8'), ..., @('usize'),
     @('i8'), ..., @('isize'), and,
     via type inference reinterpretation, @('f32') and @('f64')).")
   (xdoc::p
    "The numeric value of the literal is not stored;
     it is computed by later phases from the digits.
     Keeping the digits as written supports exact reprinting."))
  ((radix radix)
   (digits string)
   (suffix string))
  :pred int-litp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-int-lit
  :short "An integer-literal witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type int-litp
  :body (make-int-lit :radix (radix-dec) :digits "" :suffix ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lit
  :short "Fixtype of literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only model integer literals.
     The other kinds
     (float, character, string, raw string,
     byte, byte string, raw byte string,
     C string, raw C string)
     will be added as the lexer grows to cover them."))
  (:int ((int int-lit)))
  :pred litp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lit
  :short "A literal witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type litp
  :body (lit-int (irr-int-lit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum doc-style
  :short "Fixtype of doc comment styles."
  :long
  (xdoc::topstring
   (xdoc::p
    "Outer doc comments (@('///') and @('/** */'))
     document the item that follows them;
     inner doc comments (@('//!') and @('/*! */'))
     document the enclosing item."))
  (:outer ())
  (:inner ())
  :pred doc-stylep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum token
  :short "Fixtype of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "An identifier token stores its name
     (without the @('r#') prefix if raw)
     and whether it is raw.
     Weak keywords and the path segment keywords used as names
     are identifier tokens;
     strict and reserved keywords are keyword tokens
     (classified per edition at lexing time; see @(see keywords)).
     A side condition on lexing is that
     a raw identifier must not be
     @('crate'), @('self'), @('super'), or @('Self').")
   (xdoc::p
    "A lifetime token stores its name
     without the leading @('\\''),
     and without the @('r#') prefix if raw
     (raw lifetimes such as @('\\'r#fn') exist since rustc 1.84);
     the anonymous lifetime @('\\'_') has name @('\"_\"').")
   (xdoc::p
    "A punctuation token stores its text,
     expected to satisfy @(tsee punctuationp).")
   (xdoc::p
    "A doc comment token stores its style,
     whether it is block-form,
     and its content text
     (between the opening and closing markers, exclusive)."))
  (:ident ((name string)
           (raw bool)))
  (:keyword ((name string)))
  (:lifetime ((name string)
              (raw bool)))
  (:lit ((lit lit)))
  (:punct ((value string)))
  (:open-delim ((delim delim)))
  (:close-delim ((delim delim)))
  (:doc-comment ((style doc-style)
                 (block bool)
                 (content string)))
  :pred tokenp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-token
  :short "A token witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type tokenp
  :body (token-ident "" nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist token-list
  :short "Fixtype of lists of tokens."
  :elt-type token
  :true-listp t
  :elementp-of-nil nil
  :pred token-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod token+span
  :short "Fixtype of tokens with spans."
  ((token token)
   (span span))
  :pred token+span-p)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-token+span
  :short "A token-with-span witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type token+span-p
  :body (make-token+span :token (irr-token) :span (irr-span)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist token+span-list
  :short "Fixtype of lists of tokens with spans."
  :elt-type token+span
  :true-listp t
  :elementp-of-nil nil
  :pred token+span-listp)

;;;;;;;;;;;;;;;;;;;;

(defrule token+span-listp-of-append
  (implies (and (token+span-listp x)
                (token+span-listp y))
           (token+span-listp (append x y)))
  :induct t
  :enable binary-append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lexeme
  :short "Fixtype of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token or trivia:
     whitespace, or a non-doc comment.
     The lexer produces lexemes;
     tokenization filters out the trivia.
     Keeping the trivia, with its text,
     supports exact reprinting of source files.")
   (xdoc::p
    "A whitespace lexeme stores its text as written.
     A comment lexeme stores whether it is block-form
     and its content text
     (between the opening and closing markers, exclusive);
     nested block comments are a single comment lexeme."))
  (:token ((token token)))
  (:whitespace ((content string)))
  (:comment ((block bool)
             (content string)))
  :pred lexemep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lexeme
  :short "A lexeme witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type lexemep
  :body (lexeme-whitespace ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist lexeme-list
  :short "Fixtype of lists of lexemes."
  :elt-type lexeme
  :true-listp t
  :elementp-of-nil nil
  :pred lexeme-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Basic checks that the fixtypes fit together as intended.

(assert-event (tokenp (token-ident "foo" nil)))
(assert-event (tokenp (token-ident "union" nil))) ; weak keyword = identifier
(assert-event (tokenp (token-keyword "fn")))
(assert-event (tokenp (token-lifetime "a" nil)))
(assert-event (tokenp (token-lifetime "_" nil)))
(assert-event (punctuationp "->"))
(assert-event (punctuationp "_"))
(assert-event (not (punctuationp "**")))
(assert-event (tokenp (token-punct "->")))
(assert-event (tokenp (token-lit (lit-int (make-int-lit :radix (radix-hex)
                                                        :digits "7f_ff"
                                                        :suffix "u16")))))
(assert-event (tokenp (token-open-delim (delim-brace))))
(assert-event (lexemep (lexeme-comment t " nested /* ok */ ")))
(assert-event (token+span-listp (list (make-token+span
                                       :token (token-keyword "fn")
                                       :span (irr-span)))))
