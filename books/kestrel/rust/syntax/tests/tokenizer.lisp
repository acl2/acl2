; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../tokenizer")

; Tests of the tokenizer.
; We check the resulting tokens (and some spans),
; in both editions where the difference matters [SC6] [SC15].

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviations for the tests.

(defmacro toks (string &optional (edition '(rust::edition-2024)))
  `(tokenize-rust-from-string ,string ,edition))

; The list of bare tokens (spans stripped), or :error.

(defun toks-only-aux (tokens+spans)
  (if (atom tokens+spans)
      nil
    (cons (token+span->token (car tokens+spans))
          (toks-only-aux (cdr tokens+spans)))))

(defun toks-only (tokens+spans)
  (if (reserrp tokens+spans)
      :error
    (toks-only-aux tokens+spans)))

(defmacro test-tokens (string expected)
  `(assert-event (equal (toks-only (toks ,string)) ,expected)))

(defmacro test-tokens-2021 (string expected)
  `(assert-event (equal (toks-only (toks ,string (rust::edition-2021)))
                        ,expected)))

(defmacro test-tokenize-fail (string)
  `(assert-event (reserrp (toks ,string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Trivia produces no tokens.

(test-tokens "" nil)
(test-tokens " " nil)
(test-tokens "// comment" nil)
(test-tokens "/* a /* nested */ b */" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifiers and keywords [SC6].

(test-tokens "foo" (list (token-ident "foo" nil)))
(test-tokens "fn" (list (token-keyword "fn")))
(test-tokens "match" (list (token-keyword "match")))
(test-tokens "abstract" (list (token-keyword "abstract"))) ; reserved
(test-tokens "union" (list (token-ident "union" nil))) ; weak keyword
(test-tokens "raw" (list (token-ident "raw" nil))) ; weak keyword

; The gen keyword is 2024-only.

(test-tokens "gen" (list (token-keyword "gen")))
(test-tokens-2021 "gen" (list (token-ident "gen" nil)))

; Raw identifiers, including [SC5].

(test-tokens "r#fn" (list (token-ident "fn" t)))
(test-tokens "r#union" (list (token-ident "union" t)))
(test-tokens "r#foo" (list (token-ident "foo" t)))
(test-tokenize-fail "r#crate")
(test-tokenize-fail "r#self")
(test-tokenize-fail "r#super")
(test-tokenize-fail "r#Self")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lifetimes: the name without the quote, and without r# if raw.

(test-tokens "'a" (list (token-lifetime "a" nil)))
(test-tokens "'_" (list (token-lifetime "_" nil)))
(test-tokens "'static" (list (token-lifetime "static" nil)))
(test-tokens "'r" (list (token-lifetime "r" nil)))
(test-tokens "'r#fn" (list (token-lifetime "fn" t)))
(test-tokens "'r#_a" (list (token-lifetime "_a" t)))
(test-tokens-2021 "'r#gen" (list (token-lifetime "gen" t)))
(test-tokens "&'a str"
             (list (token-punct "&")
                   (token-lifetime "a" nil)
                   (token-ident "str" nil)))

; Raw lifetimes with the [SC5] exclusions, as in rustc's
; tests/ui/lifetimes/raw/raw-lt-invalid-raw-id.rs ('r#_ is rejected
; by the lexer; see the lexer tests).

(test-tokenize-fail "'r#crate")
(test-tokenize-fail "'r#self")
(test-tokenize-fail "'r#super")
(test-tokenize-fail "'r#Self")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Doc comments become tokens; other comments do not (see above).

(test-tokens "///doc"
             (list (token-doc-comment (doc-style-outer) nil "doc")))
(test-tokens "///"
             (list (token-doc-comment (doc-style-outer) nil "")))
(test-tokens "//!doc"
             (list (token-doc-comment (doc-style-inner) nil "doc")))
(test-tokens "////plain" nil) ; four slashes: plain comment, not doc

; Block doc comments: the content is the text
; between the "/**" or "/*!" and the "*/".

(test-tokens "/** doc */"
             (list (token-doc-comment (doc-style-outer) t " doc ")))
(test-tokens "/**a*/"
             (list (token-doc-comment (doc-style-outer) t "a")))
(test-tokens "/*! doc */"
             (list (token-doc-comment (doc-style-inner) t " doc ")))
(test-tokens "/*!*/"
             (list (token-doc-comment (doc-style-inner) t "")))
(test-tokens "/** a /* b */ c */"
             (list (token-doc-comment (doc-style-outer) t " a /* b */ c ")))
(test-tokens "/**
 * a
 */"
             (list (token-doc-comment (doc-style-outer) t "
 * a
 ")))
(test-tokens "/** a */ b /*! c */"
             (list (token-doc-comment (doc-style-outer) t " a ")
                   (token-ident "b" nil)
                   (token-doc-comment (doc-style-inner) t " c ")))

; Block comments that are not doc comments:
; two stars and nothing else, three stars or more.

(test-tokens "/**/" nil)
(test-tokens "/***/" nil)
(test-tokens "/****/" nil)
(test-tokens "/*** not doc */" nil)
(test-tokens "/**/ */" (list (token-punct "*") (token-punct "/")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Integer literals: radix, digits as written, suffix.

(defmacro int-tok (radix digits suffix)
  `(token-lit (lit-int (make-int-lit :radix ,radix
                                     :digits ,digits
                                     :suffix ,suffix))))

(test-tokens "0" (list (int-tok (radix-dec) "0" "")))
(test-tokens "123_456" (list (int-tok (radix-dec) "123_456" "")))
(test-tokens "1u8" (list (int-tok (radix-dec) "1" "u8")))
(test-tokens "1px" (list (int-tok (radix-dec) "1" "px")))
(test-tokens "0b1_01" (list (int-tok (radix-bin) "1_01" "")))
(test-tokens "0o77" (list (int-tok (radix-oct) "77" "")))
(test-tokens "0xF_Fu32" (list (int-tok (radix-hex) "F_F" "u32")))
(test-tokens "0usize" (list (int-tok (radix-dec) "0" "usize")))

; The digits of a hexadecimal literal extend over the letters
; that are hexadecimal digits; its suffix starts at another letter.
; After the digits of the other radixes, those letters start a suffix.

(test-tokens "0x1f" (list (int-tok (radix-hex) "1f" "")))
(test-tokens "0x1F" (list (int-tok (radix-hex) "1F" "")))
(test-tokens "0xabcdef" (list (int-tok (radix-hex) "abcdef" "")))
(test-tokens "0x1e3" (list (int-tok (radix-hex) "1e3" "")))
(test-tokens "0x1_f_" (list (int-tok (radix-hex) "1_f_" "")))
(test-tokens "0x1fu8" (list (int-tok (radix-hex) "1f" "u8")))
(test-tokens "0x1g" (list (int-tok (radix-hex) "1" "g")))
(test-tokens "0x1Gf" (list (int-tok (radix-hex) "1" "Gf")))
(test-tokens "1f" (list (int-tok (radix-dec) "1" "f")))
(test-tokens "0b1a" (list (int-tok (radix-bin) "1" "a")))
(test-tokens "0o7F" (list (int-tok (radix-oct) "7" "F")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Float literals: the text of the number as written, and the suffix.

(defmacro float-tok (text suffix)
  `(token-lit (lit-float (make-float-lit :text ,text
                                         :suffix ,suffix))))

(test-tokens "2." (list (float-tok "2." "")))
(test-tokens "0.5" (list (float-tok "0.5" "")))
(test-tokens "1e10" (list (float-tok "1e10" "")))
(test-tokens "1E-10" (list (float-tok "1E-10" "")))
(test-tokens "1_000.000_1" (list (float-tok "1_000.000_1" "")))
(test-tokens "123.0f64" (list (float-tok "123.0" "f64")))
(test-tokens "12E+99_f64" (list (float-tok "12E+99_" "f64")))
(test-tokens "1.5_f32" (list (float-tok "1.5_" "f32")))
(test-tokens "1e_1" (list (float-tok "1e_1" "")))
(test-tokens "1.5px" (list (float-tok "1.5" "px")))

; After an exponent, a suffix may start with "e".

(test-tokens "2e5e6" (list (float-tok "2e5" "e6")))
(test-tokens "2.0e5e6" (list (float-tok "2.0e5" "e6")))

; An integer literal with a float suffix is an integer literal token.

(test-tokens "5f32" (list (int-tok (radix-dec) "5" "f32")))
(test-tokens "0x01_f32" (list (int-tok (radix-hex) "01_f32" "")))

; A period after a number belongs to a float literal unless
; a period, an underscore, or the start of an identifier follows it [SC14].

(test-tokens "1..2" (list (int-tok (radix-dec) "1" "")
                          (token-punct "..")
                          (int-tok (radix-dec) "2" "")))
(test-tokens "1.0..2.0" (list (float-tok "1.0" "")
                              (token-punct "..")
                              (float-tok "2.0" "")))
(test-tokens "1.max(2)" (list (int-tok (radix-dec) "1" "")
                              (token-punct ".")
                              (token-ident "max" nil)
                              (token-open-delim (delim-paren))
                              (int-tok (radix-dec) "2" "")
                              (token-close-delim (delim-paren))))
(test-tokens "2.f64" (list (int-tok (radix-dec) "2" "")
                           (token-punct ".")
                           (token-ident "f64" nil)))
(test-tokens "1._" (list (int-tok (radix-dec) "1" "")
                         (token-punct ".")
                         (token-punct "_")))
(test-tokens "1.+2" (list (float-tok "1." "")
                          (token-punct "+")
                          (int-tok (radix-dec) "2" "")))

; In a nested tuple field access, the lexer reads the two indices
; and the period between them as one float literal, as rustc's lexer does
; (rustc's parser then splits it).

(test-tokens "x.0.1" (list (token-ident "x" nil)
                           (token-punct ".")
                           (float-tok "0.1" "")))

; Reserved numeric forms [SC7].

(test-tokenize-fail "1e")
(test-tokenize-fail "2.0em")
(test-tokenize-fail "0x1.5")
(test-tokenize-fail "0b1e2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Character and string literals: the text between the delimiters as written
; (escapes unprocessed), whether byte, the string kind,
; the number of "#" of a raw string, and the suffix.

(defmacro char-tok (byte text suffix)
  `(token-lit (lit-char (make-char-lit :byte ,byte
                                       :text ,text
                                       :suffix ,suffix))))

(defmacro str-tok (kind raw text suffix)
  `(token-lit (lit-str (make-str-lit :kind ,kind
                                     :raw ,raw
                                     :text ,text
                                     :suffix ,suffix))))

(test-tokens "'a'" (list (char-tok nil "a" "")))
(test-tokens "'\\n'" (list (char-tok nil "\\n" "")))
(test-tokens "'\\u{1F600}'" (list (char-tok nil "\\u{1F600}" "")))
(test-tokens "b'x'" (list (char-tok t "x" "")))
(test-tokens "b'\\xFF'" (list (char-tok t "\\xFF" "")))
(test-tokens "'a'_x" (list (char-tok nil "a" "_x")))

(test-tokens "\"hello\"" (list (str-tok (str-kind-plain) nil "hello" "")))
(test-tokens "\"\"" (list (str-tok (str-kind-plain) nil "" "")))
(test-tokens "\"a\\\"b\"" (list (str-tok (str-kind-plain) nil "a\\\"b" "")))
(test-tokens "\"a\\
  b\"" (list (str-tok (str-kind-plain) nil "a\\
  b" ""))) ; a string continuation is kept as written
(test-tokens "b\"x\"" (list (str-tok (str-kind-byte) nil "x" "")))
(test-tokens "c\"x\"" (list (str-tok (str-kind-c) nil "x" "")))
(test-tokens-2021 "c\"x\"" (list (str-tok (str-kind-c) nil "x" "")))
(test-tokens "\"a\"suffix" (list (str-tok (str-kind-plain) nil "a" "suffix")))

; Raw strings: the text is everything between the delimiters [SC10].

(test-tokens "r\"x\"" (list (str-tok (str-kind-plain) 0 "x" "")))
(test-tokens "r\"\"" (list (str-tok (str-kind-plain) 0 "" "")))
(test-tokens "r##\"a\"#b\"##" (list (str-tok (str-kind-plain) 2 "a\"#b" "")))
(test-tokens "br#\"x\"#" (list (str-tok (str-kind-byte) 1 "x" "")))
(test-tokens "cr\"x\"" (list (str-tok (str-kind-c) 0 "x" "")))
(test-tokens "r#\"a\"#s" (list (str-tok (str-kind-plain) 1 "a" "s")))

; Non-ASCII text is kept UTF-8 encoded, as for identifiers.

(assert-event
 (equal (toks-only (tokenize-rust (list #x22 #xe9 #x22) ; e with acute accent
                                  (rust::edition-2024)))
        (list (str-tok (str-kind-plain)
                       nil
                       (acl2::implode (list (code-char #xc3) (code-char #xa9)))
                       ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Punctuation (with maximal munch) and delimiters.

(test-tokens ">>=" (list (token-punct ">>=")))
(test-tokens "_" (list (token-punct "_")))
(test-tokens "->" (list (token-punct "->")))
(test-tokens "..=" (list (token-punct "..=")))
(test-tokens "([{}])"
             (list (token-open-delim (delim-paren))
                   (token-open-delim (delim-bracket))
                   (token-open-delim (delim-brace))
                   (token-close-delim (delim-brace))
                   (token-close-delim (delim-bracket))
                   (token-close-delim (delim-paren))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Small programs, with trivia dropped.

(test-tokens "fn main() {}"
             (list (token-keyword "fn")
                   (token-ident "main" nil)
                   (token-open-delim (delim-paren))
                   (token-close-delim (delim-paren))
                   (token-open-delim (delim-brace))
                   (token-close-delim (delim-brace))))

(test-tokens "let x = 1; // init
x += 2;"
             (list (token-keyword "let")
                   (token-ident "x" nil)
                   (token-punct "=")
                   (int-tok (radix-dec) "1" "")
                   (token-punct ";")
                   (token-ident "x" nil)
                   (token-punct "+=")
                   (int-tok (radix-dec) "2" "")
                   (token-punct ";")))

(test-tokens "println!(\"{}\", x);"
             (list (token-ident "println" nil)
                   (token-punct "!")
                   (token-open-delim (delim-paren))
                   (str-tok (str-kind-plain) nil "{}" "")
                   (token-punct ",")
                   (token-ident "x" nil)
                   (token-close-delim (delim-paren))
                   (token-punct ";")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lexing failures propagate ([SC7] to [SC12]).

(test-tokenize-fail "foo#bar") ; [SC8]
(test-tokenize-fail "0b12") ; [SC7]
(test-tokenize-fail "'\\u{D800}'") ; [SC9]
(test-tokenize-fail "r#\"x\"") ; [SC10]
(test-tokenize-fail "\"Foo\"_") ; [SC11]
(test-tokenize-fail "'ab'") ; [SC12]
(test-tokenize-fail "'a#") ; [SC8]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Spans: offsets into the input, counted in code points,
; from the start of a token to just after its end.
; The whitespace and the comments between tokens count.

; The start and the end of the span of a token with span.

(defun span-offsets (token+span)
  (b* ((span (token+span->span token+span)))
    (cons (span->start span) (span->end span))))

; The line and the column of an offset in a list of code points.

(defun line+column (offset nats)
  (b* ((pos (position-of-offset offset nats)))
    (cons (position->line pos) (position->column pos))))

(assert-event
 (b* ((tokens+spans (toks "a
bc"))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans))
   (and (equal (span-offsets ts1) '(0 . 1))
        (equal (span-offsets ts2) '(2 . 4)))))

(assert-event
 (b* ((tokens+spans (toks "a /* c */ b// d
  c"))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2 ts3) tokens+spans))
   (and (equal (span-offsets ts1) '(0 . 1))
        (equal (span-offsets ts2) '(10 . 11))
        (equal (span-offsets ts3) '(18 . 19)))))

; Positions are computed from offsets:
; lines advance at line feeds, columns count code points.

(assert-event
 (b* ((nats (acl2::string=>nats "a
bc")))
   (and (equal (line+column 0 nats) '(1 . 0)) ; a
        (equal (line+column 1 nats) '(1 . 1)) ; the line feed
        (equal (line+column 2 nats) '(2 . 0)) ; b
        (equal (line+column 3 nats) '(2 . 1)) ; c
        (equal (line+column 4 nats) '(2 . 2))))) ; the end

; Non-ASCII whitespace (LINE SEPARATOR) counts as one code point,
; and as one column, not a line.

(assert-event
 (b* ((nats (list #x61 #x2028 #x62))
      (tokens+spans (tokenize-rust nats (rust::edition-2024)))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans))
   (and (equal (token+span->token ts1) (token-ident "a" nil))
        (equal (token+span->token ts2) (token-ident "b" nil))
        (equal (span-offsets ts2) '(2 . 3))
        (equal (line+column 2 nats) '(1 . 2)))))

; A string literal can span lines.

(assert-event
 (b* ((string "\"a
b\" c")
      (nats (acl2::string=>nats string))
      (tokens+spans (toks string))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans))
   (and (equal (span-offsets ts1) '(0 . 5))
        (equal (line+column 0 nats) '(1 . 0)) ; the opening quote
        (equal (line+column 4 nats) '(2 . 1)) ; the closing quote
        (equal (span-offsets ts2) '(6 . 7))
        (equal (line+column 6 nats) '(2 . 3))))) ; c

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Reserved guards [SC15]: in edition 2024, a "#" immediately followed by
; another "#" or by a string literal is rejected; in edition 2021,
; the same text is separate tokens.
; Each case below was run through rustc 1.87.0 in both editions.
; The first two are from the rustc tests transcribed in
; rustc-lexer-vectors.lisp, where they lex (lexing has no editions).

(test-tokenize-fail "foo ##bar")
(test-tokenize-fail "r\"\"##")
(test-tokenize-fail "##")
(test-tokenize-fail "###")
(test-tokenize-fail "#\"a\"")
(test-tokenize-fail "#\"a\"#")
(test-tokenize-fail "m!(#\"x\")")

(test-tokens-2021 "foo ##bar" (list (token-ident "foo" nil)
                                    (token-punct "#")
                                    (token-punct "#")
                                    (token-ident "bar" nil)))
(test-tokens-2021 "r\"\"##" (list (str-tok (str-kind-plain) 0 "" "")
                                  (token-punct "#")
                                  (token-punct "#")))
(test-tokens-2021 "#\"a\"#" (list (token-punct "#")
                                  (str-tok (str-kind-plain) nil "a" "")
                                  (token-punct "#")))

; A "#" followed by anything else is not a reserved guard:
; whitespace or a comment; a raw string, byte string, or character literal.
; And a raw string literal takes its own "#".

(test-tokens "# #" (list (token-punct "#") (token-punct "#")))
(test-tokens "#/**/#" (list (token-punct "#") (token-punct "#")))
(test-tokens "# \"a\"" (list (token-punct "#")
                             (str-tok (str-kind-plain) nil "a" "")))
(test-tokens "#r\"a\"" (list (token-punct "#")
                             (str-tok (str-kind-plain) 0 "a" "")))
(test-tokens "#b\"a\"" (list (token-punct "#")
                             (str-tok (str-kind-byte) nil "a" "")))
(test-tokens "#'a'" (list (token-punct "#") (char-tok nil "a" "")))
(test-tokens "r#\"abc\"##" (list (str-tok (str-kind-plain) 1 "abc" "")
                                 (token-punct "#")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexeme-level abstraction keeps trivia, for exact reprinting.

(assert-event
 (equal (abs-lexeme-list (lexemize-rust-from-string "x // c")
                         (rust::edition-2024))
        (list (lexeme-token (token-ident "x" nil))
              (lexeme-whitespace " ")
              (lexeme-comment nil " c"))))
