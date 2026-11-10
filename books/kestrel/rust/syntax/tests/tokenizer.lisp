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
; in both editions where the difference matters [SC6].

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviations for the tests.

(defmacro toks (string &optional (edition '(rust::edition-2024)))
  `(tokenize-rust-from-string ,string ,edition "test.rs"))

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
                                  (rust::edition-2024)
                                  "test.rs"))
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

; Spans: lines advance at line feeds, columns count code points.

(assert-event
 (b* ((tokens+spans (toks "a
bc"))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans)
      (span1 (token+span->span ts1))
      (span2 (token+span->span ts2)))
   (and (equal (position->line (span->start span1)) 1)
        (equal (position->column (span->start span1)) 0)
        (equal (position->line (span->end span1)) 1)
        (equal (position->column (span->end span1)) 0)
        (equal (position->line (span->start span2)) 2)
        (equal (position->column (span->start span2)) 0)
        (equal (position->line (span->end span2)) 2)
        (equal (position->column (span->end span2)) 1))))

; Non-ASCII whitespace (LINE SEPARATOR) counts as one column, not a line.

(assert-event
 (b* ((tokens+spans (tokenize-rust (list #x61 #x2028 #x62)
                                   (rust::edition-2024)
                                   "test.rs"))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans))
   (and (equal (token+span->token ts1) (token-ident "a" nil))
        (equal (token+span->token ts2) (token-ident "b" nil))
        (equal (position->column (span->start (token+span->span ts2))) 2))))

; A string literal can span lines.

(assert-event
 (b* ((tokens+spans (toks "\"a
b\" c"))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans)
      (span1 (token+span->span ts1))
      (span2 (token+span->span ts2)))
   (and (equal (position->line (span->start span1)) 1)
        (equal (position->column (span->start span1)) 0)
        (equal (position->line (span->end span1)) 2)
        (equal (position->column (span->end span1)) 1)
        (equal (position->line (span->start span2)) 2)
        (equal (position->column (span->start span2)) 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexeme-level abstraction keeps trivia, for exact reprinting.

(assert-event
 (equal (abs-lexeme-list (lexemize-rust-from-string "x // c")
                         (rust::edition-2024))
        (list (lexeme-token (token-ident "x" nil))
              (lexeme-whitespace " ")
              (lexeme-comment nil " c"))))
