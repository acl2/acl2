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

(defmacro toks (string &optional (edition '(rust::edition-e2024)))
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
  `(assert-event (equal (toks-only (toks ,string (rust::edition-e2021)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lexing failures propagate ([SC7], [SC8], not-in-slice forms).

(test-tokenize-fail "foo#bar") ; [SC8]
(test-tokenize-fail "0b12") ; [SC7]
(test-tokenize-fail "\"hello\"") ; strings not in slice yet
(test-tokenize-fail "'a'") ; chars not in slice yet

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
                                   (rust::edition-e2024)
                                   "test.rs"))
      ((when (reserrp tokens+spans)) nil)
      ((list ts1 ts2) tokens+spans))
   (and (equal (token+span->token ts1) (token-ident "a" nil))
        (equal (token+span->token ts2) (token-ident "b" nil))
        (equal (position->column (span->start (token+span->span ts2))) 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexeme-level abstraction keeps trivia, for exact reprinting.

(assert-event
 (equal (abs-lexeme-list (lexemize-rust-from-string "x // c")
                         (rust::edition-e2024))
        (list (lexeme-token (token-ident "x" nil))
              (lexeme-whitespace " ")
              (lexeme-comment nil " c"))))
