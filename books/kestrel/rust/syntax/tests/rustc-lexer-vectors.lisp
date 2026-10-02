; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../lexer")

; Lexical test vectors transcribed from the rustc test suite
; (repository rust-lang/rust, tag 1.87.0 -- the pinned compiler):
;
;   tests/ui/lexer/lex-bad-binary-literal.rs
;   tests/ui/lexer/lex-bad-octal-literal.rs
;   tests/ui/lexer/lex-bad-numeric-literals.rs
;   tests/ui/rust-2021/reserved-prefixes.rs
;
; Only the cases within the current grammar slice are transcribed
; (no floats, strings, or character literals).
; The transcription respects rustc's STAGING:
; cases rustc rejects in its lexer
; (invalid digits in a based literal, no valid digits,
; reserved prefixes) must fail here [SC7] [SC8],
; while cases rustc rejects only in later validation phases
; (float suffixes on based literals, out-of-range values)
; must LEX here, since our lexer models only the lexing phase.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-lex (string n)
  `(assert-event
    (b* ((trees (lexemize-rust-from-string ,string)))
      (and (not (reserrp trees))
           (equal (len trees) ,n)))))

(defmacro test-lex-fail (string)
  `(assert-event
    (b* ((trees (lexemize-rust-from-string ,string)))
      (reserrp trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tests/ui/lexer/lex-bad-binary-literal.rs:
; all "invalid digit for a base 2 literal" (lexer-stage) [SC7].

(test-lex-fail "0b121")
(test-lex-fail "0b10_10301")
(test-lex-fail "0b30")
(test-lex-fail "0b41")
(test-lex-fail "0b5")
(test-lex-fail "0b6")
(test-lex-fail "0b7")
(test-lex-fail "0b8")
(test-lex-fail "0b9")

; tests/ui/lexer/lex-bad-octal-literal.rs:
; all "invalid digit for a base 8 literal" (lexer-stage) [SC7].

(test-lex-fail "0o18")
(test-lex-fail "0o1234_9_5670")

; tests/ui/lexer/lex-bad-numeric-literals.rs,
; the "no valid digits" cases (lexer-stage) [SC7].

(test-lex-fail "0o")
(test-lex-fail "0x")
(test-lex-fail "0b")
(test-lex-fail "0xu32")
(test-lex-fail "0ou32")
(test-lex-fail "0bu32")

; tests/ui/lexer/lex-bad-numeric-literals.rs,
; cases that LEX and are rejected only by
; rustc's later literal-validation phase
; ("...float literal is not supported" on suffixes,
; "integer literal is too large"):
; one lexeme each here, matching rustc's lexer.

(test-lex "0o2f32" 1)
(test-lex "0o123f64" 1)
(test-lex "0b101f64" 1)
(test-lex "9900000000000000000000000000999999999999999999999999999999" 1)
(test-lex "0o37777777777777777777777777777777777777777770" 1)
(test-lex "0xffffffffffffffffffffffffffffffff0" 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tests/ui/rust-2021/reserved-prefixes.rs,
; the in-slice "prefix `...` is unknown" cases (lexer-stage) [SC8].

(test-lex-fail "foo#bar")
(test-lex-fail "foo\"bar\"")
(test-lex-fail "foo'b'")
(test-lex-fail "foo'b")
(test-lex-fail "foo# bar")
(test-lex-fail "foo#! bar")
(test-lex-fail "foo## bar")
(test-lex-fail "foo#bar#")

; tests/ui/rust-2021/reserved-prefixes.rs,
; the cases that are fine (whitespace or punctuation intervenes,
; or the prefix is a genuine raw identifier).

(test-lex "foo # bar" 5) ; foo, space, #, space, bar
(test-lex "foo #bar" 4) ; foo, space, #, bar
(test-lex "foo!#bar" 4) ; foo, !, #, bar
(test-lex "foo ##bar" 5) ; foo, space, #, #, bar
(test-lex "r#foo#bar" 3) ; raw identifier r#foo, then #, bar

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Slice-boundary artifacts, documented:
; these involve float syntax, which is not in the grammar slice yet,
; so they lex as several lexemes here;
; rustc lexes them as one float literal and rejects it in validation.
; When float literals enter the slice, these counts will change.

(test-lex "0o1.0" 3) ; 0o1, ., 0
(test-lex "0x539.0" 3) ; 0x539, ., 0
(test-lex "0b111.101" 3) ; 0b111, ., 101
(test-lex "1e+" 3) ; 1, e, + (suffixes cannot start with e)
(test-lex "0o6e6f32" 2) ; 0o6, then identifier e6f32
(test-lex "0o5.0e5" 4) ; 0o5, ., 0, then identifier e5
(test-lex "0o4e4" 2) ; 0o4, then identifier e4
