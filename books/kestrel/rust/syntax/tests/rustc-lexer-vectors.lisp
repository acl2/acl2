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
; (repository rust-lang/rust, tag 1.87.0 -- the pinned compiler),
; from the files named in the comments below.
;
; Only the cases within the current grammar slice are transcribed
; (no floats, block doc comments, or non-ASCII identifiers),
; plus the documented slice-boundary artifacts at the end.
; The transcription respects rustc's STAGING:
; cases rustc rejects in its lexer
; (invalid digits in a based literal, no valid digits,
; reserved prefixes, malformed or unterminated literals,
; invalid escapes, an underscore suffix,
; a lifetime followed by a single quote)
; must fail here [SC7] [SC8] [SC9] [SC10] [SC11] [SC12],
; while cases rustc rejects only in later phases
; (float suffixes on based literals, out-of-range values,
; suffixes on character and string literals,
; extra "#" after a raw string, keywords as lifetime names)
; must LEX here, since our lexer models only the lexing phase.
; Cases that the tokenizer rejects ([SC5] for raw lifetimes)
; are in the tokenizer tests.
; Inputs with non-ASCII characters are given as lists of code points.

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

(defmacro test-lex-nats (nats n)
  `(assert-event
    (b* ((trees (lexemize-rust ,nats)))
      (and (not (reserrp trees))
           (equal (len trees) ,n)))))

(defmacro test-lex-nats-fail (nats)
  `(assert-event
    (b* ((trees (lexemize-rust ,nats)))
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
(test-lex "r\"foo\"#bar" 3) ; raw string r"foo", then #, bar
(test-lex "r#foo#bar" 3) ; raw identifier r#foo, then #, bar

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tests/ui/lexer/lex-bad-char-literals-{1,...,7}.rs (lexer-stage):
; numeric escapes that are too short, unknown escapes,
; character literals with zero or several code points,
; unterminated character literals, and empty unicode escapes.
; U+25CF is BLACK CIRCLE.

(test-lex-fail "'\\x1'")
(test-lex-fail "\"\\x1\"")
(test-lex-nats-fail (list #x27 #x5c #x25cf #x27)) ; '\<U+25CF>'
(test-lex-nats-fail (list #x22 #x5c #x25cf #x22)) ; "\<U+25CF>"
(test-lex-fail "'nope'")
(test-lex-nats-fail (list #x27 #x25cf #x25cf #x27)) ; two code points
(test-lex-nats-fail (list #x27 #x25cf #x20 #x20 #xa #x3b)) ; unterminated
(test-lex-fail "'\\x10\\x10'")
(test-lex-fail "'ab'")
(test-lex-fail "'cd'")
(test-lex-fail "'ef'")
(test-lex "\"\"" 1)
(test-lex-fail "''")
(test-lex-fail "'\\u{}'")
(test-lex "'/'" 1)
(test-lex "b'/'" 1)
(test-lex-fail "' hello // here's a comment")

; tests/ui/lexer/lex-bad-str-literal-as-char-{1,2,3}.rs (lexer-stage):
; string contents in single quotes.

(test-lex-fail "println!('1 + 1');")
(test-lex-fail "println!(' 1 + 1');")
(test-lex-fail "println!('hello world');")

; tests/ui/parser/bad-char-literals.rs (lexer-stage):
; characters that must be escaped in a character literal,
; and a literal NUL among other characters.

(test-lex-fail "'''")
(test-lex-fail (acl2::implode (list #\' (code-char 10) #\'))) ; line feed
(test-lex-fail (acl2::implode (list #\' (code-char 13) #\'))) ; CR
(test-lex-fail (acl2::implode (list #\' #\- (code-char 0) #\- #\'))) ; NUL
(test-lex-fail (acl2::implode (list #\' (code-char 9) #\'))) ; tab

; tests/ui/parser/unicode-character-literal.rs (lexer-stage):
; a character followed by combining marks is several code points.

(test-lex-nats-fail (list #x27 #x2660 #xfe0f #x27))
(test-lex-nats-fail (list #x27 #x73 #x323 #x307 #x302 #x30a #x27))
(test-lex-nats-fail (list #x27 #x41 #x30a #x27))

; tests/ui/parser/ascii-only-character-escape.rs (lexer-stage):
; \x escapes above \x7F only in byte strings (and C strings).

(test-lex-fail "\"\\x80\"")
(test-lex-fail "\"\\xff\"")
(test-lex-fail "\"\\xe2\"")
(test-lex "b\"\\x00e2\"" 1)

; tests/ui/parser/byte-literals.rs,
; tests/ui/parser/byte-string-literals.rs,
; tests/ui/parser/raw/raw-byte-string-literals.rs (lexer-stage):
; unknown and malformed byte escapes, unescaped characters,
; non-ASCII characters (U+00E9), bare CR, bad raw delimiters,
; and unterminated literals.

(test-lex-fail "b'\\f'")
(test-lex-fail "b'\\x0Z'")
(test-lex-fail (acl2::implode (list #\b #\' (code-char 9) #\'))) ; tab
(test-lex-fail "b'''")
(test-lex-nats-fail (list #x62 #x27 #xe9 #x27))
(test-lex-fail "b'a")
(test-lex-fail "b\"\\f\"")
(test-lex-fail "b\"\\x0Z\"")
(test-lex-nats-fail (list #x62 #x22 #xe9 #x22))
(test-lex-nats-fail (list #x62 #x72 #x23 #x23 #x22 #xe9 #x22 #x23 #x23))
(test-lex-fail "b\"a")
(test-lex-fail (acl2::implode (list #\b #\r #\" #\a (code-char 13) #\")))
(test-lex-nats-fail (list #x62 #x72 #x22 #xe9 #x22))
(test-lex-fail "br##~\"a\"~##")

; tests/ui/parser/new-unicode-escapes-{1,2,3,4}.rs (lexer-stage):
; unterminated, overlong, surrogate, out-of-range, and malformed
; unicode escapes [SC9].

(test-lex-fail "\"\\u{2603\"")
(test-lex-fail "\"\\u{260311111111}\"")
(test-lex-fail "\"\\u{d805}\"")
(test-lex-fail "\"\\u{ffffff}\"")
(test-lex-fail "\"\\u{lol}\"")

; tests/ui/parser/issues/issue-23620-invalid-escapes.rs (lexer-stage):
; unicode escapes in byte literals and byte strings,
; incomplete unicode escapes, and short or malformed \x escapes.

(test-lex-fail "b\"\\u{a66e}\"")
(test-lex-fail "b'\\u{a66e}'")
(test-lex-fail "b'\\u'")
(test-lex-fail "b'\\x5'")
(test-lex-fail "b'\\xxy'")
(test-lex-fail "'\\x5'")
(test-lex-fail "'\\xxy'")
(test-lex-fail "b\"\\u{a4a4} \\xf \\u\"")
(test-lex-fail "\"\\xf \\u\"")
(test-lex-fail "\"\\u8f\"")

; tests/ui/parser/wrong-escape-of-curly-braces.rs,
; tests/ui/parser/bad-escape-suggest-raw-string.rs (lexer-stage):
; unknown escapes in strings, but not in raw strings.

(test-lex "\"{{everything fine}}\"" 1)
(test-lex-fail "\"\\{it is wrong\\}\"")
(test-lex "r\"ab\\[c\"" 1)
(test-lex-fail "\"ab\\[c\"")

; tests/ui/parser/trailing-carriage-return-in-string.rs,
; tests/ui/lexer/lex-bare-cr-string-literal-doc-comment.rs
; (the string cases; the doc comment cases are [SC3], not yet covered),
; tests/ui/parser/unbalanced-doublequote.rs (lexer-stage):
; a string continuation is a backslash before a line feed,
; a bare CR is not allowed in strings,
; and strings must be terminated.

(test-lex "\"This is \\
 a test\"" 1)
(test-lex-fail (acl2::implode (append (coerce "\"This is \\" 'list)
                                      (list (code-char 13))
                                      (coerce " a test\"" 'list))))
(test-lex-fail (acl2::implode (list #\" #\f #\o #\o (code-char 13)
                                    #\b #\a #\r #\")))
(test-lex-fail (acl2::implode (list #\r #\" #\b #\a #\r (code-char 13)
                                    #\f #\o #\o #\")))
(test-lex-fail (acl2::implode (list #\" #\f #\o #\o #\\ (code-char 13)
                                    #\b #\a #\r #\")))
(test-lex-fail "\"
}")

; tests/ui/lexer/error-stage.rs,
; tests/ui/parser/bad-lit-suffixes.rs,
; tests/ui/parser/lit-err-in-macro.rs:
; any suffix on any literal lexes,
; and is rejected only by rustc's later literal-validation phase.

(test-lex "\"string\"any_suffix" 1)
(test-lex "10u123" 1)
(test-lex "0b10f32" 1)
(test-lex "999340282366920938463463374607431768211455999" 1)
(test-lex "\"C\"suffix" 1)
(test-lex "\"\"suffix" 1)
(test-lex "b\"\"suffix" 1)
(test-lex "r#\"\"#suffix" 1)
(test-lex "br#\"\"#suffix" 1)
(test-lex "'a'suffix" 1)
(test-lex "b'a'suffix" 1)
(test-lex "1234u1024" 1)
(test-lex "1234i1024" 1)
(test-lex "1234f1024" 1)
(test-lex "1234suffix" 1)
(test-lex "0b101suffix" 1)
(test-lex "0suffix" 1)
(test-lex "\"Foo\"__" 1)

; tests/ui/parser/underscore-suffix-for-string.rs:
; except that rustc's lexer rejects an underscore suffix [SC11].

(test-lex-fail "\"Foo\"_")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tests/ui/parser/raw/{raw-string,raw-string-2,raw-byte-string-eof,
; raw-str-unterminated,raw-str-delim,too-many-hash,
; issue-70677-panic-on-unterminated-raw-str-at-eof}.rs (lexer-stage):
; unterminated raw strings, invalid delimiters,
; and too many "#" [SC10].

(test-lex-fail "r##\"lol\"#;")
(test-lex-fail "r###\"here's a long string\"# \"# \"##;")
(test-lex-fail "br##\"a\"#;")
(test-lex-fail "r#\" string literal goes on
        and on
")
(test-lex-fail "r#~\"#\"~#")
(test-lex-fail (acl2::implode (cons #\r (acl2::repeat 256 #\#))))
(test-lex-fail "r\"")

; tests/ui/parser/raw/raw-str-unbalanced.rs,
; tests/ui/parser/raw/raw-str-in-macro-call.rs:
; "#" after a raw string are separate tokens,
; rejected (if at all) only by rustc's parser.

(test-lex "r#\"\"##" 2)
(test-lex "r#\"
      \"####" 4)
(test-lex "r\"\"" 1)
(test-lex "r\"\"##" 3)
(test-lex "r#\"abc\"##" 2)
(test-lex "r#\"abc\"#" 1)

; tests/ui/rfcs/rfc-3348-c-string-literals/{basic,non-ascii,no-nuls}.rs:
; C strings, with non-ASCII characters (U+1F980) and escapes,
; must not contain NUL, written directly or as an escape [SC9];
; rustc's lexer rejects NUL even in macro arguments.
; (edition-2015-2018-lexing.rs is about editions before 2021.)

(test-lex "b\"test\\0\"" 1)
(test-lex "c\"test\"" 1)
(test-lex-nats (append (acl2::string=>nats "c\"\\xEF\\x80")
                       (list #x1f980)
                       (acl2::string=>nats "\\u{1F980}\""))
               1)
(test-lex-fail "c\"\\0\"")
(test-lex-fail "c\"\\u{00}\"")
(test-lex-fail (acl2::implode (list #\c #\" (code-char 0) #\")))
(test-lex-fail "c\"\\x00\"")
(test-lex-fail (acl2::implode (list #\c #\r #\" (code-char 0) #\")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tests/ui/lifetimes/raw/{simple,static-lt,prim-lt,macro-lt,lifetimes-eq}.rs,
; tests/ui/rust-2024/raw-gen-lt.rs:
; raw lifetimes, which may have keyword names.
; (tests/ui/lifetimes/raw/three-tokens.rs is about edition 2015.)

(test-lex "'r#struct" 1)
(test-lex "'r#static" 1)
(test-lex "'r#i32" 1)
(test-lex "'r#gen" 1)
(test-lex "'r#struct: loop { break 'r#struct; }" 13)
(test-lex "fn test<'r#a>(x: &'a ()) {}" 19)

; tests/ui/lifetimes/raw/multiple-prefixes.rs:
; the raw lifetime 'r#r, then #, then r
; (rejected only by rustc's parser).

(test-lex "'r#r#r" 3)

; tests/ui/lifetimes/raw/immediately-followed-by-lt.rs (lexer-stage):
; a raw lifetime followed by a single quote [SC12].

(test-lex-fail "'r#long'id")

; tests/ui/lifetimes/raw/raw-lt-invalid-raw-id.rs (lexer-stage):
; 'r#_ is not a raw lifetime, since a lone underscore is not an
; identifier, so it is the lifetime 'r followed by "#" [SC8].
; The other cases of this test ('r#self etc.) lex here,
; and the tokenizer rejects them [SC5].

(test-lex-fail "'r#_")

; tests/ui/lexer/prefixed-lifetime.rs,
; tests/ui/lexer/dont-ice-on-invalid-lifetime-in-macro-definition.rs
; (lexer-stage): reserved prefixes [SC8].

(test-lex-fail "'foo#lifetime")
(test-lex-fail "e::<f'g>")

; tests/ui/parser/numeric-lifetime.rs (lexer-stage):
; no lifetime starts with a digit.

(test-lex-fail "struct S<'1> { s: &'1 usize }")

; tests/ui/parser/label-is-actually-char.rs,
; tests/ui/parser/cfg-keyword-lifetime.rs,
; tests/ui/lifetimes/raw/gen-lt.rs:
; lifetimes that only rustc's parser rejects
; (a label without a loop, a keyword name).

(test-lex "'a;" 2)
(test-lex "'abc;" 2)
(test-lex "'a'..='b" 3)
(test-lex "'c'..='def" 3)
(test-lex "['a, 'b, 'cde]" 9)
(test-lex "'ref" 1)
(test-lex "'gen" 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Slice-boundary artifacts, documented:
; these involve float syntax, which is not in the grammar slice yet,
; so they lex as several lexemes here.
; rustc reads each as one float literal,
; and rejects all of these in its lexer
; (a float literal with a radix prefix, or an exponent without digits),
; so they will fail here when float literals enter the slice.

(test-lex "0o1.0" 3) ; 0o1, ., 0
(test-lex "0x539.0" 3) ; 0x539, ., 0
(test-lex "0b111.101" 3) ; 0b111, ., 101
(test-lex "1e+" 3) ; 1, e, + (suffixes cannot start with e)
(test-lex "0o6e6f32" 2) ; 0o6, then identifier e6f32
(test-lex "0o5.0e5" 4) ; 0o5, ., 0, then identifier e5
(test-lex "0o4e4" 2) ; 0o4, then identifier e4

; From tests/ui/lexer/error-stage.rs and tests/ui/parser/bad-lit-suffixes.rs:
; rustc reads each as one float literal,
; rejecting 0b10.0f32 in its lexer (binary float literal),
; and the others only in validation (invalid width or suffix),
; so with float literals in the slice,
; 0b10.0f32 will fail here and the others will be single lexemes.

(test-lex "10.0f123" 3) ; 10, ., 0f123
(test-lex "0b10.0f32" 3) ; 0b10, ., 0f32
(test-lex "1234.5f1024" 3) ; 1234, ., 5f1024
(test-lex "1.0suffix" 3) ; 1, ., 0suffix
(test-lex "1.0e10suffix" 4) ; 1, ., 0, then identifier e10suffix
