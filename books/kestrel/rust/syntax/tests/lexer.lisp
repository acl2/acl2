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

; Tests of the lexer.
; Each test checks whether lexing succeeds,
; and if it succeeds, how many lexemes result;
; the theorems in the lexer book guarantee that
; successful results match the grammar and cover the input,
; so the counts (together with the failure tests)
; are a good behavioral fingerprint.

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

; Empty input.

(test-lex "" 0)

; Whitespace.

(test-lex " " 1)
(test-lex "
  " 1) ; spaces and line feed are one whitespace lexeme
(assert-event ; non-ASCII whitespace: LEFT-TO-RIGHT MARK, LINE SEPARATOR
 (b* ((trees (lexemize-rust (list #x200e #x2028))))
   (and (not (reserrp trees))
        (equal (len trees) 1))))

; Identifiers and keywords (all identifier-or-keyword lexemes here).

(test-lex "foo" 1)
(test-lex "foo bar" 3)
(test-lex "_a" 1)
(test-lex "_" 1) ; punctuation, not identifier
(test-lex "_ _a" 3)
(test-lex "fn" 1)
(test-lex "r#fn" 1)
(test-lex "r#union" 1)
(test-lex "r" 1)
(test-lex "rx" 1)

; Reserved prefixes [SC8].

(test-lex-fail "foo#bar")
(test-lex-fail "r#1") ; r would be an identifier followed by #
(test-lex "r #foo" 4) ; but with whitespace: r, ws, #, foo

; Comments, including the ////-related classification quirks.

(test-lex "// c" 1)
(test-lex "//" 1)
(test-lex "///" 1) ; outer line doc, empty content
(test-lex "///doc" 1)
(test-lex "//!doc" 1)
(test-lex "////plain" 1)
(test-lex "// c
x" 3) ; comment, whitespace (line feed), identifier
(test-lex "/**/" 1)
(test-lex "/* a */" 1)
(test-lex "/* a /* nested */ b */" 1)
(test-lex "/* a /* nested */ b */ c */" 6) ; comment, ws, c, ws, *, /
(test-lex-fail "/*")
(test-lex-fail "/* /* */")

; Integer literals, including the [SC7] reserved forms.

(test-lex "0" 1)
(test-lex "123" 1)
(test-lex "123_456" 1)
(test-lex "1_" 1)
(test-lex "0b1_01" 1)
(test-lex "0b_1" 1)
(test-lex "0o77" 1)
(test-lex "0o_7" 1)
(test-lex "0xF_Fu32" 1)
(test-lex "1u8" 1)
(test-lex "1px" 1) ; any identifier-shaped suffix lexes
(test-lex "0usize" 1)
(test-lex-fail "0b")
(test-lex-fail "0b_")
(test-lex-fail "0b12")
(test-lex-fail "0o8")
(test-lex-fail "0x")
(test-lex "1e5" 2) ; float literals not in this slice: 1 then e5
(test-lex "1.5" 3) ; float literals not in this slice: 1 then . then 5

; Punctuation and maximal munch [SC1].

(test-lex "+" 1)
(test-lex "a+b" 3)
(test-lex "a += b" 5)
(test-lex ">>=" 1)
(test-lex ">> =" 3)
(test-lex "x >>= 1..=2" 7)
(test-lex "1..2" 3)
(test-lex "..." 1)
(test-lex ".. ." 3)
(test-lex "::" 1)
(test-lex ": :" 3)
(test-lex "->" 1)
(test-lex "<-" 1)
(test-lex "~" 1)
(test-lex "@" 1)
(test-lex "&&" 1)
(test-lex "& &" 3)
(test-lex "<<=" 1)

; Delimiters.

(test-lex "()" 2)
(test-lex "([{}])" 6)

; A small program.

(test-lex "fn main() {}" 8)
(test-lex "fn add(x: u32, y: u32) -> u32 { x + y }" 29)

; Character, byte, string, byte-string, and C-string literals,
; and their raw forms.

(test-lex "\"hello\"" 1)
(test-lex "'a'" 1)
(test-lex "b'x'" 1)
(test-lex "b\"x\"" 1)
(test-lex "c\"x\"" 1)
(test-lex "r\"x\"" 1)
(test-lex "br\"x\"" 1)
(test-lex "cr\"x\"" 1)
(test-lex "\"x\" \"y\"" 3)
(test-lex "println!(\"{}\", x);" 9)

; Suffixes on any literal.

(test-lex "\"a\"b" 1)
(test-lex "'a'_x" 1)
(test-lex "r#\"a\"#suffix" 1)

; A suffix is lexed greedily, before any reserved-prefix check:
; "a"foo"b" is a literal with suffix foo, then another literal
; (as rustc 1.87.0 lexes it).

(test-lex "\"a\"foo\"b\"" 2)
(test-lex "'a'b'c'" 2)
(test-lex "\"a\"r#b" 3) ; suffix r, then #, then b

; A lone underscore after a character or string literal
; is rejected [SC11]; a longer suffix starting with an underscore
; is fine, and integer digits absorb underscores.

(test-lex-fail "'a'_")
(test-lex-fail "b'a'_")
(test-lex-fail "\"Foo\"_")
(test-lex-fail "b\"x\"_")
(test-lex-fail "c\"x\"_")
(test-lex-fail "r\"x\"_")
(test-lex-fail "br#\"x\"#_")
(test-lex-fail "cr\"x\"_")
(test-lex "\"Foo\"__" 1)
(test-lex "\"Foo\" _" 3)
(test-lex "1_" 1)

; Escapes.

(test-lex "\"\\n\\r\\t\\\\\\0\\'\\\"\"" 1)
(test-lex "'\\x7F'" 1)
(test-lex-fail "'\\x80'") ; ASCII escapes go up to \x7F
(test-lex "b'\\x80'" 1) ; byte escapes take any byte
(test-lex "'\\u{10FFFF}'" 1)
(test-lex "'\\u{1_F6_00}'" 1)
(test-lex-fail "'\\u{D800}'") ; surrogate [SC9]
(test-lex-fail "'\\u{110000}'") ; beyond the Unicode range [SC9]
(test-lex-fail "'\\u{1234567}'") ; more than six digits
(test-lex-fail "\"\\q\"") ; unknown escape
(test-lex-fail "b'\\u{41}'") ; no unicode escapes in byte literals
(test-lex-fail "c\"\\0\"") ; no NUL in C strings
(test-lex-fail "c\"\\x00\"")
(test-lex-fail "c\"\\u{0}\"") ; [SC9]

; A string continuation (backslash before a line feed) and a multi-line
; string.

(test-lex "\"line\\
  more\"" 1)
(test-lex "\"two
lines\"" 1)

; A bare carriage return is not allowed in a string literal.

(test-lex-fail (acl2::implode (list #\" (code-char 13) #\")))

; Raw strings end at the first double quote followed by as many "#" as
; opened them [SC10].

(test-lex "r#\"a\"b\"#" 1)
(test-lex "r##\"a\"#b\"##" 1)
(test-lex "r\"a\\nb\"" 1) ; no escapes in raw strings
(test-lex-fail "r#\"x\"") ; missing closing "#"
(test-lex-fail (acl2::implode (append (list #\r)
                                      (acl2::repeat 256 #\#)
                                      (list #\" #\")
                                      (acl2::repeat 256 #\#))))

; Malformed literals.

(test-lex-fail "\"unterminated")
(test-lex-fail "'ab'")
(test-lex-fail "''")

; Reserved prefixes [SC8], including a lone underscore.

(test-lex-fail "foo\"x\"")
(test-lex-fail "foo'x'")
(test-lex-fail "b#x")
(test-lex-fail "_#")
(test-lex-fail "_\"x\"")

; Not yet covered by the grammar slice: lifetimes.

(test-lex-fail "&'a str")
