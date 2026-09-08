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

; Not yet covered by the grammar slice: strings, chars, lifetimes.

(test-lex-fail "\"hello\"")
(test-lex-fail "'a'")
(test-lex-fail "&'a str")
