; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../extra-grammatical-restrictions")
(include-book "../lexer")

; Tests of the executable parts of the declarative side-condition
; specifications, applied to CSTs produced by the (certified) lexer.
; The non-executable parts (the define-sk maximal-munch conditions)
; are the subject of the future lexer-satisfies-lexing-okp proof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC8]: which lexemes are subject to the reserved-prefix condition.

(defmacro test-ident-lexeme (string yes/no)
  `(assert-event
    (equal (identifier-or-keyword-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-ident-lexeme "foo" t)
(test-ident-lexeme "fn" t) ; keywords are identifier-or-keyword lexemes
(test-ident-lexeme "_a" t)
(test-ident-lexeme "r#fn" nil) ; raw identifier
(test-ident-lexeme "r" t) ; plain identifier, no raw prefix
(test-ident-lexeme "123" nil)
(test-ident-lexeme " " nil)
(test-ident-lexeme "// c" nil)
(test-ident-lexeme "+" nil)
(test-ident-lexeme "(" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC8]: the adjacency condition against the remaining input.

(defmacro test-reserved-prefix (string rest-nats yes/no)
  `(assert-event
    (equal (lexeme-cst-reserved-prefix-okp
            (car (lexemize-rust-from-string ,string))
            ,rest-nats)
           ,yes/no)))

(test-reserved-prefix "foo" (list #x23) nil) ; foo#
(test-reserved-prefix "foo" (list #x27) nil) ; foo'
(test-reserved-prefix "foo" (list #x22) nil) ; foo"
(test-reserved-prefix "fn" (list #x22) nil) ; keywords too
(test-reserved-prefix "foo" (list #x20) t) ; foo followed by space
(test-reserved-prefix "foo" nil t) ; foo at end of input
(test-reserved-prefix "r#fn" (list #x23) t) ; raw identifiers exempt
(test-reserved-prefix "123" (list #x23) t) ; non-identifiers exempt
(test-reserved-prefix "_" (list #x23) nil) ; _#
(test-reserved-prefix "_" (list #x27) nil) ; _'
(test-reserved-prefix "_" (list #x22) nil) ; _"
(test-reserved-prefix "_" (list #x20) t) ; _ followed by space

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC11]: which lexemes are subject to the underscore condition.

(defmacro test-literal-lexeme (string yes/no)
  `(assert-event
    (equal (char-or-string-literal-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-literal-lexeme "'a'" t)
(test-literal-lexeme "b'a'" t)
(test-literal-lexeme "\"s\"" t)
(test-literal-lexeme "b\"s\"" t)
(test-literal-lexeme "c\"s\"" t)
(test-literal-lexeme "r\"s\"" t)
(test-literal-lexeme "br#\"s\"#" t)
(test-literal-lexeme "cr\"s\"" t)
(test-literal-lexeme "\"s\"suffix" t)
(test-literal-lexeme "123" nil) ; integer literals are not covered
(test-literal-lexeme "foo" nil)
(test-literal-lexeme "_" nil)

; [SC11]: the adjacency condition against the remaining input.

(defmacro test-literal-underscore (string rest-nats yes/no)
  `(assert-event
    (equal (lexeme-cst-literal-underscore-okp
            (car (lexemize-rust-from-string ,string))
            ,rest-nats)
           ,yes/no)))

(test-literal-underscore "\"Foo\"" (list #x5f) nil) ; "Foo"_
(test-literal-underscore "'a'" (list #x5f) nil) ; 'a'_
(test-literal-underscore "br#\"x\"#" (list #x5f) nil) ; br#"x"#_
(test-literal-underscore "\"Foo\"" (list #x20 #x5f) t) ; "Foo" _
(test-literal-underscore "\"Foo\"" nil t) ; at end of input
(test-literal-underscore "foo" (list #x5f) t) ; non-literals exempt

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC2] and lexeme validity on lexer output.

(defmacro test-lexeme-okp (string)
  `(assert-event
    (lexeme-cst-okp (car (lexemize-rust-from-string ,string)))))

(test-lexeme-okp "/**/")
(test-lexeme-okp "/* a /* nested */ b */")
(test-lexeme-okp "foo")
(test-lexeme-okp "0xF_Fu32")
(test-lexeme-okp " ")
(test-lexeme-okp "\"a\\\"b\"")
(test-lexeme-okp "r##\"a\"#b\"##")
