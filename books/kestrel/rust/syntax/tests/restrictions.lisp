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
