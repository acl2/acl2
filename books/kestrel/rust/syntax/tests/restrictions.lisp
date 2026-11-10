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
(test-reserved-prefix "_a" (list #x23) nil) ; _a#
(test-reserved-prefix "_1" (list #x22) nil) ; _1"
(test-reserved-prefix "foo" (list #x20) t) ; foo followed by space
(test-reserved-prefix "foo" nil t) ; foo at end of input
(test-reserved-prefix "r#fn" (list #x23) t) ; raw identifiers exempt
(test-reserved-prefix "123" (list #x23) t) ; non-identifiers exempt
(test-reserved-prefix "_" (list #x23) nil) ; _#
(test-reserved-prefix "_" (list #x27) nil) ; _'
(test-reserved-prefix "_" (list #x22) nil) ; _"
(test-reserved-prefix "_" (list #x20) t) ; _ followed by space

; [SC8], lifetimes: which lifetime lexemes are subject to the "#" condition.

(defmacro test-non-raw-lifetime-lexeme (string yes/no)
  `(assert-event
    (equal (non-raw-lifetime-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-non-raw-lifetime-lexeme "'a" t)
(test-non-raw-lifetime-lexeme "'_" t)
(test-non-raw-lifetime-lexeme "'r" t)
(test-non-raw-lifetime-lexeme "'r#a" nil) ; raw lifetime
(test-non-raw-lifetime-lexeme "'a'" nil) ; character literal
(test-non-raw-lifetime-lexeme "foo" nil)

(test-reserved-prefix "'a" (list #x23) nil) ; 'a#
(test-reserved-prefix "'_" (list #x23) nil) ; '_#
(test-reserved-prefix "'r" (list #x23 #x31) nil) ; 'r#1
(test-reserved-prefix "'r#a" (list #x23) t) ; raw lifetimes exempt
(test-reserved-prefix "'a" (list #x20 #x23) t) ; 'a #
(test-reserved-prefix "'a" (list #x22) t) ; only # for lifetimes

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

; [SC12]: which lexemes are subject to the single quote condition.

(defmacro test-lifetime-lexeme (string yes/no)
  `(assert-event
    (equal (lifetime-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-lifetime-lexeme "'a" t)
(test-lifetime-lexeme "'_" t)
(test-lifetime-lexeme "'r#a" t)
(test-lifetime-lexeme "'a'" nil) ; character literal
(test-lifetime-lexeme "a" nil)

; [SC12]: the adjacency condition against the remaining input.

(defmacro test-lifetime-quote (string rest-nats yes/no)
  `(assert-event
    (equal (lexeme-cst-lifetime-quote-okp
            (car (lexemize-rust-from-string ,string))
            ,rest-nats)
           ,yes/no)))

(test-lifetime-quote "'ab" (list #x27) nil) ; 'ab'
(test-lifetime-quote "'r#a" (list #x27) nil) ; 'r#a'
(test-lifetime-quote "'a" (list #x20 #x27) t) ; 'a '
(test-lifetime-quote "'a" nil t) ; at end of input
(test-lifetime-quote "'a'" (list #x27) t) ; character literals exempt

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
(test-lexeme-okp "'a")
(test-lexeme-okp "'r#fn")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC13]: a string continuation takes all the whitespace after it.

; The lexer's CSTs satisfy the condition,
; for string, byte string, and C string literals,
; also with a carriage return in the whitespace,
; and with two string continuations in a row.

(test-lexeme-okp "\"a\\
  b\"")
(test-lexeme-okp "b\"a\\
  b\"")
(test-lexeme-okp "c\"a\\

  b\"")
(test-lexeme-okp (acl2::implode (list #\" #\a #\\ (code-char 10)
                                      #\Space (code-char 13) (code-char 9)
                                      #\b #\")))
(test-lexeme-okp "\"a\\
\\
b\"")

; A CST for the six characters " \ LF space x "
; in which the string continuation ends before the space,
; so that the space is a character of the string.
; It matches the grammar, but it violates [SC13];
; the lexer's CST for the same characters is a different one, and valid.

(defun body-item (tree)
  (abnf::make-tree-nonleaf :rulename? nil
                           :branches (list (list tree))))

(defconst *short-continue-cst*
  (b* (((mv dquote &) (lex-dquote (list #x22)))
       ((mv cont &) (lex-string-continue (list #x5c #xa)))
       ((mv sp &) (lex-string-literal-char (list #x20)))
       ((mv x &) (lex-string-literal-char (list #x78)))
       (no-suffix (abnf::make-tree-nonleaf :rulename? nil :branches nil))
       (literal (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "string-literal")
                 :branches (list (list dquote)
                                 (list (body-item cont)
                                       (body-item sp)
                                       (body-item x))
                                 (list dquote)
                                 (list no-suffix))))
       (token (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "token")
               :branches (list (list literal)))))
    (abnf::make-tree-nonleaf
     :rulename? (abnf::rulename "lexeme")
     :branches (list (list token)))))

(assert-event (equal (abnf::tree->string *short-continue-cst*)
                     (list #x22 #x5c #xa #x20 #x78 #x22)))
(assert-event (lexeme-cst-p *short-continue-cst*))
(assert-event (not (lexeme-cst-string-continues-okp *short-continue-cst*)))
(assert-event (not (lexeme-cst-okp *short-continue-cst*)))
(assert-event
 (b* ((trees (lexemize-rust (list #x22 #x5c #xa #x20 #x78 #x22))))
   (and (equal (len trees) 1)
        (lexeme-cst-okp (car trees))
        (not (equal (car trees) *short-continue-cst*)))))
