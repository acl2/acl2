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
(test-lexeme-okp "/*/ */")

; [SC2]: a "/*" inside a block comment opens a nested comment
; even when a "/" follows its "*",
; so these character sequences are not complete block comments,
; and the lexer rejects them.

(defmacro test-not-block-comment (string)
  `(assert-event
    (and (not (block-comment-string-p (string=>nats ,string)))
         (reserrp (lexemize-rust-from-string ,string)))))

(test-not-block-comment "/*/")
(test-not-block-comment "/*/*/")
(test-not-block-comment "/* xyz /*/")
(test-not-block-comment "/* xyz /*/ */")
(test-lexeme-okp "foo")
(test-lexeme-okp "0xF_Fu32")
(test-lexeme-okp " ")
(test-lexeme-okp "\"a\\\"b\"")
(test-lexeme-okp "r##\"a\"#b\"##")
(test-lexeme-okp "'a")
(test-lexeme-okp "'r#fn")
(test-lexeme-okp "1.")
(test-lexeme-okp "1_000.5e-3f64")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC14]: which lexemes are subject to the condition.

(defmacro test-float-period-lexeme (string yes/no)
  `(assert-event
    (equal (float-period-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-float-period-lexeme "1." t)
(test-float-period-lexeme "1_." t)
(test-float-period-lexeme "1.5" nil)
(test-float-period-lexeme "1e5" nil)
(test-float-period-lexeme "1" nil)
(test-float-period-lexeme "." nil) ; punctuation
(test-float-period-lexeme ".." nil)

; [SC14]: the condition against the remaining input.

(defmacro test-float-period (string rest-nats yes/no)
  `(assert-event
    (equal (lexeme-cst-float-period-okp
            (car (lexemize-rust-from-string ,string))
            ,rest-nats)
           ,yes/no)))

(test-float-period "1." nil t) ; at end of input
(test-float-period "1." (list #x2b) t) ; 1.+
(test-float-period "1." (list #x20 #x61) t) ; 1. a
(test-float-period "1." (list #x2e) nil) ; 1..
(test-float-period "1." (list #x5f) nil) ; 1._
(test-float-period "1." (list #x61) nil) ; 1.a
(test-float-period "1." (list #x45) nil) ; 1.E
(test-float-period "1.5" (list #x2e) t) ; other float literals are exempt
(test-float-period "1" (list #x2e) t) ; and so are other lexemes

; The characters that can start an identifier, in the specification,
; are those for which the lexer lexes an identifier-start.

(defun identifier-start-codes-agree (n)
  (if (zp n)
      t
    (b* ((code (1- n))
         ((mv tree &) (lex-identifier-start (list code))))
      (and (equal (identifier-start-code-p code)
                  (not (reserrp tree)))
           (identifier-start-codes-agree (1- n))))))

(comp t) ; added by Matt K. to prevent stack overflow in GCL

(assert-event (identifier-start-codes-agree #x3000))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC7]: which lexemes are subject to the condition.

(defmacro test-number-literal-lexeme (string yes/no)
  `(assert-event
    (equal (number-literal-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-number-literal-lexeme "1" t)
(test-number-literal-lexeme "0x1f" t)
(test-number-literal-lexeme "1u8" t)
(test-number-literal-lexeme "1." t)
(test-number-literal-lexeme "1.5e5f32" t)
(test-number-literal-lexeme "a1" nil)
(test-number-literal-lexeme "'1'" nil)
(test-number-literal-lexeme "." nil)

; [SC7]: the conditions against the remaining input.

(defmacro test-reserved-number (string rest-nats yes/no)
  `(assert-event
    (equal (lexeme-cst-reserved-number-okp
            (car (lexemize-rust-from-string ,string))
            ,rest-nats)
           ,yes/no)))

; A number literal followed by e or E.

(test-reserved-number "1" (list #x65) nil) ; 1e
(test-reserved-number "1" (list #x45 #x2b) nil) ; 1E+
(test-reserved-number "1_" (list #x65) nil) ; 1_e
(test-reserved-number "1.0" (list #x65 #x6d) nil) ; 1.0em
(test-reserved-number "1" (list #x20 #x65) t) ; 1 e
(test-reserved-number "1" nil t) ; at end of input
(test-reserved-number "1e5" nil t)
(test-reserved-number "+" (list #x65) t) ; other lexemes are exempt

; A literal with a radix prefix and no suffix,
; followed by a period that would belong to it.

(test-reserved-number "0x1" (list #x2e #x35) nil) ; 0x1.5
(test-reserved-number "0x1f" (list #x2e #x35) nil) ; 0x1f.5 (f is a digit)
(test-reserved-number "0b1" (list #x2e) nil) ; 0b1. at end of input
(test-reserved-number "0o7_" (list #x2e #x20) nil) ; 0o7_. and a space
(test-reserved-number "0x1" (list #x2e #x2e) t) ; 0x1..
(test-reserved-number "0x1" (list #x2e #x61) t) ; 0x1.a
(test-reserved-number "0x1" (list #x2e #x5f) t) ; 0x1._
(test-reserved-number "0b1u8" (list #x2e #x30) t) ; with a suffix
(test-reserved-number "0x1g" (list #x2e #x30) t) ; with a suffix
(test-reserved-number "1" (list #x2e #x2e) t) ; decimal literals are exempt

; Text that starts with a radix prefix,
; read as the decimal literal 0 with a suffix.
; For 0b1 there is also the CST with a binary literal,
; which is the lexer's, and is valid.
; For 0b12 there is only the CST with the decimal literal 0;
; it is a valid lexeme CST, so maximal munch chooses it,
; and the condition rejects it, as the lexer rejects the input.

(defun zero-with-suffix-cst (suffix-nats)
  (b* (((mv zero &) (lex-dec-literal (list #x30)))
       ((mv suffix &) (lex-suffix-no-e suffix-nats))
       (literal (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "integer-literal")
                 :branches (list (list (body-item zero))
                                 (list (body-item suffix)))))
       (token (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "token")
               :branches (list (list literal)))))
    (abnf::make-tree-nonleaf
     :rulename? (abnf::rulename "lexeme")
     :branches (list (list token)))))

(defconst *0b1-as-decimal-cst* (zero-with-suffix-cst (list #x62 #x31)))

(assert-event (equal (abnf::tree->string *0b1-as-decimal-cst*)
                     (list #x30 #x62 #x31)))
(assert-event (lexeme-cst-okp *0b1-as-decimal-cst*))
(assert-event (dec-integer-literal-lexeme-cst-p *0b1-as-decimal-cst*))
(assert-event (not (lexeme-cst-reserved-number-okp *0b1-as-decimal-cst* nil)))
(assert-event
 (b* ((trees (lexemize-rust-from-string "0b1")))
   (and (equal (len trees) 1)
        (lexeme-cst-okp (car trees))
        (not (dec-integer-literal-lexeme-cst-p (car trees)))
        (lexeme-cst-reserved-number-okp (car trees) nil))))

(defconst *0b12-as-decimal-cst* (zero-with-suffix-cst (list #x62 #x31 #x32)))

(assert-event (equal (abnf::tree->string *0b12-as-decimal-cst*)
                     (list #x30 #x62 #x31 #x32)))
(assert-event (lexeme-cst-okp *0b12-as-decimal-cst*))
(assert-event (not (lexeme-cst-reserved-number-okp *0b12-as-decimal-cst* nil)))
(assert-event (reserrp (lexemize-rust-from-string "0b12")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC15]: which lexemes are subject to the reserved guard condition,
; and the condition against the remaining input.
; The condition holds in edition 2024 only;
; the tokenizer tests check that the tokenizer applies it there.

(defmacro test-pound-lexeme (string yes/no)
  `(assert-event
    (equal (pound-lexeme-cst-p (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-pound-lexeme "#" t)
(test-pound-lexeme "!" nil)
(test-pound-lexeme "r#a" nil) ; raw identifier
(test-pound-lexeme "r#\"a\"#" nil) ; raw string literal

(defmacro test-reserved-guard (string rest-nats yes/no)
  `(assert-event
    (equal (lexeme-cst-reserved-guard-okp
            (car (lexemize-rust-from-string ,string))
            ,rest-nats)
           ,yes/no)))

(test-reserved-guard "#" (list #x23) nil) ; ##
(test-reserved-guard "#" (list #x22 #x61 #x22) nil) ; #"a"
(test-reserved-guard "#" (list #x20 #x23) t) ; # #
(test-reserved-guard "#" (list #x5b) t) ; #[
(test-reserved-guard "#" (list #x72 #x22 #x22) t) ; #r""
(test-reserved-guard "#" (list #x27 #x61 #x27) t) ; #'a'
(test-reserved-guard "#" nil t) ; # at end of input
(test-reserved-guard "!" (list #x23) t) ; only # is subject to it
(test-reserved-guard "r#\"a\"#" (list #x23) t) ; a raw string, then #

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC3]: which lexemes are doc comments, and the condition on them.

(defmacro test-doc-comment-lexeme (string yes/no)
  `(assert-event
    (equal (doc-comment-lexeme-cst-p
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-doc-comment-lexeme "///a" t)
(test-doc-comment-lexeme "//!a" t)
(test-doc-comment-lexeme "/** a */" t)
(test-doc-comment-lexeme "/*! a */" t)
(test-doc-comment-lexeme "//a" nil)
(test-doc-comment-lexeme "////a" nil)
(test-doc-comment-lexeme "/* a */" nil)
(test-doc-comment-lexeme "/**/" nil)
(test-doc-comment-lexeme "/*** a */" nil)
(test-doc-comment-lexeme "a" nil)

; A plain comment with a carriage return satisfies the condition.

(assert-event
 (b* ((trees (lexemize-rust (list #x2f #x2f #x61 #xd #x62)))) ; //a CR b
   (and (equal (len trees) 1)
        (lexeme-cst-doc-comment-cr-okp (car trees)))))

; The rules let a doc comment extend over a carriage return.
; The lexer does not produce such a CST, so we build two here,
; with the lexing functions for the rules alone, which do not check [SC3].
; Each is a valid lexeme CST, and the condition rejects it,
; as the lexer rejects the input.

(defun doc-lexeme-cst (doc-tree)
  (abnf::make-tree-nonleaf
   :rulename? (abnf::rulename "lexeme")
   :branches (list (list (abnf::make-tree-nonleaf
                          :rulename? (abnf::rulename "comment")
                          :branches (list (list doc-tree)))))))

(defconst *line-doc-with-cr* ; ///a CR b
  (list #x2f #x2f #x2f #x61 #xd #x62))

(defconst *line-doc-with-cr-cst*
  (b* (((mv tree &) (lex-outer-line-doc *line-doc-with-cr*)))
    (doc-lexeme-cst tree)))

(assert-event (equal (abnf::tree->string *line-doc-with-cr-cst*)
                     *line-doc-with-cr*))
(assert-event (lexeme-cst-okp *line-doc-with-cr-cst*))
(assert-event (doc-comment-lexeme-cst-p *line-doc-with-cr-cst*))
(assert-event (not (lexeme-cst-doc-comment-cr-okp *line-doc-with-cr-cst*)))
(assert-event (reserrp (lexemize-rust *line-doc-with-cr*)))

(defconst *block-doc-with-cr* ; /*! CR */
  (list #x2f #x2a #x21 #x20 #xd #x20 #x2a #x2f))

(defconst *block-doc-with-cr-cst*
  (b* (((mv tree &) (lex-inner-block-doc *block-doc-with-cr*)))
    (doc-lexeme-cst tree)))

(assert-event (equal (abnf::tree->string *block-doc-with-cr-cst*)
                     *block-doc-with-cr*))
(assert-event (lexeme-cst-okp *block-doc-with-cr-cst*))
(assert-event (doc-comment-lexeme-cst-p *block-doc-with-cr-cst*))
(assert-event (not (lexeme-cst-doc-comment-cr-okp *block-doc-with-cr-cst*)))
(assert-event (reserrp (lexemize-rust *block-doc-with-cr*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC10]: a raw literal ends at its first terminator.

; The lexer's CSTs satisfy the condition,
; for raw string, raw byte string, and raw C string literals,
; with and without "#", and with a suffix.

(defmacro test-raw-termination (string yes/no)
  `(assert-event
    (equal (lexeme-cst-raw-termination-okp
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-raw-termination "r\"a\"" t)
(test-raw-termination "r\"\"" t)
(test-raw-termination "r#\"a\"#" t)
(test-raw-termination "r#\"a\"b\"#" t) ; a double quote in the body
(test-raw-termination "r##\"a\"#b\"##" t) ; too few # in the body
(test-raw-termination "br\"a\"" t)
(test-raw-termination "br#\"a\"#" t)
(test-raw-termination "cr\"a\"" t)
(test-raw-termination "cr#\"a\"#" t)
(test-raw-termination "r#\"a\"#suffix" t)
(test-raw-termination "\"a\"" t) ; other lexemes satisfy the condition
(test-raw-termination "r#a" t)
(test-raw-termination "foo" t)

(test-lexeme-okp "r\"a\"")
(test-lexeme-okp "br#\"a\"#")
(test-lexeme-okp "cr##\"a\"#b\"##")

; A raw literal ends at its first terminator,
; and the rest of the input is other lexemes.

(assert-event
 (b* ((trees (lexemize-rust-from-string "r\"a\" \"b\"")))
   (and (equal (len trees) 3)
        (equal (abnf::tree->string (car trees))
               (string=>nats "r\"a\"")))))

(assert-event
 (b* ((trees (lexemize-rust-from-string "r#\"a\"##")))
   (and (equal (len trees) 2)
        (equal (abnf::tree->string (car trees))
               (string=>nats "r#\"a\"#")))))

; A CST for the eight characters r"a" "b" as one raw string literal,
; whose body is the five characters a" "b.
; The lexer does not produce such a CST, so we build it here,
; with the lexing function for the content of a raw literal,
; told to end the body at a double quote followed by "#".
; It matches the grammar, but it violates [SC10],
; so it is not a valid lexeme CST.

(defun token-lexeme-cst (tree)
  (abnf::make-tree-nonleaf
   :rulename? (abnf::rulename "lexeme")
   :branches (list (list (abnf::make-tree-nonleaf
                          :rulename? (abnf::rulename "token")
                          :branches (list (list tree)))))))

(defconst *long-raw-string-cst*
  (b* (((mv prefix &) (abnf::parse-schars "r" (string=>nats "r")))
       ((mv content &)
        (lex-raw-string-content 0 1 (string=>nats "\"a\" \"b\"#")))
       ((mv no-suffix &) (lex-option-suffix nil)))
    (token-lexeme-cst
     (abnf::make-tree-nonleaf
      :rulename? (abnf::rulename "raw-string-literal")
      :branches (list (list prefix) (list content) (list no-suffix))))))

(assert-event (equal (abnf::tree->string *long-raw-string-cst*)
                     (string=>nats "r\"a\" \"b\"")))
(assert-event (lexeme-cst-p *long-raw-string-cst*))
(assert-event (not (lexeme-cst-raw-termination-okp *long-raw-string-cst*)))
(assert-event (not (lexeme-cst-okp *long-raw-string-cst*)))

; At most 255 "#" before the opening double quote.

(defun raw-string-with-pounds (n)
  (b* ((pounds (make-list n :initial-element #x23)))
    (append (list #x72) pounds (list #x22 #x61 #x22) pounds))) ; r#..."a"#...

(assert-event
 (raw-content-string-p (cdr (raw-string-with-pounds 255))))
(assert-event
 (not (raw-content-string-p (cdr (raw-string-with-pounds 256)))))

(assert-event
 (b* ((trees (lexemize-rust (raw-string-with-pounds 255))))
   (and (equal (len trees) 1)
        (lexeme-cst-okp (car trees)))))
(assert-event
 (reserrp (lexemize-rust (raw-string-with-pounds 256))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC9]: the values of unicode escapes.

; The lexer's CSTs satisfy the condition,
; for character, string, and C string literals.

(defmacro test-unicode-escapes (string yes/no)
  `(assert-event
    (equal (lexeme-cst-unicode-escapes-okp
            (car (lexemize-rust-from-string ,string)))
           ,yes/no)))

(test-unicode-escapes "'\\u{0}'" t)
(test-unicode-escapes "'\\u{D7FF}'" t)
(test-unicode-escapes "'\\u{E000}'" t)
(test-unicode-escapes "'\\u{10FFFF}'" t)
(test-unicode-escapes "'\\u{1_F6_00_}'" t)
(test-unicode-escapes "\"a\\u{41}b\\u{0}\"" t)
(test-unicode-escapes "c\"a\\u{41}b\"" t)
(test-unicode-escapes "'a'" t) ; no unicode escape
(test-unicode-escapes "\"\\x41\"" t)
(test-unicode-escapes "foo" t) ; other lexemes satisfy the condition

; The lexer rejects the inputs with other values.

(defmacro test-unicode-escape-rejected (string)
  `(assert-event (reserrp (lexemize-rust-from-string ,string))))

(test-unicode-escape-rejected "'\\u{110000}'")
(test-unicode-escape-rejected "'\\u{D800}'")
(test-unicode-escape-rejected "'\\u{DFFF}'")
(test-unicode-escape-rejected "\"\\u{FFFFFF}\"")
(test-unicode-escape-rejected "c\"\\u{D800}\"")
(test-unicode-escape-rejected "c\"\\u{0}\"")
(test-unicode-escape-rejected "c\"\\u{0_0}\"")

; The rule for unicode escapes allows those values.
; The lexer does not produce a CST with one, so we build three here,
; from the parts of a unicode escape, without the check of its value.
; Each is a valid lexeme CST, and the condition rejects it,
; as the lexer rejects the input.

(defun unicode-escape-item (string)
  (b* ((input (string=>nats string))
       ((mv tree1 input1) (abnf::parse-schars "\\u{" input))
       ((mv tree2 input2) (lex-hex-digit-underscores input1))
       ((mv trees3 input3) (lex-unicode-escape-groups 5 input2))
       ((mv tree4 &) (abnf::parse-ichars "}" input3)))
    (body-item (abnf::make-tree-nonleaf
                :rulename? (abnf::rulename "unicode-escape")
                :branches (list (list tree1)
                                (cons tree2 trees3)
                                (list tree4))))))

(defconst *char-with-large-escape-cst* ; '\u{110000}'
  (b* (((mv quote &) (abnf::parse-ichars "'" (string=>nats "'")))
       ((mv no-suffix &) (lex-option-suffix nil)))
    (token-lexeme-cst
     (abnf::make-tree-nonleaf
      :rulename? (abnf::rulename "char-literal")
      :branches (list (list quote)
                      (list (unicode-escape-item "\\u{110000}"))
                      (list quote)
                      (list no-suffix))))))

(assert-event (equal (abnf::tree->string *char-with-large-escape-cst*)
                     (string=>nats "'\\u{110000}'")))
(assert-event (lexeme-cst-okp *char-with-large-escape-cst*))
(assert-event
 (not (lexeme-cst-unicode-escapes-okp *char-with-large-escape-cst*)))

(defconst *string-with-surrogate-escape-cst* ; "a\u{D800}"
  (b* (((mv dquote &) (lex-dquote (list #x22)))
       ((mv a &) (lex-string-literal-char (list #x61)))
       ((mv no-suffix &) (lex-option-suffix nil)))
    (token-lexeme-cst
     (abnf::make-tree-nonleaf
      :rulename? (abnf::rulename "string-literal")
      :branches (list (list dquote)
                      (list (body-item a)
                            (unicode-escape-item "\\u{D800}"))
                      (list dquote)
                      (list no-suffix))))))

(assert-event (equal (abnf::tree->string *string-with-surrogate-escape-cst*)
                     (string=>nats "\"a\\u{D800}\"")))
(assert-event (lexeme-cst-okp *string-with-surrogate-escape-cst*))
(assert-event
 (not (lexeme-cst-unicode-escapes-okp *string-with-surrogate-escape-cst*)))

; A unicode escape with the value zero is valid in a string literal,
; and not in a C string literal.

(defconst *c-string-with-zero-escape-cst* ; c"\u{0}"
  (b* (((mv prefix &) (abnf::parse-schars "c" (string=>nats "c")))
       ((mv dquote &) (lex-dquote (list #x22)))
       ((mv no-suffix &) (lex-option-suffix nil)))
    (token-lexeme-cst
     (abnf::make-tree-nonleaf
      :rulename? (abnf::rulename "c-string-literal")
      :branches (list (list prefix)
                      (list dquote)
                      (list (unicode-escape-item "\\u{0}"))
                      (list dquote)
                      (list no-suffix))))))

(assert-event (equal (abnf::tree->string *c-string-with-zero-escape-cst*)
                     (string=>nats "c\"\\u{0}\"")))
(assert-event (lexeme-cst-okp *c-string-with-zero-escape-cst*))
(assert-event
 (not (lexeme-cst-unicode-escapes-okp *c-string-with-zero-escape-cst*)))
(test-unicode-escapes "\"\\u{0}\"" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC6]: which lexemes are keywords, in each edition.

(defmacro test-keyword-lexeme (string edition yes/no)
  `(assert-event
    (equal (keyword-lexeme-cst-p
            (car (lexemize-rust-from-string ,string))
            ,edition)
           ,yes/no)))

(test-keyword-lexeme "fn" (rust::edition-2021) t) ; strict
(test-keyword-lexeme "fn" (rust::edition-2024) t)
(test-keyword-lexeme "self" (rust::edition-2021) t)
(test-keyword-lexeme "Self" (rust::edition-2024) t)
(test-keyword-lexeme "async" (rust::edition-2021) t)
(test-keyword-lexeme "try" (rust::edition-2021) t) ; reserved
(test-keyword-lexeme "abstract" (rust::edition-2024) t)
(test-keyword-lexeme "gen" (rust::edition-2021) nil) ; reserved from 2024
(test-keyword-lexeme "gen" (rust::edition-2024) t)
(test-keyword-lexeme "union" (rust::edition-2021) nil) ; weak
(test-keyword-lexeme "union" (rust::edition-2024) nil)
(test-keyword-lexeme "safe" (rust::edition-2024) nil)
(test-keyword-lexeme "foo" (rust::edition-2024) nil)
(test-keyword-lexeme "fnx" (rust::edition-2024) nil)
(test-keyword-lexeme "Fn" (rust::edition-2024) nil)
(test-keyword-lexeme "_" (rust::edition-2024) nil) ; punctuation
(test-keyword-lexeme "r#fn" (rust::edition-2024) nil) ; raw identifier
(test-keyword-lexeme "'static" (rust::edition-2024) nil) ; lifetime
(test-keyword-lexeme "\"fn\"" (rust::edition-2024) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [SC5]: raw identifiers and raw lifetimes with excluded names.
; The lexer accepts them: each of these inputs is one lexeme,
; and a valid one.  The condition rejects them.

(defmacro test-raw-name (string yes/no)
  `(assert-event
    (b* ((trees (lexemize-rust-from-string ,string)))
      (and (equal (len trees) 1)
           (lexeme-cst-okp (car trees))
           (equal (lexeme-cst-raw-name-okp (car trees))
                  ,yes/no)))))

(test-raw-name "r#crate" nil)
(test-raw-name "r#self" nil)
(test-raw-name "r#super" nil)
(test-raw-name "r#Self" nil)
(test-raw-name "'r#crate" nil)
(test-raw-name "'r#self" nil)
(test-raw-name "'r#super" nil)
(test-raw-name "'r#Self" nil)
(test-raw-name "r#fn" t) ; other keywords may be raw identifiers
(test-raw-name "r#crates" t)
(test-raw-name "r#Crate" t)
(test-raw-name "r#selfish" t)
(test-raw-name "'r#fn" t)
(test-raw-name "'r#selfish" t)
(test-raw-name "crate" t) ; not raw
(test-raw-name "'self" t)
(test-raw-name "r#\"crate\"#" t) ; a raw string
(test-raw-name "\"r#crate\"" t)
(test-raw-name "// r#crate" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The conditions that tokenization checks, on the lexer's output:
; [SC5] in both editions, and [SC15] in edition 2024.
; All these inputs lex.

(defmacro test-tokenization-conditions (string edition yes/no)
  `(assert-event
    (b* ((input (string=>nats ,string))
         (trees (lexemize-rust input)))
      (and (not (reserrp trees))
           (equal (tokenization-conditions-okp trees input ,edition)
                  ,yes/no)))))

(test-tokenization-conditions "fn f() {}" (rust::edition-2021) t)
(test-tokenization-conditions "fn f() {}" (rust::edition-2024) t)
(test-tokenization-conditions "" (rust::edition-2024) t)

(test-tokenization-conditions "r#crate" (rust::edition-2021) nil) ; [SC5]
(test-tokenization-conditions "r#crate" (rust::edition-2024) nil)
(test-tokenization-conditions "a + r#self;" (rust::edition-2021) nil)
(test-tokenization-conditions "&'r#Self x" (rust::edition-2024) nil)
(test-tokenization-conditions "r#fn 'r#fn" (rust::edition-2021) t)
(test-tokenization-conditions "r#fn 'r#fn" (rust::edition-2024) t)

(test-tokenization-conditions "##" (rust::edition-2021) t) ; [SC15]
(test-tokenization-conditions "##" (rust::edition-2024) nil)
(test-tokenization-conditions "#\"a\"" (rust::edition-2021) t)
(test-tokenization-conditions "#\"a\"" (rust::edition-2024) nil)
(test-tokenization-conditions "a # # b" (rust::edition-2024) t)
(test-tokenization-conditions "#[a] #!" (rust::edition-2024) t)
(test-tokenization-conditions "x ##" (rust::edition-2021) t)
(test-tokenization-conditions "x ##" (rust::edition-2024) nil)

(test-tokenization-conditions "r#crate ##" (rust::edition-2021) nil) ; both
(test-tokenization-conditions "r#crate ##" (rust::edition-2024) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The suffix of a hexadecimal literal.
; This is a rule of the grammar, not a side condition:
; the suffix does not start with a hexadecimal digit.
; So no CST reads 0x1f as the literal 0x1 with the suffix f.
; We build the two trees that would, one for each alternative
; of the rule for integer literals; neither matches the grammar.
; The lexer's CST for 0x1f has the digits 1f and no suffix.

(defun hex-1-with-suffix-f-cst (groupp)
  (b* (((mv hex &) (lex-hex-literal (string=>nats "0x1")))
       ((mv suffix &) (lex-suffix-no-e (string=>nats "f"))))
    (token-lexeme-cst
     (abnf::make-tree-nonleaf
      :rulename? (abnf::rulename "integer-literal")
      :branches (list (list (if groupp (body-item hex) hex))
                      (list (body-item suffix)))))))

(assert-event (equal (abnf::tree->string (hex-1-with-suffix-f-cst nil))
                     (string=>nats "0x1f")))
(assert-event (equal (abnf::tree->string (hex-1-with-suffix-f-cst t))
                     (string=>nats "0x1f")))
(assert-event (not (lexeme-cst-p (hex-1-with-suffix-f-cst nil))))
(assert-event (not (lexeme-cst-p (hex-1-with-suffix-f-cst t))))

(assert-event
 (b* ((trees (lexemize-rust-from-string "0x1f")))
   (and (equal (len trees) 1)
        (lexeme-cst-okp (car trees)))))

; With a suffix that starts with another letter,
; the tree for the second alternative is the lexer's.

(assert-event
 (b* (((mv hex &) (lex-hex-literal (string=>nats "0x1")))
      ((mv suffix &) (lex-suffix-no-hex-digit (string=>nats "g")))
      (trees (lexemize-rust-from-string "0x1g")))
   (and (equal (len trees) 1)
        (lexeme-cst-okp (car trees))
        (equal (car trees)
               (token-lexeme-cst
                (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "integer-literal")
                 :branches (list (list hex)
                                 (list (body-item suffix)))))))))

; After a decimal, binary, or octal literal,
; a suffix may start with a letter that is a hexadecimal digit.

(test-lexeme-okp "1f32")
(test-lexeme-okp "0b1a")
(test-lexeme-okp "0o7F")
