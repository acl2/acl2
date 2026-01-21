; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "parsing")

(include-book "../definition/syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tools to test the ACL2 abstractor of Leo, i.e. the CST-to-AST mapping.
; Since it is often inconvenient to test the abstractor in isolation,
; having to manually construct relatively large CSTs,
; we use the lexer or parser to construct CSTs from Unicode inputs.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that lexing and then abstracting a construct
; succeeds and returns the expected result.

(defmacro test-lex-abs (lex-fn abs-fn input output)
  `(assert-event
    (b* ((input (input-to-unicode-points ,input))
         (cst (lex-full ,lex-fn input))
         (ast (,abs-fn cst)))
      (equal ast ,output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that parsing and then abstracting a construct
; succeeds and returns the expected result.

(defmacro test-parse-abs (parse-fn abs-fn input output)
  `(assert-event
    (b* ((input (input-to-unicode-points ,input))
         ((mv cst &) (parse-full ,parse-fn input))
         (ast (,abs-fn cst)))
      (equal ast ,output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that parsing and then abstracting a file
; succeeds and returns the expected result.

(defmacro test-parse-abs-file (input output)
  `(assert-event
    (b* ((input (input-to-unicode-points ,input))
         (cst (parse-from-codepoints input))
         (ast (abs-file cst)))
      (equal ast ,output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This adds abstracting to PARSE-FROM-FILE-AT-PATH+ from the parser interface.
; The parser interface has more than just that function,
; so we could complement the following function with additional ones
; that add abstracting to the corresponding parser interface functions.

(define parse-and-abstract-from-file-at-path+ ((path stringp) state)
  :returns (mv (file file-resultp)
               (tree abnf::tree-resultp)
               (lexemes abnf::tree-listp)
               state)
  :parents (parser-abstractor-interface)
  :short "Parse and abstract a Leo file at a path."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the file, obtaining a file CST and a list of lexemes CSTs
     if there is no error.
     We call the abstractor on the file CST, obtaining a file AST
     if there is no error.
     These three items (file CST, lexeme CSTs, and file AST)
     are what is needed to check the correctness of Leo parsing,
     according to the specification."))
  (b* (((mv file-cst lexeme-csts state) (parse-from-file-at-path+ path state))
       ((when (reserrp file-cst))
        (mv (reserrf :cst-error) file-cst lexeme-csts state))
       (file-ast (abs-file file-cst)))
    (mv file-ast file-cst lexeme-csts state))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Example:

(b* (((mv file tree lexemes state)
      (parse-and-abstract-file-at-path "../add_simple.leo" state)))
  (acl2::value (list file tree lexemes)))

|#
