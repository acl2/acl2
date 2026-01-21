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

(include-book "parser-interface")
(include-book "syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-abstractor-interface
  :parents (lexing-and-parsing)
  :short "API functions for parsing and abstracting Leo programs from CST to AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "This section defines convenient functions
     (whose names start with @('ast-from-'))
     for parsing and abstracting Leo programs and fragments.")
   (xdoc::p
    "By \"parsing\", we mean lexing, tokenization, and parsing, with
     the result being a CST (concrete syntax tree) for a Leo @('file').
     By \"abstracting\", we mean simplifying the CST into an abstract syntax
     tree (AST).")
   (xdoc::p
    "A list of specific Leo constructs is supported:
     @('file'), @('statement'), @('expression'), and @('token').
     For @('token'), we only support identifiers and atomic-literals."))
  :order-subtopics t
  :default-parent t)

; Additional interface functions can be added; see parser-interface.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; API functions that do lexing, tokenization, parsing, and AST abstraction
;; for a given grammar rule name.

;; What should abstraction do for a token?
;; In the case of keyword, numeral, symbol, and annotation tokens, it is
;; not clear that we ever need to find something to which we can abstract them,
;; so we do not support those tokens here at this time.
;; For identifier and atomic-literal tokens, it is straightforward:
;; we use abs-identifier and abs-atomic-literal.

;; NOTE: For rule-name "token", callers should understand that
;; the AST returned will be either an identifierp or literalp
;; (or reserrp).

(define ast-from-fragment ((rule-name stringp) (source-code stringp))
  :returns (ast-result (or (file-resultp ast-result)
                           (statement-resultp ast-result)
                           (expression-resultp ast-result)
                           (identifier-resultp ast-result)
                           (literal-resultp ast-result)))
  :short "Parse and abstract to AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Supported grammar rule names are @('file'), @('statement'), @('expression'),
     and @('token').")
   (xdoc::p
    "If the given rule cannot be parsed or if there are tokens left over,
     or if the resulting CST cannot be abstracted to AST,
     then a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('source-code'), when converted to codes, is required to be valid
     UTF-8."))
  (b* ((cst (parse-fragment-to-CST rule-name source-code))
       ((when (reserrp cst))
        cst))
    (if (equal rule-name "file")
        (abs-file cst)
      (if (equal rule-name "statement")
          (abs-statement cst)
        (if (equal rule-name "expression")
            (abs-expression cst)
          (if (equal rule-name "token")
              ;; The tokenizer lowers tokens to their inner tree.
              ;; The possible tokens are
              ;; keyword, identifier, atomic-literal, numeral, annotation, and symbol
              ;; Right now we only abstract identifier and atomic-literal.
              (b* (((okf rulename?) (abnf::check-tree-nonleaf? cst))
                   ((when (equal rulename? "identifier"))
                    (abs-identifier cst))
                   ((when (equal rulename? "atomic-literal"))
                    (abs-atomic-literal cst)))
                (reserrf (cons :not-yet-supported-token-type rulename?)))
            (reserrf (cons :not-yet-supported-top-level-rule-name rule-name))))))))

; Examples:
; (ast-from-fragment "token" "abc")
; (ast-from-fragment "token" "\"abc\"")
; (ast-from-fragment "expression" "\"abc\"")
; (ast-from-fragment "statement" "return \"abc\";")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parsing and abstracting full Leo file from various input types.

(define ast-from-string  ((leo-string stringp))
  :returns (tree file-resultp)
  :short "Parse UTF-8 ACL2 string and abstract to a Leo file AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, parses, and abstracts a Leo source file expressed
     as a string of acl2 characters whose char-codes are UTF-8 bytes.
     Returns a @('file') abstract syntax tree (AST).")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes the entire string or a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('leo-string'), when converted to codes, is required to be valid
     UTF-8."))
  (b* ((file-cst (parse-from-string leo-string))
       ((when (reserrp file-cst))
        file-cst))
    (abs-file file-cst)))

(define ast-from-file-at-path ((path stringp) state)
  :returns (mv (tree file-resultp)
               state)
  :short "Parse and abstract a Leo file at a path into an AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function attempts to parse and abstract a Leo source file at a given path.
     If parsing is successful, we return a @('file') AST (and state).
     If parsing is unsuccessful, we return an error value as first result."))
  (b* (((mv file-cst state) (parse-from-file-at-path path state))
       ((when (reserrp file-cst))
        (mv file-cst state)))
    (mv (abs-file file-cst) state)))
