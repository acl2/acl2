; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/boolean-result" :dir :system)
(include-book "tokenizer")
(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (concrete-syntax)
  :short "An executable parser of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple parser for Yul code.
     The main entry point is @('parse-yul')."))
  :order-subtopics t
  :default-parent t)

;; Some conventions:
;; * If a parsing function just fails to parse, a resulterr is returned
;;   so that its caller can try other alternatives.
;; * If a parsing function fails due to malformed or unexpected input,
;;   we throw a hard error, and then return a resulterr for logic reasons.
;; When successful, some parsing functions just eat (e.g., parse-symbol);
;; some parsing functions sometimes just eat and sometimes eat and build (e.g., parse-keyword);
;; and some parsing functions always eat and build (e.g., parse-identifier).
;; If it only eats, there is only one return value, which is the remaining tokens.
;; If it sometimes or always builds,
;; there is another return value of type "-option" for the built object.
;; If parsing is successful and something is built, the built object is returned,
;; but if either (a) parsing is successful but doesn't build anything or
;; (b) parsing is not successful, then the built object returned is NIL.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token type: symbol

;; We could compute *yul-symbols* starting with this:
;;   (abnf::lookup-rulename (abnf::rulename "symbol") abnf::*def-parse-grammar*)
;; Currently the rule looks like
;;   symbol = "." / "," / "->" / "(" / ")" / ":=" / "{" / "}"

(defval *yul-symbols*
  '( "." "," "->" "(" ")" ":=" "{" "}"))

(define parse-symbol ((symbol stringp) (tokens abnf::tree-listp))
  :returns (tokens-after-symbol-or-resulterr abnf::tree-list-resultp)
  :short "Attempts to eat the named @('symbol'), returning either the list of remaining tokens or a resulterr."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('parse-symbol') does not build any AST on its own, since there is no Yul AST node class
     whose surface syntax can consist solely of a single symbol.")
   (xdoc::p
    "In this context, @('symbol') is a nonterminal in the ABNF grammar for Yul,
     and its alternatives are terminal symbols.
     See @('abnf-grammar-new.txt').")
   (xdoc::p
    "Parsing a symbol as a concrete syntax tree means we look for a nonleaf tree
      where the rulename is @('\"symbol\"')
      and the leafterm has the bytes (ASCII codes) of the terminal symbol's string."))

  ;; It is a logic error for this function to be called with a first argument that
  ;; does not name a valid Yul symbol.
  (if (not (member-equal symbol *yul-symbols*))
      (prog2$ (er hard? 'top-level
                  (string-append "parse-symbol called on something not in *yul-symbols*: " symbol))
              (err (cons "program logic error" tokens)))

    (b* (((when (endp tokens))
          ;; It is possible this always indicates malformed input or logic error.
          ;; However, just in case this can occur on a false parse branch,
          ;; we will detect and report it in the top-level entry point
          ;; rather than throwing a hard error here.
          (err (cons (string-append "ran out of tokens when trying to parse symbol: " symbol) tokens)))

         (putative-symbol-tree (first tokens))
         ((unless (and (abnf::tree-case putative-symbol-tree :nonleaf)
                       (equal (abnf::tree-nonleaf->rulename? putative-symbol-tree)
                              (abnf::rulename "symbol"))))
          ;; This is normal when trying various alternatives, so just return the resulterr.
          (err (cons "token is not a symbol" tokens)))

         (branches (abnf::tree-nonleaf->branches putative-symbol-tree))
         ((unless (and (listp branches)
                       (equal (len branches) 1)
                       (listp (car branches))
                       (equal (len (car branches)) 1)
                       (abnf::treep (caar branches))
                       (abnf::tree-case (caar branches) :leafterm)))
          ;; Once we know it is a nonleaf for rulename symbol, the structure should be fixed,
          ;; so this is a hard error.
          (prog2$ (er hard? 'top-level
                      (string-append "symbol token seems to have the wrong structure for symbol:" symbol))
                  (err (cons "program logic error 2" tokens))))

         (leafterm-nats (abnf::tree-leafterm->get (caar branches)))
         ((unless (acl2::unsigned-byte-listp 8 leafterm-nats))
          ;; Another incorrect structure hard error
          (prog2$ (er hard? 'top-level
                      (string-append "unexpected type of leafterm nats when parsing symbol: " symbol))
                  (err (cons "program logic error 3" tokens))))

         (terminal-symbol (acl2::nats=>string leafterm-nats))
         ((unless (equal symbol terminal-symbol))
          ;; We didn't find this symbol, but something else might be valid at this point.
          (err (cons (concatenate 'string
                                  "looking for symbol: '" symbol
                                  "', but received symbol: '" terminal-symbol "'")
                     tokens))))
      (abnf::tree-list-fix (rest tokens))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token type: symbol
;; PARSE-KEYWORD eats the given keyword.

;; We could compute *yul-keywords* starting with this:
;;   (abnf::lookup-rulename (abnf::rulename "keyword") abnf::*def-parse-grammar*)
;; Currently the rule looks like
;;   keyword = %s"function" / %s"if" / %s"for" / %s"switch" / %s"case" / %s"default" / %s"let" / %s"leave" / %s"break" / %s"continue"

(defval *yul-keywords*
  '( "function" "if" "for" "switch" "case" "default" "let" "leave" "break" "continue" ))

(define parse-keyword ((keyword stringp) (tokens abnf::tree-listp))
  :returns (mv (ast-node statement-optionp) (tokens-after-keyword-or-resulterr abnf::tree-list-resultp))
  :short "Attempts to eat the named @('keyword')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns two values: an optional statement AST node and either the list of remaining tokens or a resulterr.")
   (xdoc::p
    "If a keyword is found, and if it is @('leave'), @('break'), or @('continue'), then
     the appropriate statement is built and returned as the first value.
     If a different keyword is found, the first value returned is @('NIL'), since no other Yul AST node
     has surface syntax consisting solely of a single keyword.
     In either case, the second value returns is the list of remaining tokens after eating the keyword token.")
   (xdoc::p
    "If no keyword is found, the first value returned is @('NIL') and the second is a resulterr.")
   (xdoc::p
    "In this context, @('keyword') is a nonterminal in the ABNF grammar for Yul,
     and its alternatives are terminals (aka terminal symbols) that are the actual keywords.
     See @('abnf-grammar-new.txt').")
   (xdoc::p
    "Parsing a keyword as a concrete syntax tree means we look for a nonleaf tree
      where the rulename is @('\"keyword\"')
      and the leafterm has the bytes (ASCII codes) of the keyword string."))

  ;; It is a logic error for this function to be called with a first argument that
  ;; does not name a valid Yul keyword.
  (if (not (member-equal keyword *yul-keywords*))
      (prog2$ (er hard? 'top-level
                  (string-append "parse-keyword called on something not in *yul-keywords*: " keyword))
              (mv nil
                  (err (cons "program logic error" tokens))))

    (b* (((when (endp tokens))
          ;; It is possible this always indicates malformed input or logic error.
          ;; However, just in case this can occur on a false parse branch,
          ;; we will detect and report it in the top-level entry point
          ;; rather than throwing a hard error here.
          (mv nil
              (err (cons (string-append "ran out of tokens when trying to parse keyword: " keyword) tokens))))

         (putative-keyword-tree (first tokens))
         ((unless (and (abnf::tree-case putative-keyword-tree :nonleaf)
                       (equal (abnf::tree-nonleaf->rulename? putative-keyword-tree)
                              (abnf::rulename "keyword"))))
          ;; This is normal when trying various alternatives, so just return the resulterr.
          (mv nil
              (err (cons "token is not a keyword" tokens))))

         (branches (abnf::tree-nonleaf->branches putative-keyword-tree))
         ((unless (and (listp branches)
                       (equal (len branches) 1)
                       (listp (car branches))
                       (equal (len (car branches)) 1)
                       (abnf::treep (caar branches))
                       (abnf::tree-case (caar branches) :leafterm)))
          ;; Once we know it is a nonleaf for rulename keyword, the structure should be fixed,
          ;; so this is a hard error.
          (prog2$ (er hard? 'top-level
                      (string-append "keyword token seems to have the wrong structure for keyword:" keyword))
                  (mv nil
                      (err (cons "program logic error 2" tokens)))))

         (leafterm-nats (abnf::tree-leafterm->get (caar branches)))
         ((unless (acl2::unsigned-byte-listp 8 leafterm-nats))
          ;; Another incorrect structure hard error
          (prog2$ (er hard? 'top-level
                      (string-append "unexpected type of leafterm nats when parsing keyword: " keyword))
                  (mv nil
                      (err (cons "program logic error 3" tokens)))))

         (terminal-keyword (acl2::nats=>string leafterm-nats))
         ((unless (equal keyword terminal-keyword))
          ;; We didn't find this keyword, but something else might be valid at this point.
          (mv nil
              (err (cons (concatenate 'string
                                      "looking for keyword: '" keyword
                                      "', but received keyword: '" terminal-keyword "'")
                         tokens)))))
      (mv (cond ((equal keyword "leave") (make-statement-leave))
                ((equal keyword "break") (make-statement-break))
                ((equal keyword "continue") (make-statement-continue))
                (t nil))
          (abnf::tree-list-fix (rest tokens)))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token type: identifier

;; After identifying the token as an identifier, Let the fringe walker gather the full text of it.

(define parse-identifier ((tokens abnf::tree-listp))
  :returns (mv (ast-node identifier-optionp) (tokens-after-identifier-or-resulterr abnf::tree-list-resultp))
  :short "Attempts to eat an identifier token and build an identifier AST node."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns two values: an optional identifier AST node and either the list of remaining tokens or a resulterr.")
   (xdoc::p
    "If an identifier token is found, the first value returned is an identifier AST node with the full token leaf text.")
   (xdoc::p
    "If no identifier is found, the first value returned is @('NIL') and the second value is a resulterr."))
  (b* (((when (endp tokens))
          ;; It is possible this always indicates malformed input or logic error.
          ;; However, just in case this can occur on a false parse branch,
          ;; we will detect and report it in the top-level entry point
          ;; rather than throwing a hard error here
          (mv nil
              (err (cons "ran out of tokens when trying to parse identifier" tokens))))

         (putative-identifier-tree (first tokens))
         ((unless (and (abnf::tree-case putative-identifier-tree :nonleaf)
                       (equal (abnf::tree-nonleaf->rulename? putative-identifier-tree)
                              (abnf::rulename "identifier"))))
          ;; This is normal when trying various alternatives, so just return the resulterr.
          (mv nil
              (err (cons "token is not an identifier" tokens)))))

    ;; For brevity, do not walk the whole identifier tree separately here, just grab the fringe text.
    ;; abnf::tree->string states it returns stringp but it actually returns a list of nats.
    ;; Grab the nats, make sure they are usigned bytes, and then convert them to a string.
    (b* ((fringe (abnf::tree->string (first tokens)))
         ((unless (acl2::unsigned-byte-listp 8 fringe))
          (prog2$ (er hard? 'top-level
                      "unexpected type of leafterm nats when parsing idenntifier")
                  (mv nil
                      (err (cons "program logic error" tokens))))))
      (mv (make-identifier :get (acl2::nats=>string fringe))
          (abnf::tree-list-fix (rest tokens))))))
