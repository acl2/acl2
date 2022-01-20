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

(include-book "std/strings/decimal" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)
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
     The parser <see topic='@(url lexer)'>lexes</see>
     and <see topic='@(url tokenizer)'>tokenizes</see>
     according to the lexical grammar rules,
     and then parses according to the syntactic grammar rules.
     See @(see grammar-new).")
   (xdoc::p
    "The primary API for parsing Yul is @(see parse-yul) and @(see parse-yul-bytes)."))
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

;; Possible future work:
;; * Regularize the return value structure so that each parse function returns
;;   a single typed value rather than multiple values.
;;   This would have the benefits of being easier to read and extend,
;;   and it would make some jobs easier for the prover.
;; * Improve error handling so that callers keep a stack of errors.
;;   This would have the benefit that you can connect the top-level error
;;   to an inner error that is closer to where a problem needs to be fixed.
;;   Of course, many soft errors are expected, since parse rules are speculatively
;;   applied, using errors to indicate a particular rule does not apply.
;;   However, when a rule starts to apply and then fails in the middle,
;;   that information is often interesting.
;; * Improve xdoc.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token type: symbol

;; We could compute *yul-symbols* starting with this:
;;   (abnf::lookup-rulename (abnf::rulename "symbol") abnf::*def-parse-grammar*)
;; Currently the rule looks like
;;   symbol = "." / "," / "->" / "(" / ")" / ":=" / "{" / "}"

(defval *yul-symbols*
  '( "." "," "->" "(" ")" ":=" "{" "}"))

(define parse-symbol ((symbol stringp) (tokens abnf::tree-listp))
  :returns (tokens-after-symbol-or-resulterr abnf::tree-list-resultp
                                             :hints
                                             (("Goal" :in-theory
                                               (enable abnf::tree-listp-when-tree-list-resultp-and-not-resulterrp))))
;  :verbosep t ; for debugging
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
                  (err (cons "cst structure error" tokens))))

         (leafterm-nats (abnf::tree-leafterm->get (caar branches)))
         ((unless (acl2::unsigned-byte-listp 8 leafterm-nats))
          ;; Another incorrect structure hard error
          (prog2$ (er hard? 'top-level
                      (string-append "unexpected type of leafterm nats when parsing symbol: " symbol))
                  (err (cons "cst structure error 2" tokens))))

         (terminal-symbol (acl2::nats=>string leafterm-nats))
         ((unless (equal symbol terminal-symbol))
          ;; We didn't find this symbol, but something else might be valid at this point.
          (err (cons (concatenate 'string
                                  "looking for symbol: '" symbol
                                  "', but received symbol: '" terminal-symbol "'")
                     tokens))))
      (abnf::tree-list-fix (rest tokens))))
  ///
  (defret len-of-parse-symbol-<
    (implies (not (resulterrp tokens-after-symbol-or-resulterr))
             (< (len tokens-after-symbol-or-resulterr)
                (len tokens)))
    :rule-classes :linear
    )
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token type: keyword

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
                      (err (cons "cst structure error" tokens)))))

         (leafterm-nats (abnf::tree-leafterm->get (caar branches)))
         ((unless (acl2::unsigned-byte-listp 8 leafterm-nats))
          ;; Another incorrect structure hard error
          (prog2$ (er hard? 'top-level
                      (string-append "unexpected type of leafterm nats when parsing keyword: " keyword))
                  (mv nil
                      (err (cons "cst structure error 2" tokens)))))

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
  ///
  (defret len-of-parse-keyword-<
    (implies (not (resulterrp tokens-after-keyword-or-resulterr))
             (< (len tokens-after-keyword-or-resulterr)
                (len tokens)))
    :rule-classes :linear)
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
                      "unexpected type of leafterm nats when parsing identifier")
                  (mv nil
                      (err (cons "cst structure error" tokens))))))
      (mv (make-identifier :get (acl2::nats=>string fringe))
          (abnf::tree-list-fix (rest tokens)))))
  ///
  (defret len-of-parse-identifier-<
    (implies (not (resulterrp tokens-after-identifier-or-resulterr))
             (< (len tokens-after-identifier-or-resulterr)
                (len tokens)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token type: literal

;; ABNF rule:
;;   literal = decimal-number / hex-number / boolean / string-literal / hex-string
;; In the AST these alternatives map directly to alternatives of the sum type LITERAL.

;; 'literal' is an alternative under 'expression',
;; and it also is part of a 'switch-statement' after "case".

;; ---------------------------------
;; decimal-number

(define cst2ast-decimal-number ((tree abnf::treep))
  :returns (ast-node? literal-optionp)
  :short "Given a :nonleaf ABNF tree with rulename \"decimal-number\",
          return the appropriate literal AST node."
  ;; We don't bother checking the whole substructure.
  (b* ((fringe (abnf::tree->string tree))
       ((unless (acl2::unsigned-byte-listp 8 fringe))
        (prog2$ (er hard? 'top-level
                    "unexpected type of leafterm nats when parsing idenntifier")
                nil))
       (decimal-number-string (acl2::nats=>string fringe))
       (maybe-nat (str::strval decimal-number-string)))
    (if (natp maybe-nat)
        (make-literal-dec-number :get maybe-nat)
      nil)))

;; ---------------------------------
;; hex-number

(define cst2ast-hex-digit-char-list ((chars str::hex-digit-char-listp))
  :returns (hex-digits hex-digit-listp)
  (cond (;; it would be good to get rid of this first condition
         (not (and (str::hex-digit-char-listp chars)
                   (true-listp chars))) nil)
        ((endp chars) nil)
        (t (cons (make-hex-digit :get (car chars))
                 (cst2ast-hex-digit-char-list (cdr chars))))))

(define cst2ast-hex-number ((tree abnf::treep))
  :returns (ast-node? literal-optionp)
  :short "Given a :nonleaf tree with rulename \"hex-number\",
          return the appropriate literal AST node."
  ;; We don't bother checking the whole substructure.
  (b* ((fringe (abnf::tree->string tree))
       ((unless (acl2::unsigned-byte-listp 8 fringe))
        (prog2$ (er hard? 'top-level
                    "unexpected type of leafterm nats when parsing identifier")
                nil))
       ((unless (and (listp fringe)
                     (> (len fringe) 2)
                     (equal (first fringe) (char-code #\0))
                     (equal (second fringe) (char-code #\x))))
        nil)
       (hex-digit-char-codes (cddr fringe))
       ((unless (acl2::unsigned-byte-listp 8 hex-digit-char-codes))
        nil)
       (hex-digit-chars (acl2::nats=>chars hex-digit-char-codes))
       ((unless (str::hex-digit-char-listp hex-digit-chars))
        nil)
       (hex-digits (cst2ast-hex-digit-char-list hex-digit-chars)))
    (make-literal-hex-number :get hex-digits)))

;; ---------------------------------
;; boolean

(define cst2ast-boolean ((tree abnf::treep))
  :returns (ast-node? literal-optionp)
  :short "Given a :nonleaf tree with rulename \"boolean\",
          return the appropriate literal AST node."
  (b* ((fringe (abnf::tree->string tree))
       ((unless (acl2::unsigned-byte-listp 8 fringe))
        (prog2$ (er hard? 'top-level
                    "unexpected type of leafterm nats when parsing identifier")
                nil))
       (fringe-string (acl2::nats=>string fringe)))
    (cond ((equal fringe-string "true") (make-literal-boolean :get t))
          ((equal fringe-string "false") (make-literal-boolean :get nil))
          (t nil))))

;; ---------------------------------
;; string-literal

(defval *single-quote-tree-list*
  :short "A CST for the single quote start or end of a Yul string."
  (list (abnf::make-tree-nonleaf :rulename? (abnf::rulename "squote")
                                 :branches (list (list (abnf::make-tree-leafterm :get (list 39)))))))

(defval *double-quote-tree-list*
  :short "A CST for the double quote start or end of a Yul string."
  (list (abnf::make-tree-nonleaf :rulename? (abnf::rulename "dquote")
                                 :branches (list (list (abnf::make-tree-leafterm :get (list 34)))))))

(defval *double-quoted-content-rulenames*
  (list (abnf::rulename "double-quoted-printable") (abnf::rulename "escape-sequence")))
(defval *single-quoted-content-rulenames*
  (list (abnf::rulename "single-quoted-printable") (abnf::rulename "escape-sequence")))


;; a single backslash for an escape sequence
(defval *list-leafterm-92*
  (list (abnf::make-tree-leafterm :get (list (char-code #\\)))))

;; a single u for the start of a 4 hex digit unicode escape
(defval *list-leafterm-u*
  (list (abnf::make-tree-leafterm :get (list (char-code #\u)))))

;; a single x for the start of a 2 hex digit unicode escape
(defval *list-leafterm-x*
  (list (abnf::make-tree-leafterm :get (list (char-code #\x)))))

(define cst2ast-uhhhh ((escape-contents abnf::tree-listp))
  :returns (escape escape-resultp)
  (b* (((unless (and (abnf::tree-listp escape-contents)
                     (equal (len escape-contents) 4)))
        (err "unexpected input to cst2ast-uhhhh"))
       (fringe (abnf::tree-list->string escape-contents))
       ((unless (and (acl2::unsigned-byte-listp 8 fringe)
                     (equal (len fringe) 4)))
        (err "unexpected input to cst2ast-uhhhh 2"))
       (hex-digit-chars (acl2::nats=>chars fringe))
       ((unless (and (str::hex-digit-char-listp hex-digit-chars)
                     (str::hex-digit-char-p (first hex-digit-chars))
                     (str::hex-digit-char-p (second hex-digit-chars))
                     (str::hex-digit-char-p (third hex-digit-chars))
                     (str::hex-digit-char-p (fourth hex-digit-chars))))
        (err "unexpected input to cst2ast-uhhhh 3")))
    (make-escape-u
     :get (make-hex-quad
           :1st (make-hex-digit :get (first hex-digit-chars))
           :2nd (make-hex-digit :get (second hex-digit-chars))
           :3rd (make-hex-digit :get (third hex-digit-chars))
           :4th (make-hex-digit :get (fourth hex-digit-chars))))))

(define cst2ast-xhh ((escape-contents abnf::tree-listp))
  :returns (escape escape-resultp)
  (b* (((unless (and (abnf::tree-listp escape-contents)
                    (equal (len escape-contents) 2)))
       (err "unexpected input to cst2ast-xhh"))
       (fringe (abnf::tree-list->string escape-contents))
       ((unless (and (equal (len fringe) 2)
                     (acl2::unsigned-byte-listp 8 fringe)))
        (err "unexpected input to cst2ast-xhh 2"))
       (hex-digit-chars (acl2::nats=>chars fringe))
       ((unless (and (str::hex-digit-char-listp hex-digit-chars)
                     (str::hex-digit-char-p (first hex-digit-chars))
                     (str::hex-digit-char-p (second hex-digit-chars))))
        (err "unexpected input to cst2ast-xhh 3")))
    (make-escape-x
     :get (make-hex-pair
           :1st (make-hex-digit :get (first hex-digit-chars))
           :2nd (make-hex-digit :get (second hex-digit-chars))))))

(define cst2ast-single-char ((escape-contents abnf::tree-listp))
  :returns (escape escape-resultp)
  (b* (((unless (and (abnf::tree-listp escape-contents)
                     (equal (len escape-contents) 1)))
        (err "unexpected input to cst2ast-single-char"))
       (fringe (abnf::tree-list->string escape-contents))
       ((unless (and (equal (len fringe) 1)
                     (acl2::unsigned-byte-listp 8 fringe)))
        (err "unexpected input to cst2ast-single-char 2")))
    (case (car fringe)
      (39 (make-escape-single-quote))
      (34 (make-escape-double-quote))
      (92 (make-escape-backslash))
      (110 (make-escape-letter-n))
      (114 (make-escape-letter-r))
      (116 (make-escape-letter-t))
      (110 (make-escape-line-feed))
      (114 (make-escape-carriage-return))
      (t (err "unrecognized escaped character in cst2ast-single-char")))))

(define cst2ast-escape-sequence ((tree abnf::treep))
  :returns (element string-element-resultp)
  (b* (((unless (and (abnf::treep tree)
                     (abnf::tree-case tree :nonleaf)
                     (equal (abnf::tree-nonleaf->rulename? tree) (abnf::rulename "escape-sequence"))))
        (err "unexpected input to cst2ast-escape-sequence"))
       ((unless (and (equal (len (abnf::tree-nonleaf->branches tree)) 2)
                     (equal (car (abnf::tree-nonleaf->branches tree)) *list-leafterm-92*)))
        (err "unexpected input to cst2ast-escape-sequence 2"))
       (second-branch (cadr (abnf::tree-nonleaf->branches tree)))
       ;; in the case of \uFFFF, for example,
       ;; second-branch looks like  ((:NONLEAF NIL (((:LEAFTERM (117))) ..) ..))
       ((unless (and (abnf::tree-listp second-branch)
                     (equal (len second-branch) 1)))
        (err "unexpected input to cst2ast-escape-sequence 3"))
       (subtree (car second-branch))
       ;; in the case of \uFFFF, for example,
       ;; subtree looks like (:NONLEAF NIL (((:LEAFTERM (117))) ..) ..)
       ((unless (and (abnf::treep subtree)
                     (abnf::tree-case subtree :nonleaf)
                     (null (abnf::tree-nonleaf->rulename? subtree))))
        (err "unexpected input to cst2ast-escape-sequence 4"))
       (escape-sequence-contents (abnf::tree-nonleaf->branches subtree))
       ;; In the case of \uFFFF, for example,
       ;;   escape-sequence-contents looks like (((:LEAFTERM (117))) ..)
       ;;   where 117 is the char code of u.
       ;; escape-sequence-contents is either
       ;; (1) a tree-list-listp with a single tree containing the single char, or
       ;; (2) it has two branches, the first of which is u or x, and the second of which
       ;; has the four or two digits.
       ((unless (abnf::tree-list-listp escape-sequence-contents))
        (err "unexpected input to cst2ast-escape-sequence 5"))
       (yul-escape-or-err
        (cond ((= (length escape-sequence-contents) 1)
               (cst2ast-single-char (car escape-sequence-contents)))
              ((and (= (length escape-sequence-contents) 2)
                    (equal (first escape-sequence-contents) *list-leafterm-u*) )
               (cst2ast-uhhhh (second escape-sequence-contents)))
              ((and (= (length escape-sequence-contents) 2)
                    (equal (first escape-sequence-contents) *list-leafterm-x*))
               (cst2ast-xhh (second escape-sequence-contents)))
              (t (err "unexpected input to cst2ast-escape-sequence 6"))))
       ((when (resulterrp yul-escape-or-err))
        yul-escape-or-err))
    (make-string-element-escape :get yul-escape-or-err)))

(define cst2ast-quoted-printable ((subtree abnf::treep) (double-quoted-p booleanp))
  :returns (element string-element-resultp)
  :short "Given a :nonleaf tree for rulename \"single-quoted-printable\"
          or \"double-quoted-printable\", returns a string-element-char."
  ;; We don't check the structure except for making sure it is a single character.
  ;; We could check the structure more.
  (declare (ignorable double-quoted-p))
  (b* (((unless (and (abnf::treep subtree)
                     (abnf::tree-case subtree :nonleaf)))
        (err "unexpected input to cst2ast-quoted-printable"))
       (fringe (abnf::tree->string subtree))
       ((unless (and (equal (len fringe) 1)
                     (acl2::unsigned-byte-p 8 (car fringe))))
        (err "unexpected input to cst2ast-quoted-printable 2")))
    (make-string-element-char :get (code-char (car fringe)))))

;; content should be a nonleaf with a rulename? nil
;; Then the branches are list of list of nonleaf
;; That lower nonleaf has rulename one of
;;   single-quoted-printable, double-quoted-printable, escape-sequence
(define cst2ast-string-literal-content ((content abnf::treep) (double-quoted-p booleanp))
  :returns (element string-element-resultp)
  (b* (((unless (and (abnf::treep content)
                     (abnf::tree-case content :nonleaf)
                     (null (abnf::tree-nonleaf->rulename? content))))
        (err "bad structure for string literal content element"))
       (branches (abnf::tree-nonleaf->branches content))
       ((unless (and (abnf::tree-list-listp branches)
                     (equal (len branches) 1)
                     (listp (car branches))
                     (equal (len (car branches)) 1)))
        (err "bad structure for string literal content element 2"))
       (subtree (caar branches))
       ((unless (and (abnf::treep subtree)
                     (abnf::tree-case subtree :nonleaf)))
        (err "bad structure for string literal content element 3"))
       (rulename (abnf::tree-nonleaf->rulename? subtree))
       ((unless (or (and double-quoted-p
                        (member-equal rulename *double-quoted-content-rulenames*))
                   (and (not double-quoted-p)
                        (member-equal rulename *single-quoted-content-rulenames*))))
         (err "bad structure for string literal content element 4"))
       (string-element (cond ((equal rulename (abnf::rulename "escape-sequence"))
                              (cst2ast-escape-sequence subtree))
                             (t
                              (cst2ast-quoted-printable subtree double-quoted-p))))
       ((when (resulterrp string-element))
          (err "bad structure for string literal content element 4")))
    string-element))

(define cst2ast-string-literal-contents ((contents abnf::tree-listp) (double-quoted-p booleanp))
  :returns (elements string-element-list-resultp)
  ;; Each tree is a nonleaf with no rulename.
  (b* (((unless (and (abnf::tree-listp contents) (booleanp double-quoted-p)))
        (err "bad call to cst2ast-string-literal-contents"))
       ((when (endp contents))
        nil)
       (first-string-element (cst2ast-string-literal-content (car contents) double-quoted-p))
       ((unless (string-elementp first-string-element))
        (err "problem in cst2ast-string-literal-contents"))
       ((unless (listp (cdr contents)))
        (err "problem in cst2ast-string-literal-contents 2"))
       (rest-string-elements (cst2ast-string-literal-contents (cdr contents) double-quoted-p))
       ((unless (string-element-listp rest-string-elements))
        (err "problem in cst2ast-string-literal-contents 3")))
    (cons first-string-element
          rest-string-elements)))

(define cst2ast-string-literal ((tree abnf::treep))
  :returns (ast-node? literal-optionp)
  :short "Given a :nonleaf tree with rulename \"string-literal\",
          return the appropriate literal AST node."
  (b* (((unless (abnf::tree-case tree :nonleaf))
          nil)
       (branches (abnf::tree-nonleaf->branches tree))
       ((unless (and (listp branches)
                     ;; needs start and end quotes
                     (= (len branches) 3)))
        nil)
       ;; The string literal must start and end with the same thing.
       ((unless (equal (first branches)
                       (third branches)))
        nil)
       (double-quoted (equal (first branches) *double-quote-tree-list*))
       ;; If not delimited by double quotes, it must have single quotes.
       ((unless (or double-quoted
                    (equal (first branches) *single-quote-tree-list*)))
        nil)
       (content (cst2ast-string-literal-contents (second branches) double-quoted))
       ((unless (string-element-listp content))
        nil))
    (make-literal-plain-string
     :get (make-plain-string
           :content content
           :double-quote-p double-quoted))))

;; ---------------------------------
;; hex-string

(define looks-like-hex-string-fringe ((fringe nat-listp))
  :returns (yes/no booleanp)
  (and (true-listp fringe)
       (>= (len fringe) 5)
       (equal (subseq fringe 0 3)
              (list (char-code #\h) (char-code #\e) (char-code #\x)))
       (equal (nth 3 fringe) (nth (- (len fringe) 1) fringe))
       (member (nth 3 fringe) (list (char-code #\") (char-code #\')))
       t)) ; just so it will return t rather than the member it found

(define hex-chars-to-hex-pair-list ((chars str::hex-digit-char-listp))
  :returns (hex-pair-list hex-pair-list-resultp)
  (cond ((null chars) nil)
        ((not (and (str::hex-digit-char-listp chars)
                   (consp chars)
                   (consp (cdr chars))
                   (str::hex-digit-char-p (first chars))
                   (str::hex-digit-char-p (second chars))))
         (err "hex-char-codes-to-hex-pair-list: chars should be a true list of hex digits"))
        (t
         (let* ((hex-digit1 (make-hex-digit :get (first chars)))
                (hex-digit2 (make-hex-digit :get (second chars)))
                (first-hex-pair (make-hex-pair :1st hex-digit1 :2nd hex-digit2)))
           (if (not (str::hex-digit-char-listp (cddr chars)))
               (err "problem in hex-char-codes-to-hex-pair-list")
             (let ((rest-hex-pairs (hex-chars-to-hex-pair-list (cddr chars))))
               (if (not (hex-pair-listp rest-hex-pairs))
                   (err "problem in hex-char-codes-to-hex-pair-list 2")
                 (cons first-hex-pair rest-hex-pairs))))))))

(define cst2ast-hex-string ((tree abnf::treep))
  :returns (ast-node? literal-optionp)
  :short "Given a :nonleaf tree with rulename \"hex-string\",
          return the appropriate literal AST node."
  (b* (((unless (and (abnf::treep tree)
                    (abnf::tree-case tree :nonleaf)))
        nil)
       ;; There should be two branches, the first of which is "hex",
       ;; and then one with the delimited hex string.
       ;; However, for simplicity let's just use strings.
       (fringe (abnf::tree-list-list->string (abnf::tree-nonleaf->branches tree)))
       ((unless (and (true-listp fringe)
                     (acl2::unsigned-byte-listp 8 fringe)
                     ;; 4 for "hex'" and 1 for the closing "'
                     (>= (len fringe) 5)))
        nil)
       (hex-chars-and-underbars (subseq fringe 4 (- (len fringe) 1)))
       (hex-char-codes (remove-equal (char-code #\_) hex-chars-and-underbars))
       ((unless (acl2::unsigned-byte-listp 8 hex-char-codes))
        nil)
       (hex-chars (acl2::nats=>chars hex-char-codes))
       ((unless (str::hex-digit-char-listp hex-chars))
        nil)
       (hex-pairs (hex-chars-to-hex-pair-list hex-chars))
       ((unless (hex-pair-listp hex-pairs))
        nil)
       )
    (make-literal-hex-string
     :get (make-hex-string :content hex-pairs
                           :double-quote-p (equal (nth 3 fringe) (char-code #\"))))))


;; ---------------------------------
;; putting the literals together in parse-literal

(define cst2ast-literal-kind ((tree abnf::treep))
  :returns (ast-node? literal-optionp)
  :short "Given a tree under :nonleaf literal, return the appropriate literal AST node."
  (b* (;; probably should be moved to the guard
       ((unless (abnf::tree-case tree :nonleaf))
        nil)
       (maybe-rulename (abnf::tree-nonleaf->rulename? tree))
       ((unless (abnf::rulenamep maybe-rulename))
        nil)
       (rulestring (abnf::rulename->get maybe-rulename)))
    (cond ((equal rulestring "decimal-number")
           (cst2ast-decimal-number tree))
          ((equal rulestring "hex-number")
           (cst2ast-hex-number tree))
          ((equal rulestring "boolean")
           (cst2ast-boolean tree))
          ((equal rulestring "string-literal")
           (cst2ast-string-literal tree))
          ((equal rulestring "hex-string")
           (cst2ast-hex-string tree))
          (t nil))))

(define parse-literal ((tokens abnf::tree-listp))
  :returns (mv (ast-node literal-optionp) (tokens-after-literal-or-resulterr abnf::tree-list-resultp))
  :short "Attempts to eat a literal and build a literal AST node."
  :long
  (xdoc::topstring
    (xdoc::p
      "Returns two values: an optional literal AST node and either the list of remaining tokens or a resulterr.")
    (xdoc::p
      "If a valid literal token is found, the first value returned
       is a literal AST node of the appropriate kind.  Different kinds have different substructure.")
    (xdoc::p
      "If no literal is found, the first value returned is @('NIL') and the second value is a resulterr."))
  (b* (((when (endp tokens))
        ;; It is possible this always indicates malformed input or logic error.
        ;; However, just in case this can occur on a false parse branch,
        ;; we will detect and report it in the top-level entry point
        ;; rather than throwing a hard error here
        (mv nil
            (err (cons "ran out of tokens when trying to parse literal" tokens))))
       ((unless (abnf::tree-listp tokens))
        (mv nil
            (err "guard of parse-literal")))

       (putative-literal-tree (first tokens))
       ((unless (and (abnf::tree-case putative-literal-tree :nonleaf)
                     (equal (abnf::tree-nonleaf->rulename? putative-literal-tree)
                            (abnf::rulename "literal"))))
        ;; This is normal when trying various alternatives, so just return the resulterr.
        (mv nil
            (err (cons "token is not a literal" tokens))))

       (branches (abnf::tree-nonleaf->branches putative-literal-tree))
       ((unless (and (listp branches)
                     (equal (len branches) 1)
                     (listp (car branches))
                     (equal (len (car branches)) 1)
                     (abnf::treep (caar branches))
                     (abnf::tree-case (caar branches) :nonleaf)))
        ;; Once we know it is a nonleaf for rulename 'literal', the structure should be fixed,
        ;; so this is a hard error.
        (prog2$ (er hard? 'top-level
                    "literal token seems to have the wrong structure for a literal")
                (mv nil
                    (err (cons "program logic error 2" tokens)))))

       (parsed-literal-kind (cst2ast-literal-kind (caar branches)))
       ((when (null parsed-literal-kind))
        (mv nil
            (err "problem with literal substructure"))))
    (mv parsed-literal-kind
        (rest tokens)))
    ///
    (defret len-of-parse-literal-<
      (implies (not (resulterrp tokens-after-literal-or-resulterr))
               (< (len tokens-after-literal-or-resulterr)
                  (len tokens)))
      :rule-classes :linear)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; path

(define parse-*-.-identifier ((tokens abnf::tree-listp))
  :returns (mv (result-asts identifier-listp) (tokens-after-identifiers abnf::tree-listp))
  :short "Parses zero or more occurrences of '\".\" identifier' and returns a list of identifier AST nodes."
  (b* ((tokens (abnf::tree-list-fix tokens))
       ((when (endp tokens)) (mv nil tokens))
       (tokens-after-dot-or-err (parse-symbol "." tokens))
       ((when (resulterrp tokens-after-dot-or-err))
        (mv nil tokens))
       ;; saw a dot; look for an identifier
       ((mv first-id tokens-after-first-id)
        (parse-identifier tokens-after-dot-or-err))
       ((when (null first-id))
        (mv nil tokens))
       ((when (resulterrp tokens-after-first-id))
        (mv nil tokens))
       ((unless (identifierp first-id))
        (mv nil tokens))
       ((mv rest-ids tokens-after-rest-ids)
        (parse-*-.-identifier tokens-after-first-id)))
    (mv (cons first-id rest-ids)
        tokens-after-rest-ids))
  :measure (len tokens)
  ///
  (defret len-of-parse-*-.-identifier
    (<= (len tokens-after-identifiers)
        (len tokens))
    :rule-classes :linear))


;; path = identifier *( "." identifier )
(define parse-path ((tokens abnf::tree-listp))
  :returns (mv (ast-node path-resultp) (tokens-after-path abnf::tree-listp))
  :short "Attempts to eat a path and build a path AST node."
  (b* (((when (endp tokens))
        (mv (err (cons "no path here" tokens))
            nil))
       ((mv first-id tokens-after-first-id)
        (parse-identifier tokens))
       ((when (null first-id))
        (mv (err (cons "can't be path since no identifier" tokens))
            nil))
       ((when (resulterrp tokens-after-first-id))
        (mv (err (cons "can't be path since no identifier 2" tokens))
            nil))
       ((mv rest-ids rest-tokens)
        (parse-*-.-identifier tokens-after-first-id))
       ((unless (mbt (< (len rest-tokens) (len tokens))))
        (mv (err (cons "logic error" (cons tokens-after-first-id tokens))) nil)))
    (mv (make-path :get (cons first-id rest-ids)) rest-tokens))
  ///
  (defret len-of-parse-path-<
    (implies (not (resulterrp ast-node))
             (< (len tokens-after-path)
                (len tokens)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable not-resulterrp-when-pathp)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; expression and function-call mutual-recursion

;; Used in parse-function-call to help out the measure proof
(define parse-identifier-and-open-paren ((tokens abnf::tree-listp))
  :returns (mv (result-ast identifier-resultp) (tokens-after-id-and-open-paren abnf::tree-listp))
  :short "Attempts to eat an identifier and a following open parenthesis, and build an identifier AST node."
  (b* (((when (endp tokens))
        (mv (err "no id here") nil))
       ((mv id-ast? tokens-after-identifier-or-error)
        (parse-identifier tokens))
       ((when (or (null id-ast?)
                  (resulterrp tokens-after-identifier-or-error)))
        (mv (err "no id here 2") nil))
       (tokens-after-paren-or-error (parse-symbol "(" tokens-after-identifier-or-error))
       ((when (resulterrp tokens-after-paren-or-error))
        (mv (err "no start of funcall here") nil)))
    (mv id-ast? tokens-after-paren-or-error))
  ///
  (defret len-of-parse-identifier-and-open-paren-<
    (implies (not (resulterrp result-ast))
             (< (len tokens-after-id-and-open-paren)
                (len tokens)))
    :rule-classes :linear))

(defines parse-yul-expressions

  ;; expression = path / function-call / literal
  (define parse-expression ((tokens abnf::tree-listp))
    :returns (mv (result-ast expression-resultp) (tokens-after-expression abnf::tree-listp))
    :short "Attempts to eat an expression and build an expression AST node."
    (b* (((when (endp tokens))
          (mv (err (cons "no expression here" tokens)) nil))

         ;; First look for the literal, since that is unambiguous
         ((mv literal-ast tokens-after-literal-or-err)
          (parse-literal tokens))
         ((when (and (literalp literal-ast)
                     (not (resulterrp tokens-after-literal-or-err))))
          (mv (make-expression-literal :get literal-ast) tokens-after-literal-or-err))

         ;; Since path and function-call both start with an identifier,
         ;; but function-call requires a following "(", try function-call next
         ((mv function-call-ast tokens-after-function-call)
          (parse-function-call tokens))
         ((unless (resulterrp function-call-ast))
          (mv (make-expression-funcall :get function-call-ast)
              tokens-after-function-call))

         ;; Finally, try path.
         ((mv path-ast tokens-after-path)
          (parse-path tokens))
         ((unless (resulterrp path-ast))
          (mv (make-expression-path :get path-ast) tokens-after-path)))

      ;; none of those worked
      (mv (err (cons "no expression here 2" tokens)) nil))
    :measure (two-nats-measure (len tokens) 1))

  ;; function-call = identifier "(" [ expression *( "," expression ) ] ")"
  (define parse-function-call ((tokens abnf::tree-listp))
    :returns (mv (result-ast funcall-resultp) (tokens-after-funcall abnf::tree-listp))
    :short "Attempts to eat a function call and build a funcall AST node."
    (b* (((mv id-or-err tokens-after-id-and-open-paren)
          (parse-identifier-and-open-paren tokens))
         ((when (resulterrp id-or-err))
          (mv (err "no function call here 0") nil))

         ;; First expression in optional expression list
         ((mv first-expression-arg-ast tokens-after-first-expression)
          (parse-expression tokens-after-id-and-open-paren)))

      (if (resulterrp first-expression-arg-ast)

          ;; There are no expressions, so we need to see a close paren now
          (b* ((tokens-after-close-paren-or-err (parse-symbol ")" tokens-after-id-and-open-paren))
               ((when (resulterrp tokens-after-close-paren-or-err))
                (mv (err (cons "no ) after zero expressions so not a function call" tokens)) nil))
               ((unless (mbt (< (len tokens-after-close-paren-or-err)
                                (len tokens))))
                (mv (err "bad logic for defret") nil))
               )
            (mv (make-funcall :name id-or-err :args nil)
                tokens-after-close-paren-or-err))

        ;; we have one expression, now get zero or more ( ","  expression )
        (b* (;; but first inform the measure proof that len of tokens is decreasing
             ((unless (mbt (< (len tokens-after-first-expression) (len tokens))))
              (mv (err "bad logic for measure") nil))
             ((mv rest-expressions rest-tokens)
              (parse-*-comma-expression tokens-after-first-expression))
             (tokens-after-close-paren-or-err2 (parse-symbol ")" rest-tokens))
             ((when (resulterrp tokens-after-close-paren-or-err2))
              (mv (err (cons "no ) after one or more expressions so not a function call" tokens)) nil)))
          (mv (make-funcall
               :name id-or-err
               :args (cons first-expression-arg-ast rest-expressions))
              tokens-after-close-paren-or-err2))))
    :measure (two-nats-measure (len tokens) 0))

  (define parse-*-comma-expression ((tokens abnf::tree-listp))
    :returns (mv (result-asts expression-listp) (tokens-after-expressions abnf::tree-listp))
    :short "Parses zero or more occurrences of '\",\" expression' and returns a list of expression AST nodes."
    (b* ((tokens (abnf::tree-list-fix tokens)) ; either this or fix every return, for return type proof
         ((when (endp tokens))
          (mv nil tokens))
         (tokens-after-comma-or-err (parse-symbol "," tokens))
         ((when (resulterrp tokens-after-comma-or-err))
          (mv nil tokens))
         ;; saw a comma; look for an expression
         ((mv first-expr tokens-after-first-expr)
          (parse-expression tokens-after-comma-or-err))
         ((when (resulterrp first-expr))
          (mv nil tokens))
         ((unless (expressionp first-expr))
          (mv nil tokens))
         ;; inform measure proof
         ((unless (mbt (< (len tokens-after-first-expr) (len tokens))))
          (mv nil nil))
         ((mv rest-exprs tokens-after-rest-exprs)
          (parse-*-comma-expression tokens-after-first-expr)))
      (mv (cons first-expr rest-exprs)
          tokens-after-rest-exprs))
    :measure (two-nats-measure (len tokens) 0))

  :verify-guards nil
  ///
  (std::defret-mutual len-of-parse-expressions-<
    (defret len-of-parse-expression-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-expression)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-expression)
    (defret len-of-parse-function-call-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-funcall)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-function-call)
    (defret len-of-parse-*-comma-expression-<=
      (<= (len tokens-after-expressions) (len tokens))
      :rule-classes :linear
      :fn parse-*-comma-expression)
    :hints (("Goal"
             :in-theory (enable not-resulterrp-when-expressionp not-resulterrp-when-funcallp)
             :expand ((parse-*-comma-expression tokens)
                      (parse-function-call tokens))))
    )

  (verify-guards parse-expression)
  )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; variable-declaration = %s"let" identifier [ ":=" expression ]
;;                      / %s"let" identifier *( "," identifier )
;;                        [ ":=" function-call ]

;; In the abstract syntax, we have two kinds of statement
;; modelling these two alternatives: variable-single and variable-multi.


(define parse-*-comma-identifier ((tokens abnf::tree-listp))
  :returns (mv (result-asts identifier-listp) (tokens-after-identifiers abnf::tree-listp))
  :short "Parses zero or more occurrences of '\",\" identifier' and returns a list of identifier AST nodes."
  (b* ((tokens (abnf::tree-list-fix tokens))
       ((when (endp tokens)) (mv nil tokens))
       (tokens-after-comma-or-err (parse-symbol "," tokens))
       ((when (resulterrp tokens-after-comma-or-err))
        (mv nil tokens))
       ;; saw a comma; look for an identifier
       ((mv first-id tokens-after-first-id)
        (parse-identifier tokens-after-comma-or-err))
       ((when (null first-id))
        (mv nil tokens))
       ((when (resulterrp tokens-after-first-id))
        (mv nil tokens))
       ((unless (identifierp first-id))
        (mv nil tokens))
       ((mv rest-ids tokens-after-rest-ids)
        (parse-*-comma-identifier tokens-after-first-id)))
    (mv (cons first-id rest-ids)
        tokens-after-rest-ids))
  :measure (len tokens)
  ///
  (defret len-of-parse-*-comma-identifier-<=
    (<= (len tokens-after-identifiers)
        (len tokens))
    :rule-classes :linear))
;; consider having theorems that say
;; (implies (null result-asts) (= (len tokens-after-identifiers) (len tokens)))
;; and
;; (implies (not (null result-asts)) (< (len tokens-after-identifiers) (len tokens)))


(define parse-variable-declaration ((tokens abnf::tree-listp))
  :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
  :short "Attempts to eat a variable declaration and build a @('statement') AST node of kind @(':variable-single') or @(':variable-multi')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The syntax diagram for "
    (xdoc::ahref "https://docs.soliditylang.org/en/v0.8.10/grammar.html#a4.SolidityParser.yulVariableDeclaration"
                 "`yul-variable-declaration'")
    " allows two ways of parsing a variable declaration with a single identifier and an initialization of a function call."
    "For example, @('let x := s(0)').")
   (xdoc::p
    "The initialization can be a @('yul-expression') which can be a @('yul-function-call'), or the initialization can be a @('yul-function-call') directly."
    "Although the syntax does not differ, and a grammar does not dictate the AST that is built,
     we still must decide what to build."
    "We decided to build an @('expression') of kind @(':funcall') containing a @('funcall') object whenever there is a single identifier.")
   (xdoc::p
    "This treatment is consistent with the handling of single and muli-assignmebnts, but in "
    (xdoc::ahref "https://docs.soliditylang.org/en/v0.8.10/grammar.html#a4.SolidityParser.yulAssignment" "that case")
    " the syntax diagram dictates at least two @('yul-path') instances prior to a direct @('yul-function-call')."))

  (b* (((mv ?key1 tokens-after-let)
        (parse-keyword "let" tokens))
       ((when (resulterrp tokens-after-let))
        (mv (err (cons "no variable decl here" tokens)) nil))
       ((mv let-var-1 tokens-after-let-var-1)
        (parse-identifier tokens-after-let))
       ((when (null let-var-1))
        (mv (err (cons "no variable decl here 2" tokens)) nil))
       ((when (resulterrp tokens-after-let-var-1))
        (mv (err (cons "no variable decl here 3" tokens)) nil))
       ;; see if there are any more identifiers (preceded by commas)
       ((mv rest-identifiers tokens-after-rest-identifiers)
        (parse-*-comma-identifier tokens-after-let-var-1))
       ;; The init is optional in both the single and multi case.
       (tokens-after-init-symbol
        (parse-symbol ":=" tokens-after-rest-identifiers))
       ((mv init-ast tokens-final)
        (if (resulterrp tokens-after-init-symbol)
            (mv nil tokens-after-rest-identifiers)
          (b* (((mv init-ast tokens-after-init)
                (if (null rest-identifiers)
                    (parse-expression tokens-after-init-symbol)
                  (parse-function-call tokens-after-init-symbol)))
               ((when (resulterrp init-ast))
                ;; the init doesn't parse, but it is optional,
                ;; so skip it and unwind the tokens
                (mv nil tokens-after-rest-identifiers)))
            (mv init-ast tokens-after-init)))))
    (mv (if (null rest-identifiers)
            (make-statement-variable-single :name let-var-1
                                            :init init-ast)
          (make-statement-variable-multi :names (cons let-var-1 rest-identifiers)
                                         :init init-ast))
        tokens-final))
  ///
  (defret len-of-parse-variable-declaration-<
    (implies (not (resulterrp result-ast))
             (< (len tokens-after-statement) (len tokens)))
    :rule-classes :linear))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note:
;; Assignment statements and function call statements are the only two kinds of statements
;; that do not begin with a keyword.

;; assignment = path ":=" expression
;;            / path 1*( "," path ) ":=" function-call


(define parse-*-comma-path ((tokens abnf::tree-listp))
  :returns (mv (result-asts path-listp) (tokens-after-paths abnf::tree-listp))
  :short "Parses zero or more occurrences of '\",\" path' and returns a list of path AST nodes."
  (b* ((tokens (abnf::tree-list-fix tokens))
       ((when (endp tokens)) (mv nil tokens))
       (tokens-after-comma-or-err (parse-symbol "," tokens))
       ((when (resulterrp tokens-after-comma-or-err))
        (mv nil tokens))
       ;; saw a comma; look for an path
       ((mv first-path tokens-after-first-path)
        (parse-path tokens-after-comma-or-err))
       ((unless (pathp first-path))
        (mv nil tokens))
       ((mv rest-paths tokens-after-rest-paths)
        (parse-*-comma-path (abnf::tree-list-fix tokens-after-first-path))))
    (mv (cons first-path rest-paths)
        (abnf::tree-list-fix tokens-after-rest-paths)))
  :measure (len tokens)
  :hints (("Goal" :in-theory (enable not-resulterrp-when-pathp)))
  :verify-guards nil
  ///
  (verify-guards parse-*-comma-path)
  (defret len-of-parse-*-comma-path-<
    (<= (len tokens-after-paths)
        (len tokens))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable not-resulterrp-when-pathp))))
  )
;; consider having theorems that say
;; (implies (null result-asts) (= (len tokens-after-paths) (len tokens)))
;; and
;; (implies (not (null result-asts)) (< (len tokens-after-paths) (len tokens)))

(define parse-assignment-statement ((tokens abnf::tree-listp))
  :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
  :short "Attempts to eat an assignment statement and build a @('statement') AST node of kind @(':assign-single') or @(':assign-multiple')."
  (b* (((mv path-ast tokens-after-path)
        (parse-path tokens))
       ((when (resulterrp path-ast))
        (mv (err (cons "no assignment statement here" tokens))
            nil))
       ;; See how many more instances of ( "," path ) can be parsed.
       ;; Use zero-or-more and then check for quantity
       ;; before deciding whether to parse expression or function-call.
       ((mv additional-paths tokens-after-additional-paths)
        (parse-*-comma-path tokens-after-path))
       (tokens-after-assignment-symbol (parse-symbol ":=" tokens-after-additional-paths))
       ((when (resulterrp tokens-after-assignment-symbol))
        (mv (err (cons "assignment statement requires ':='" tokens)) nil))
       ((mv init-ast tokens-after-init-form)
        (if (null additional-paths)
            (parse-expression tokens-after-assignment-symbol)
          (parse-function-call tokens-after-assignment-symbol)))
       ((when (resulterrp init-ast))
        (mv (err (cons "assignment statement does not finish properly" tokens))
            nil)))
    (mv (if (null additional-paths)
            (make-statement-assign-single :target path-ast
                                          :value init-ast)
          (make-statement-assign-multi :targets (cons path-ast additional-paths)
                                       :value init-ast))
        tokens-after-init-form))
  ///
  (defret len-of-parse-assignment-statement-<
    (implies (not (resulterrp result-ast))
             (< (len tokens-after-statement) (len tokens)))
    :rule-classes :linear)
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; leave statement

(define parse-leave-statement ((tokens abnf::tree-listp))
  :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
  :short "Attempts to eat a @('\"leave\"') keyword and build a @('statement') AST node of kind @(':leave')."
  (b* (((mv statement-or-nil tokens-after-statement)
        (parse-keyword "leave" tokens)))
    (if (or (not (statementp statement-or-nil))
            (resulterrp tokens-after-statement))
        (mv (err "no leave statement here") (abnf::tree-list-fix tokens))
      (mv statement-or-nil (abnf::tree-list-fix tokens-after-statement))))
  ///
  (defret len-of-parse-leave-statement-<
    (implies (not (resulterrp result-ast))
             (< (len tokens-after-statement) (len tokens)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; break statement

(define parse-break-statement ((tokens abnf::tree-listp))
  :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
  :short "Attempts to eat a @('\"break\"') keyword and build a @('statement') AST node of kind @(':break')."
  (b* (((mv statement-or-nil tokens-after-statement)
        (parse-keyword "break" tokens)))
    (if (or (not (statementp statement-or-nil))
            (resulterrp tokens-after-statement))
        (mv (err "no break statement here") (abnf::tree-list-fix tokens))
      (mv statement-or-nil (abnf::tree-list-fix tokens-after-statement))))
  ///
  (defret len-of-parse-break-statement-<
    (implies (not (resulterrp result-ast))
             (< (len tokens-after-statement) (len tokens)))
    :rule-classes :linear))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; continue statement

(define parse-continue-statement ((tokens abnf::tree-listp))
  :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
  :short "Attempts to eat a @('\"continue\"') keyword and build a @('statement') AST node of kind @(':continue')."
  (b* (((mv statement-or-nil tokens-after-statement)
        (parse-keyword "continue" tokens)))
    (if (or (not (statementp statement-or-nil))
            (resulterrp tokens-after-statement))
        (mv (err "no continue statement here") (abnf::tree-list-fix tokens))
      (mv statement-or-nil (abnf::tree-list-fix tokens-after-statement))))
  ///
  (defret len-of-parse-continue-statement-<
    (implies (not (resulterrp result-ast))
             (< (len tokens-after-statement) (len tokens)))
    :rule-classes :linear))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; mutual recursion:
;; block, if-statement, for-statement, switch-statement, function-definition

;; [ Note: From the examples in solidity/test/libyul/yulOptimizerTests/*.yul
;;   the top level is either a block or an object.
;;   We do not support yul objects at this time. ]

;; The following hand-written recursive-descent parser is intended
;; to follow the syntactic grammar described in abnf-grammar-new.txt.

;; The top-level ast node is assumed to be a block, so that is what parse-yul will call.
;; But conceptually, a block is just one sort of statement, so we define that first.

;; tokens is a list of abnf trees, each of which has a rulename
;; from the set {"keyword", "literal", "identifier", "symbol"}

(defines parse-yul-statements

  ;; Note on return values.
  ;; If a given construct is not seen in the token stream,
  ;; we return '() as the new token stream (although it doesn't much matter what we return).
  ;; If we want to refer to the token stream, we put it in the err object
  ;; instead of returning it as the second value.

  ;; Note: use the same order to try statement alternatives
  ;; as they appear in the abnf grammar, as long as that will work.
  ;; If that does not work, permute as needed, but document why it must be permuted.
  (define parse-statement ((tokens abnf::tree-listp))
    :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
    (b* (((when (endp tokens))
          (mv (err "no statement here") nil))

         ;; block
         ((mv block-result tokens-after) (parse-block tokens))
         ((unless (resulterrp block-result))
          (mv (make-statement-block :get block-result)
              tokens-after))

         ;; variable declaration
         ((mv decl-result tokens-after) (parse-variable-declaration tokens))
         ((unless (resulterrp decl-result))
          (mv decl-result tokens-after))

         ;; assignment
         ((mv assignment-result tokens-after) (parse-assignment-statement tokens))
         ((unless (resulterrp assignment-result))
          (mv assignment-result tokens-after))

         ;; function call
         ((mv function-call-result tokens-after) (parse-function-call tokens))
         ((unless (resulterrp function-call-result))
          (mv (make-statement-funcall :get function-call-result)
              tokens-after))

         ;; if statement
         ((mv if-result tokens-after) (parse-if-statement tokens))
         ((unless (resulterrp if-result))
          (mv if-result tokens-after))

         ;; for statement
         ((mv for-result tokens-after) (parse-for-statement tokens))
         ((unless (resulterrp for-result))
          (mv for-result tokens-after))

         ;; switch statement
         ((mv switch-result tokens-after) (parse-switch-statement tokens))
         ((unless (resulterrp switch-result))
          (mv switch-result tokens-after))

         ;; leave
         ((mv leave-result tokens-after) (parse-leave-statement tokens))
         ((unless (resulterrp leave-result))
          (mv leave-result tokens-after))
         ;; break
         ((mv break-result tokens-after) (parse-break-statement tokens))
         ((unless (resulterrp break-result))
          (mv break-result tokens-after))
         ;; continue
         ((mv continue-result tokens-after) (parse-continue-statement tokens))
         ((unless (resulterrp continue-result))
          (mv continue-result tokens-after))

         ;; function definition
         ((mv fundef-result tokens-after) (parse-fundef tokens))
         ((unless (resulterrp fundef-result))
          (mv (make-statement-fundef :get fundef-result)
              tokens-after))

         )
      ;; if none of those
      (mv (err (cons "no statement seen" tokens)) nil))
    :measure (two-nats-measure (len tokens) 1))

  (define parse-block ((tokens abnf::tree-listp))
    :returns (mv (result-ast block-resultp) (tokens-after-block abnf::tree-listp))
    :short "Eats a block (delimited by @('{ }')) and builds a @('block') AST node."
    (b* (((when (endp tokens))
          (mv (err "no block here") nil))

         ;; parse required symbol "{"
         (tokens-after-open-brace-or-err
          (parse-symbol "{" tokens))
         ((when (resulterrp tokens-after-open-brace-or-err))
          (mv (err (cons "no block start here" tokens)) nil))
         ;; parse zero or more statements
         ((mv block-statements tokens-after-block-statements)
          (parse-*-statement tokens-after-open-brace-or-err))
         ;; parse required symbol "}"
         (tokens-after-close-brace-or-err
          (parse-symbol "}" tokens-after-block-statements))
         ((when (resulterrp tokens-after-close-brace-or-err))
          (mv (err (cons "no close brace for block" tokens)) nil))
         ((unless (mbt (< (len tokens-after-close-brace-or-err)
                          (len tokens))))
          (mv (err "logic error") nil)))
      (mv (make-block :statements block-statements)
          (abnf::tree-list-fix tokens-after-close-brace-or-err)))
    :measure (two-nats-measure (len tokens) 0))

  ;; if-statement = %s"if" expression block
  (define parse-if-statement ((tokens abnf::tree-listp))
    :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
    :short "Eats an @('if') statement and builds a @('statement') AST node of kind @(':if')."
    (b* (((when (endp tokens))
          (mv (err "no if statement here") nil))
         ;; parse required keyword "if"
         ((mv ?if-ast-node tokens-after-if-or-resulterr)
          (parse-keyword "if" tokens))
         ((when (resulterrp tokens-after-if-or-resulterr))
          (mv (err "no if statement here 2") nil))
         ((mv expression-or-err tokens-after-if-expression)
          (parse-expression tokens-after-if-or-resulterr))
         ((when (resulterrp expression-or-err))
          (mv (err "no expression after 'if'") nil))
         ((mv block-or-err tokens-after-if-block)
          (parse-block tokens-after-if-expression))
         ((unless (blockp block-or-err))
          (mv (err "no block after 'if' expression") nil)))
      (mv (make-statement-if :test expression-or-err
                             :body block-or-err)
          (abnf::tree-list-fix tokens-after-if-block)))
    :measure (two-nats-measure (len tokens) 0))

  ;; for-statement = %s"for" block expression block block
  (define parse-for-statement ((tokens abnf::tree-listp))
    :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
    :short "Eats a @('for') statement and builds a @('statement') AST node of kind @(':for')."
    (b* (((when (endp tokens))
          (mv (err "no for statement here") nil))

         ;; parse required keyword "for"
         ((mv ?for-ast-node tokens-after-for-or-resulterr)
          (parse-keyword "for" tokens))
         ((when (resulterrp tokens-after-for-or-resulterr))
          (mv (err "no for statement here 2") nil))

         ;; parse init block
         ((mv init-block tokens-after-init-block)
          (parse-block tokens-after-for-or-resulterr))
         ((when (resulterrp init-block))
          (mv (err "no init block after 'for'") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-init-block)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse test expression
         ((mv test-expression tokens-after-test-expression)
          (parse-expression tokens-after-init-block))
         ((when (resulterrp test-expression))
          (mv (err "no test expression for 'for'") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-test-expression)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse update block
         ((mv update-block tokens-after-update-block)
          (parse-block tokens-after-test-expression))
         ((when (resulterrp update-block))
          (mv (err "no update block for 'for'") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-update-block)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse body block
         ((mv body-block tokens-after-body-block)
          (parse-block tokens-after-update-block))
         ((when (resulterrp body-block))
          (mv (err "no body block for 'for'") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-body-block)
                          (len tokens))))
          (mv (err "logic error") nil)))

      (mv (make-statement-for :init init-block
                              :test test-expression
                              :update update-block
                              :body body-block)
          (abnf::tree-list-fix tokens-after-body-block)))
    :measure (two-nats-measure (len tokens) 0))

  ;; switch-statement = %s"switch" expression
  ;;                    ( 1*( %s"case" literal block ) [ %s"default" block ]
  ;;                      / %s"default" block )
  (define parse-switch-statement ((tokens abnf::tree-listp))
    :returns (mv (result-ast statement-resultp) (tokens-after-statement abnf::tree-listp))
    :short "Eats a @('switch') statement and builds a @('statement') AST node of kind @(':switch')."
    (b* (((when (endp tokens))
          (mv (err "no switch statement here") nil))

         ;; parse required keyword "switch"
         ((mv ?switch-ast-node tokens-after-switch-or-resulterr)
          (parse-keyword "switch" tokens))
         ((when (resulterrp tokens-after-switch-or-resulterr))
          (mv (err "no switch statement here 2") nil))

         ;; parse target expression
         ((mv target-expression tokens-after-target-expression)
          (parse-expression tokens-after-switch-or-resulterr))
         ((when (resulterrp target-expression))
          (mv (err "no target expression after 'switch'") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-target-expression)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse as many case clauses as we see (zero or more)
         ;; This combines the two alternatives; we will sort them out later.
         ((mv case-clauses tokens-after-case-clauses)
          (parse-*-case-clause tokens-after-target-expression))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-case-clauses)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; Parse an optional default clause.
         ;; Although the "default" keyword is not used anywhere else,
         ;; the most correct thing is if either the keyword or the block fails,
         ;; the whole clause fails and the clause is omitted.
         ((mv default-block-option tokens-after-block-option)
          (b* (;; parse default block keyword
               ((mv ?default-ast tokens-after-default-or-resulterr)
                (parse-keyword "default" tokens-after-case-clauses))
               ((when (resulterrp tokens-after-default-or-resulterr))
                (mv nil tokens-after-case-clauses))
               ;; parse default block
               ((mv default-block tokens-after-default-block)
                (parse-block tokens-after-default-or-resulterr))
               ((when (resulterrp default-block))
                (mv nil tokens-after-case-clauses)))
            (mv default-block tokens-after-default-block)))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-block-option)
                          (len tokens))))
          (mv (err "logic error") nil)))

      (if (and (null case-clauses) (null default-block-option))
          (mv (err "switch default block is not optional if there are no case clauses")
              nil)
        (mv (make-statement-switch
             :target target-expression
             :cases case-clauses
             :default default-block-option)
            (abnf::tree-list-fix tokens-after-block-option))))
    :measure (two-nats-measure (len tokens) 0))

  (define parse-case-clause ((tokens abnf::tree-listp))
    :returns (mv (result-ast swcase-resultp) (tokens-after-clause abnf::tree-listp))
    :short "Eats a @('case') clause for a @('switch') statement and builds an @('swcase') AST node."
    (b* (((when (endp tokens))
          (mv (err "no case clause here") nil))

         ;; parse required keyword "case"
         ((mv ?case-ast-node tokens-after-case-or-resulterr)
          (parse-keyword "case" tokens))
         ((when (resulterrp tokens-after-case-or-resulterr))
          (mv (err "no case clause here 2") nil))

         ;; parse the case's value, a literal
         ((mv value-literal? tokens-after-value-literal-or-resulterr)
          (parse-literal tokens-after-case-or-resulterr))
         ((unless (and (literalp value-literal?)
                       (not (resulterrp tokens-after-value-literal-or-resulterr))))
          (mv (err "can't parse case's value literal") nil))

         ;; parse the case's body, a block
         ((mv body-block tokens-after-body-block)
          (parse-block tokens-after-value-literal-or-resulterr))
         ((when (resulterrp body-block))
          (mv (err "can't parse case's body block") nil)))

      (mv (make-swcase :value value-literal?
                   :body body-block)
          tokens-after-body-block))
    :measure (two-nats-measure (len tokens) 0))

  (define parse-*-case-clause ((tokens abnf::tree-listp))
    :returns (mv (result-asts swcase-listp) (tokens-after-clauses abnf::tree-listp))
    :short "Eats as many case clauses and possible (zero or more)."
    :long
    (xdoc::topstring
     (xdoc::p
      "Although the syntax diagram for 'switch' shows one-or-more case clauses in the first alternative,
       the second alternative shows zero case clauses, so we combine those into this
       single function that parses zero-or-more clauses."))
    (b* (((when (endp tokens)) (mv nil nil))
         ((mv first-clause tokens-after-clause) (parse-case-clause tokens))
         ((when (resulterrp first-clause))
          ; found zero clauses here
          (mv nil (abnf::tree-list-fix tokens)))
         ;; We found first-clause, now look for more.
         ;; But first, help out the measure proof.
         ((unless (mbt (< (len tokens-after-clause) (len tokens))))
          (mv nil nil))
         ((mv rest-clauses rest-tokens)
          (parse-*-case-clause tokens-after-clause)))
      (mv (abnf::list-fix (cons first-clause rest-clauses))
          (abnf::tree-list-fix rest-tokens)))
    :measure (two-nats-measure (len tokens) 2))

  (define parse-fundef ((tokens abnf::tree-listp))
    :returns (mv (result-ast fundef-resultp) (tokens-after-fundef abnf::tree-listp))
    :short "Eats a function definition and builds a @('fundef') AST node."
    (b* (((when (endp tokens))
          (mv (err "no function definition here") nil))

         ;; parse required keyword "function"
         ((mv ?function-ast-node tokens-after-function-or-resulterr)
          (parse-keyword "function" tokens))
         ((when (resulterrp tokens-after-function-or-resulterr))
          (mv (err "no function definition here 2") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-function-or-resulterr)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse the function's name, an identifier
         ((mv id-or-null tokens-after-id-or-resulterr)
          (parse-identifier tokens-after-function-or-resulterr))
         ((when (null id-or-null))
          (mv (err "missing function name") nil))
         ((when (resulterrp tokens-after-id-or-resulterr))
          (mv (err "missing function name") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-id-or-resulterr)
                          (len tokens))))
            (mv (err "logic error") nil))

         ;; parse the required "("
         (tokens-after-open-paren (parse-symbol "(" tokens-after-id-or-resulterr))
         ((when (resulterrp tokens-after-open-paren))
          (mv (err "missing '(' in function definition") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-open-paren)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; Parse the function inputs, zero or more identifiers separated by commas.
         ;; Zero identifiers is allowed, so we return (mv nil tokens-after-open-paren)
         ;; in that case.
         ((mv input-ids tokens-after-input-ids)
          (b* (;; first identifier
               ((mv first-id tokens-after-first-id)
                (parse-identifier tokens-after-open-paren))
               ((when (null first-id))
                (mv nil tokens-after-open-paren))
               ((when (resulterrp tokens-after-first-id))
                (mv nil tokens-after-open-paren))
               ;; remaining identifiers
               ((mv rest-ids tokens-after-rest-ids)
                (parse-*-comma-identifier tokens-after-first-id)))
            (mv (cons first-id rest-ids) tokens-after-rest-ids)))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-input-ids)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse the required ")"
         (tokens-after-close-paren (parse-symbol ")" tokens-after-input-ids))
         ((when (resulterrp tokens-after-close-paren))
          (mv (err "missing ')' in function definition") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-close-paren)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; the "->" is optional
         ((mv output-ids tokens-after-output-ids)
          (b* ((tokens-after-arrow (parse-symbol "->" tokens-after-close-paren))
               ((when (resulterrp tokens-after-arrow))
                (mv nil tokens-after-close-paren))

               ;; inform the measure proof of the intermediate decrease
               ((unless (mbt (< (len tokens-after-arrow)
                                (len tokens))))
                (mv (err "logic error") nil))

               ;; Parse the function outputs, one or more identifiers separated by commas.
               ;; The first identifier is required since we already saw a "->"
               ((mv first-output-id tokens-after-first-output-id)
                (parse-identifier tokens-after-arrow))
               ((when (null first-output-id))
                (mv (err "missing output identifier in function definition") nil))
               ((when (resulterrp tokens-after-first-output-id))
                (mv (err "missing output identifier in function definition") nil))

               ;; inform the measure proof of the intermediate decrease
               ((unless (mbt (< (len tokens-after-first-output-id)
                                (len tokens))))
                (mv (err "logic error") nil))

               ;; remaining output identifiers
               ((mv rest-output-ids tokens-after-rest-output-ids)
                (parse-*-comma-identifier tokens-after-first-output-id))

               ;; inform the measure proof of the intermediate decrease
               ((unless (mbt (< (len tokens-after-rest-output-ids)
                                (len tokens))))
                (mv (err "logic error") nil)))
            (mv (cons first-output-id rest-output-ids)
                tokens-after-rest-output-ids)))
         ((when (resulterrp output-ids))
          (mv (err (cons "parse error in output ids" output-ids)) nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-output-ids)
                          (len tokens))))
          (mv (err "logic error") nil))

         ;; parse the required function body block
         ((mv body-block tokens-after-body-block)
          (parse-block tokens-after-output-ids))
         ((when (resulterrp body-block))
          (mv (err "no function definition body") nil))
         ;; inform the measure proof of the intermediate decrease
         ((unless (mbt (< (len tokens-after-body-block)
                          (len tokens))))
          (mv (err "logic error") nil)))

      (mv (make-fundef :name id-or-null
                       :inputs input-ids
                       :outputs output-ids
                       :body body-block)
          tokens-after-body-block))
    :measure (two-nats-measure (len tokens) 0))

  (define parse-*-statement ((tokens abnf::tree-listp))
    :returns (mv (result-asts statement-listp) (tokens-after-statements abnf::tree-listp))
    :short "Eats as many statements as possible (zero or more)."
    :long
    (xdoc::topstring
     (xdoc::p
      "In Yul, there is no statement separator.  There is enough syntax on each
       statement rule to make it reasonably easy to disambiguate the statements."))
    (b* (((when (endp tokens)) (mv nil nil))
         ((mv first-statement tokens-after-statement) (parse-statement tokens))
         ((when (resulterrp first-statement))
          ;; found zero statements here
          (mv nil (abnf::tree-list-fix tokens)))
         ;; We found first-statement, now look for more and return those found.
         ;; But first, help out the measure proof.
         ((unless (mbt (< (len tokens-after-statement) (len tokens))))
          (mv nil nil))
         ((mv rest-statements rest-tokens)
          (parse-*-statement tokens-after-statement)))
      (mv (abnf::list-fix (cons first-statement rest-statements))
          (abnf::tree-list-fix rest-tokens)))
    :measure (two-nats-measure (len tokens) 2))

  :ruler-extenders :all  ; it is possible that some of the uses of mbt to prove
    ; token length decrease are unnecessary after we added :ruler-extenders :all

  :verify-guards nil
  ///

  (std::defret-mutual len-of-parse-statements-<
    (defret len-of-parse-statement-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-statement)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-statement)
    (defret len-of-parse-block-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-block)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-block)
    (defret len-of-parse-if-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-statement)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-if-statement)
    (defret len-of-parse-for-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-statement)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-for-statement)
    (defret len-of-parse-switch-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-statement)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-switch-statement)
    (defret len-of-parse-case-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-clause)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-case-clause)
    (defret len-of-parse-*-case-clause-<=
      (<= (len tokens-after-clauses)
          (len tokens))
      :rule-classes :linear
      :fn parse-*-case-clause)
    (defret len-of-parse-fundef-<
      (implies (not (resulterrp result-ast))
               (< (len tokens-after-fundef)
                  (len tokens)))
      :rule-classes :linear
      :fn parse-fundef)
    (defret len-of-parse-*-statement-<=
      (<= (len tokens-after-statements)
          (len tokens))
      :rule-classes :linear
      :fn parse-*-statement)
    :hints (("Goal" :expand ((parse-*-statement tokens)
                             (parse-*-case-clause tokens)))))

  (verify-guards parse-statement)
  )


(define parse-yul ((yul-string stringp))
  :returns (block? block-resultp)
  :short "Parses a Yul source program string into abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('yul-string') must contain the surface syntax of a single Yul block.")
   (xdoc::p "Returns either a block or a resulterrp.
             Yul object notation is not supported at this time."))
  (b* ((tokens (tokenize-yul yul-string))
       ((when (resulterrp tokens))
        tokens)
       ((mv top-block tokens-after-ast) (parse-block tokens))
       ((when (resulterrp top-block))
        top-block)
       ;; We may want to relax this next restriction if we want multiple things
       ;; at the top level.
       ((unless (null tokens-after-ast))
        (err "after parsing top-level yul block, there should be no more tokens")))
    top-block))


;; variation on parse-yul that takes a list of bytes
(define parse-yul-bytes ((yul-bytes nat-listp))
  :returns (block? block-resultp)
  :short "Parses the Yul source program bytes into abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does the same thing as @(see parse-yul), but does not need to
convert the string to bytes first."))
  (b* ((tokens (tokenize-yul-bytes yul-bytes))
       ((when (resulterrp tokens))
        tokens)
       ((mv top-block tokens-after-ast) (parse-block tokens))
       ((when (resulterrp top-block))
        top-block)
       ;; We may want to relax this next restriction if we want multiple things
       ;; at the top level.
       ((unless (null tokens-after-ast))
        (err "after parsing top-level yul block, there should be no more tokens")))
    top-block))
