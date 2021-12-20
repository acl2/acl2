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
                      (err (cons "cst structure error" tokens))))))
      (mv (make-identifier :get (acl2::nats=>string fringe))
          (abnf::tree-list-fix (rest tokens))))))

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
        (rest tokens))))
