; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Contributing author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "grammar")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer
  :parents (concrete-syntax)
  :short "An executable lexer of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple lexer for the Yul lexical grammar.
     The grammar is defined in ABNF.
     See @(see grammar).")
   (xdoc::p
    "The primary API for lexing Yul is
     @(see lexemeize-yul) and @(see lexemeize-yul-bytes).")
   (xdoc::p
    "The lexer is defined in three sections:")
   (xdoc::ol
    (xdoc::li
     "Generation of specialized generator macros for this lexer.")
    (xdoc::li
     "Table of lexing functions for groups, options, and repetitions
      that occur internally to Yul grammar rules.")
    (xdoc::li
     "Definitions of lexing functions,
      most of which are just calls to macros that generate the functions,
      but some of which are hand-written
      due to limitations in the current parser generators.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 1:
;; Generation of specialized generator macros for this lexer.

(abnf::defdefparse yul
  :package "YUL"
  :grammar *grammar*
  :prefix lex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 2:
;; Table of lexing functions for groups, options, and repetitions.

;; --------------------------------
;; components for rule hex-string

;; The rule hex-string requires the components:
;; 1. the repetition 2hex-digit
;; 2. an optional underbar
;; 3. the group: ( [ "_" ] 2hex-digit )
;; 4. the repetition: *( [ "_" ] 2hex-digit )
;; 5. the option: [ 2hex-digit *( [ "_" ] 2hex-digit ) ]
;; 6. the big group after %s"hex".

;; --------------------------------
;; components for rule escape-sequence

;; The rule escape-sequence requires the components,
;; from inside to outside:
;; 1. The group:
;;    ( squote / dquote / %s"\" / %s"n" / %s"r" / %s"t" / lf / cr )
;;    call it "escape-sequence-single", as in a single char indicator
;; 2. 4hex-digit
;; 3. The group:
;;    ( ( squote / dquote / %s"\" / %s"n" / %s"r" / %s"t" / lf / cr )
;;      / %s"u" 4hex-digit
;;      / %s"x" 2hex-digit )
;;    call it "escape-sequence-body"

;; --------------------------------
;; components for rule string-literal

;; The rule string-literal requires the components,
;; from inside to outside:
;; 1. The group:
;;    ( double-quoted-printable / escape-sequence )
;; 2. The repetition, zero or more of #1:
;;    *( double-quoted-printable / escape-sequence )
;; 3. The group:
;;    ( single-quoted-printable / escape-sequence )
;; 4. The repetition, zero or more of #3:
;;    *( single-quoted-printable / escape-sequence )

;; --------------------------------
;; components for rule whitespace

;; rule:  whitespace = 1*whitespace-char
;; However, we don't yet have a generator for repeat one-or-more.
;; So we define a generator for zero-or-more and then,
;; in Part 3: "Define Lexing Functions" section below,
;; we generate the zero-or-more lexing function and call it
;; from lex-whitespace.

;; The repetition *whitespace-char does not actually appear in the rule!
;; It is just used to generate the zero-or-more lexing function
;; that we call from lex-whitespace.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event

 `(defparse-yul-group-table

    ;; component 3 for hex-string
    "( [ \"_\" ] 2hex-digit )" group-optional-underbar-and-two-hex-digits

    ;; component 6 for hex-string
    ,(str::cat "( dquote [ 2hex-digit *( [ \"_\" ] 2hex-digit ) ] dquote "
               "/ squote [ 2hex-digit *( [ \"_\" ] 2hex-digit ) ] squote )")
    group-for-hex-string

    ;; component 1 for escape-sequence
    "( squote / dquote / %s\"\\\" / %s\"n\" / %s\"r\" / %s\"t\" / lf / cr )"
    group-escape-sequence-single

    ;; component 3 for escape-sequence
    ,(str::cat
      "( ( squote / dquote / %s\"\\\" / %s\"n\" / %s\"r\" / %s\"t\" / lf / cr )"
      "  / %s\"u\" 4hex-digit"
      "  / %s\"x\" 2hex-digit )")
    group-escape-sequence-body

    ;; component 1 for string-literal
    "( double-quoted-printable / escape-sequence )" group-dquoted-or-escape

    ;; component 3 for string-literal
    "( single-quoted-printable / escape-sequence )" group-squoted-or-escape))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-yul-option-table

  ;; component 2 for hex-string
  "[ \"_\" ]" optional-underbar

  ;; component 5 for hex-string
  "[ 2hex-digit *( [ \"_\" ] 2hex-digit ) ]" optional-sequence-of-2hex-digits)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-yul-repetition-table

  "*decimal-digit" repetition-*-decimal-digit

  "*hex-digit" repetition-*-hex-digit

  ;; component 1 for hex-string
  "2hex-digit" repetition-2-hex-digits

  ;; component 4 for hex-string
  "*( [ \"_\" ] 2hex-digit )" repetition-*-optional-underbar-and-two-hex-digits

  ;; component 2 for escape-sequence
  "4hex-digit" repetition-4-hex-digits

  ;; component 2 for string-literal
  "*( double-quoted-printable / escape-sequence )"
  repetition-*-dquoted-or-escape

  ;; component 4 for string-literal
  "*( single-quoted-printable / escape-sequence )"
  repetition-*-squoted-or-escape

  "*identifier-rest" repetition-*-identifier-rest

  "*whitespace-char" repetition-*-whitespace-char

  "*not-lf-or-cr" repetition-*-not-lf-or-cr

  "*lexeme" repetition-*-lexeme)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 3:
;; Define Lexing Functions

;; Create the lexing functions for the above.

;; When we can't use the generators and we write lexing functions by hand,
;; we use the following naming convention for the trees and input sequences.
;; If we parse "foo" as a single element (or as a repetition)
;; then we call the tree(s) returned "tree(s)-foo"
;; and we call the remaining input "input-after-foo".

(defparse-yul-rulename "boolean")
(defparse-yul-rulename "dquote")
(defparse-yul-rulename "squote")
(defparse-yul-rulename "lf")
(defparse-yul-rulename "cr")
(defparse-yul-rulename "decimal-digit")
(defparse-yul-rulename "nonzero-decimal-digit")
(defparse-yul-rulename "hex-digit")

;; Used for decimal-number
(defparse-yul-*-rulename "decimal-digit")
(defparse-yul-rulename "decimal-number")

;; Used for hex-number
(defparse-yul-*-rulename "hex-digit")
(defparse-yul-rulename "hex-number")


;; --------------------------------
;; rule hex-string
;; See above "components for rule hex-string for the numbering.
;; Top-level alternation, then concatenation, are handled by rule.

;; 1. the repetition 2hex-digit
;;
;; There is no generator for this yet, so we define the lexing function
;; that is mentioned in *def-parse-repetition-fns*:
;;
(define lex-repetition-2-hex-digits ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex exactly 2 hexadecimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lex an 8-bit number expressed in hex."))
  (b* (((mv tree-digit1 input-after-digit1) (lex-hex-digit input))
       ((when (reserrp tree-digit1))
        (mv tree-digit1
            (nat-list-fix input)))
       ((mv tree-digit2 input-after-digit2) (lex-hex-digit input-after-digit1))
       ((when (reserrp tree-digit2))
        (mv tree-digit2
            ;; Note, this error result does not mention the successful
            ;; first hex digit, but that is fine, because rules fail
            ;; all the time and other rules succeed.
            (nat-list-fix input))))
    (mv (list tree-digit1 tree-digit2)
        input-after-digit2))
  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-2-hex-digits-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; 2. an optional underbar
(defparse-yul-option "[ \"_\" ]")

;; 3. the group: ( [ "_" ] 2hex-digit )
(defparse-yul-group "( [ \"_\" ] 2hex-digit )")

;; 4. the repetition: *( [ "_" ] 2hex-digit )
(defparse-yul-*-group "( [ \"_\" ] 2hex-digit )")
;; Note, this actually builds the repetition containing the group
;; and looks it up in the table of lexing functions for repetitions.

;; 5. the group: 2hex-digit *( [ "_" ] 2hex-digit )
;;    used as the option: [ 2hex-digit *( [ "_" ] 2hex-digit ) ]
(defparse-yul-option "[ 2hex-digit *( [ \"_\" ] 2hex-digit ) ]")

;; 6. ( dquote [ 2hex-digit *( [ "_" ] 2hex-digit ) ] dquote
;;    / squote [ 2hex-digit *( [ "_" ] 2hex-digit ) ] squote )
(make-event
 `(defparse-yul-group
    ,(str::cat "( dquote [ 2hex-digit *( [ \"_\" ] 2hex-digit ) ] dquote "
               "/ squote [ 2hex-digit *( [ \"_\" ] 2hex-digit ) ] squote )")))

;; Finally, the rule hex-string
(defparse-yul-rulename "hex-string")

;; --------------------------------

(defparse-yul-rulename "double-quoted-printable")
(defparse-yul-rulename "single-quoted-printable")

;; --------------------------------
;; rule escape-sequence

;; 1. The alternation (used as a group):
;;    ( squote / dquote / %s"\" / %s"n" / %s"r" / %s"t" / lf / cr )
(defparse-yul-group
  "( squote / dquote / %s\"\\\" / %s\"n\" / %s\"r\" / %s\"t\" / lf / cr )")

;; 2. the repetition 4hex-digit
;;
;; There is no generator for this yet, so we define the lexing function
;; that is mentioned in *def-parse-repetition-fns*:
;;
(define lex-repetition-4-hex-digits ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex exactly 4 hexadecimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lex a 16-bit number expressed in hex."))
  (b* (((mv tree-digit1 input-after-digit1) (lex-hex-digit input))
       ((when (reserrp tree-digit1))
        (mv tree-digit1
            (nat-list-fix input)))
       ((mv tree-digit2 input-after-digit2) (lex-hex-digit input-after-digit1))
       ((when (reserrp tree-digit2))
        (mv tree-digit2
            (nat-list-fix input)))
       ((mv tree-digit3 input-after-digit3) (lex-hex-digit input-after-digit2))
       ((when (reserrp tree-digit3))
        (mv tree-digit3
            (nat-list-fix input)))
       ((mv tree-digit4 input-after-digit4) (lex-hex-digit input-after-digit3))
       ((when (reserrp tree-digit4))
        (mv tree-digit4
            (nat-list-fix input)))
       )
    (mv (list tree-digit1 tree-digit2 tree-digit3 tree-digit4)
        input-after-digit4))
  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-4-hex-digits-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; 3. The group:
;;    ( ( squote / dquote / %s"\" / %s"n" / %s"r" / %s"t" / lf / cr )
;;      / %s"u" 4hex-digit
;;      / %s"x" 2hex-digit )
(make-event
 `(defparse-yul-group
    ,(str::cat
      "( ( squote / dquote / %s\"\\\" / %s\"n\" / %s\"r\" / %s\"t\" / lf / cr )"
      "  / %s\"u\" 4hex-digit"
      "  / %s\"x\" 2hex-digit )")))

;; Finally, the rule escape-sequence
(defparse-yul-rulename "escape-sequence")


;; --------------------------------
;; rule string-literal

;; 1. ( double-quoted-printable / escape-sequence )
(defparse-yul-group "( double-quoted-printable / escape-sequence )")

;; 2. *( double-quoted-printable / escape-sequence )
(defparse-yul-*-group "( double-quoted-printable / escape-sequence )")

;; 3. ( single-quoted-printable / escape-sequence )
(defparse-yul-group "( single-quoted-printable / escape-sequence )")

;; 4. *( single-quoted-printable / escape-sequence )
(defparse-yul-*-group "( single-quoted-printable / escape-sequence )")

;; the rule string-literal
(defparse-yul-rulename "string-literal")

;; --------------------------------

;; The rule for literal looks like this, with alternative numbers added
;; literal = decimal-number  1
;;         / hex-number      2
;;         / boolean         3
;;         / string-literal  4
;;         / hex-string      5

;; We must try hex-number before decimal-number in our lexer,
;; so that the initial 0 in 0x is not lexed as a decimal-number.
(defparse-yul-rulename "literal" :order (2 1 3 4 5))

;; --------------------------------

(defparse-yul-rulename "lowercase-letter")
(defparse-yul-rulename "uppercase-letter")
(defparse-yul-rulename "identifier-start")
(defparse-yul-rulename "identifier-rest")
(defparse-yul-*-rulename "identifier-rest")
(defparse-yul-rulename "identifier")

;; --------------------------------

(defparse-yul-rulename "whitespace-char")
(defparse-yul-*-rulename "whitespace-char")
; the preceding forms generates the function
; lex-repetition-*-whitespace-char

(define lex-whitespace ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Lex rule @('whitespace = 1*whitespace-char')."
  (b* (((mv tree-1char input-after-1char)
        (lex-whitespace-char input))
       ((when (reserrp tree-1char))
        (mv (reserrf "whitespace problem")
            (nat-list-fix input)))
       ((mv trees-restchars input-after-restchars)
        (lex-repetition-*-whitespace-char input-after-1char))
       ;; Can an error even happen?  Wouldn't it just return NIL (zero trees)?
       ;; Check error just in case.
       ((when (reserrp trees-restchars))
        (mv (reserrf "whitespace problem")
            (nat-list-fix input))))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "whitespace")
         :branches (list (cons tree-1char trees-restchars)))
        input-after-restchars))
  :hooks (:fix)
  ///
  (defret len-of-lex-whitespace-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))


;; --------------------------------

(defparse-yul-rulename "not-star")
(defparse-yul-rulename "not-star-or-slash")

(defines lex-rest-of-block-comment-fns
  :short "Mutually recursive part of block comment lexing."

  (define lex-rest-of-block-comment ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Lex rule @('rest-of-block-comment')."
    (b* (((mv trees input-after-trees)
          (b* (;; There are two alternatives.
               ;; First alternative:  ( "*" rest-of-block-comment-after-star )
               ((mv tree-star+rest input-after-star+rest)
                (b* (((mv tree-star input-after-star)
                      (abnf::parse-ichars "*" input))
                     ((when (reserrp tree-star))
                      (mv (reserrf "problem lexing \"*\"") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment-after-star
                       input-after-star))
                     ((when (reserrp tree-rest))
                      (mv (reserrf "problem lexing rest-of-block-comment-after-star") input)))
                  ;; combine the two trees into tree-star+rest
                  (mv (list (list tree-star) (list tree-rest))
                      input-after-rest)))
               ((unless (reserrp tree-star+rest))
                (mv tree-star+rest input-after-star+rest))
               ;; otherwise, try the second alternative:
               ;; ( not-star rest-of-block-comment )
               ((mv tree-not-star+rest
                    input-after-not-star+rest)
                (b* (((mv tree-not-star input-after-not-star)
                      (lex-not-star input))
                     ((when (reserrp tree-not-star))
                      (mv (reserrf "problem lexing not-star") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment input-after-not-star))
                     ((when (reserrp tree-rest))
                      (mv (reserrf "problem lexing rest-of-block-comment") input)))
                  ;; combine the two trees into
                  ;; tree-not-star+rest
                  (mv (list (list tree-not-star)
                            (list tree-rest))
                      input-after-rest))))
            (mv tree-not-star+rest
                input-after-not-star+rest)))
         ((when (reserrp trees))
          (mv trees (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "rest-of-block-comment")
           :branches trees)
          input-after-trees))
    :measure (len input))

  (define lex-rest-of-block-comment-after-star ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Lex rule @('rest-of-block-comment-after-star')."
    (b* (((mv trees input-after-trees)
          (b* (;; There are three alternatives.
               ;; First alternative: "/"
               ((mv tree-slash input-after-slash)
                (abnf::parse-ichars "/" input))
               ((unless (reserrp tree-slash))
                (mv (list (list tree-slash)) input-after-slash))
               ;; second alternative: ( "*" rest-of-block-comment-after-star )
               ((mv tree-star+rest input-after-star+rest)
                (b* (((mv tree-star input-after-star)
                      (abnf::parse-ichars "*" input))
                     ((when (reserrp tree-star))
                      (mv (reserrf "problem lexing \"*\"") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment-after-star
                       input-after-star))
                     ((when (reserrp tree-rest))
                      (mv (reserrf "problem lexing rest-of-block-comment-after-star") input)))
                  ;; combine the two trees into tree-star+rest
                  (mv (list (list tree-star)
                            (list tree-rest))
                      input-after-rest)))
               ((unless (reserrp tree-star+rest))
                (mv tree-star+rest input-after-star+rest))
               ;; otherwise, try the third alternative:
               ;; not-star-or-slash rest-of-block-comment
               ((mv tree-not-star-or-slash+rest
                    input-after-not-star-or-slash+rest)
                (b* (((mv tree-not-star-or-slash input-after-not-star-or-slash)
                      (lex-not-star-or-slash input))
                     ((when (reserrp tree-not-star-or-slash))
                      (mv (reserrf "problem lexing not-star-or-slash") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment input-after-not-star-or-slash))
                     ((when (reserrp tree-rest))
                      (mv (reserrf "problem lexing rest-of-block-comment") input)))
                  ;; combine the two trees into
                  ;; tree-not-star-or-slash+rest
                  (mv (list (list tree-not-star-or-slash)
                            (list tree-rest))
                      input-after-rest))))
            (mv tree-not-star-or-slash+rest
                input-after-not-star-or-slash+rest)))
         ((when (reserrp trees))
          (mv trees (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "rest-of-block-comment-after-star")
           :branches trees)
          input-after-trees))
    :measure (len input))

  :ruler-extenders :all

  :verify-guards nil ; done below
  ///
  (verify-guards lex-rest-of-block-comment)

  ;; We have two defret theorems.
  ;; 1. If we don't filter out result errors, the length of input bytes is nonincreasing
  ;; 2. If we do filter out result errors, the length of input bytes is strictly decreasing

  (std::defret-mutual len-of-input-after-lex-block-comment-fns-<=
    (defret len-of-input-after-rest-of-block-comment-<=
      (<= (len rest-input)
          (len input))
      :rule-classes :linear
      :fn lex-rest-of-block-comment)
    (defret len-of-input-after-rest-of-block-comment-after-star-<=
      (<= (len rest-input)
          (len input))
      :rule-classes :linear
      :fn lex-rest-of-block-comment-after-star))

  (std::defret-mutual len-of-input-after-lex-block-comment-fns-<
    (defret len-of-input-after-rest-of-block-comment-<
      (implies (not (reserrp tree))
               (< (len rest-input)
                  (len input)))
      :rule-classes :linear
      :fn lex-rest-of-block-comment)
    (defret len-of-input-after-rest-of-block-comment-after-star-<
      (implies (not (reserrp tree))
               (< (len rest-input)
                  (len input)))
      :rule-classes :linear
      :fn lex-rest-of-block-comment-after-star)))

(defparse-yul-rulename "block-comment")

;; --------------------------------
;; end of line comments

(defparse-yul-rulename "not-lf-or-cr")
(defparse-yul-*-rulename "not-lf-or-cr")
(defparse-yul-rulename "end-of-line-comment")
;; and a rule that recognizes either a block comment or an end-of-line-comment
(defparse-yul-rulename "comment")

;; --------------------------------
;; keywords, symbols, tokens, and lexemes

(defparse-yul-rulename "keyword")
(defparse-yul-rulename "symbol")
(defparse-yul-rulename "token")
(defparse-yul-rulename "lexeme")

;; --------------------------------
;; list of lexemes
;; lex-repetition-*-lexeme cann be used to tokenize a file
;; ( We do not define a rule "file-lexemes = *lexeme"
;;   since (1) there is no need to construct a tree around the list, and
;;   (2) the generator macro def-parse-rulename does not support nullable rules
;;   since it generates a return theorem that the rest-input be shorter than the input.)

(defparse-yul-*-rulename "lexeme")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Top-level interface functions

(define lexemeize-yul ((yul-string stringp))
  :returns (mv (erp booleanp) (yul-lexemes abnf::tree-listp))
  :short "Lexes the bytes of @('yul-string') into a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token, comment, or whitespace.  Lexemize-yul returns
     two values: an error flag and a list of these lexemes in @('abnf::tree') form.
     Lexemes are further separated into keyword, literal, identifier, or
     symbol.  Recombining these lexemes is done in the @(see parser)."))
  (b* (((mv trees rest-input)
        (lex-repetition-*-lexeme (acl2::string=>nats yul-string)))
       ;; It is probably impossible for trees to be reserrp, since
       ;; this call would instead just return the input that was not lexed.
       ;; However, check error trees for completeness.
       ((when (reserrp trees))
        (prog2$ (cw "tokenize-yul: reserrp should not happen here")
                (mv t nil)))
       ;; If the input ends in the middle of a token,
       ;; e.g., in a string without a closing quote,
       ;; then there will be remaining input.
       ;; Since this function starts with a presumably complete string,
       ;; we consider this an error.
       ;; Another useful function could be one that tokenizes from an input stream
       ;; and returns incomplete tokens as the rest of the stream.
       ((unless (null rest-input))
        (prog2$ (cw "tokenize-yul: string given cannot be fully tokenized; returning list of abnf trees found so far")
                (mv t trees))))
    (mv nil trees)))

;; A variation on lexemize-yul that takes a list of bytes
(define lexemeize-yul-bytes ((yul-bytes nat-listp))
  :returns (mv (erp booleanp) (yul-lexemes abnf::tree-listp))
  :short "Lexes the bytes into a list of lexemes."
  :long "This does the same thing as @(see lexemeize-yul), but does not need to
convert the string to bytes first."
  (b* (((mv trees rest-input)
        (lex-repetition-*-lexeme yul-bytes))
       ;; It is probably impossible for trees to be reserrp, since
       ;; this call would instead just return the input that was not lexed.
       ;; However, check error trees for completeness.
       ((when (reserrp trees))
        (prog2$ (cw "tokenize-yul: reserrp should not happen here")
                (mv t nil)))
       ;; If the input ends in the middle of a token,
       ;; e.g., in a string without a closing quote,
       ;; then there will be remaining input.
       ;; Since this function starts with a presumably complete program,
       ;; we consider this an error.
       ;; Another useful function could be one that tokenizes from an input stream
       ;; and returns incomplete tokens as the rest of the stream.
       ((unless (null rest-input))
        (prog2$ (cw "tokenize-yul: bytes given cannot be fully tokenized; returning list of abnf trees found so far")
                (mv t trees))))
    (mv nil trees)))
