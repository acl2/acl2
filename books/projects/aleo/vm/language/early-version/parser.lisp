; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM-EARLY")

(include-book "grammar")

(include-book "../../../leo/early-version/definition/addresses")
(include-book "../../../leo/early-version/definition/characters")
(include-book "../../../leo/early-version/definition/bit-sizes")

(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "projects/abnf/constructor-utilities" :dir :system)
(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)
(include-book "unicode/read-utf8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defxdoc+ ...)
; Right now lexing and parsing is combined into one pass ("level").

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 1:
;; Generate specialized macros for this parser.

(abnf::defdefparse aleo
  :package "ALEOVM-EARLY"
  :grammar *grammar*
  :prefix lex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 2:
;; Tables of parsing functions for groups, options, and repetitions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-aleo-group-table

  ;; --------------------------------
  ;; components for rule ws:
  ;; ws = *( 1*plain-ws / escaped-lf )

  "( 1*plain-ws / escaped-lf )" group-1*-plain-ws/escaped-lf

  ;; --------------------------------
  ;; components for rule "line-comment"
  ;; line-comment = "//" *( escaped-lf / not-lf-or-cr )

  "( escaped-lf / not-lf-or-cr )" group-escaped-lf/not-lf-or-cr

  ;; --------------------------------
  ;; components for rule "cws"

  "( comment / ws )" group-comment/ws

  ;; --------------------------------
  ;; components for rule "identifier"

  "( letter / digit / \"_\" )" group-letter/digit/_

  ;; --------------------------------
  ;; components for rule "register-access"
  ;;   register-access = register *( "." identifier )

  "( \".\" identifier )" group-dot-identifier

  ;; --------------------------------
  ;; components for rule "arithmetic-literal"
  ;; and rules that build arithmetic literals, e.g.:
  ;;   signed-literal = [ "-" ] 1*( digit *"_" ) signed-type

  "( digit *\"_\" )" group-digit-*-underbar

  ;; --------------------------------
  ;; components for rule "address-literal"

  ;; TODO[AC]: not clear why the following is a group (it is not in the grammar).
  ;; The group used for rule "address-char"
  ;;   "0" / "2" / ... / %s"z"
  ;; Note that the default for a string in ABNF is insensitive,
  ;; so if there is no %s in front of the string, it is
  ;; an insensitive string in the abstract syntax.
  ;; Additional note: it would be good to improve the generators
  ;; to handle disjunctions of single characters.
  "( \"0\" / \"2\" / \"3\" / \"4\" / \"5\" / \"6\" / \"7\" / \"8\" / \"9\" / %s\"a\" / %s\"c\" / %s\"d\" / %s\"e\" / %s\"f\" / %s\"g\" / %s\"h\" / %s\"j\" / %s\"k\" / %s\"l\" / %s\"m\" / %s\"n\" / %s\"p\" / %s\"q\" / %s\"r\" / %s\"s\" / %s\"t\" / %s\"u\" / %s\"v\" / %s\"w\" / %s\"x\" / %s\"y\" / %s\"z\" )" group-address-char

  "( address-char *\"_\" )" group-address-char-*-underbar

  ;; --------------------------------
  ;; components for rule "escaped-char"

  "( dq / \"\\\" / \"/\" / %s\"n\" / %s\"r\" / %s\"t\" / %s\"b\" / %s\"f\" / %s\"u\" \"{\" 1*6hex-digit \"}\" )" group-escaped-char-body

  ;; --------------------------------
  ;; Components for rule "entry-type"

  ;; I'm not sure "visibility" is the right technical term
  ;; so it is fine to change this name to something more official.
  "( %s\".constant\" / %s\".public\" / %s\".private\" )" group-entry-type-visibility

  ;; --------------------------------
  ;; Components for rule "record"

  "( %s\"address.public\" / %s\"address.private\" )" group-address-public/private

  "( %s\"u64.public\" / %s\"u64.private\" )" group-u64-public/private

  ;; --------------------------------
  ;; Components for rule "commit-op"

  "( \"256\" / \"512\" / \"768\" / \"1024\" )" group-bhp-sizes

  "( \"64\" / \"128\" )" group-ped-sizes

  ;; --------------------------------
  ;; Components for rule "hash-op"

  "( \"2\" / \"4\" / \"8\" )" group-psd-sizes

  ;; --------------------------------
  ;; Components for rule "unary"

  "( operand ws )" group-1-operand

  ;; --------------------------------
  ;; Components for rule "cast"

  ;; Note: is `1*( ws operand ) ws` the same as `ws 1*( operand ws)` ?
  ;; If so, maybe we could change the rule for "cast" to the latter
  ;; so that it makes use of the same `(operand ws)` group that `binary` uses.
  ;; The rule `call` is in a similar situation.

  "( ws operand )" group-1-ws-operand

  ;; --------------------------------
  ;; Components for rule "call"

  "( locator / identifier )" group-locator/identifier

  "( ws register )" group-1-ws-register

  ;; --------------------------------
  ;; Components for rule "instruction"

  "( unary / binary / ternary / is / assert / commit / hash / cast / call )" group-instruction-body

  ;; --------------------------------
  ;; Components for rule "program"

  "( mapping / struct / record / function / transition )" group-program-declaration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-aleo-option-table

  ;; --------------------------------
  ;; components for rule "arithmetic-literal"
  ;; and rules that build arithmetic literals, e.g.:
  ;;   signed-literal = [ "-" ] 1*( digit *"_" ) signed-type

  "[ \"-\" ]" optional-hyphen

  "[ finalize-command finalize ]" optional-transition-finalize)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-aleo-repetition-table

  ;; --------------------------------
  ;; components for rule ws:
  ;; ws = *( 1*plain-ws / escaped-lf )

  ;; This particular piece of syntax does not
  ;; actually appear in any rule!
  ;; It is just used to generate the zero-or-more lexing function
  ;; that we can call.
  "*plain-ws" repetition-*-plain-ws

  ;; This is not used by a generator but it will be
  ;; when we generate lexers for 1*xxx.
  "1*plain-ws" repetition-1*-plain-ws

  "*( 1*plain-ws / escaped-lf )" repetition-*-plain-ws-or-escaped-lf

  ;; --------------------------------
  ;; components for rule "line-comment"
  ;; line-comment = "//" *( escaped-lf / not-lf-or-cr )

  "*( escaped-lf / not-lf-or-cr )" repetition-*-escaped-lf/not-lf-or-cr

  ;; --------------------------------
  ;; components for rule "cws"

  "*( comment / ws )" repetition-*-comment/ws

  ;; --------------------------------
  ;; components for rule "identifier"

  "*( letter / digit / \"_\" )" repetition-*-letter/digit/_

  ;; --------------------------------
  ;; components for rule "register"
  ;;   register = %s"r" 1*digit

  ;; This particular piece of syntax does not
  ;; actually appear in any rule!
  ;; It is just used to generate the zero-or-more lexing function
  ;; that we can call.
  "*digit" repetition-*-digit

  "1*digit" repetition-1*-digit

  ;; --------------------------------
  ;; components for rule "register-access"
  ;;   register-access = register *( "." identifier )

  "*( \".\" identifier )" repetition-*-dot-identifier

  ;; --------------------------------
  ;; components for rule "arithmetic-literal"
  ;; and rules that build arithmetic literals, e.g.:
  ;;   signed-literal = [ "-" ] 1*( digit *"_" ) signed-type

  "*\"_\"" repetition-*-underbar

  "*( digit *\"_\" )" repetition-*-digit-*-underbar

  "1*( digit *\"_\" )" repetition-1*-digit-*-underbar

  ;; --------------------------------
  ;; components for rule "address-literal"

  ;; for use by ;; 1*( address-char *"_" )
  "*( address-char *\"_\" )" repetition-*-address-char-*-underbar

  "1*( address-char *\"_\" )" repetition-1*-address-char-*-underbar

  ;; --------------------------------
  ;; components for rule "escaped-char"

  "*hex-digit" repetition-*-hex-digit

  "1*6hex-digit" repetition-1*6-hex-digit

  ;; --------------------------------
  ;; Components for rule "string-literal"

  "*string-element" repetition-*-string-element

  ;; --------------------------------
  ;; Components for rule "struct"

  ;; See also *plain-ws for why we have both 0*tuple and 1*tuple here

  "*tuple" repetition-*-tuple

  "1*tuple" repetition-1*-tuple

  ;; --------------------------------
  ;; Components for rule "record"

  "*entry" repetition-*-entry

  ;; We don't need to define an entry for "1operand"
  ;; because the generator for rule "unary" understands a default repeat range of 1.

  ;; --------------------------------
  ;; Components for rule "binary"

  "2( operand ws )" repetition-2-operands

  ;; --------------------------------
  ;; Components for rule "ternary"

  "3( operand ws )" repetition-3-operands

  ;; --------------------------------
  ;; Components for rule "cast"

  "*( ws operand )" repetition-*-ws-operand

  "1*( ws operand )" repetition-1*-ws-operand

  ;; --------------------------------
  ;; Components for rule "call"

  "*( ws register )" repetition-*-ws-register

  "1*( ws register )" repetition-1*-ws-register

  ;; --------------------------------
  ;; Components for rule "function"

  "*function-input" repetition-*-function-input

  "*function-output" repetition-*-function-output

  "*instruction" repetition-*-instruction

  "1*instruction" repetition-1*-instruction

  ;; --------------------------------
  ;; Components for rule "finalize"

  "*finalize-input" repetition-*-finalize-input

  "*finalize-output" repetition-*-finalize-output

  "*command" repetition-*-command

  "1*command" repetition-1*-command

  ;; --------------------------------
  ;; Components for rule "transition"

  "*transition-input" repetition-*-transition-input

  "*transition-output" repetition-*-transition-output

  ;; --------------------------------
  ;; Components for rule "program"

  "*import" repetition-*-import

  "*( mapping / struct / record / function / transition )" repetition-*-program-declaration

  "1*( mapping / struct / record / function / transition )" repetition-1*-program-declaration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 3:
;; Define Lexing Functions

;; Create the lexing functions for the above.

;; When we can't use the generators and we write lexing functions by hand,
;; we use the following naming convention for the trees and input sequences.
;; If we parse "foo" as a single element (or as a repetition)
;; then we call the tree(s) returned "tree(s)-foo"
;; and we call the remaining input "input-after-foo".

(defparse-aleo-rulename "ht")
(defparse-aleo-rulename "lf")
(defparse-aleo-rulename "cr")
(defparse-aleo-rulename "sp")
(defparse-aleo-rulename "dq")

(defparse-aleo-rulename "visible-ascii")

;; This is only used by character, which is not used by other rules.
;; (defparse-aleo-rulename "safe-ascii")

(defparse-aleo-rulename "safe-nonascii")

;; This is not used by other rules.
;; (defparse-aleo-character "character")

;; --------------------------------
;; We want to change the grammar to remove this...
(defparse-aleo-rulename "escaped-lf")

(defparse-aleo-rulename "plain-ws")

;; --------------------------------
;; rule "ws"

;; We generate a parser for *plain-ws to use in the next definition
;; (since there is no generator for 1*plain-ws yet).
(defparse-aleo-*-rulename "plain-ws")

;; 1*plain-ws
;; There is no generator for this yet, so we define the lexing function
;; that is mentioned in *def-parse-repetition-fns*
(define lex-repetition-1*-plain-ws ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*plain-ws')."
  (b* (((mv tree-1-plain-ws input-after-1)
        (lex-plain-ws input))
       ((when (reserrp tree-1-plain-ws))
        (mv tree-1-plain-ws
            (acl2::nat-list-fix input)))
       ((mv trees-rest-plain-ws input-after-rest)
        (lex-repetition-*-plain-ws input-after-1))
       ;; check error just in case
       ((when (reserrp trees-rest-plain-ws))
        (mv (reserrf "1*plain-ws problem")
            (acl2::nat-list-fix input))))
    (mv (cons tree-1-plain-ws trees-rest-plain-ws)
        input-after-rest))
  :hooks (:fix)
  ///
  (defret len-of-lex-1*-plain-ws-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; 1*plain-ws / escaped-lf
(defparse-aleo-group "( 1*plain-ws / escaped-lf )")

;; *( 1*plain-ws / escaped-lf )
(defparse-aleo-*-group "( 1*plain-ws / escaped-lf )")

;; We want to simplify this when we get rid of "escaped-lf"
;; ws = *( 1*plain-ws / escaped-lf )
(defparse-aleo-rulename "ws")

;; Move to tests:
#||
(lex-ws (acl2::string=>nats ""))
(lex-ws (acl2::string=>nats " "))
(lex-ws (acl2::string=>nats " 	\\
"))
||#

;; --------------------------------
;; rule "line-comment"

(defparse-aleo-rulename "not-lf-or-cr")

;;  Although the default here is ":order (1 2)",
;;  we state it explicitly since this order is required for correct parsing.
(defparse-aleo-group "( escaped-lf / not-lf-or-cr )" :order (1 2))
(defparse-aleo-*-group "( escaped-lf / not-lf-or-cr )")

(defparse-aleo-rulename "line-comment")

;; Move to tests:
#||
(lex-line-comment (acl2::string=>nats "//"))
(lex-line-comment (acl2::string=>nats "//\\"))
;; This must consume the LF:
(lex-line-comment (acl2::string=>nats "//\\
"))
;; This stops before the CR
(lex-line-comment '(47 47 92 13))
;; This stops before the LF
(lex-line-comment (acl2::string=>nats "//\\stuff
"))
||#

;; --------------------------------
;; rules composing "block-comment"

(defparse-aleo-rulename "not-star")
(defparse-aleo-rulename "not-star-or-slash")

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
          (mv trees (acl2::nat-list-fix input))))
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
          (mv trees (acl2::nat-list-fix input))))
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

(defparse-aleo-rulename "block-comment")

;; Move to tests:
#||
(lex-block-comment (acl2::string=>nats "/**/"))
(lex-block-comment (acl2::string=>nats "/* * /
**/"))
(lex-block-comment (acl2::string=>nats "/* *
/*/"))
|#

;; --------------------------------
;; rule "comment"

(defparse-aleo-rulename "comment")

;; --------------------------------
;; rule "cws"

;; This:
;;    (defparse-aleo-group *lex-alternation-comment/ws* :order (1 2))
;; doesn't work because ws can be empty,
;; and the generator defines
;; DEFTHM LEN-OF-LEX-GROUP-COMMENT/WS-<
;; which is not correct.
;; So we write lex-group-comment/ws by hand.

(define lex-group-comment/ws ((input nat-listp))
  :returns (mv (ret-tree abnf::tree-resultp)
               (ret-input nat-listp))
  :short "Lex @('( comment / ws )')."
  (b* (((mv tree1 input1)
        (lex-comment input))
       ((when (not (reserrp tree1)))
        (mv (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree1)))
            input1))
       ((mv tree2 input2)
        (lex-ws input))
       ((when (not (reserrp tree2)))
        (mv (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree2)))
            input2)))
    (mv (reserrf
         (list
          :found (list tree1 tree2)
          :required "( comment / ws )"))
        (nat-list-fix input)))
  :hooks (:fix)
  ///
  (defret len-of-lex-group-comment/ws-<=
    (<= (len ret-input)
        (len input))
    :rule-classes :linear))

;; This:
;:   (defparse-aleo-*-group *lex-alternation-comment/ws*)
;; doesn't work because the generated recursive function doesn't terminate,
;; because ws can be empty.
;; So we write lex-repetition-*-comment/ws by hand.

(define lex-repetition-*-comment/ws ((input nat-listp))
  :returns (mv (ret-trees abnf::tree-listp)
               (ret-input nat-listp))
  :short "Lex @('*( comment / ws )')."
  (b* (((mv tree1 input1)
        (lex-group-comment/ws input))
       ;; "comment" requires some input, but "ws" does not.
       ;; If zero input was successfully lexed, we DON'T  want to build a CST
       ;; of one empty ws; instead we want to return
       ;; zero elements of *( comment / ws ).
       ((when (or (reserrp tree1)
                  (= (len input1) (len input))))
        (mv nil (nat-list-fix input)))
       ((mv rest-trees rest-input)
        (lex-repetition-*-comment/ws input1)))
    (mv (cons tree1 rest-trees)
        (nat-list-fix rest-input)))
  :hooks (:fix)
  :measure (len input)
  :verify-guards nil ; done below
  ///
  (verify-guards lex-repetition-*-comment/ws)

  (defret len-of-lex-repetition-*-comment/ws
    (<= (len ret-input)
        (len input))
    :rule-classes :linear))

;; This:
;;   (defparse-aleo-rulename "cws")
;; doesn't work because it creates a ( DEFTHM LEN-OF-LEX-CWS-< ...)
;; but its contents can be empty.

(define lex-cws ((input nat-listp))
  :returns (mv (ret-tree abnf::tree-resultp)
               (ret-input nat-listp))
  (b* (((mv tree-ws input-after-ws)
        (lex-ws input))
       ((when (reserrp tree-ws))
        ;; This should never happen, so maybe something about that
        ;; should be added to the error.
        (mv tree-ws (nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-comment/ws input-after-ws)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "cws")
         :branches (list
                    (list tree-ws)
                    trees))
        input-after-trees
        ))
  :hooks (:fix)
  ///
  (defret len-of-lex-cws
    (<= (len ret-input)
        (len input))
    :rule-classes :linear))


;; --------------------------------
;; letters and digits

(defparse-aleo-rulename "uppercase-letter")

(defparse-aleo-rulename "lowercase-letter")

(defparse-aleo-rulename "letter")

(defparse-aleo-rulename "digit")

(defparse-aleo-rulename "hex-digit")


;; --------------------------------
;; rule "identifier"

(defparse-aleo-group "( letter / digit / \"_\" )")
(defparse-aleo-*-group "( letter / digit / \"_\" )")

(defparse-aleo-rulename "identifier")

;; Move to tests:
#||
(lex-identifier (acl2::string=>nats "a"))
(lex-identifier (acl2::string=>nats "Z"))
(lex-identifier (acl2::string=>nats "a_"))
(lex-identifier (acl2::string=>nats "Z0"))
(lex-identifier (acl2::string=>nats "Z_9"))
||#


;; --------------------------------
;; program-id and locator

(defparse-aleo-rulename "program-id")
(defparse-aleo-rulename "locator")


;; --------------------------------
;; rule "register"

;; We generate a parser for *digit to use in the next definition
;; (since there is no generator for 1*digit yet).
(defparse-aleo-*-rulename "digit")

(define lex-repetition-1*-digit ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*digit')."
  (b* (((mv tree-1 input-after-1)
        (lex-digit input))
       ((when (reserrp tree-1))
        (mv tree-1
            (acl2::nat-list-fix input)))
       ((mv trees-rest input-after-rest)
        (lex-repetition-*-digit input-after-1))
       ;; check error just in case
       ((when (reserrp trees-rest))
        (mv (reserrf "1*digit problem")
            (acl2::nat-list-fix input))))
    (mv (cons tree-1 trees-rest)
        input-after-rest))
  :hooks (:fix)
  ///
  (defret len-of-lex-1*-digit-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-aleo-rulename "register")

;; Move to tests:
#||
(lex-register (acl2::string=>nats "r0"))
(lex-register (acl2::string=>nats "r99999999"))
;; Must fail (i.e., leaves (82 48) in input):
(lex-register (acl2::string=>nats "R0"))
||#

;; --------------------------------
;; rule "register-access"

(defparse-aleo-group "( \".\" identifier )")
(defparse-aleo-*-group "( \".\" identifier )")

(defparse-aleo-rulename "register-access")

;; Move to tests:
#||
(lex-register-access (acl2::string=>nats "r0.z_A9_"))
||#


;; --------------------------------
;; rules "unsigned-type" through "arithmetic-type"
;;
;; These are later in the aleo.abnf
;; but they are needed for the arithmetic literals
;; so we moved them here.

(defparse-aleo-rulename "unsigned-type")
(defparse-aleo-rulename "signed-type")
(defparse-aleo-rulename "integer-type")
(defparse-aleo-rulename "field-type")
(defparse-aleo-rulename "group-type")
(defparse-aleo-rulename "scalar-type")
(defparse-aleo-rulename "arithmetic-type")


;; --------------------------------
;; rule "signed-literal"

(defparse-aleo-option "[ \"-\" ]")

(define lex-repetition-*-underbar ((input nat-listp))
  :returns
  (mv (trees abnf::tree-listp)
      (rest-input nat-listp))
  :short "Lex zero or more underbars."
  (b* (((mv tree-underbar1 input-after-underbar1)
        (abnf::parse-ichars "_" input))
       ((when (reserrp tree-underbar1))
        (mv nil (nat-list-fix input)))
       ((mv trees-rest input-after-rest)
        (lex-repetition-*-underbar input-after-underbar1)))
    (mv (cons tree-underbar1 trees-rest)
        input-after-rest))
  :measure (len input)
  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-*-underbar
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

(defparse-aleo-group "( digit *\"_\" )")

(defparse-aleo-*-group "( digit *\"_\" )")

(define lex-repetition-1*-digit-*-underbar ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*( digit *\"_\"')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-group-digit-*-underbar input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-digit-*-underbar input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-digit-*-underbar-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-digit-*-underbar-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "signed-literal")

;; Move to tests:
#||
(lex-signed-literal (acl2::string=>nats "0i8"))
(lex-signed-literal (acl2::string=>nats "-0i16"))
(lex-signed-literal (acl2::string=>nats "0_i32"))
(lex-signed-literal (acl2::string=>nats "-9__i64"))
(lex-signed-literal (acl2::string=>nats "-0010__i128"))
||#

;; --------------------------------
;; rules "unsigned-literal" through "arithmetic-literal"

(defparse-aleo-rulename "unsigned-literal")
(defparse-aleo-rulename "integer-literal")
(defparse-aleo-rulename "field-literal")
(defparse-aleo-rulename "group-literal")
(defparse-aleo-rulename "scalar-literal")
(defparse-aleo-rulename "arithmetic-literal")


;; --------------------------------
;; rules for remaining literal types

(defparse-aleo-rulename "address-type")
(defparse-aleo-rulename "boolean-type")
(defparse-aleo-rulename "string-type")
(defparse-aleo-rulename "literal-type")


;; --------------------------------
;; rule "address-literal"
;;   address-literal = %s"aleo1" 1*( address-char *"_" )

;; The following:
;;   (acl2::with-output :off :all :gag-mode t
;;     (defparse-aleo-rulename "address-char")
;; takes far too long to generate.
;; It is a good candidate for improving generator efficiency!
;; Currently, we define a list of valid address-char char codes
;; and check if a single nat is in the list.

(defconst *address-char-nats*
  ;; Warning, this idiom will only work right if all the chars in the string
  ;; have char-code < 256.
  (string=>nats "023456789acdefghjklmnpqrstuvwxyz"))

(define address-char-nat-p (n)
  :returns (y/n booleanp)
  (not (null (member n *address-char-nats* :test 'eql))))

(define lex-group-address-char ((input nat-listp))
  :returns
  (mv (tree abnf::tree-resultp)
      (rest-input nat-listp))
  (b* (((mv first-nat input-after-first-nat)
        (abnf::parse-next input))
       ((when (reserrp first-nat))
        (mv (reserrf-push first-nat)
            (nat-list-fix input)))
       ((unless (address-char-nat-p first-nat))
        (mv (reserrf "not a valid address char")
            (nat-list-fix input)))
       )
    (mv (abnf::tree-leafterm (list first-nat))
        input-after-first-nat))
  :hooks (:fix)
  ///
  (defret len-of-lex-group-address-char-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; The following:
;;   (defparse-aleo-rulename "address-char")
;; still is too slow at this point, since it still tries to generate the
;; disjunction instead of noticing that the disjunction abstract syntax
;; is in *lex-alternation-address-char*.
;; So we write the function for the rule by hand.

(define lex-address-char ((input nat-listp))
  :short "Lex an @('address-char')."
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((mv tree-char input-after-char)
        (lex-group-address-char input))
       ((when (reserrp tree-char))
        (mv (reserrf-push tree-char)
            (nat-list-fix input))))
    (mv (abnf-tree-wrap tree-char "address-char")
        input-after-char))
  :hooks (:fix)
  ///
  (defret len-of-lex-address-char-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)
  (defret len-of-lex-address-char-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-aleo-group "( address-char *\"_\" )")
(defparse-aleo-*-group "( address-char *\"_\" )")

(define lex-repetition-1*-address-char-*-underbar ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*( address-char *\"_\" )')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-group-address-char-*-underbar input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-digit-*-underbar input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-address-char-*-underbar-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-address-char-*-underbar-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "address-literal")

;; Move to tests:
#||
(lex-address-literal (string=>nats "aleo10"))
(lex-address-literal (string=>nats "aleo10_"))
(lex-address-literal (string=>nats "aleo1z__"))
(lex-address-literal (string=>nats "aleo1ac"))
||#


;; --------------------------------
;; rule "boolean-literal"

(defparse-aleo-rulename "boolean-literal")


;; --------------------------------
;; rule "escaped-char"

(defparse-aleo-*-rulename "hex-digit")

(define lex-repetition-1*6-hex-digit ((input nat-listp))
  :returns (mv (trees abnf::tree-list-resultp)
               (rest-input nat-listp))
  :short "Lex a @('1*6hex-digit')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lex Unicode escape sequences.
     We just lex any number of hexadecimal digits,
     and we ensure that we find between one and six.
     If we read none, it is clearly a failure.
     If we read more than six, there is no point in
     just considering the first six and continuing the lexing,
     because the six hexadecimal digits must be followed by a closing brace:
     so, if instead there is a seventh hexadecimal digit,
     this cannot be part of a valid Unicode character escape."))
  (b* (((mv trees input1) (lex-repetition-*-hex-digit input))
       ((unless (and (<= 1 (len trees))
                     (<= (len trees) 6)))
        (mv (reserrf (list :found trees))
            (nat-list-fix input))))
    (mv trees input1))
  :hooks (:fix)
  ///

  (defret len-of-lex-1*6-hex-digit-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

(defparse-aleo-group "( dq / \"\\\" / \"/\" / %s\"n\" / %s\"r\" / %s\"t\" / %s\"b\" / %s\"f\" / %s\"u\" \"{\" 1*6hex-digit \"}\" )")

(defparse-aleo-rulename "escaped-char")

;; Move to tests:
#||
(lex-escaped-char (string=>nats "\\\""))
(lex-escaped-char (string=>nats "\\\\"))
(lex-escaped-char (string=>nats "\\/"))
(lex-escaped-char (string=>nats "\\n"))
(lex-escaped-char (string=>nats "\\r"))
(lex-escaped-char (string=>nats "\\t"))
(lex-escaped-char (string=>nats "\\b"))
(lex-escaped-char (string=>nats "\\f"))
(lex-escaped-char (string=>nats "\\u{0}"))
(lex-escaped-char (string=>nats "\\u{a}"))
(lex-escaped-char (string=>nats "\\u{A}"))
(lex-escaped-char (string=>nats "\\u{000000}"))
(lex-escaped-char (string=>nats "\\u{ffffff}"))
(lex-escaped-char (string=>nats "\\u{FFFFFF}"))
||#

;; --------------------------------
;; rule "string-literal"

(defparse-aleo-rulename "not-dq-or-backslash")
(defparse-aleo-rulename "escaped-ws")
(defparse-aleo-rulename "string-element")
(defparse-aleo-*-rulename "string-element")
(defparse-aleo-rulename "string-literal")

;; Move to tests:
#||
(lex-string-literal (string=>nats "\"\""))
(lex-string-literal (string=>nats "\"abc\""))
(lex-string-literal (string=>nats "\" \""))
;; Note that the nats are Unicode code points.
;; UTF-8 must be decoded to code points before being passed to the parser.
(lex-string-literal '(34 1071 34)) ; Я
(lex-string-literal (string=>nats "\"\\\""))
;; Unusual rule "escaped-ws" allows 1 or more whitespaces after the backslash.
;; Because some editors truncate trailing whitespace, I insert spaces
;; as numbers.
(lex-string-literal (append (string=>nats "\"\\") '(32 32 32)
                            (string=>nats "
	\"")))
(lex-string-literal (string=>nats "\"a\nb\rc\t\""))
||#

;; --------------------------------
;; rule "literal"

(defparse-aleo-rulename "literal")

;; Move to tests:
#||
(lex-literal (string=>nats "-3i8"))
(lex-literal (string=>nats "3__i8"))
(lex-literal (string=>nats "3u8")) ; yes, it allows "-" for now
(lex-literal (string=>nats "-3__u8"))
(lex-literal (string=>nats "-3_field"))
(lex-literal (string=>nats "-0__group"))
(lex-literal (string=>nats "3scalar"))
(lex-literal (string=>nats "aleo10"))
(lex-literal (string=>nats "aleo10_"))
||#

;; --------------------------------

(defparse-aleo-rulename "operand")

;; --------------------------------

(defparse-aleo-rulename "plaintext-type")

(defparse-aleo-rulename "value-type")

;; Move to tests:
#||
(lex-value-type (string=>nats "u16.constant"))
(lex-value-type (string=>nats "foo.constant"))
(lex-value-type (string=>nats "field.public"))
(lex-value-type (string=>nats "scalar.private"))
(lex-value-type (string=>nats "foo.record"))
(lex-value-type (string=>nats "prog.id/foo.record"))
||#

(defparse-aleo-rulename "finalize-type")

;; Move to tests:
#||
(lex-finalize-type (string=>nats "i128.public"))
(lex-finalize-type (string=>nats "bar.public"))
(lex-finalize-type (string=>nats "bar.record"))
(lex-finalize-type (string=>nats "prog.id/bar.record"))
||#


;; --------------------------------
;; rule "entry-type"

(defparse-aleo-group "( %s\".constant\" / %s\".public\" / %s\".private\" )")
(defparse-aleo-rulename "entry-type")

;; Move to tests:
#||
(lex-entry-type (string=>nats "address.constant"))
(lex-entry-type (string=>nats "foo.constant"))
(lex-entry-type (string=>nats "boolean.public"))
(lex-entry-type (string=>nats "foo.public"))
(lex-entry-type (string=>nats "string.private"))
(lex-entry-type (string=>nats "foo.private"))
||#


(defparse-aleo-rulename "register-type")

;; Move to tests:
#||
(lex-register-type (string=>nats "prog.id/bar.record"))
(lex-register-type (string=>nats "bar.record"))
(lex-register-type (string=>nats "group"))
(lex-register-type (string=>nats "bar"))
||#


;; --------------------------------
;; rule "import"

(defparse-aleo-rulename "import")

;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------
;; rule "mapping"

(defparse-aleo-rulename "mapping-key")
(defparse-aleo-rulename "mapping-value")
(defparse-aleo-rulename "mapping")

;; Move to tests:
#||
;; from leo/examples/token/build/main.aleo
(lex-mapping (string=>nats "
mapping account:
	key left as address.public;
	value right as u64.public;"))
||#


;; --------------------------------
;; rule "tuple"

(defparse-aleo-rulename "tuple")

;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------
;; rule "struct"

(defparse-aleo-*-rulename "tuple")

(define lex-repetition-1*-tuple ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*tuple')."
  (b* (((mv tree-1-tuple input-after-1)
        (lex-tuple input))
       ((when (reserrp tree-1-tuple))
        (mv tree-1-tuple
            (acl2::nat-list-fix input)))
       ((mv trees-rest-tuple input-after-rest)
        (lex-repetition-*-tuple input-after-1))
       ;; check error just in case
       ((when (reserrp trees-rest-tuple))
        (mv (reserrf "1*tuple problem")
            (acl2::nat-list-fix input))))
    (mv (cons tree-1-tuple trees-rest-tuple)
        input-after-rest))
  :hooks (:fix)
  ///
  (defret len-of-lex-1*-tuple-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-aleo-rulename "struct")

;; Move to tests:
#||
;; from leo/examples/message/build/main.aleo
(lex-struct (string=>nats "
struct message:
    first as field;
    second as field;"))
||#

;; --------------------------------

(defparse-aleo-rulename "entry")

;; --------------------------------
;; rule "record"

(defparse-aleo-group "( %s\"address.public\" / %s\"address.private\" )")
(defparse-aleo-group "( %s\"u64.public\" / %s\"u64.private\" )")
(defparse-aleo-*-rulename "entry")
(defparse-aleo-rulename "record")

;; Move to tests:
#||
;; from leo/examples/token/build/main.aleo
(lex-record (string=>nats "record token:
    owner as address.private;
    gates as u64.private;
    amount as u64.private;"))
||#


;; --------------------------------
;; rule "unary-op"

;; :order says to try "abs.w" before "abs"
(defparse-aleo-rulename "unary-op" :order (2 1 3 4 5 6 7 8))

;; Move to tests:
#||
(lex-unary-op (string=>nats "abs"))
(lex-unary-op (string=>nats "abs.w"))
||#


;; --------------------------------
;; rule "binary-op"

;; The following:
;;   (acl2::with-output :off :all :gag-mode t
;;     (defparse-aleo-rulename "binary-op"))
;; takes far too long to generate (killed after 24 min and 180 GB allocated).
;; It is a good candidate for improving generator efficiency!

(define lex-binary-op ((input nat-listp))
  :short "Lex a @('binary-op')."
  :returns (mv (ret-tree abnf::tree-resultp)
               (ret-input nat-listp))
  ;; We make sure to reorder the op names so that a longer op name
  ;; is tried before a shorter op name that is a prefix of the longer one.
  (b* (((mv outer-tree outer-input-after-tree)
        (b* (((mv tree input-after-tree)
              (abnf::parse-schars "add.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "add" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "sub.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "sub" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "mul.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "mul" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "div.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "div" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "rem.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "rem" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "mod" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "pow.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "pow" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "shl.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "shl" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "shr.w" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "shr" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "and" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "or" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "xor" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "nand" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "nor" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "gte" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "gt" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "lte" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree))

             ((mv tree input-after-tree)
              (abnf::parse-schars "lt" input))
             ((unless (reserrp tree))
              (mv tree input-after-tree)))

          (mv (reserrf-push tree)
              (nat-list-fix input))))

       ((when (reserrp outer-tree))
        (mv outer-tree (nat-list-fix input))))

    (mv (abnf-tree-wrap outer-tree "binary-op")
        outer-input-after-tree))
  :hooks (:fix)
  ///
  (defret len-of-lex-binary-op-<=
    (<= (len ret-input)
        (len input))
    :rule-classes :linear)
  (defret len-of-lex-binary-op-<
    (implies (not (reserrp ret-tree))
             (< (len ret-input)
                (len input)))
    :rule-classes :linear))

;; Move to tests:
#||
(lex-binary-op (string=>nats "add"))
(lex-binary-op (string=>nats "add.w"))
(lex-binary-op (string=>nats "lte"))
(lex-binary-op (string=>nats "lt"))
||#

;; --------------------------------

(defparse-aleo-rulename "ternary-op")

;; --------------------------------
;; rule "is-op"

(defparse-aleo-rulename "is-op")

;; Move to tests:
#||
(lex-is-op (string=>nats "is.eq"))
(lex-is-op (string=>nats "is.neq"))
||#


;; --------------------------------
;; rule "assert-op"

(defparse-aleo-rulename "assert-op")

;; Move to tests:
#||
(lex-assert-op (string=>nats "assert.eq"))
(lex-assert-op (string=>nats "assert.neq"))
||#


;; --------------------------------
;; rule "commit-op"

(defparse-aleo-group "( \"256\" / \"512\" / \"768\" / \"1024\" )")
(defparse-aleo-group "( \"64\" / \"128\" )")

(defparse-aleo-rulename "commit-op")

;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------
;; rule "hash-op"

(defparse-aleo-group "( \"2\" / \"4\" / \"8\" )")

(defparse-aleo-rulename "hash-op")

;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------
;; rule "unary"

(defparse-aleo-group "( operand ws )")

(defparse-aleo-rulename "unary")

;; Move to tests:
#||
(lex-unary (string=>nats "not r10 into r86"))
||#


;; --------------------------------
;; rule "binary"

(define lex-repetition-2-operands ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('2( operand ws )')."

  (b* (((mv tree-operand-ws-1 input-after-operand-ws-1)
        (lex-group-1-operand input))
       ((when (reserrp tree-operand-ws-1))
        (mv (reserrf-push tree-operand-ws-1)
            (acl2::nat-list-fix input)))

       ((mv tree-operand-ws-2 input-after-operand-ws-2)
        (lex-group-1-operand input-after-operand-ws-1))
       ((when (reserrp tree-operand-ws-2))
        (mv (reserrf-push tree-operand-ws-2)
            (acl2::nat-list-fix input))))

    (mv (list tree-operand-ws-1 tree-operand-ws-2)
        input-after-operand-ws-2))

  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-2-operands-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-aleo-rulename "binary")

;; Move to tests:
#||
;; "binary" does not include the final ";".  That is in "instruction"
(lex-binary (string=>nats "and r2 r4 into r79"))
||#


;; --------------------------------
;; rule "ternary"

(define lex-repetition-3-operands ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('3( operand ws )')."

  (b* (((mv tree-operand-ws-1 input-after-operand-ws-1)
        (lex-group-1-operand input))
       ((when (reserrp tree-operand-ws-1))
        (mv (reserrf-push tree-operand-ws-1)
            (acl2::nat-list-fix input)))

       ((mv tree-operand-ws-2 input-after-operand-ws-2)
        (lex-group-1-operand input-after-operand-ws-1))
       ((when (reserrp tree-operand-ws-2))
        (mv (reserrf-push tree-operand-ws-2)
            (acl2::nat-list-fix input)))

       ((mv tree-operand-ws-3 input-after-operand-ws-3)
        (lex-group-1-operand input-after-operand-ws-2))
       ((when (reserrp tree-operand-ws-3))
        (mv (reserrf-push tree-operand-ws-3)
            (acl2::nat-list-fix input))))

    (mv (list tree-operand-ws-1 tree-operand-ws-2 tree-operand-ws-3)
        input-after-operand-ws-3))

  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-3-operands-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-aleo-rulename "ternary")

;; Move to tests:
#||
(lex-ternary (string=>nats "ternary r1216 r1218 r1215 into r1220"))
||#


;; --------------------------------

(defparse-aleo-rulename "is")

;; Move to tests:
#||
(lex-is (string=>nats "is.eq r20 0u32 into r21"))
||#


;; --------------------------------

(defparse-aleo-rulename "assert")

;; No instances yet in /leo/
;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------

(defparse-aleo-rulename "commit")

;; No instances yet in /leo/
;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------

(defparse-aleo-rulename "hash")

;; No instances yet in /leo/
;; Move to tests:
#||
(lex- (string=>nats ""))
||#


;; --------------------------------
;; rule "cast"

(defparse-aleo-group "( ws operand )")
(defparse-aleo-*-group "( ws operand )")

(define lex-repetition-1*-ws-operand ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*( ws operand )')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-group-1-ws-operand input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-ws-operand input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-ws-operand-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-ws-operand-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "cast")

;; Move to tests:
#||
(lex-cast (string=>nats "cast r0.owner r0.gates r3 into r4 as token.record"))
(lex-cast (string=>nats "cast r0 0u64 r1 into r2 as token.record"))
||#


;; --------------------------------
;; rule "call"

(defparse-aleo-group "( locator / identifier )")

(defparse-aleo-group "( ws register )")
(defparse-aleo-*-group "( ws register )")

(define lex-repetition-1*-ws-register ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*( ws register )')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-group-1-ws-register input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-ws-register input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-ws-register-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-ws-register-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "call")

;; Move to tests:
#||
(lex-call (string=>nats "call sealsTableLookup r4 into r5"))
||#


;; --------------------------------
;; rule "instruction"

(defparse-aleo-group "( unary / binary / ternary / is / assert / commit / hash / cast / call )")

(defparse-aleo-rulename "instruction")

;; Move to tests:
#||
(lex-instruction (string=>nats "
not r10 into r86;"))
(lex-instruction (string=>nats "
and r2 r4 into r79;"))
(lex-instruction (string=>nats "
ternary r1216 r1218 r1215 into r1220;"))
(lex-instruction (string=>nats "
is.eq r20 0u32 into r21;"))
(lex-instruction (string=>nats "
cast r0.owner r0.gates r3 into r4 as token.record;"))
(lex-instruction (string=>nats "
cast r0.owner r0.gates r3 into r4 as token.record;"))
(lex-instruction (string=>nats "
call sealsTableLookup r4 into r5;"))
||#

;; --------------------------------
;; rule "decrement"

(defparse-aleo-rulename "decrement")

;; Move to tests:
#||
(lex-decrement (string=>nats "
decrement account[r0] by r2;"))
||#


;; --------------------------------
;; rule "increment"

(defparse-aleo-rulename "increment")

;; Move to tests:
#||
(lex-increment (string=>nats "
increment account[r0] by r1;"))
||#


;; --------------------------------
;; rule "command"

(defparse-aleo-rulename "command")


;; --------------------------------
;; rule "finalize-command"

(defparse-aleo-rulename "finalize-command")

;; Move to tests:
#||
(lex-finalize-command (string=>nats "
    finalize r1 r2;"))
||#


;; --------------------------------
;; rule "function"

(defparse-aleo-rulename "function-input")
(defparse-aleo-rulename "function-output")

(defparse-aleo-*-rulename "function-input")
(defparse-aleo-*-rulename "function-output")

(defparse-aleo-*-rulename "instruction")

(define lex-repetition-1*-instruction ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*instruction')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-instruction input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-instruction input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-instruction-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-instruction-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "function")

;; Move to tests:
#||
(lex-function (string=>nats "
function is_even_and_nonzero:
    input r0 as field;
    div r0 2field into r1;
    lt r1 r0 into r2;
    output r2 as boolean;"))
||#


;; --------------------------------
;; rule "finalize"

(defparse-aleo-rulename "finalize-input")
(defparse-aleo-rulename "finalize-output")

(defparse-aleo-*-rulename "finalize-input")
(defparse-aleo-*-rulename "finalize-output")

(defparse-aleo-*-rulename "command")

(define lex-repetition-1*-command ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*command')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-command input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-command input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-command-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-command-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "finalize")

;; Move to tests:
#||
(lex-finalize-input (string=>nats "
    input r0 as address.public;"))

(lex-finalize (string=>nats "
finalize transfer_public:
    input r0 as address.public;
    input r1 as address.public;
    input r2 as u64.public;
    decrement account[r0] by r2;
    increment account[r1] by r2;"))
||#


;; --------------------------------
;; rule "transition"

(defparse-aleo-rulename "transition-input")
(defparse-aleo-rulename "transition-output")

(defparse-aleo-*-rulename "transition-input")
(defparse-aleo-*-rulename "transition-output")

(defparse-aleo-option "[ finalize-command finalize ]")

(defparse-aleo-rulename "transition")


;; Move to tests:
#||
(lex-transition (string=>nats "
transition transfer_private:
    input r0 as token.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.amount r2 into r3;
    cast r0.owner r0.gates r3 into r4 as token.record;
    cast r1 0u64 r2 into r5 as token.record;
    output r4 as token.record;
    output r5 as token.record;"))
||#


;; --------------------------------
;; rule "program"

(defparse-aleo-*-rulename "import")

(defparse-aleo-group "( mapping / struct / record / function / transition )")

(defparse-aleo-*-group "( mapping / struct / record / function / transition )")

(define lex-repetition-1*-program-declaration ((input nat-listp))
  :returns
  (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*( mapping / struct / record / function / transition )')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-group-program-declaration input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-repetition-*-program-declaration input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-repetition-1*-program-declaration-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-repetition-1*-program-declaration-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear)
  )

(defparse-aleo-rulename "program")


;; Move to tests:
#||
;; leo/examples/message/build/main.aleo
(lex-program (string=>nats "program message.aleo;

struct message:
    first as field;
    second as field;

transition main:
    input r0 as message.private;
    cast r0.first r0.second into r1 as message;
    add r1.first r1.second into r2;
    output r2 as field.private;
"))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
