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

(include-book "keywords")
(include-book "addresses")
(include-book "grammar")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)
(include-book "unicode/read-utf8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer
  :parents (lexing-and-parsing)
  :short "An executable lexer of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple lexer for the Leo lexical grammar.
     Efficiency is not the primary focus for now;
     correctness and simplicity are.
     In the future, we may optimize this lexer,
     or we may use "
    (xdoc::seetopic "apt::apt" "APT")
    " to do so.")
   (xdoc::p
    "To support context-dependent lexing,
     this lexer does not provide any code to lex a file prior to parsing;
     rather, it provides lexing code that the parser calls as needed.")
   (xdoc::p
    "The lexer consists of a collection of lexing functions,
     each of which takes a list of natural numbers as input,
     which represents the Unicode characters that remain to lex
     in the Leo file being lexed.
     Each function returns two results:
     the first result is either an error
     or an ABNF tree (or list of trees) for the recognized lexeme(s);
     the second result is
     the remaining list of natural numbers after the lexeme.
     While from a conceptual point of view
     it would be better for all these lexing functions to return a single result
     that is either an error
     or a pair consisting of an ABNF tree or tree list plus remaining inputs,
     by returning two results we make the execution more efficient
     by avoiding constructing and deconstructing the pair.")
   (xdoc::p
    "Some of the code of this lexer is generated
     via the parser generation tools in the ABNF library
     (where `parser' in that context refers to the general idea of
     recognizing and structuring strings in a formal language,
     which also describes what Leo lexing does).
     Other code is written by hand,
     due to limitations in the aforementioned parser generation tools,
     such as the efficiency of the generated code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lex-generation-macros
  :short "Lexing generation macros specialized to this lexer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee abnf::defdefparse) to generate specialized macros
     to generate (some of) the Leo lexer.
     See the user documentation of @(tsee abnf::defdefparse) for details."))

  (abnf::defdefparse leo
    :package "LEO-EARLY"
    :grammar *grammar*
    :prefix lex))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lex-generation-tables
  :short "ABNF group, option, and repetition tables
          for generating lexing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the user documentation of @(tsee abnf::defdefparse) for details."))

  (defparse-leo-group-table
    "( letter / decimal-digit / \"_\" )" letter/decdigit/underscore
    "( lowercase-letter / decimal-digit )" lcletter/decdigit
    "( %s\"u8\" / %s\"u16\" / %s\"u32\" / %s\"u64\" / %s\"u128\" )" u8/16/32/64/128
    "( %s\"i8\" / %s\"i16\" / %s\"i32\" / %s\"i64\" / %s\"i128\" )" i8/16/32/64/128)

  (defparse-leo-option-table)

  (defparse-leo-repetition-table
    "*not-line-feed-or-carriage-return" *-not-line-feed-or-carriage-return
    "*( letter / decimal-digit / \"_\" )" *-letter/decdigit/underscore
    "*( lowercase-letter / decimal-digit )" *-lcletter/decdigit
    "*decimal-digit" *-decimal-digit
    "1*decimal-digit" 1*-decimal-digit
    "1*6hexadecimal-digit" 1*6-hexadecimal-digit
    "*string-literal-element" *-string-literal-element
    "*hexadecimal-digit" *-hexadecimal-digit
    "58( lowercase-letter / decimal-digit )" 58-lcletter/decdigit
    "*lexeme" *-lexeme))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lexing functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "horizontal-tab")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "line-feed")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "carriage-return")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "space")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "visible-ascii")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "safe-ascii")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "safe-nonascii")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "double-quote")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "single-quote")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "not-star-or-line-feed-or-carriage-return")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "not-star-or-slash-or-line-feed-or-carriage-return")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "not-line-feed-or-carriage-return")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename
  "not-double-quote-or-backslash-or-line-feed-or-carriage-return")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "line-terminator"
  :order (1 3 2)) ; try CR LF before just CR

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "whitespace")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-*-rulename "not-line-feed-or-carriage-return")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "line-comment")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines lex-rest-of-block-comment-+-lex-rest-of-block-comment-after-star
  :short "Lex a @('rest-of-block-comment')
          or a @('rest-of-block-comment-after-star')."

  (define lex-rest-of-block-comment ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Lex a @('rest-of-block-comment')."
    (b* (((mv treess input)
          (b* (((mv treess1 input1)
                (b* (((mv tree input) (abnf::parse-ichars "*" input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree))
                     ((mv tree input)
                      (lex-rest-of-block-comment-after-star input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees2 (list tree)))
                  (mv (list trees1 trees2) input)))
               ((when (not (reserrp treess1))) (mv treess1 input1))
               ((mv treess2 input2)
                (b* (((mv tree input)
                      (lex-not-star-or-line-feed-or-carriage-return input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree))
                     ((mv tree input) (lex-rest-of-block-comment input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees2 (list tree)))
                  (mv (list trees1 trees2) input)))
               ((when (not (reserrp treess2))) (mv treess2 input2))
               ((mv treess3 input3)
                (b* (((mv tree input) (lex-line-terminator input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree))
                     ((mv tree input) (lex-rest-of-block-comment input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees2 (list tree)))
                  (mv (list trees1 trees2) input)))
               ((when (not (reserrp treess3))) (mv treess3 input3)))
            (mv (reserrf (list :found (list treess1 treess2)))
                (nat-list-fix input))))
         ((when (reserrp treess)) (mv treess input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "rest-of-block-comment")
           :branches treess)
          input))
    :measure (len input))

  (define lex-rest-of-block-comment-after-star ((input nat-listp))
    :short "Lex a @('rest-of-block-comment-after-star')."
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    (b* (((mv treess input)
          (b* (((mv treess1 input1)
                (b* (((mv tree input) (abnf::parse-ichars "/" input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree)))
                  (mv (list trees1) input)))
               ((when (not (reserrp treess1))) (mv treess1 input1))
               ((mv treess2 input2)
                (b* (((mv tree input) (abnf::parse-ichars "*" input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree))
                     ((mv tree input)
                      (lex-rest-of-block-comment-after-star input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees2 (list tree)))
                  (mv (list trees1 trees2) input)))
               ((when (not (reserrp treess2))) (mv treess2 input2))
               ((mv treess3 input3)
                (b* (((mv tree input)
                      (lex-not-star-or-slash-or-line-feed-or-carriage-return input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree))
                     ((mv tree input) (lex-rest-of-block-comment input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees2 (list tree)))
                  (mv (list trees1 trees2) input)))
               ((when (not (reserrp treess3))) (mv treess3 input3))
               ((mv treess4 input4)
                (b* (((mv tree input) (lex-line-terminator input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees1 (list tree))
                     ((mv tree input) (lex-rest-of-block-comment input))
                     ((when (reserrp tree)) (mv (reserrf-push tree) input))
                     (trees2 (list tree)))
                  (mv (list trees1 trees2) input)))
               ((when (not (reserrp treess4))) (mv treess4 input4)))
            (mv (reserrf (list :found (list treess1 treess2 treess3)))
                (nat-list-fix input))))
         ((when (reserrp treess)) (mv treess input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "rest-of-block-comment-after-star")
           :branches treess)
          input))
    :measure (len input))

  :ruler-extenders :all

  :verify-guards nil ; done below
  ///
  (verify-guards lex-rest-of-block-comment)

  (defret-mutual
    len-of-lex-rest-of-block-comment-+-lex-rest-of-block-comment-after-star-<=
    (defret len-of-lex-rest-of-block-comment-<=
      (<= (len rest-input)
          (len input))
      :rule-classes :linear
      :fn lex-rest-of-block-comment)
    (defret len-of-lex-rest-of-block-comment-after-star-<=
      (<= (len rest-input)
          (len input))
      :rule-classes :linear
      :fn lex-rest-of-block-comment-after-star))

  (defret-mutual
    len-of-lex-rest-of-block-comment-+-lex-rest-of-block-comment-after-star-<
    (defret len-of-lex-rest-of-block-comment-<
      (implies (not (reserrp tree))
               (< (len rest-input)
                  (len input)))
      :rule-classes :linear
      :fn lex-rest-of-block-comment)
    (defret len-of-lex-rest-of-block-comment-after-star-<
      (implies (not (reserrp tree))
               (< (len rest-input)
                  (len input)))
      :rule-classes :linear
      :fn lex-rest-of-block-comment-after-star)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "block-comment")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "comment")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "uppercase-letter")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "lowercase-letter")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "letter")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "decimal-digit")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "octal-digit")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "hexadecimal-digit")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-group "( letter / decimal-digit / \"_\" )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-*-group "( letter / decimal-digit / \"_\" )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "identifier")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-group "( lowercase-letter / decimal-digit )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-*-group "( lowercase-letter / decimal-digit )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-58-lcletter/decdigit ((input nat-listp))
  :returns (mv (trees abnf::tree-list-resultp)
               (rest-input nat-listp))
  :short "Lex a @('58( lowercase-letter / decimal-digit )')."
  (b* (((mv trees input1) (lex-*-lcletter/decdigit input))
       ((unless (= (len trees) 58))
        (mv (reserrf (list :found trees :required 58)) (nat-list-fix input))))
    (mv trees input1))
  :hooks (:fix)
  ///

  (defret len-of-lex-58-lcletter/decdigit-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-58-lcletter/decdigit-<
    (implies (not (reserrp trees))
             (<= (len rest-input)
                 (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "address-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-identifier/keyword/boolean/address ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Lex an @('identifier')
          or a @('keyword')
          or a @('boolean-literal')
          or an @('address-literal')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexically, these are all identifiers, in the sense that
     they are instances of the @('identifier') rule,
     on a purely grammatical basis.
     Thus, we start by lexing a (grammatical) identifier.
     Then we check whether it is a keyword,
     in which case we re-classify the ABNF tree as a @('keyword') tree.
     Otherwise, we check whether it is a boolean literal,
     in which case we re-classify the ABNF tree as a @('boolean-literal).
     Otherwise, we chek whether it is an address:
     in this case, we need to re-lex it,
     so that we can construct and return an @('address-literal').
     Otherwise, we return the @('identifier') tree,
     unless it is or starts with @('aleo1').")
   (xdoc::p
    "Note that keywords, boolean literals, and address literals
     are all disjoint."))
  (b* (((mv tree input1) (lex-identifier input))
       ((when (reserrp tree)) (mv (reserrf-push tree) input1))
       (nats (abnf::tree->string tree))
       ((unless (unsigned-byte-listp 8 nats)) (mv (reserrf :impossible) input1))
       (str (nats=>string nats))
       ((when (member-equal str *keywords*))
        (mv (abnf-tree-wrap (abnf::tree-leafterm nats) "keyword")
            input1))
       ((when (member-equal str (list "true" "false")))
        (mv (abnf-tree-wrap (abnf::tree-leafterm nats) "boolean-literal")
            input1))
       ((when (address-string-p str))
        (b* (((mv tree input) (lex-address-literal input))
             ((when (reserrp tree)) (mv (reserrf :impossible) input)))
          (mv tree input)))
       ((when (and (>= (length str) 5)
                   (equal (subseq str 0 5) "aleo1")))
        (mv (reserrf (list :found str)) input1)))
    (mv tree input1))
  :hooks (:fix)
  ///

  (defret len-of-lex-identifier/keyword/boolean/address-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-identifier/keyword/boolean/address-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-*-rulename "decimal-digit")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-1*-decimal-digit ((input nat-listp))
  :returns (mv (trees
                abnf::tree-list-resultp
                :hints
                (("Goal"
                  :in-theory
                  (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
               (rest-input nat-listp))
  :short "Lex a @('1*decimal-digit')."
  (b* (((mv tree input) (lex-decimal-digit input))
       ((when (reserrp tree)) (mv (reserrf-push tree) input))
       ((mv trees input) (lex-*-decimal-digit input)))
    (mv (cons tree trees) input))
  :hooks (:fix)
  ///

  (defret len-of-lex-1*-decimal-digit-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-1*-decimal-digit-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "numeral")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-group
  "( %s\"u8\" / %s\"u16\" / %s\"u32\" / %s\"u64\" / %s\"u128\" )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "unsigned-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-group
  "( %s\"i8\" / %s\"i16\" / %s\"i32\" / %s\"i64\" / %s\"i128\" )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "signed-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "integer-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "field-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "product-group-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "scalar-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "single-quote-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "double-quote-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "backslash-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "line-feed-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "carriage-return-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "horizontal-tab-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "null-character-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "simple-character-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "ascii-character-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-*-rulename "hexadecimal-digit")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-1*6-hexadecimal-digit ((input nat-listp))
  :returns (mv (trees abnf::tree-list-resultp)
               (rest-input nat-listp))
  :short "Lex a @('1*6hexadecimal-digit')."
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
  (b* (((mv trees input1) (lex-*-hexadecimal-digit input))
       ((unless (and (<= 1 (len trees))
                     (<= (len trees) 6)))
        (mv (reserrf (list :found trees))
            (nat-list-fix input))))
    (mv trees input1))
  :hooks (:fix)
  ///

  (defret len-of-lex-1*6-hexadecimal-digit-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "unicode-character-escape")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "string-literal-element")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-*-rulename "string-literal-element")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "string-literal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-leo-rulename "annotation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-symbol ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Lex a @('symbol')."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is critical that symbols that are prefixes of other symbols
     are tried after trying the longer ones,
     to satisfy the longest lexing requirement."))
  (b* (((mv tree input)
        (b* (((mv tree input1) (abnf::parse-schars ")group" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "(" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ")" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "[" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "]" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "{" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "}" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "&&=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "&&" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "||=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "||" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "&=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "&" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "|=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "|" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "^=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "^" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "_" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "?" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "," input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ";" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ".." input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "." input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "::" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ":" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "!=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "!" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "<<=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "<<" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ">>=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ">>" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "=>" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "==" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "<=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "<" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ">=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars ">" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "+=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "+" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "/=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "/" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "%=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "%" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "->" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "-=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "-" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "**=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "**" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "*=" input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (abnf::parse-ichars "*" input))
             ((when (not (reserrp tree))) (mv tree input1)))
          (mv (reserrf :no-symbol) (nat-list-fix input))))
       ((when (reserrp tree)) (mv tree input)))
    (mv (abnf-tree-wrap tree "symbol") input))
  :hooks (:fix)
  ///

  (defret len-of-lex-symbol-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-symbol-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-numeric-literal ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Lex an @('atomic-literal') that is a numeric literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, lex an
     @('integer-literal'),
     @('field-literal'),
     @('product-group-literal'), or
     @('scalar-literal').
     Return a @('numeric-literal') tree that wraps that tree if successful.")
   (xdoc::p
    "It is convenient to have this lexing function,
     called when lexing a token,
     since numeric literals all start with a decimal digit,
     and also share some structure that may enable future optimizations.
     Currently this lexing function is not very optimized,
     as it tries each kind of literal independently."))
  (b* (((mv tree input)
        (b* (((mv tree input1) (lex-integer-literal input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (lex-field-literal input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (lex-product-group-literal input))
             ((when (not (reserrp tree))) (mv tree input1))
             ((mv tree input1) (lex-scalar-literal input))
             ((when (not (reserrp tree))) (mv tree input1)))
          (mv (reserrf :no-numeric-literal) (nat-list-fix input))))
       ((when (reserrp tree)) (mv tree input)))
    (mv (abnf-tree-wrap tree "numeric-literal") input))
  :hooks (:fix)
  ///

  (defret len-of-lex-numeric-literal-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-numeric-literal-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex-token ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Lex a @('token')."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, lex a
     @('keyword'),
     @('identifier'),
     @('atomic-literal'),
     @('numeral') (that is not part of an atomic literal), or
     @('symbol').")
   (xdoc::p
    "If the next input is an at sign,
     the token may only be an annotation.
     If the next input is a double quote,
     the token may only be a string literal.
     If the next input is a decimal digit,
     the token may only be a numeric literal or a bare numeral.
     Otherwise, we try to lex something that starts with a letter
     (identifier, or keyword, or boolean, or address).
     Note that we need to wrap string, boolean and address literals
     with @('atomic-literal') so that the returned CST will match
     the lexical grammar rules.
     Finally, we try to lex a symbol."))
  (b* (((when (endp input)) (mv (reserrf :end-of-input) nil))
       (next (lnfix (car input)))
       ((when (= next (char-code #\@)))
        (b* (((mv tree input) (lex-annotation input))
             ((when (reserrp tree)) (mv (reserrf-push tree) input)))
          (mv (abnf-tree-wrap tree "token")
              input)))
       ((when (= next (char-code #\")))
        (b* (((mv tree input) (lex-string-literal input))
             ((when (reserrp tree)) (mv (reserrf-push tree) input)))
          (mv (abnf-tree-wrap
               (abnf-tree-wrap tree "atomic-literal")
               "token")
              input)))
       ((when (or (and (<= (char-code #\0) next)
                       (<= next (char-code #\9)))))
        (b* (((mv tree input1) (lex-numeric-literal input))
             ((when (not (reserrp tree)))
              (mv (abnf-tree-wrap
                   (abnf-tree-wrap tree "atomic-literal")
                   "token")
                  input1))
             ((mv tree input2) (lex-numeral input))
             ((when (not (reserrp tree)))
              (mv (abnf-tree-wrap tree "token")
                  input2)))
          (mv (reserrf-push tree) (nat-list-fix input))))
       ((mv tree input) (lex-identifier/keyword/boolean/address input))
       ((when (not (reserrp tree)))
        (mv (abnf-tree-wrap
             (cond ((abnf-tree-with-root-p tree "boolean-literal")
                    (abnf-tree-wrap tree "atomic-literal"))
                   ((abnf-tree-with-root-p tree "address-literal")
                    (abnf-tree-wrap tree "atomic-literal"))
                   (t tree))
             "token")
            input))
       ((mv tree input) (lex-symbol input))
       ((when (not (reserrp tree)))
        (mv (abnf-tree-wrap tree "token")
            input)))
    (mv (reserrf :no-token) input))
  :hooks (:fix)
  ///

  (defret len-of-lex-token-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-token-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rule:
;;   lexeme = token / comment / whitespace
;; Comments must be tried before tokens, since "/" is a token.
;; Since whitespace is simpler and more plentiful than comments,
;; try whitespace first.
(defparse-leo-rulename "lexeme" :order (3 2 1))

(defparse-leo-*-rulename "lexeme")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; lexemize leo source code into a sequence of lexemes

(defthm unicode-scalar-values-are-natp
  (implies (acl2::ustring? nats)
           (nat-listp nats)))

(define lexemize-leo ((leo-codepoints nat-listp))
  :returns (leo-lexemes abnf::tree-list-resultp)
  :short "Lexes the Unicode code points @('leo-codepoints') into a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token, comment, or whitespace.  @('lexemize-leo') returns
     two values: an error flag and a list of these lexemes in @('abnf::tree') form.
     Lexemes are further separated into keyword, literal, identifier, or
     symbol.  Recombining these lexemes is done in the parser.")
   (xdoc::p
    "If the input cannot be fully lexed, a reserrp is returned."))
  (b* (((mv trees rest-input)
        (lex-*-lexeme leo-codepoints))
       ;; It is probably impossible for trees to be reserrp, since
       ;; this call would instead just return the input that was not lexed.
       ;; However, check error trees for completeness.
       ((when (reserrp trees))
        (reserrf (cons :unexpected-reserrp trees)))
       ;; If the input ends in the middle of a token,
       ;; e.g., in a string without a closing quote,
       ;; then there will be remaining input.
       ;; Since this function starts with a presumably complete string,
       ;; we consider this an error.  The error object returns two values:
       ;; the abnf trees lexed and the rest of the codepoints.
       ;; Another useful function could be one that expects this
       ;; condition and returns these values without a reserr.
       ((unless (null rest-input))
        (reserrf (cons :cannot-fully-lex (cons trees rest-input)))))
    trees))

(define lexemize-leo-from-bytes ((leo-bytes nat-listp))
  :returns (leo-lexemes abnf::tree-list-resultp)
  :short "Lexes the UTF-8 bytes into a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token, comment, or whitespace.  @('lexemize-leo-from-bytes') returns
     two values: an error flag and a list of these lexemes in @('abnf::tree') form.
     Lexemes are further separated into keyword, literal, identifier, or
     symbol.  Recombining these lexemes is done in the parser.")
   (xdoc::p
    "If the input cannot be fully lexed, a reserrp is returned."))
  (b* (((unless (unsigned-byte-listp 8 leo-bytes))
        (reserrf (cons :invalid-octets leo-bytes)))
       (codepoints (acl2::utf8=>ustring leo-bytes))
       ;; if not valid utf8, codepoints will be the symbol ACL2::FAIL
       ((unless (nat-listp codepoints))
        (reserrf (cons :invalid-utf-8 leo-bytes))))
    (lexemize-leo codepoints)))

(define lexemize-leo-from-string ((leo-string stringp))
  :returns (leo-lexemes abnf::tree-list-resultp)
  :short "Lexes the UTF-8 @('leo-string') into a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token, comment, or whitespace.  @('lexemize-leo-from-string') returns
     two values: an error flag and a list of these lexemes in @('abnf::tree') form.
     Lexemes are further separated into keyword, literal, identifier, or
     symbol.  Recombining these lexemes is done in the parser.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('leo-string'), when converted to codes, is required to be valid
     UTF-8.")
   (xdoc::p
    "If the input cannot be fully lexed, a reserrp is returned."))
  (b* (((unless (stringp leo-string))
        (reserrf (cons :not-a-string leo-string)))
       (octets (string=>nats leo-string)))
    (lexemize-leo-from-bytes octets)))
