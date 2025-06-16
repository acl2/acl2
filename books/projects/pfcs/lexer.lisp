; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "grammar")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)
(include-book "unicode/read-utf8" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer
  :parents (concrete-syntax)
  :short "An executable lexer of PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple lexer for the PFCS lexical grammar.
     Efficiency is not the primary focus for now;
     correctness and simplicity are.
     In the future, we may optimize this lexer,
     or we may use "
    (xdoc::seetopic "apt::apt" "APT")
    " to do so.")
   (xdoc::p
    "Note that the lexical grammar for PFCS consists of a subset
     of ASCII characters that is also a subset of Unicode
     characters that UTF-8 encodes in a single byte.
     However, some of this lexer code is written to support the
     possibility of future concrete syntax that is UTF-8 encoded
     as multiple bytes. Hence the references to ``Unicode characters''.")
   (xdoc::p
    "The lexer consists of a collection of lexing functions,
     each of which takes a list of natural numbers as input,
     which represents the Unicode codepoints of characters that remain
     to lex in the PFCS phrase being lexed.
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
     which also describes what PFCS lexing does).
     Other code is written by hand,
     due to limitations in the aforementioned parser generation tools,
     such as the efficiency of the generated code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 1:
;; Generate specialized macros for this parser.

(defsection lex-generation-macros
  :short "Lexing generation macros specialized to this lexer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee abnf::defdefparse) to generate specialized macros
     to generate (some of) the PFCS lexer.
     See the user documentation of @(tsee abnf::defdefparse) for details."))

  (abnf::defdefparse pfcs
    :package "PFCS"
    :grammar *grammar*
    :prefix lex))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 2:
;; Tables of parsing functions for groups, options, and repetitions.

(defsection lex-generation-tables
  :short "ABNF group, option, and repetition tables
          for generating lexing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the user documentation of @(tsee abnf::defdefparse) for details."))

  (defparse-pfcs-group-table

      ;; --------------------------------
      ;; components for rule identifier:
      ;; identifier = letter *( letter / digit / "_" )

      "( letter / digit / \"_\" )" group-letter/digit/_
    )

  (defparse-pfcs-option-table

      ;; --------------------------------
      ;; components for rule "line-terminator":
      ;; line-terminator = [ carriage-return ] line-feed

      "[ carriage-return ]" optional-cr

      ;; --------------------------------
      ;; components for rule "relation-constraint"
      ;; relation-constraint = identifier "("
      ;;                       [ expression *( "," expression ) ] ")"

      "[ expression *( \",\" expression ) ]" optional-expressions

      ;; --------------------------------
      ;; components for rule "definition"
      ;; definition = identifier "(" [ identifier *( "," identifier ) ] ")"
      ;;              ":=" "{" [ constraint *( "," constraint ) ] "}"

      "[ identifier *( \",\" identifier ) ]" optional-identifiers
      "[ constraint *( \",\" constraint ) ]" optional-constraints
    )

  (defparse-pfcs-repetition-table

      ;; --------------------------------
      ;; components for rule numeral:
      ;; numeral = 1*digit

      "*digit" *-digit
      "1*digit" 1*-digit

      ;; --------------------------------
      ;; components for rule:
      ;;   identifier = letter *( letter / digit / "_" )

      "*( letter / digit / \"_\" )" *-rest-of-identifier

      ;; --------------------------------
      ;; components for rule:
      ;;   relation-constraint = identifier "("
      ;;                         [ expression *( "," expression ) ] ")"

      "*( \",\" expression )" *-comma-expression

      ;; --------------------------------
      ;; components for rule:
      ;;   definition = identifier "(" [ identifier *( "," identifier ) ] ")"
      ;;                ":=" "{" [ constraint *( "," constraint ) ] "}"

      "*( \",\" identifier )" *-comma-identifier
      "*( \",\" constraint )" *-comma-constraint

      ;; --------------------------------
      ;; for a sequence of lexemes
      "*lexeme" *-lexeme
      )
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 3:
;; Define Lexing Functions

;; Create the lexing functions for the above.

;; When we can't use the generators and we write lexing functions by hand,
;; we use the following naming convention for the trees and input sequences.
;; If we parse "foo" as a single element (or as a repetition)
;; then we call the tree(s) returned "tree(s)-foo"
;; and we call the remaining input "input-after-foo".


;; --------------------------------
;; Simple rules that don't depend on other rules.

(defparse-pfcs-rulename "line-feed")
(defparse-pfcs-rulename "carriage-return")
(defparse-pfcs-rulename "space")
(defparse-pfcs-rulename "uppercase-letter")
(defparse-pfcs-rulename "lowercase-letter")
(defparse-pfcs-rulename "letter")
(defparse-pfcs-rulename "digit")


;; --------------------------------
;; rule line-terminator:
;;   line-terminator = [ carriage-return ] line-feed

;; defines lex-optional-cr (see defparse-pfcs-option-table above)
(defparse-pfcs-option "[ carriage-return ]")

(defparse-pfcs-rulename "line-terminator")


;; --------------------------------
;; rule whitespace:
;;   whitespace = space / line-terminator

(defparse-pfcs-rulename "whitespace")


;; --------------------------------
;; rule numeral:
;;   numeral = 1*digit

(defparse-pfcs-*-rulename "digit")

(define lex-1*-digit ((input nat-listp))
  :returns
    (mv (trees abnf::tree-list-resultp
             :hints
             (("Goal" :in-theory
               (enable abnf::treep-when-tree-resultp-and-not-reserrp))))
      (rest-input nat-listp))
  :short "Lex @('1*digit')."
  (b* (((mv tree-thing1 input-after-thing1)
        (lex-digit input))
       ((when (reserrp tree-thing1))
        (mv (reserrf-push tree-thing1)
            (acl2::nat-list-fix input)))
       ((mv trees input-after-trees)
        (lex-*-digit input-after-thing1)))
    (mv (cons tree-thing1 trees)
        input-after-trees))
  :hooks (:fix)

  ///
  (defret len-of-lex-1*-digit-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-lex-1*-digit-<
    (implies (not (reserrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-pfcs-rulename "numeral")


;; --------------------------------
;; rule identifier
;;   identifier = letter *( letter / digit / "_" )

;; defines lex-group-letter/digit/_ (see defparse-pfcs-group-table above)
(defparse-pfcs-group "( letter / digit / \"_\")")

(defparse-pfcs-*-group "( letter / digit / \"_\")")

(defparse-pfcs-rulename "identifier")


;; --------------------------------
;; rule operator

(defparse-pfcs-rulename "operator")


;; --------------------------------
;; rule separator

(defparse-pfcs-rulename "separator")


;; --------------------------------
;; rule token

(defparse-pfcs-rulename "token")


;; --------------------------------
;; rule lexeme

;; Rule: lexeme = token / whitespace
;; Since whitespace is simpler to lex than tokens, try lexing it first.
(defparse-pfcs-rulename "lexeme" :order (2 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The lexer breaks down The PFCS source code into a sequence of lexemes.

(defparse-pfcs-*-rulename "lexeme")

(defrule unicode-scalar-values-are-natp
  (implies (acl2::ustring? nats)
           (nat-listp nats))
  :induct t)

(define lexemize-pfcs ((pfcs-codepoints nat-listp))
  :returns (pfcs-lexemes abnf::tree-list-resultp)
  :short "Lexes the Unicode codepoints @('pfcs-codepoints') into lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token or whitespace.  @('lexemize-pfcs') returns two
     values: an error flag and a list of these lexemes in @('abnf::tree')
     form.")
   (xdoc::p
    "If the input cannot be fully lexed, a reserrp is returned."))
  (b* (((mv trees rest-input)
        (lex-*-lexeme pfcs-codepoints))
       ;; It is probably impossible for trees to be reserrp, since
       ;; this call would instead just return the input that was not lexed.
       ;; However, check error trees for completeness.
       ((when (reserrp trees))
        (reserrf (cons :unexpected-reserrp trees)))
       ;; If there is input left that was not lexed, return an error.
       ;; It is unlikely this can happen without triggering an earlier error
       ;; but if it does, we should look at it.
       ((unless (null rest-input))
        (reserrf (cons :cannot-fully-lex (cons trees rest-input)))))
    trees))

(define lexemize-pfcs-from-bytes ((pfcs-bytes nat-listp))
  :returns (pfcs-lexemes abnf::tree-list-resultp)
  :short "Lexes the UTF-8 bytes into a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token or whitespace.  @('lexemize-pfcs-from-bytes') returns
     two values: an error flag and a list of these lexemes in @('abnf::tree')
     form.")
   (xdoc::p
    "If the input cannot be fully lexed, a reserrp is returned."))
  (b* (((unless (unsigned-byte-listp 8 pfcs-bytes))
        (reserrf (cons :invalid-octets pfcs-bytes)))
       ;; The following converts a sequence of UTF-8 bytes into Unicode
       ;; codepoint numbers.
       ;; Currently this is more general than needed for PFCS, but
       ;; but it is a good pattern in case we need future support of characters
       ;; encoded by multi-byte UTF-8.
       (codepoints (acl2::utf8=>ustring pfcs-bytes))
       ;; if not valid utf8, codepoints will be the symbol ACL2::FAIL
       ((unless (nat-listp codepoints))
        (reserrf (cons :invalid-utf-8 pfcs-bytes))))
    (lexemize-pfcs codepoints)))

(define lexemize-pfcs-from-string ((pfcs-string stringp))
  :returns (pfcs-lexemes abnf::tree-list-resultp)
  :short "Lexes the UTF-8 @('pfcs-string') into a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lexeme is a token or whitespace.  @('lexemize-pfcs-from-string') returns
     two values: an error flag and a list of these lexemes in @('abnf::tree')
     form.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('pfcs-string'), when converted to codes, is required to be valid
     UTF-8.")
   (xdoc::p
    "If the input cannot be fully lexed, a reserrp is returned."))
  (b* (((unless (stringp pfcs-string))
        (reserrf (cons :not-a-string pfcs-string)))
       (octets (string=>nats pfcs-string)))
    (lexemize-pfcs-from-bytes octets)))
