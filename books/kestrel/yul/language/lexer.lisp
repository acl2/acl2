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

(include-book "grammar-new")

(include-book "kestrel/abnf/parser-generators" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexer
  :parents (concrete-syntax)
  :short "An executable lexer of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple lexer for the Yul lexical grammar.  The grammar is defined in ABNF.
     See @(see grammar-new).")
   (xdoc::p
    "The lexer is defined in three sections:")
   (xdoc::ol
    (xdoc::li
     "Named pieces of "
     (xdoc::seetopic "abnf::abstract-syntax" "ABNF abstract syntax")
     " that occur internally to Yul grammar rules.")
    (xdoc::li
     "Parser generator control constants (see "
     (xdoc::seetopic "abnf::parser-generators" "parser-generators")
     ") that are used to help generate the lexing functions:"
     (xdoc::ul
      (xdoc::li "a constant containing the ABNF abstract syntax form of the lexical grammar")
      (xdoc::li "a constant containing the prefix that is attached to an ABNF rule name to generate its lexing function name")
      (xdoc::li "three constants (for groups, options, and repetitions) that map the abstract syntax structures in section 1 to names of the lexing functions")))
    (xdoc::li
     "Definitions of lexing functions, most of which are just calls to macros that generate the functions, but some of which are hand-written due to limitations in the current parser generators.")))
  :order-subtopics t
  :default-parent t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 1:
;; Named Abstract Syntax for Rule Components.

;; Named constants for lexing groups, options, and repetitions internal
;; to named ABNF rules.

;; Naming conventions for the named constants:
;; 1. if it is a repetition, it starts with "*lex-repetition-"
;;    followed by the counts and then some designation of the thing
;;    being repeated.
;; 2. if it is an alternation (list of concatenations, each of which is a
;;    list of repetitions), then it can be used to build either a group element
;;    or an option element.  The name starts with "*lex-alternation-".

;; The naming conventions for the generated lexing functions
;; are different for group and option elements (see below).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *lex-repetition-*-decimal-digit*
  :short "The repetition @('*decimal-digit')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "decimal-digit"))
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))

(defval *lex-repetition-*-hex-digit*
  :short "The repetition @('*hex-digit')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "hex-digit"))
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))

;; --------------------------------
;; components for rule hex-string

;; The rule hex-string requires the components:
;; 1. the repetition 2hex-digit
;; 2. an underbar, which needs to be encapsulated in an alternation
;;    because it is made optional
;; 3. the concatenation (a group): ( [ "_" ] 2hex-digit )
;; 4. the repetition: *( [ "_" ] 2hex-digit )
;; 5. the group:
;;      2hex-digit *( [ "_" ] 2hex-digit )
;;    used as an option:
;;      [ 2hex-digit *( [ "_" ] 2hex-digit ) ]
;; 6. the big alternation after %s"hex".

;; 1. 2hex-digit
(defval *lex-repetition-2-hex-digits*
  :short "The repetition @('2hex-digit')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "hex-digit"))
   :range (abnf::make-repeat-range
           :min 2
           :max (acl2::make-nati-finite :get 2))))

;; 2. "_" (used for [ "_" ])
(defval *lex-alternation-underbar*
  :short "The item @('[ \"_\" ]')."
  ;; Note: This is actually an alternation.
  ;; The optionality is introduced at the outer element level,
  ;; by making an element of type option, rather than an element of type group.
  ;; That is why the repeat range is 1 to 1.
  (list
   ;; a single item in the alternation:
   (list
    ;; a single repetition in the concatenation:
    (abnf::make-repetition
     :element (abnf::element-char-val (abnf::char-val-insensitive "_"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))))

;; 3. ( [ "_" ] 2hex-digit )
(defval *lex-alternation-optional-underbar-and-two-hex-digits*
  :short "The group @('( [ \"_\" ] 2hex-digit )')."
  (list
   ;; a single item in the alternation:
   (list
    ;; Two repetitions in the concatenation:
    ;; 1. an optional underbar
    (abnf::make-repetition
     :element (abnf::make-element-option
               :get *lex-alternation-underbar*)
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1)))
    ;; 2. a repetition of 2 hex digits
    *lex-repetition-2-hex-digits*)))

;; 4. *( [ "_" ] 2hex-digit )
(defval *lex-repetition-*-optional-underbar-and-two-hex-digits*
  :short "The repetition @('*( [ \"_\" ] 2hex-digit )')."
  (abnf::make-repetition
   :element (abnf::make-element-group
             :get *lex-alternation-optional-underbar-and-two-hex-digits*)
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))

;; 5. 2hex-digit *( [ "_" ] 2hex-digit )
(defval *lex-alternation-sequence-of-2hex-digits*
  :short "The item @('2hex-digit *( [ \"_\" ] 2hex-digit )')."
  (list
   ;; a single item in the alternation:
   (list
    ;; Two repetitions in the concatenation:
    ;; 1. 2hex-digit
    *lex-repetition-2-hex-digits*
    ;; 2. 0 or more additional 2hex-digits, with optional underbar separators
    *lex-repetition-*-optional-underbar-and-two-hex-digits*)))

;; 6. ( dquote [ 2hex-digit *( [ "_" ] 2hex-digit ) ] dquote
;;    / squote [ 2hex-digit *( [ "_" ] 2hex-digit ) ] squote )
(defval *lex-alternation-for-hex-string*
  :short "The alternation after @('%s\"hex\"')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Includes two alternatives depending on the type of
     delimiting quotes used: one for @('dquote') and one for
     @('squote')."))
  (list
   ;; two concatenations in the alternation.
   ;; first concatenation, with three repetitions:
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "dquote"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1)))
    (abnf::make-repetition
     :element (abnf::make-element-option
               :get *lex-alternation-sequence-of-2hex-digits*)
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1)))
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "dquote"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; second concatenation, the same except swap dquotes and squotes
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "squote"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1)))
    (abnf::make-repetition
     :element (abnf::make-element-option
               :get *lex-alternation-sequence-of-2hex-digits*)
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1)))
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "squote"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))))

;; --------------------------------
;; components for rule escape-sequence

;; The rule escape-sequence requires the components,
;; from inside to outside:
;; 1. The alternation (used as a group):
;;    ( squote / dquote / %s"n" / %s"r" / %s"t" / lf / cr )
;;    call it "escape-sequence-single", as in a single char indicator
;; 2. 4hex-digit
;; 3. The alternation (used as a group):
;;    ( ( squote / dquote / %s"n" / %s"r" / %s"t" / lf / cr )
;;      / %s"u" 4hex-digit
;;      / %s"x" 2hex-digit )
;;    call it "escape-sequence-body"

(defval *lex-alternation-escape-sequence-single*
  :short "The alternation @('( squote / dquote / %s\"\\\" / %s\"n\" / %s\"r\" / %s\"t\" / lf / cr )')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that backslash does not escape characters in an ABNF grammar @('quoted-string'),
     as you can see in the alternation."))
  (list
   ;; 8 concatenations, each with a single repetition
   ;; 1. squote
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "squote"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 2. dquote
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "dquote"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 3. "\"
   (list
    (abnf::make-repetition
     :element (abnf::element-char-val
               (abnf::char-val-sensitive "\\"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 4. "n"
   (list
    (abnf::make-repetition
     :element (abnf::element-char-val
               (abnf::char-val-sensitive "n"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 5. "r"
   (list
    (abnf::make-repetition
     :element (abnf::element-char-val
               (abnf::char-val-sensitive "r"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 6. "t"
   (list
    (abnf::make-repetition
     :element (abnf::element-char-val
               (abnf::char-val-sensitive "t"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 7. lf
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "lf"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 8. cr
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "cr"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))))

(defval *lex-repetition-4-hex-digits*
  :short "The repetition @('4hex-digit')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "hex-digit"))
   :range (abnf::make-repeat-range
           :min 4
           :max (acl2::make-nati-finite :get 4))))

(defval *lex-alternation-escape-sequence-body*
  :short "The stuff after the backslash in an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p "The alteration @tsee('*lex-alternation-escape-sequence-single*') or uHHHH or xHH."))
  (list
   ;; 3 concatenations:
   ;; 1. a concatentation containing a single repetition of a single char escape sequence
   (list
    (abnf::make-repetition
     :element (abnf::element-group *lex-alternation-escape-sequence-single*)
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   ;; 2. a concatenation of two repetitions: "u" followed by 4 hex digits
   (list
    (abnf::make-repetition
     :element (abnf::element-char-val
               (abnf::char-val-sensitive "u"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1)))
    *lex-repetition-4-hex-digits*)
   ;; 3. a concatenation of two repetitions: "x" followed by 2 hex digits
    (list
     (abnf::make-repetition
      :element (abnf::element-char-val
                (abnf::char-val-sensitive "x"))
      :range (abnf::make-repeat-range
              :min 1
              :max (acl2::nati-finite 1)))
     *lex-repetition-2-hex-digits*)))


;; --------------------------------
;; components for rule string-literal

;; The rule string-literal requires the components,
;; from inside to outside:
;; 1. The alternation (used as a group):
;;    ( double-quoted-printable / escape-sequence )
;; 2. The repetition, zero or more of #1:
;;    *( double-quoted-printable / escape-sequence )
;; 3. The alternation (used as a group):
;;    ( single-quoted-printable / escape-sequence )
;; 4. The repetition, zero or more of #3:
;;    *( single-quoted-printable / escape-sequence )

;; 1.
(defval *lex-alternation-dquoted-or-escape*
  :short "The group @('( double-quoted-printable / escape-sequence )')."
  (list
   ;; the alternation has two concatenations, each with a single repetition
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "double-quoted-printable"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "escape-sequence"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))))

;; 2.
(defval *lex-repetition-*-dquoted-or-escape*
  :short "The repetition @('*( double-quoted-printable / escape-sequence )')."
  (abnf::make-repetition
   :element (abnf::make-element-group
             :get *lex-alternation-dquoted-or-escape*)
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))

;; 3.
(defval *lex-alternation-squoted-or-escape*
  :short "The group @('( single-quoted-printable / escape-sequence )')."
  (list
   ;; the alternation has two concatenations, each with a single repetition
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "single-quoted-printable"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))
   (list
    (abnf::make-repetition
     :element (abnf::element-rulename
               (abnf::rulename "escape-sequence"))
     :range (abnf::make-repeat-range
             :min 1
             :max (acl2::nati-finite 1))))))

;; 4.
(defval *lex-repetition-*-squoted-or-escape*
  :short "The repetition @('*( single-quoted-printable / escape-sequence )')."
  (abnf::make-repetition
   :element (abnf::make-element-group
             :get *lex-alternation-squoted-or-escape*)
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))


;; --------------------------------
;; components for rule identifier

(defval *lex-repetition-*-identifier-rest*
  :short "The repetition @('*identifier-rest')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "identifier-rest"))
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))


;; --------------------------------
;; components for rule whitespace

;; rule:  whitespace = 1*whitespace-char
;; However, we don't yet have a generator for repeat one-or-more.
;; So we define a generator for zero-or-more and then,
;; in Part 3: "Define Lexing Functions" section below,
;; we generate the zero-or-more lexing function and call it
;; from lex-whitespace.

;; This particular pieces of abstract syntax does not
;; actually appear in the rule!
;; It is just used to generate the zero-or-more lexing function
;; that we call from lex-whitespace.

(defval *lex-repetition-*-whitespace-char*
  :short "The repetition @('*whitespace-char')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "whitespace-char"))
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))


;; --------------------------------
;; components for rule end-of-line-comment

(defval *lex-repetition-*-not-lf-or-cr*
  :short "The repetition @('*not-lf-or-cr')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "not-lf-or-cr"))
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))


;; --------------------------------
;; component for *lexeme

(defval *lex-repetition-*-lexeme*
  :short "The repetition @('*lexeme')."
  (abnf::make-repetition
   :element (abnf::element-rulename
             (abnf::rulename "lexeme"))
   :range (abnf::make-repeat-range
           :min 0
           :max (acl2::nati-infinity))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 2:
;; Parser Generator Control Constants

;; Constants for the ABNF parser generation tools.

;; See xdoc: Parser-generators
;; There are 5 prenamed constants in the ABNF grammar that must be defined
;; in order to use the parser generation macros.
;; They are:
;;   *def-parse-grammar*
;;   *def-parse-fn-name*
;;   *def-parse-group-fns*
;;   *def-parse-option-fns*
;;   *def-parse-repetition-fns*
;; Current limitation: can only generate one parser in a given world state.

;; Naming conventions for the constants named by these constants is
;; described above.
;; Naming conventions for the lexing functions named by these constants:
;; 1. if it is a repetition, the function has exactly the same name as
;;    its descriptor constant but without the stars at beginning and end.
;; 2. if the descriptor constant contains an alternation,
;;    the function will use "group" or "optional" instead
;;    of "alternation", depending on whether the function is in
;;    *def-parse-group-fns* or *def-parse-option-fns*, respectively.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval abnf::*def-parse-grammar*
  :short "The ABNF abstract syntax form of the grammar to be used for lexing."
  *grammar-new*
  ///
  (assert-event (abnf::rulelistp abnf::*def-parse-grammar*)))

(defval abnf::*def-parse-fn-name*
  :short "Prefix for lexing function names."
  :long "Name to prepend (with '-') to the ABNF rule name to get the parsing
  function's name."
  'lex
  ///
  (assert-event (symbolp abnf::*def-parse-fn-name*)))

(defval abnf::*def-parse-group-fns*
  :short "Alist of lexing functions for unnamed ABNF group elements internal to a rule."
  (list
   (cons *lex-alternation-optional-underbar-and-two-hex-digits*
         'lex-group-optional-underbar-and-two-hex-digits)
   (cons *lex-alternation-for-hex-string*
         'lex-group-for-hex-string)
   (cons *lex-alternation-escape-sequence-single*
         'lex-group-escape-sequence-single)
   (cons *lex-alternation-escape-sequence-body*
         'lex-group-escape-sequence-body)
   (cons *lex-alternation-dquoted-or-escape*
         'lex-group-dquoted-or-escape)
   (cons *lex-alternation-squoted-or-escape*
         'lex-group-squoted-or-escape)
   )
  ///
  (assert-event (abnf::alternation-symbol-alistp abnf::*def-parse-group-fns*)))

(defval abnf::*def-parse-option-fns*
  :short "Alist of lexing functions for unnamed ABNF optional elements internal to a rule."
  (list
   (cons *lex-alternation-underbar*
         'lex-optional-underbar)
   (cons *lex-alternation-sequence-of-2hex-digits*
         'lex-optional-sequence-of-2hex-digits)
   )
  ///
  ;; Both groups and optional items are alternations,
  ;; so abnf::alternation-symbol-alistp is also the correct predicate here.
  (assert-event (abnf::alternation-symbol-alistp abnf::*def-parse-option-fns*)))

(defval abnf::*def-parse-repetition-fns*
  :short "Alist of lexing functions for unnamed ABNF repetitions internal to a rule."
  (list
   (cons *lex-repetition-*-decimal-digit*
         'lex-repetition-*-decimal-digit)
   (cons *lex-repetition-*-hex-digit*
         'lex-repetition-*-hex-digit)
   (cons *lex-repetition-2-hex-digits*
         'lex-repetition-2-hex-digits)
   (cons *lex-repetition-*-optional-underbar-and-two-hex-digits*
         'lex-repetition-*-optional-underbar-and-two-hex-digits)
   (cons *lex-repetition-4-hex-digits*
         'lex-repetition-4-hex-digits)
   (cons *lex-repetition-*-dquoted-or-escape*
         'lex-repetition-*-dquoted-or-escape)
   (cons *lex-repetition-*-squoted-or-escape*
         'lex-repetition-*-squoted-or-escape)
   (cons *lex-repetition-*-identifier-rest*
         'lex-repetition-*-identifier-rest)
   (cons *lex-repetition-*-whitespace-char*
         'lex-repetition-*-whitespace-char)
   (cons *lex-repetition-*-not-lf-or-cr*
         'lex-repetition-*-not-lf-or-cr)
   (cons *lex-repetition-*-lexeme*
         'lex-repetition-*-lexeme)
   )
  ///
  (assert-event (abnf::repetition-symbol-alistp abnf::*def-parse-repetition-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 3:
;; Define Lexing Functions

;; Create the lexing functions for the above.

;; When we can't use the generators and we write lexing functions by hand,
;; we use the following naming convention for the trees and input sequences.
;; If we parse "foo" as a single element (or as a repetition)
;; then we call the tree(s) returned "tree(s)-foo"
;; and we call the remaining input "input-after-foo".

(abnf::def-parse-rulename "boolean")
(abnf::def-parse-rulename "dquote")
(abnf::def-parse-rulename "squote")
(abnf::def-parse-rulename "lf")
(abnf::def-parse-rulename "cr")
(abnf::def-parse-rulename "decimal-digit")
(abnf::def-parse-rulename "nonzero-decimal-digit")
(abnf::def-parse-rulename "hex-digit")

;; Used for decimal-number
(abnf::def-parse-*-rulename "decimal-digit")
(abnf::def-parse-rulename "decimal-number")

;; Used for hex-number
(abnf::def-parse-*-rulename "hex-digit")
(abnf::def-parse-rulename "hex-number")


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
               (enable abnf::treep-when-tree-resultp-and-not-resulterrp))))
      (rest-input nat-listp))
  :short "Lex exactly 2 hexadecimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lex an 8-bit number expressed in hex."))
  (b* (((mv tree-digit1 input-after-digit1) (lex-hex-digit input))
       ((when (resulterrp tree-digit1))
        (mv tree-digit1
            (acl2::nat-list-fix input)))
       ((mv tree-digit2 input-after-digit2) (lex-hex-digit input-after-digit1))
       ((when (resulterrp tree-digit2))
        (mv tree-digit2
            ;; Note, this error result does not mention the successful
            ;; first hex digit, but that is fine, because rules fail
            ;; all the time and other rules succeed.
            (acl2::nat-list-fix input))))
    (mv (list tree-digit1 tree-digit2)
        input-after-digit2))
  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-2-hex-digits-<
    (implies (not (resulterrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; 2. an optional underbar,
(abnf::def-parse-option *lex-alternation-underbar*)

;; 3. the concatenation (a group): ( [ "_" ] 2hex-digit )
(abnf::def-parse-group *lex-alternation-optional-underbar-and-two-hex-digits*)

;; 4. the repetition: *( [ "_" ] 2hex-digit )
(abnf::def-parse-*-group *lex-alternation-optional-underbar-and-two-hex-digits*)
;; Note, this actually builds the repetition containing the group
;; (aka *lex-repetition-*-optional-underbar-and-two-hex-digits*)
;; and looks it up in *def-parse-repetition-fns*

;; 5. the group: 2hex-digit *( [ "_" ] 2hex-digit )
;;    used as the option: [ 2hex-digit *( [ "_" ] 2hex-digit ) ]
(abnf::def-parse-option *lex-alternation-sequence-of-2hex-digits*)

;; 6. ( dquote [ 2hex-digit *( [ "_" ] 2hex-digit ) ] dquote
;;    / squote [ 2hex-digit *( [ "_" ] 2hex-digit ) ] squote )
(abnf::def-parse-group *lex-alternation-for-hex-string*)

;; Finally, the rule hex-string
(abnf::def-parse-rulename "hex-string")

;; --------------------------------

(abnf::def-parse-rulename "double-quoted-printable")
(abnf::def-parse-rulename "single-quoted-printable")

;; --------------------------------
;; rule escape-sequence

;; 1. The alternation (used as a group):
;;    ( squote / dquote / %s"n" / %s"r" / %s"t" / lf / cr )
(abnf::def-parse-group *lex-alternation-escape-sequence-single*)

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
               (enable abnf::treep-when-tree-resultp-and-not-resulterrp))))
      (rest-input nat-listp))
  :short "Lex exactly 4 hexadecimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to lex a 16-bit number expressed in hex."))
  (b* (((mv tree-digit1 input-after-digit1) (lex-hex-digit input))
       ((when (resulterrp tree-digit1))
        (mv tree-digit1
            (acl2::nat-list-fix input)))
       ((mv tree-digit2 input-after-digit2) (lex-hex-digit input-after-digit1))
       ((when (resulterrp tree-digit2))
        (mv tree-digit2
            (acl2::nat-list-fix input)))
       ((mv tree-digit3 input-after-digit3) (lex-hex-digit input-after-digit2))
       ((when (resulterrp tree-digit3))
        (mv tree-digit3
            (acl2::nat-list-fix input)))
       ((mv tree-digit4 input-after-digit4) (lex-hex-digit input-after-digit3))
       ((when (resulterrp tree-digit4))
        (mv tree-digit4
            (acl2::nat-list-fix input)))
       )
    (mv (list tree-digit1 tree-digit2 tree-digit3 tree-digit4)
        input-after-digit4))
  :hooks (:fix)
  ///
  (defret len-of-lex-repetition-4-hex-digits-<
    (implies (not (resulterrp trees))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; 3. The alternation (used as a group):
;;    ( ( squote / dquote / %s"n" / %s"r" / %s"t" / lf / cr )
;;      / %s"u" 4hex-digit
;;      / %s"x" 2hex-digit )
(abnf::def-parse-group *lex-alternation-escape-sequence-body*)

;; Finally, the rule escape-sequence
(abnf::def-parse-rulename "escape-sequence")


;; --------------------------------
;; rule string-literal

;; 1. ( double-quoted-printable / escape-sequence )
(abnf::def-parse-group *lex-alternation-dquoted-or-escape*)

;; 2. *( double-quoted-printable / escape-sequence )
(abnf::def-parse-*-group *lex-alternation-dquoted-or-escape*)

;; 3. ( single-quoted-printable / escape-sequence )
(abnf::def-parse-group *lex-alternation-squoted-or-escape*)

;; 4. *( single-quoted-printable / escape-sequence )
(abnf::def-parse-*-group *lex-alternation-squoted-or-escape*)

;; the rule string-literal
(abnf::def-parse-rulename "string-literal")

;; --------------------------------

;; The rule for literal looks like this, with alternative numbers added
;; literal = decimal-number  1
;;        / hex-number       2
;;        / boolean          3
;;        / string-literal   4
;;        / hex-string       5

;; We must try hex-number before decimal-number in our lexer,
;; so that the initial 0 in 0x is not lexed as a decimal-number.
(abnf::def-parse-rulename "literal" :order (2 1 3 4 5))

;; --------------------------------

(abnf::def-parse-rulename "lowercase-letter")
(abnf::def-parse-rulename "uppercase-letter")
(abnf::def-parse-rulename "identifier-start")
(abnf::def-parse-rulename "identifier-rest")
(abnf::def-parse-*-rulename "identifier-rest")
(abnf::def-parse-rulename "identifier")

;; --------------------------------

(abnf::def-parse-rulename "whitespace-char")
(abnf::def-parse-*-rulename "whitespace-char")
; the preceding forms generates the function
; lex-repetition-*-whitespace-char

(define lex-whitespace ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Lex rule @('whitespace = 1*whitespace-char')."
  (b* (((mv tree-1char input-after-1char)
        (lex-whitespace-char input))
       ((when (resulterrp tree-1char))
        (mv (err "whitespace problem")
            (acl2::nat-list-fix input)))
       ((mv trees-restchars input-after-restchars)
        (lex-repetition-*-whitespace-char input-after-1char))
       ;; Can an error even happen?  Wouldn't it just return NIL (zero trees)?
       ;; Check error just in case.
       ((when (resulterrp trees-restchars))
        (mv (err "whitespace problem")
            (acl2::nat-list-fix input))))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "whitespace")
         :branches (list (cons tree-1char trees-restchars)))
        input-after-restchars))
  :hooks (:fix)
  ///
  (defret len-of-lex-whitespace-<
    (implies (not (resulterrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))


;; --------------------------------

(abnf::def-parse-rulename "not-star")
(abnf::def-parse-rulename "not-star-or-slash")

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
                     ((when (resulterrp tree-star))
                      (mv (err "problem lexing \"*\"") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment-after-star
                       input-after-star))
                     ((when (resulterrp tree-rest))
                      (mv (err "problem lexing rest-of-block-comment-after-star") input)))
                  ;; combine the two trees into tree-star+rest
                  (mv (list (list tree-star) (list tree-rest))
                      input-after-rest)))
               ((unless (resulterrp tree-star+rest))
                (mv tree-star+rest input-after-star+rest))
               ;; otherwise, try the second alternative:
               ;; ( not-star rest-of-block-comment )
               ((mv tree-not-star+rest
                    input-after-not-star+rest)
                (b* (((mv tree-not-star input-after-not-star)
                      (lex-not-star input))
                     ((when (resulterrp tree-not-star))
                      (mv (err "problem lexing not-star") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment input-after-not-star))
                     ((when (resulterrp tree-rest))
                      (mv (err "problem lexing rest-of-block-comment") input)))
                  ;; combine the two trees into
                  ;; tree-not-star+rest
                  (mv (list (list tree-not-star)
                            (list tree-rest))
                      input-after-rest))))
            (mv tree-not-star+rest
                input-after-not-star+rest)))
         ((when (resulterrp trees))
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
               ((unless (resulterrp tree-slash))
                (mv (list (list tree-slash)) input-after-slash))
               ;; second alternative: ( "*" rest-of-block-comment-after-star )
               ((mv tree-star+rest input-after-star+rest)
                (b* (((mv tree-star input-after-star)
                      (abnf::parse-ichars "*" input))
                     ((when (resulterrp tree-star))
                      (mv (err "problem lexing \"*\"") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment-after-star
                       input-after-star))
                     ((when (resulterrp tree-rest))
                      (mv (err "problem lexing rest-of-block-comment-after-star") input)))
                  ;; combine the two trees into tree-star+rest
                  (mv (list (list tree-star)
                            (list tree-rest))
                      input-after-rest)))
               ((unless (resulterrp tree-star+rest))
                (mv tree-star+rest input-after-star+rest))
               ;; otherwise, try the third alternative:
               ;; not-star-or-slash rest-of-block-comment
               ((mv tree-not-star-or-slash+rest
                    input-after-not-star-or-slash+rest)
                (b* (((mv tree-not-star-or-slash input-after-not-star-or-slash)
                      (lex-not-star-or-slash input))
                     ((when (resulterrp tree-not-star-or-slash))
                      (mv (err "problem lexing not-star-or-slash") input))
                     ((mv tree-rest input-after-rest)
                      (lex-rest-of-block-comment input-after-not-star-or-slash))
                     ((when (resulterrp tree-rest))
                      (mv (err "problem lexing rest-of-block-comment") input)))
                  ;; combine the two trees into
                  ;; tree-not-star-or-slash+rest
                  (mv (list (list tree-not-star-or-slash)
                            (list tree-rest))
                      input-after-rest))))
            (mv tree-not-star-or-slash+rest
                input-after-not-star-or-slash+rest)))
         ((when (resulterrp trees))
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
      (implies (not (resulterrp tree))
               (< (len rest-input)
                  (len input)))
      :rule-classes :linear
      :fn lex-rest-of-block-comment)
    (defret len-of-input-after-rest-of-block-comment-after-star-<
      (implies (not (resulterrp tree))
               (< (len rest-input)
                  (len input)))
      :rule-classes :linear
      :fn lex-rest-of-block-comment-after-star)))

(abnf::def-parse-rulename "block-comment")

;; --------------------------------
;; end of line comments

(abnf::def-parse-rulename "not-lf-or-cr")
(abnf::def-parse-*-rulename "not-lf-or-cr")
(abnf::def-parse-rulename "end-of-line-comment")
;; and a rule that recognizes either a block comment or an end-of-line-comment
(abnf::def-parse-rulename "comment")

;; --------------------------------
;; keywords, symbols, tokens, and lexemes

(abnf::def-parse-rulename "keyword")
(abnf::def-parse-rulename "symbol")
(abnf::def-parse-rulename "token")
(abnf::def-parse-rulename "lexeme")

;; --------------------------------
;; list of lexemes
;; lex-repetition-*-lexeme cann be used to tokenize a file
;; ( We do not define a rule "file-lexemes = *lexeme"
;;   since (1) there is no need to construct a tree around the list, and
;;   (2) the generator macro def-parse-rulename does not support nullable rules
;;   since it generates a return theorem that the rest-input be shorter than the input.)

(abnf::def-parse-*-rulename "lexeme")
