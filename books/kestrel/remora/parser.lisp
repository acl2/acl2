; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "grammar")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (grammar)
  :short "An executable parser for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a parser for the Remora grammar.
     It operates on lists of natural numbers representing
     Unicode code point integers (excluding surrogates).")
   (xdoc::p
    "The parser is defined in three sections:")
   (xdoc::ol
    (xdoc::li
     "Generation of specialized generator macros for this parser.")
    (xdoc::li
     "Tables of parsing functions for groups, options, and repetitions
      that occur internally to Remora grammar rules.")
    (xdoc::li
     "Definitions of parsing functions,
      most of which are calls to macros that generate the functions,
      but some of which are hand-written
      due to limitations in the current parser generators.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 1:
;; Generation of specialized generator macros for this parser.

(defsection parse-generation-macros
  :short "Parsing generation macros specialized to this parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee abnf::defdefparse) to generate specialized macros
     to generate (some of) the Remora parser.
     See the user documentation of @(tsee abnf::defdefparse) for details."))

  (abnf::defdefparse remora
    :package "REMORA"
    :grammar *grammar*
    :prefix parse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 2:
;; Tables of parsing functions for groups, options, and repetitions.

(defsection parse-generation-tables
  :short "ABNF group, option, and repetition tables
          for generating parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the user documentation of @(tsee abnf::defdefparse) for details."))

  (defparse-remora-group-table

    ;; exponent: ( "e" / "E" )
    "( \"e\" / \"E\" )" group-e-or-E

    ;; num-val: ( float-lit / decimal )
    "( float-lit / decimal )" group-float-lit-or-decimal

    ;; ws: ( unicode-space / comment )
    "( unicode-space / comment )" group-unicode-space-or-comment

    ;; comment: ( %x00-09 / %x0B-D7FF / %xE000-10FFFF )
    "( %x00-09 / %x0B-D7FF / %xE000-10FFFF )" group-comment-char

    ;; ---- Groups for ws-separated repetitions ----
    "( ws exp )" group-ws-exp
    "( ws type-exp )" group-ws-type-exp
    "( ws extent )" group-ws-extent
    "( ws atom )" group-ws-atom
    "( ws pat )" group-ws-pat
    "( ws bind )" group-ws-bind
    "( ws dim )" group-ws-dim
    "( ws shape )" group-ws-shape
    "( ws type-param )" group-ws-type-param
    "( ws extent-param )" group-ws-extent-param
    "( ws decimal )" group-ws-decimal

    ;; ---- Groups for keyword/operator alternatives ----
    ;; arrow-type
    "( \"->\" / %x2192 )" group-arrow
    ;; forall-type
    "( \"Forall\" / %x2200 )" group-forall
    ;; pi-type
    "( \"Pi\" / %x03A0 )" group-pi
    ;; sigma-type
    "( \"Sigma\" / %x03A3 )" group-sigma
    ;; lambda
    "( \"fn\" / %x03BB )" group-fn
    ;; type-lambda inner group
    "( \"t\" %x03BB )" group-t-lambda
    ;; type-lambda
    "( \"t-fn\" / ( \"t\" %x03BB ) )" group-t-fn
    ;; index-lambda inner group
    "( \"i\" %x03BB )" group-i-lambda
    ;; index-lambda
    "( \"i-fn\" / ( \"i\" %x03BB ) )" group-i-fn)

  (defparse-remora-option-table

    ;; num-val: [ "+" / "-" ]
    ;; also used in exponent
    "[ \"+\" / \"-\" ]" optional-sign

    ;; float-lit: [ exponent ]
    "[ exponent ]" optional-exponent

    ;; fun-bind, tfun-bind, ifun-bind
    "[ ws \":\" ws type-exp ]" optional-type-annotation)

  (defparse-remora-repetition-table

    ;; decimal: 1*DIGIT; also used in float-lit, exponent, num-escape
    "*digit" repetition-*-digit
    "1*digit" repetition-1*-digit

    ;; comment: *( %x00-09 / %x0B-D7FF / %xE000-10FFFF )
    "*( %x00-09 / %x0B-D7FF / %xE000-10FFFF )" repetition-*-comment-char

    ;; ws: *( unicode-space / comment )
    "*( unicode-space / comment )" repetition-*-unicode-space-or-comment

    ;; num-escape: *hexdig (for 1*hexdig pattern)
    "*hexdig" repetition-*-hexdig

    ;; identifier: *id-continue
    "*id-continue" repetition-*-id-continue

    ;; string-lit: *char-literal
    "*char-literal" repetition-*-char-literal

    ;; ---- Repetitions for ws-separated lists ----
    "*( ws exp )" repetition-*-ws-exp
    "1*( ws exp )" repetition-1*-ws-exp
    "*( ws type-exp )" repetition-*-ws-type-exp
    "*( ws extent )" repetition-*-ws-extent
    "*( ws atom )" repetition-*-ws-atom
    "1*( ws atom )" repetition-1*-ws-atom
    "*( ws pat )" repetition-*-ws-pat
    "*( ws bind )" repetition-*-ws-bind
    "*( ws dim )" repetition-*-ws-dim
    "*( ws shape )" repetition-*-ws-shape
    "*( ws type-param )" repetition-*-ws-type-param
    "*( ws extent-param )" repetition-*-ws-extent-param
    "*( ws decimal )" repetition-*-ws-decimal

    ;; unbox-exp: *( extent-param ws )
    "*( extent-param ws )" repetition-*-extent-param-ws))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Part 3:
;; Define parsing functions.
;; Built bottom-up from terminal rules to the top-level program rule.

;; ---- Core ABNF rules ----

(defparse-remora-rulename "digit")
(defparse-remora-rulename "dquote")

;; hexdig = digit / "A" / "B" / "C" / "D" / "E" / "F"
;;                / "a" / "b" / "c" / "d" / "e" / "f"
;; Hand-written because 13 alternatives cause combinatorial proof blowup.

(define hexdigp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a hex digit code point."
  (b* ((nat (nfix nat)))
    (or (and (<= #x30 nat) (<= nat #x39))   ; 0-9
        (and (<= #x41 nat) (<= nat #x46))   ; A-F
        (and (<= #x61 nat) (<= nat #x66)))) ; a-f
  :hooks (:fix))

(define parse-hexdig ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('hexdig')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "hexdig: end of input") nil))
       (byte (car input))
       ((unless (hexdigp byte))
        (mv (reserrf "hexdig: not a hex digit") input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "hexdig")
         :branches (list (list (abnf::tree-leafterm (list byte)))))
        (cdr input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-hexdig-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-hexdig-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; ---- Whitespace and comments ----

;; unicode-space has 14 single-value/range alternatives;
;; hand-written to avoid combinatorial proof blowup.

(define unicode-spacep ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a Unicode whitespace code point."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code points for which Haskell's
     @('Data.Char.isSpace') returns true.
     See the @('unicode-space') rule in @('grammar.abnf')."))
  (b* ((nat (nfix nat)))
    (or (eql nat #x09)                        ; HORIZONTAL TAB
        (eql nat #x0A)                        ; LINE FEED
        (eql nat #x0B)                        ; VERTICAL TAB
        (eql nat #x0C)                        ; FORM FEED
        (eql nat #x0D)                        ; CARRIAGE RETURN
        (eql nat #x20)                        ; SPACE
        (eql nat #xA0)                        ; NO-BREAK SPACE
        (eql nat #x1680)                      ; OGHAM SPACE MARK
        (and (<= #x2000 nat) (<= nat #x200A)) ; EN QUAD .. HAIR SPACE
        (eql nat #x2028)                      ; LINE SEPARATOR
        (eql nat #x2029)                      ; PARAGRAPH SEPARATOR
        (eql nat #x202F)                      ; NARROW NO-BREAK SPACE
        (eql nat #x205F)                      ; MEDIUM MATHEMATICAL SPACE
        (eql nat #x3000)))                    ; IDEOGRAPHIC SPACE
  :hooks (:fix))

(define parse-unicode-space ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('unicode-space')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "unicode-space: end of input") nil))
       (nat (car input))
       ((unless (unicode-spacep nat))
        (mv (reserrf "unicode-space: not a whitespace code point") input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "unicode-space")
         :branches (list (list (abnf::tree-leafterm (list nat)))))
        (cdr input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-unicode-space-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-unicode-space-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;; Repetition *( %x00-09 / %x0B-D7FF / %xE000-10FFFF ), used in comment.
(defparse-remora-group "( %x00-09 / %x0B-D7FF / %xE000-10FFFF )")
(defparse-remora-*-group "( %x00-09 / %x0B-D7FF / %xE000-10FFFF )")

(defparse-remora-rulename "comment")

;; Repetition *( unicode-space / comment ), used in ws.
(defparse-remora-group "( unicode-space / comment )")
(defparse-remora-*-group "( unicode-space / comment )")

(defparse-remora-rulename "ws")

;; ---- Lexical primitives ----

;; [SC1] Repetitions *digit and 1*digit are greedy, ensuring that e.g.
;; "123" is parsed as one decimal, not "1" then "2" then "3".
(defparse-remora-*-rulename "digit")
(defparse-remora-1*-rulename "digit")

(defparse-remora-rulename "decimal")

;; Group ( "e" / "E" ) and option [ "+" / "-" ], used in exponent.
(defparse-remora-group "( \"e\" / \"E\" )")
(defparse-remora-option "[ \"+\" / \"-\" ]")

(defparse-remora-rulename "exponent")

;; Option [ exponent ], used in float-lit.
(defparse-remora-option "[ exponent ]")

(defparse-remora-rulename "float-lit")

;; ---- Base values ----

(defparse-remora-rulename "bool-val")

;; Group ( float-lit / decimal ), used in num-val.
(defparse-remora-group "( float-lit / decimal )")

(defparse-remora-rulename "num-val")
(defparse-remora-rulename "base-val")

;; ---- Identifiers ----

;; non-ascii, id-start, id-continue all have 9-13 range alternatives;
;; hand-written to avoid combinatorial proof blowup.

(define non-asciip ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a non-ASCII non-whitespace non-surrogate
          code point."
  (b* ((nat (nfix nat)))
    (or (and (<= #x80 nat) (<= nat #x9F))
        (and (<= #xA1 nat) (<= nat #x167F))
        (and (<= #x1681 nat) (<= nat #x1FFF))
        (and (<= #x200B nat) (<= nat #x2027))
        (and (<= #x202A nat) (<= nat #x202E))
        (and (<= #x2030 nat) (<= nat #x205E))
        (and (<= #x2060 nat) (<= nat #x2FFF))
        (and (<= #x3001 nat) (<= nat #xD7FF))
        (and (<= #xE000 nat) (<= nat #x10FFFF))))
  :hooks (:fix))

(define parse-non-ascii ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('non-ascii')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "non-ascii: end of input") nil))
       (nat (car input))
       ((unless (non-asciip nat))
        (mv (reserrf "non-ascii: not a non-ASCII identifier char") input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "non-ascii")
         :branches (list (list (abnf::tree-leafterm (list nat)))))
        (cdr input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-non-ascii-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-non-ascii-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define id-startp ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a valid identifier start code point."
  (b* ((nat (nfix nat)))
    (or (and (<= #x00 nat) (<= nat #x08))
        (and (<= #x0E nat) (<= nat #x1F))
        (eql nat #x21)
        (and (<= #x24 nat) (<= nat #x26))
        (and (<= #x2A nat) (<= nat #x2B))
        (and (<= #x2D nat) (<= nat #x2F))
        (eql nat #x3A)
        (and (<= #x3C nat) (<= nat #x3F))
        (and (<= #x41 nat) (<= nat #x5A))
        (and (<= #x5E nat) (<= nat #x5F))
        (and (<= #x61 nat) (<= nat #x7A))
        (and (<= #x7E nat) (<= nat #x7F))
        (non-asciip nat)))
  :hooks (:fix))

(define parse-id-start ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse an @('id-start')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "id-start: end of input") nil))
       (nat (car input))
       ((unless (id-startp nat))
        (mv (reserrf "id-start: not a valid start char") input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "id-start")
         :branches (list (list (abnf::tree-leafterm (list nat)))))
        (cdr input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-id-start-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-id-start-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define id-continuep ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a valid identifier continuation
          code point."
  (b* ((nat (nfix nat)))
    (or (and (<= #x00 nat) (<= nat #x08))
        (and (<= #x0E nat) (<= nat #x1F))
        (eql nat #x21)
        (and (<= #x24 nat) (<= nat #x26))
        (and (<= #x2A nat) (<= nat #x2B))
        (and (<= #x2D nat) (<= nat #x3A))   ; includes digits and :
        (and (<= #x3C nat) (<= nat #x3F))
        (and (<= #x41 nat) (<= nat #x5A))
        (and (<= #x5E nat) (<= nat #x5F))
        (and (<= #x61 nat) (<= nat #x7A))
        (and (<= #x7E nat) (<= nat #x7F))
        (non-asciip nat)))
  :hooks (:fix))

(define parse-id-continue ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse an @('id-continue')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "id-continue: end of input") nil))
       (nat (car input))
       ((unless (id-continuep nat))
        (mv (reserrf "id-continue: not a valid continue char") input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "id-continue")
         :branches (list (list (abnf::tree-leafterm (list nat)))))
        (cdr input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-id-continue-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-id-continue-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; [SC1] Max-munch: parse-identifier is greedy because *id-continue
;; consumes as many continuation characters as possible.  This ensures
;; that e.g. "fn2" is parsed as one identifier, not "fn" + "2".
;; [SC2] Keyword exclusion: parse-identifier does NOT reject keywords.
;; A separate check is needed at the semantic level to reject identifiers
;; whose text equals a reserved keyword.
(defparse-remora-*-rulename "id-continue")
(defparse-remora-rulename "identifier")

;; ---- String literals and escape sequences ----

;; char-escape has 10 single-char alternatives; hand-written.

(define char-escapep ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a natural number is a char-escape mnemonic code point."
  (b* ((nat (nfix nat)))
    (or (eql nat #x61)   ; a
        (eql nat #x62)   ; b
        (eql nat #x66)   ; f
        (eql nat #x6E)   ; n
        (eql nat #x72)   ; r
        (eql nat #x74)   ; t
        (eql nat #x76)   ; v
        (eql nat #x5C)   ; backslash
        (eql nat #x22)   ; double quote
        (eql nat #x27))) ; single quote
  :hooks (:fix))

(define parse-char-escape ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('char-escape')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "char-escape: end of input") nil))
       (nat (car input))
       ((unless (char-escapep nat))
        (mv (reserrf "char-escape: not a char-escape") input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "char-escape")
         :branches (list (list (abnf::tree-leafterm (list nat)))))
        (cdr input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-char-escape-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-char-escape-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; ascii-escape has 33 multi-character alternatives; hand-written.
;; Uses abnf::parse-ichars for matching. Longer prefixes tried first
;; (e.g. SOH before SO, ESC before EM).

(define parse-ascii-escape ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse an @('ascii-escape')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Matches one of 33 ASCII control character names.
     Longer prefixes are tried first (SOH before SO, ESC before EM)."))
  (b* (((mv inner-tree inner-rest)
        (b* (((mv tree rest) (abnf::parse-ichars "NUL" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "SOH" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "STX" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "ETX" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "EOT" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "ENQ" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "ACK" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "BEL" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "BS" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "HT" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "LF" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "VT" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "FF" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "CR" input))
             ((unless (reserrp tree)) (mv tree rest))
             ;; SOH already tried; SO is safe now
             ((mv tree rest) (abnf::parse-ichars "SO" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "SI" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "DLE" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "DC1" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "DC2" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "DC3" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "DC4" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "NAK" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "SYN" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "ETB" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "CAN" input))
             ((unless (reserrp tree)) (mv tree rest))
             ;; ESC already tried; EM is safe now
             ((mv tree rest) (abnf::parse-ichars "ESC" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "EM" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "SUB" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "FS" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "GS" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "RS" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "US" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "SP" input))
             ((unless (reserrp tree)) (mv tree rest))
             ((mv tree rest) (abnf::parse-ichars "DEL" input))
             ((unless (reserrp tree)) (mv tree rest)))
          (mv (reserrf-push tree) (nat-list-fix input))))
       ((when (reserrp inner-tree))
        (mv inner-tree (nat-list-fix input))))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "ascii-escape")
         :branches (list (list inner-tree)))
        inner-rest))
  :hooks (:fix)
  ///
  (defret len-of-parse-ascii-escape-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-ascii-escape-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; caret-escape = "^" %x40-5F
;; Hand-written: concatenation of a char-val and a num-val range.

(define parse-caret-escape ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('caret-escape')."
  (b* (((mv tree-caret input1) (abnf::parse-ichars "^" input))
       ((when (reserrp tree-caret))
        (mv (reserrf-push tree-caret) (nat-list-fix input)))
       ((mv tree-ctrl input2) (abnf::parse-range #x40 #x5F input1))
       ((when (reserrp tree-ctrl))
        (mv (reserrf-push tree-ctrl) (nat-list-fix input))))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "caret-escape")
         :branches (list (list tree-caret tree-ctrl)))
        input2))
  :hooks (:fix)
  ///
  (defret len-of-parse-caret-escape-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-caret-escape-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; Repetition *hexdig, needed for num-escape's "x" 1*HEXDIG alternative.
(defparse-remora-*-rulename "hexdig")

;; num-escape = 1*DIGIT / "o" 1*(%x30-37) / "x" 1*HEXDIG
;; Hand-written because 1*(%x30-37) is a repetition of a bare num-val range.

(define parse-octal-digits ((input nat-listp))
  :returns (mv (trees abnf::tree-listp)
               (rest-input nat-listp))
  :short "Parse zero or more octal digits (@('%x30-37'))."
  :measure (len input)
  (b* (((mv tree input1) (abnf::parse-range #x30 #x37 input))
       ((when (reserrp tree)) (mv nil (nat-list-fix input))))
    (mv-let (trees input2) (parse-octal-digits input1)
      (mv (cons tree trees) input2)))
  :hooks (:fix)
  ///
  (defret len-of-parse-octal-digits-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear))

(define parse-num-escape ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('num-escape')."
  (b* (;; Try 1*DIGIT (decimal)
       ((mv trees-digits rest-digits) (parse-repetition-1*-digit input))
       ((unless (reserrp trees-digits))
        (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "num-escape")
             :branches (list trees-digits))
            rest-digits))
       ;; Try "o" 1*(%x30-37)
       ((mv tree-o input1) (abnf::parse-ichars "o" input))
       ((when (not (reserrp tree-o)))
        (b* (((mv tree-first input2) (abnf::parse-range #x30 #x37 input1))
             ((when (reserrp tree-first))
              (mv (reserrf "num-escape: expected octal digit after o")
                  (nat-list-fix input)))
             ((mv more-trees input3) (parse-octal-digits input2)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "num-escape")
               :branches (list (list tree-o) (cons tree-first more-trees)))
              input3)))
       ;; Try "x" 1*HEXDIG
       ((mv tree-x input1) (abnf::parse-ichars "x" input))
       ((when (not (reserrp tree-x)))
        (b* (((mv tree-first input2) (parse-hexdig input1))
             ((when (reserrp tree-first))
              (mv (reserrf "num-escape: expected hex digit after x")
                  (nat-list-fix input)))
             ((mv more-trees input3) (parse-repetition-*-hexdig input2)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "num-escape")
               :branches (list (list tree-x) (cons tree-first more-trees)))
              input3))))
    (mv (reserrf "num-escape: no match") (nat-list-fix input)))
  :hooks (:fix)
  ///
  (defret len-of-parse-num-escape-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-num-escape-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; escape-char = char-escape / ascii-escape / caret-escape / num-escape
(defparse-remora-rulename "escape-char")

;; char-literal has 4 large ranges + escape; hand-written.

(define char-literal-nonescape-p ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a non-escape char-literal."
  (b* ((nat (nfix nat)))
    (or (and (<= #x00 nat) (<= nat #x21))
        (and (<= #x23 nat) (<= nat #x5B))
        (and (<= #x5D nat) (<= nat #xD7FF))
        (and (<= #xE000 nat) (<= nat #x10FFFF))))
  :hooks (:fix))

(define parse-char-literal ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('char-literal')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "char-literal: end of input") nil))
       (nat (car input))
       ;; Non-escape case: any char except " (%x22) and \ (%x5C)
       ((when (char-literal-nonescape-p nat))
        (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "char-literal")
             :branches (list (list (abnf::tree-leafterm (list nat)))))
            (cdr input)))
       ;; Escape case: "\" escape-char
       ((unless (eql nat #x5C))
        (mv (reserrf "char-literal: invalid char") input))
       ((mv esc-tree rest-after-esc) (parse-escape-char (cdr input)))
       ((when (reserrp esc-tree))
        (mv (reserrf-push esc-tree) input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "char-literal")
         :branches (list (list (abnf::tree-leafterm (list #x5C))
                               esc-tree)))
        rest-after-esc))
  :hooks (:fix)
  ///
  (defret len-of-parse-char-literal-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-char-literal-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; string-lit = DQUOTE *char-literal DQUOTE
(defparse-remora-*-rulename "char-literal")
(defparse-remora-rulename "string-lit")

;; ---- Type and extent parameters ----

(defparse-remora-rulename "type-param")
(defparse-remora-rulename "extent-param")

;; ---- Dimensions, shapes, extents ----
;; These rules are mutually recursive, so they must be hand-written
;; using defines. Two clusters:
;;   1. dim / dim-arith (dim-arith calls *dim)
;;   2. shape / shape-paren / extent (shape ↔ extent, shape ↔ shape-paren)

;; shape-lit is independent; auto-generate it first.
(defparse-remora-group "( ws decimal )")
(defparse-remora-*-group "( ws decimal )")
(defparse-remora-rulename "shape-lit")

;; Cluster 1: dim / dim-arith
;; dim = "$" identifier / decimal / "(" ws dim-arith ws ")"
;; dim-arith = "+" *( ws dim ) / "*" *( ws dim ) / "-" *( ws dim )

(defines parse-dim+dim-arith
  :ruler-extenders :all
  ;; Lexicographic measure: (len input, flag).
  ;; Flag 2 for parse-*-ws-dim, 1 for parse-dim, 0 for parse-dim-arith.
  ;; When parse-*-ws-dim calls parse-dim on post-ws input (same len),
  ;; the flag decreases from 2 to 1.
  (define parse-dim ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 1)
    :short "Parse a @('dim')."
    (b* (;; Try "$" identifier
         ((mv tree-dollar input1) (abnf::parse-ichars "$" input))
         ((when (not (reserrp tree-dollar)))
          (b* (((mv tree-id input2) (parse-identifier input1))
               ((when (reserrp tree-id))
                (mv (reserrf-push tree-id) (nat-list-fix input))))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "dim")
                 :branches (list (list tree-dollar tree-id)))
                input2)))
         ;; Try decimal
         ((mv tree-dec input1) (parse-decimal input))
         ((when (not (reserrp tree-dec)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "dim")
               :branches (list (list tree-dec)))
              input1))
         ;; Try "(" ws dim-arith ws ")"
         ((mv tree-open input1) (abnf::parse-ichars "(" input))
         ((when (reserrp tree-open))
          (mv (reserrf "dim: no match") (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "dim: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-da input3) (parse-dim-arith input2))
         ((when (reserrp tree-da))
          (mv (reserrf-push tree-da) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars ")" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "dim")
           :branches (list (list tree-open tree-ws1 tree-da tree-ws2 tree-close)))
          input5)))

  (define parse-dim-arith ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse a @('dim-arith')."
    (b* (;; Try each operator: +, *, -
         ;; All have the same structure: OP *( ws dim )
         ((mv tree-op input1)
          (b* (((mv tree rest) (abnf::parse-ichars "+" input))
               ((unless (reserrp tree)) (mv tree rest))
               ((mv tree rest) (abnf::parse-ichars "*" input))
               ((unless (reserrp tree)) (mv tree rest))
               ((mv tree rest) (abnf::parse-ichars "-" input))
               ((unless (reserrp tree)) (mv tree rest)))
            (mv (reserrf "dim-arith: expected +, *, or -")
                (nat-list-fix input))))
         ((when (reserrp tree-op))
          (mv tree-op (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "dim-arith: impossible") (nat-list-fix input)))
         ;; Parse *( ws dim )
         ((mv trees-dims input2) (parse-*-ws-dim input1)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "dim-arith")
           :branches (list (list tree-op) trees-dims))
          input2)))

  (define parse-*-ws-dim ((input nat-listp))
    :returns (mv (trees abnf::tree-listp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 2)
    :short "Parse @('*( ws dim )')."
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-dim input2) (parse-dim input1))
         ((when (reserrp tree-dim)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more-trees input3) (parse-*-ws-dim input2)))
      (mv (cons (abnf::make-tree-nonleaf
                 :rulename? nil
                 :branches (list (list tree-ws tree-dim)))
                more-trees)
          input3)))
  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))
  :verify-guards nil
  ///
  (defret-mutual len-of-parse-dim+dim-arith
    (defret len-of-parse-dim-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-dim)
    (defret len-of-parse-dim-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-dim)
    (defret len-of-parse-dim-arith-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-dim-arith)
    (defret len-of-parse-dim-arith-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-dim-arith)
    (defret len-of-parse-*-ws-dim-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-*-ws-dim)
    :hints (("Goal" :in-theory (enable parse-dim parse-dim-arith parse-*-ws-dim))))
  (verify-guards parse-dim
    :hints (("Goal" :in-theory (disable parse-dim parse-dim-arith parse-*-ws-dim)))))

;; Cluster 2: shape / shape-paren / extent
;; shape = "@" identifier / dim / "(" ws shape-paren ws ")" / "[" ws *( ws extent ) ws "]"
;; shape-paren = "dims" *( ws dim ) / "++" *( ws shape )
;; extent = dim / shape

(defines parse-shape+extent
  :ruler-extenders :all
  (define parse-shape ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 1)
    :short "Parse a @('shape')."
    (b* (;; Try "@" identifier
         ((mv tree-at input1) (abnf::parse-ichars "@" input))
         ((when (not (reserrp tree-at)))
          (b* (((mv tree-id input2) (parse-identifier input1))
               ((when (reserrp tree-id))
                (mv (reserrf-push tree-id) (nat-list-fix input))))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "shape")
                 :branches (list (list tree-at tree-id)))
                input2)))
         ;; Try dim
         ((mv tree-dim input1) (parse-dim input))
         ((when (not (reserrp tree-dim)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "shape")
               :branches (list (list tree-dim)))
              input1))
         ;; Try "(" ws shape-paren ws ")"
         ((mv tree-open input1) (abnf::parse-ichars "(" input))
         ((when (not (reserrp tree-open)))
          (b* (((mv tree-ws1 input2) (parse-ws input1))
               ((when (reserrp tree-ws1))
                (mv (reserrf-push tree-ws1) (nat-list-fix input)))
               ((mv tree-sp input3) (parse-shape-paren input2))
               ((when (reserrp tree-sp))
                (mv (reserrf-push tree-sp) (nat-list-fix input)))
               ((mv tree-ws2 input4) (parse-ws input3))
               ((when (reserrp tree-ws2))
                (mv (reserrf-push tree-ws2) (nat-list-fix input)))
               ((mv tree-close input5) (abnf::parse-ichars ")" input4))
               ((when (reserrp tree-close))
                (mv (reserrf-push tree-close) (nat-list-fix input))))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "shape")
                 :branches (list (list tree-open tree-ws1 tree-sp tree-ws2 tree-close)))
                input5)))
         ;; Try "[" ws *( ws extent ) ws "]"
         ((mv tree-open input1) (abnf::parse-ichars "[" input))
         ((when (reserrp tree-open))
          (mv (reserrf "shape: no match") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv trees-exts input3) (parse-*-ws-extent input2))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars "]" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "shape")
           :branches (list (list tree-open tree-ws1)
                           trees-exts
                           (list tree-ws2 tree-close)))
          input5)))

  (define parse-shape-paren ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse a @('shape-paren')."
    (b* (;; Try "dims" *( ws dim )
         ((mv tree-kw input1) (abnf::parse-ichars "dims" input))
         ((when (not (reserrp tree-kw)))
          (b* (((mv trees-dims input2) (parse-*-ws-dim input1)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "shape-paren")
                 :branches (list (list tree-kw) trees-dims))
                input2)))
         ;; Try "++" *( ws shape )
         ((mv tree-kw input1) (abnf::parse-ichars "++" input))
         ((when (reserrp tree-kw))
          (mv (reserrf "shape-paren: expected dims or ++")
              (nat-list-fix input)))
         ((mv trees-shapes input2) (parse-*-ws-shape input1)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "shape-paren")
           :branches (list (list tree-kw) trees-shapes))
          input2)))

  (define parse-extent ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 2)
    :short "Parse an @('extent')."
    (b* (;; Try dim first (per grammar ordering)
         ((mv tree-dim input1) (parse-dim input))
         ((when (not (reserrp tree-dim)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "extent")
               :branches (list (list tree-dim)))
              input1))
         ;; Try shape
         ((mv tree-shape input1) (parse-shape input))
         ((when (reserrp tree-shape))
          (mv (reserrf "extent: no match") (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "extent")
           :branches (list (list tree-shape)))
          input1)))

  (define parse-*-ws-shape ((input nat-listp))
    :returns (mv (trees abnf::tree-listp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 4)
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-shape input2) (parse-shape input1))
         ((when (reserrp tree-shape)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-shape input2)))
      (mv (cons (abnf::make-tree-nonleaf
                 :rulename? nil
                 :branches (list (list tree-ws tree-shape)))
                more)
          input3)))

  (define parse-*-ws-extent ((input nat-listp))
    :returns (mv (trees abnf::tree-listp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 3)
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-ext input2) (parse-extent input1))
         ((when (reserrp tree-ext)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-extent input2)))
      (mv (cons (abnf::make-tree-nonleaf
                 :rulename? nil
                 :branches (list (list tree-ws tree-ext)))
                more)
          input3)))

  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))
  :verify-guards nil
  ///
  (defret-mutual len-of-parse-shape+extent
    (defret len-of-parse-shape-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-shape)
    (defret len-of-parse-shape-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-shape)
    (defret len-of-parse-shape-paren-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-shape-paren)
    (defret len-of-parse-shape-paren-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-shape-paren)
    (defret len-of-parse-extent-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-extent)
    (defret len-of-parse-extent-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-extent)
    (defret len-of-parse-*-ws-shape-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-*-ws-shape)
    (defret len-of-parse-*-ws-extent-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-*-ws-extent)
    :hints (("Goal" :in-theory
             (disable parse-shape parse-shape-paren parse-extent
                      parse-*-ws-shape parse-*-ws-extent))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-shape) clause)
                 '(:expand (parse-shape input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-shape-paren) clause)
                 '(:expand (parse-shape-paren input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-extent) clause)
                 '(:expand (parse-extent input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-shape) clause)
                 '(:expand (parse-*-ws-shape input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-extent) clause)
                 '(:expand (parse-*-ws-extent input)))))
  (verify-guards parse-shape
    :hints (("Goal" :in-theory (disable parse-shape parse-shape-paren
                                        parse-extent parse-*-ws-shape
                                        parse-*-ws-extent)))))

;; ---- Types ----

;; Non-recursive type helpers (already-admitted dependencies only).
(defparse-remora-rulename "atom-type-var")
(defparse-remora-rulename "array-type-var")
(defparse-remora-rulename "base-type")

;; Groups for keyword/operator alternatives in type rules.
(defparse-remora-group "( \"->\" / %x2192 )")
(defparse-remora-group "( \"Forall\" / %x2200 )")
(defparse-remora-group "( \"Pi\" / %x03A0 )")
(defparse-remora-group "( \"Sigma\" / %x03A3 )")

;; Repetitions for non-recursive params (type-param, extent-param already defined).
(defparse-remora-group "( ws type-param )")
(defparse-remora-*-group "( ws type-param )")
(defparse-remora-group "( ws extent-param )")
(defparse-remora-*-group "( ws extent-param )")

;; Type rules are self-recursive: type-exp → bracket-type/array-type/etc → type-exp.
;; Hand-written using defines.

(defines parse-types
  :ruler-extenders :all

  (define parse-type-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 3)
    :short "Parse a @('type-exp')."
    (b* (;; Try atom-type-var
         ((mv tree input1) (parse-atom-type-var input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
               :branches (list (list tree))) input1))
         ;; Try array-type-var
         ((mv tree input1) (parse-array-type-var input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
               :branches (list (list tree))) input1))
         ;; Try base-type
         ((mv tree input1) (parse-base-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
               :branches (list (list tree))) input1))
         ;; Try bracket-type
         ((mv tree input1) (parse-bracket-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
               :branches (list (list tree))) input1))
         ;; Try "(" ws type-exp-paren ws ")"
         ((mv tree-open input1) (abnf::parse-ichars "(" input))
         ((when (reserrp tree-open))
          (mv (reserrf "type-exp: no match") (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "type-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-body input3) (parse-type-exp-paren input2))
         ((when (reserrp tree-body))
          (mv (reserrf-push tree-body) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars ")" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
           :branches (list (list tree-open tree-ws1 tree-body tree-ws2 tree-close)))
          input5)))

  (define parse-bracket-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 2)
    :short "Parse a @('bracket-type')."
    (b* (((mv tree-open input1) (abnf::parse-ichars "[" input))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "bracket-type: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-te input3) (parse-type-exp input2))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input)))
         ((mv trees-exts input4) (parse-*-ws-extent input3))
         ((mv tree-ws2 input5) (parse-ws input4))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input6) (abnf::parse-ichars "]" input5))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bracket-type")
           :branches (list (list tree-open tree-ws1 tree-te)
                           trees-exts
                           (list tree-ws2 tree-close)))
          input6)))

  (define parse-type-exp-paren ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 1)
    :short "Parse a @('type-exp-paren')."
    (b* (((mv tree input1) (parse-array-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp-paren")
               :branches (list (list tree))) input1))
         ((mv tree input1) (parse-arrow-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp-paren")
               :branches (list (list tree))) input1))
         ((mv tree input1) (parse-forall-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp-paren")
               :branches (list (list tree))) input1))
         ((mv tree input1) (parse-pi-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp-paren")
               :branches (list (list tree))) input1))
         ((mv tree input1) (parse-sigma-type input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp-paren")
               :branches (list (list tree))) input1)))
      (mv (reserrf "type-exp-paren: no match") (nat-list-fix input))))

  (define parse-array-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse an @('array-type')."
    (b* (((mv tree-a input1) (abnf::parse-ichars "A" input))
         ((when (reserrp tree-a))
          (mv (reserrf-push tree-a) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "array-type: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-te input3) (parse-type-exp input2))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-sh input5) (parse-shape input4))
         ((when (reserrp tree-sh))
          (mv (reserrf-push tree-sh) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "array-type")
           :branches (list (list tree-a tree-ws1 tree-te tree-ws2 tree-sh)))
          input5)))

  (define parse-arrow-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse an @('arrow-type')."
    (b* (((mv tree-kw input1) (parse-group-arrow input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "arrow-type: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((unless (mbt (< (len input4) (len input))))
          (mv (reserrf "arrow-type: impossible") (nat-list-fix input)))
         ((mv trees-tes input5) (parse-*-ws-type-exp input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "arrow-type: impossible") (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "type: impossible") (nat-list-fix input)))
         ((mv tree-te input9) (parse-type-exp input8))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "arrow-type")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-tes
                           (list tree-ws3 tree-close tree-ws4 tree-te)))
          input9)))

  (define parse-forall-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse a @('forall-type')."
    (b* (((mv tree-kw input1) (parse-group-forall input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "forall-type: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-tps input5) (parse-repetition-*-ws-type-param input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "type: impossible") (nat-list-fix input)))
         ((mv tree-te input9) (parse-type-exp input8))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "forall-type")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-tps
                           (list tree-ws3 tree-close tree-ws4 tree-te)))
          input9)))

  (define parse-pi-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse a @('pi-type')."
    (b* (((mv tree-kw input1) (parse-group-pi input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "pi-type: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-eps input5) (parse-repetition-*-ws-extent-param input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "type: impossible") (nat-list-fix input)))
         ((mv tree-te input9) (parse-type-exp input8))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "pi-type")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-eps
                           (list tree-ws3 tree-close tree-ws4 tree-te)))
          input9)))

  (define parse-sigma-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse a @('sigma-type')."
    (b* (((mv tree-kw input1) (parse-group-sigma input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "sigma-type: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-eps input5) (parse-repetition-*-ws-extent-param input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "type: impossible") (nat-list-fix input)))
         ((mv tree-te input9) (parse-type-exp input8))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "sigma-type")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-eps
                           (list tree-ws3 tree-close tree-ws4 tree-te)))
          input9)))

  (define parse-*-ws-type-exp ((input nat-listp))
    :returns (mv (trees abnf::tree-listp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 4)
    :short "Parse @('*( ws type-exp )')."
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-te input2) (parse-type-exp input1))
         ((when (reserrp tree-te)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-type-exp input2)))
      (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                 :branches (list (list tree-ws tree-te)))
                more)
          input3)))

  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))
  :verify-guards nil
  ///
  (defret-mutual len-of-parse-types
    (defret len-of-parse-type-exp-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-type-exp)
    (defret len-of-parse-type-exp-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-type-exp)
    (defret len-of-parse-bracket-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-bracket-type)
    (defret len-of-parse-bracket-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-bracket-type)
    (defret len-of-parse-type-exp-paren-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-type-exp-paren)
    (defret len-of-parse-type-exp-paren-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-type-exp-paren)
    (defret len-of-parse-array-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-array-type)
    (defret len-of-parse-array-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-array-type)
    (defret len-of-parse-arrow-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-arrow-type)
    (defret len-of-parse-arrow-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-arrow-type)
    (defret len-of-parse-forall-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-forall-type)
    (defret len-of-parse-forall-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-forall-type)
    (defret len-of-parse-pi-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-pi-type)
    (defret len-of-parse-pi-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-pi-type)
    (defret len-of-parse-sigma-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-sigma-type)
    (defret len-of-parse-sigma-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-sigma-type)
    (defret len-of-parse-*-ws-type-exp-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-*-ws-type-exp)
    :hints (("Goal" :in-theory
             (disable parse-type-exp parse-bracket-type parse-type-exp-paren
                      parse-array-type parse-arrow-type parse-forall-type
                      parse-pi-type parse-sigma-type parse-*-ws-type-exp))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-type-exp) clause)
                 '(:expand (parse-type-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-bracket-type) clause)
                 '(:expand (parse-bracket-type input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-type-exp-paren) clause)
                 '(:expand (parse-type-exp-paren input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-array-type) clause)
                 '(:expand (parse-array-type input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-arrow-type) clause)
                 '(:expand (parse-arrow-type input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-forall-type) clause)
                 '(:expand (parse-forall-type input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-pi-type) clause)
                 '(:expand (parse-pi-type input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-sigma-type) clause)
                 '(:expand (parse-sigma-type input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-type-exp) clause)
                 '(:expand (parse-*-ws-type-exp input)))))
  (verify-guards parse-type-exp
    :hints (("Goal" :in-theory
             (disable parse-type-exp parse-bracket-type parse-type-exp-paren
                      parse-array-type parse-arrow-type parse-forall-type
                      parse-pi-type parse-sigma-type parse-*-ws-type-exp)))))

;; ---- Patterns ----

(defparse-remora-rulename "pat")
(defparse-remora-group "( ws pat )")
(defparse-remora-*-group "( ws pat )")

;; ---- Non-recursive rules (bindings/params that don't reference exp) ----

;; Generate groups/reps now that type-exp and extent are defined.
(defparse-remora-group "( ws type-exp )")
(defparse-remora-*-group "( ws type-exp )")
(defparse-remora-group "( ws extent )")
(defparse-remora-*-group "( ws extent )")
(defparse-remora-option "[ ws \":\" ws type-exp ]")
;; *( extent-param ws ) for unbox-exp will be handled inside the
;; big defines block (unusual reversed pattern).

(defparse-remora-rulename "type-args")
(defparse-remora-rulename "idx-args")
(defparse-remora-rulename "type-params")
(defparse-remora-rulename "idx-params")
(defparse-remora-rulename "type-bind")
(defparse-remora-rulename "extent-bind")

;; Lambda keyword groups (just literals, no recursion).
(defparse-remora-group "( \"fn\" / %x03BB )")
(defparse-remora-group "( \"t\" %x03BB )")
(defparse-remora-group "( \"t-fn\" / ( \"t\" %x03BB ) )")
(defparse-remora-group "( \"i\" %x03BB )")
(defparse-remora-group "( \"i-fn\" / ( \"i\" %x03BB ) )")

;; ---- Expressions, atoms, and bindings ----
;; These are all mutually recursive (exp → atom → lambda → exp,
;; exp → let-exp → bind → val-bind → exp, etc.).
;; Hand-written using defines with two-nats-measure.
;;
;; Flag assignments (higher = called by lower with same input):
;; 30: *-ws-exp, 29: *-ws-atom, 28: *-ws-bind
;; 27: paren-exp-body, 26: app-exp
;; 25-19: at-app-exp, array-exp, frame-exp, tapp-exp, iapp-exp, unbox-exp, let-exp
;; 18: exp, 17: atom, 16: bracket-frame, 15: paren-exp
;; 14: atom-body, 13: bind-body, 12: bind
;; 11-7: val-bind, fun-bind, tfun-bind, ifun-bind, at-fun-bind
;; 6-3: lambda, type-lambda, index-lambda, box-expr

(defines parse-expressions
  :ruler-extenders :all

  (define parse-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 18)
    :short "Parse an @('exp')."
    (b* (((mv tree rest) (parse-atom input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "exp")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-bracket-frame input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "exp")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-identifier input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "exp")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-string-lit input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "exp")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-paren-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "exp")
               :branches (list (list tree))) rest)))
      (mv (reserrf "exp: no match") (nat-list-fix input))))

  (define parse-bracket-frame ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 16)
    :short "Parse a @('bracket-frame')."
    (b* (((mv tree-open input1) (abnf::parse-ichars "[" input))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "bracket-frame: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-e input3) (parse-exp input2))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input)))
         ((unless (mbt (< (len input3) (len input))))
          (mv (reserrf "impossible") (nat-list-fix input)))
         ((mv trees-more input4) (parse-*-ws-exp input3))
         ((mv tree-ws2 input5) (parse-ws input4))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input6) (abnf::parse-ichars "]" input5))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bracket-frame")
           :branches (list (list tree-open tree-ws1 tree-e)
                           trees-more
                           (list tree-ws2 tree-close)))
          input6)))

  (define parse-paren-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 15)
    :short "Parse a @('paren-exp')."
    (b* (((mv tree-open input1) (abnf::parse-ichars "(" input))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "paren-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-body input3) (parse-paren-exp-body input2))
         ((when (reserrp tree-body))
          (mv (reserrf-push tree-body) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars ")" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp")
           :branches (list (list tree-open tree-ws1 tree-body tree-ws2 tree-close)))
          input5)))

  (define parse-paren-exp-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 27)
    :short "Parse a @('paren-exp-body')."
    (b* (((mv tree rest) (parse-array-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-frame-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-tapp-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-iapp-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-unbox-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-let-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-at-app-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest))
         ;; app-exp must be last [SC3]
         ((mv tree rest) (parse-app-exp input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
               :branches (list (list tree))) rest)))
      (mv (reserrf "paren-exp-body: no match") (nat-list-fix input))))

  (define parse-app-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 26)
    :short "Parse an @('app-exp')."
    (b* (((mv tree-e input1) (parse-exp input))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "app-exp: impossible") (nat-list-fix input)))
         ((mv trees-more input2) (parse-*-ws-exp input1)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "app-exp")
           :branches (list (list tree-e) trees-more))
          input2)))

  (define parse-array-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 24)
    :short "Parse an @('array-exp')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "array" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "array-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-sl input3) (parse-shape-lit input2))
         ((when (reserrp tree-sl))
          (mv (reserrf-push tree-sl) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ;; 1*( ws atom ): need at least one
         ((mv tree-ws3 input5) (parse-ws input4))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((unless (mbt (< (len input5) (len input))))
          (mv (reserrf "array-exp: impossible") (nat-list-fix input)))
         ((mv tree-a1 input6) (parse-atom input5))
         ((when (reserrp tree-a1))
          (mv (reserrf "array-exp: need at least one atom") (nat-list-fix input)))
         ((unless (mbt (< (len input6) (len input))))
          (mv (reserrf "array-exp: impossible") (nat-list-fix input)))
         ((mv trees-more input7) (parse-*-ws-atom input6)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "array-exp")
           :branches (list (list tree-kw tree-ws1 tree-sl tree-ws2)
                           (cons (abnf::make-tree-nonleaf :rulename? nil
                                  :branches (list (list tree-ws3 tree-a1)))
                                 trees-more)))
          input7)))

  (define parse-frame-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 23)
    :short "Parse a @('frame-exp')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "frame" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "frame-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-sl input3) (parse-shape-lit input2))
         ((when (reserrp tree-sl))
          (mv (reserrf-push tree-sl) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ;; 1*( ws exp )
         ((mv tree-ws3 input5) (parse-ws input4))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((unless (mbt (< (len input5) (len input))))
          (mv (reserrf "frame-exp: impossible") (nat-list-fix input)))
         ((mv tree-e1 input6) (parse-exp input5))
         ((when (reserrp tree-e1))
          (mv (reserrf "frame-exp: need at least one exp") (nat-list-fix input)))
         ((unless (mbt (< (len input6) (len input))))
          (mv (reserrf "frame-exp: impossible") (nat-list-fix input)))
         ((mv trees-more input7) (parse-*-ws-exp input6)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "frame-exp")
           :branches (list (list tree-kw tree-ws1 tree-sl tree-ws2)
                           (cons (abnf::make-tree-nonleaf :rulename? nil
                                  :branches (list (list tree-ws3 tree-e1)))
                                 trees-more)))
          input7)))

  (define parse-tapp-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 22)
    :short "Parse a @('tapp-exp')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "t-app" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "tapp-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-e input3) (parse-exp input2))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input)))
         ((mv trees-tes input4) (parse-repetition-*-ws-type-exp input3)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "tapp-exp")
           :branches (list (list tree-kw tree-ws1 tree-e) trees-tes))
          input4)))

  (define parse-iapp-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 21)
    :short "Parse an @('iapp-exp')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "i-app" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "iapp-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-e input3) (parse-exp input2))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input)))
         ((mv trees-exts input4) (parse-repetition-*-ws-extent input3)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "iapp-exp")
           :branches (list (list tree-kw tree-ws1 tree-e) trees-exts))
          input4)))

  ;; [SC4] The Haskell parser guards each extent-param with
  ;; notFollowedBy ")".  Our parser uses greedy *( extent-param ws )
  ;; without lookahead, which produces the same result for well-formed input.
  (define parse-unbox-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 20)
    :short "Parse an @('unbox-exp')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "unbox" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "unbox-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ;; *( extent-param ws ) — inline the loop
         ((mv trees-eps input5) (parse-*-extent-param-ws input4))
         ((mv tree-id input6) (parse-identifier input5))
         ((when (reserrp tree-id))
          (mv (reserrf-push tree-id) (nat-list-fix input)))
         ((mv tree-ws3 input7) (parse-ws input6))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((unless (mbt (< (len input7) (len input))))
          (mv (reserrf "unbox-exp: impossible") (nat-list-fix input)))
         ((mv tree-e1 input8) (parse-exp input7))
         ((when (reserrp tree-e1))
          (mv (reserrf-push tree-e1) (nat-list-fix input)))
         ((mv tree-ws4 input9) (parse-ws input8))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((mv tree-close input10) (abnf::parse-ichars ")" input9))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws5 input11) (parse-ws input10))
         ((when (reserrp tree-ws5))
          (mv (reserrf-push tree-ws5) (nat-list-fix input)))
         ((unless (mbt (< (len input11) (len input))))
          (mv (reserrf "unbox-exp: impossible") (nat-list-fix input)))
         ((mv tree-e2 input12) (parse-exp input11))
         ((when (reserrp tree-e2))
          (mv (reserrf-push tree-e2) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "unbox-exp")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-eps
                           (list tree-id tree-ws3 tree-e1 tree-ws4
                                 tree-close tree-ws5 tree-e2)))
          input12)))

  (define parse-let-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 19)
    :short "Parse a @('let-exp')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "let" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "let-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((unless (mbt (< (len input4) (len input))))
          (mv (reserrf "impossible") (nat-list-fix input)))
         ((mv trees-binds input5) (parse-*-ws-bind input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "let-exp: impossible") (nat-list-fix input)))
         ((mv tree-e input9) (parse-exp input8))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "let-exp")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-binds
                           (list tree-ws3 tree-close tree-ws4 tree-e)))
          input9)))

  (define parse-at-app-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 25)
    :short "Parse an @('at-app-exp')."
    (b* (((mv tree-at input1) (abnf::parse-ichars "@" input))
         ((when (reserrp tree-at))
          (mv (reserrf-push tree-at) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "at-app-exp: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-e input3) (parse-exp input2))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-ta input5) (parse-type-args input4))
         ((when (reserrp tree-ta))
          (mv (reserrf-push tree-ta) (nat-list-fix input)))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-ia input7) (parse-idx-args input6))
         ((when (reserrp tree-ia))
          (mv (reserrf-push tree-ia) (nat-list-fix input)))
         ((unless (mbt (< (len input7) (len input))))
          (mv (reserrf "at-app-exp: impossible") (nat-list-fix input)))
         ((mv trees-more input8) (parse-*-ws-exp input7)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "at-app-exp")
           :branches (list (list tree-at tree-ws1 tree-e tree-ws2
                                 tree-ta tree-ws3 tree-ia)
                           trees-more))
          input8)))

  (define parse-atom ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 17)
    :short "Parse an @('atom')."
    (b* (((mv tree rest) (parse-base-val input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom")
               :branches (list (list tree))) rest))
         ((mv tree-open input1) (abnf::parse-ichars "(" input))
         ((when (reserrp tree-open))
          (mv (reserrf "atom: no match") (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "atom: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-body input3) (parse-atom-body input2))
         ((when (reserrp tree-body))
          (mv (reserrf-push tree-body) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars ")" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom")
           :branches (list (list tree-open tree-ws1 tree-body tree-ws2 tree-close)))
          input5)))

  (define parse-atom-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 14)
    :short "Parse an @('atom-body')."
    (b* (((mv tree rest) (parse-lambda input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-type-lambda input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-index-lambda input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-box-expr input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom-body")
               :branches (list (list tree))) rest)))
      (mv (reserrf "atom-body: no match") (nat-list-fix input))))

  (define parse-lambda ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 6)
    :short "Parse a @('lambda')."
    (b* (((mv tree-kw input1) (parse-group-fn input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "lambda: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-pats input5) (parse-repetition-*-ws-pat input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "lambda: impossible") (nat-list-fix input)))
         ((mv tree-e input9) (parse-exp input8))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "lambda")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-pats
                           (list tree-ws3 tree-close tree-ws4 tree-e)))
          input9)))

  (define parse-type-lambda ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 5)
    :short "Parse a @('type-lambda')."
    (b* (((mv tree-kw input1) (parse-group-t-fn input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "type-lambda: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-tps input5) (parse-repetition-*-ws-type-param input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "type-lambda: impossible") (nat-list-fix input)))
         ((mv tree-e input9) (parse-exp input8))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-lambda")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-tps
                           (list tree-ws3 tree-close tree-ws4 tree-e)))
          input9)))

  (define parse-index-lambda ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 4)
    :short "Parse an @('index-lambda')."
    (b* (((mv tree-kw input1) (parse-group-i-fn input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "index-lambda: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-eps input5) (parse-repetition-*-ws-extent-param input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "index-lambda: impossible") (nat-list-fix input)))
         ((mv tree-e input9) (parse-exp input8))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "index-lambda")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-eps
                           (list tree-ws3 tree-close tree-ws4 tree-e)))
          input9)))

  (define parse-box-expr ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 3)
    :short "Parse a @('box-expr')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "box" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "box-expr: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv trees-exts input5) (parse-repetition-*-ws-extent input4))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input7) (abnf::parse-ichars ")" input6))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input8) (len input))))
          (mv (reserrf "box-expr: impossible") (nat-list-fix input)))
         ((mv tree-e input9) (parse-exp input8))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input)))
         ((mv tree-ws5 input10) (parse-ws input9))
         ((when (reserrp tree-ws5))
          (mv (reserrf-push tree-ws5) (nat-list-fix input)))
         ((mv tree-te input11) (parse-type-exp input10))
         ((when (reserrp tree-te))
          (mv (reserrf-push tree-te) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "box-expr")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2)
                           trees-exts
                           (list tree-ws3 tree-close tree-ws4 tree-e
                                 tree-ws5 tree-te)))
          input11)))

  (define parse-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 12)
    :short "Parse a @('bind')."
    (b* (((mv tree-open input1) (abnf::parse-ichars "(" input))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "bind: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-body input3) (parse-bind-body input2))
         ((when (reserrp tree-body))
          (mv (reserrf-push tree-body) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars ")" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind")
           :branches (list (list tree-open tree-ws1 tree-body tree-ws2 tree-close)))
          input5)))

  (define parse-bind-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 13)
    :short "Parse a @('bind-body')."
    (b* (((mv tree rest) (parse-val-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-fun-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-tfun-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-ifun-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-type-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-extent-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest))
         ((mv tree rest) (parse-at-fun-bind input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
               :branches (list (list tree))) rest)))
      (mv (reserrf "bind-body: no match") (nat-list-fix input))))

  (define parse-val-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 11)
    :short "Parse a @('val-bind')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "val" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "val-bind: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ;; Try "val" ws identifier ws exp
         ((mv tree-id input3) (parse-identifier input2))
         ((when (reserrp tree-id))
          (mv (reserrf-push tree-id) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-e input5) (parse-exp input4))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "val-bind")
           :branches (list (list tree-kw tree-ws1 tree-id tree-ws2 tree-e)))
          input5)))

  (define parse-fun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 10)
    :short "Parse a @('fun-bind')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "fun" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "fun-bind: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open))
          (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-id input5) (parse-identifier input4))
         ((when (reserrp tree-id))
          (mv (reserrf-push tree-id) (nat-list-fix input)))
         ((mv trees-pats input6) (parse-repetition-*-ws-pat input5))
         ((mv tree-opt input7) (parse-optional-type-annotation input6))
         ((when (reserrp tree-opt))
          (mv (reserrf-push tree-opt) (nat-list-fix input)))
         ((mv tree-ws3 input8) (parse-ws input7))
         ((when (reserrp tree-ws3))
          (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-close input9) (abnf::parse-ichars ")" input8))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws4 input10) (parse-ws input9))
         ((when (reserrp tree-ws4))
          (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((unless (mbt (< (len input10) (len input))))
          (mv (reserrf "fun-bind: impossible") (nat-list-fix input)))
         ((mv tree-e input11) (parse-exp input10))
         ((when (reserrp tree-e))
          (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "fun-bind")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2 tree-id)
                           trees-pats
                           (list tree-opt tree-ws3 tree-close tree-ws4 tree-e)))
          input11)))

  (define parse-tfun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 9)
    :short "Parse a @('tfun-bind')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "t-fun" input))
         ((when (reserrp tree-kw))
          (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "tfun-bind: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1)) (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open)) (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2)) (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-id input5) (parse-identifier input4))
         ((when (reserrp tree-id)) (mv (reserrf-push tree-id) (nat-list-fix input)))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3)) (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-open2 input7) (abnf::parse-ichars "(" input6))
         ((when (reserrp tree-open2)) (mv (reserrf-push tree-open2) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4)) (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((mv trees-tps input9) (parse-repetition-*-ws-type-param input8))
         ((mv tree-ws5 input10) (parse-ws input9))
         ((when (reserrp tree-ws5)) (mv (reserrf-push tree-ws5) (nat-list-fix input)))
         ((mv tree-close2 input11) (abnf::parse-ichars ")" input10))
         ((when (reserrp tree-close2)) (mv (reserrf-push tree-close2) (nat-list-fix input)))
         ((mv tree-opt input12) (parse-optional-type-annotation input11))
         ((when (reserrp tree-opt))
          (mv (reserrf-push tree-opt) (nat-list-fix input)))
         ((mv tree-ws6 input13) (parse-ws input12))
         ((when (reserrp tree-ws6)) (mv (reserrf-push tree-ws6) (nat-list-fix input)))
         ((mv tree-close input14) (abnf::parse-ichars ")" input13))
         ((when (reserrp tree-close)) (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws7 input15) (parse-ws input14))
         ((when (reserrp tree-ws7)) (mv (reserrf-push tree-ws7) (nat-list-fix input)))
         ((unless (mbt (< (len input15) (len input))))
          (mv (reserrf "tfun-bind: impossible") (nat-list-fix input)))
         ((mv tree-e input16) (parse-exp input15))
         ((when (reserrp tree-e)) (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "tfun-bind")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2 tree-id
                                 tree-ws3 tree-open2 tree-ws4)
                           trees-tps
                           (list tree-ws5 tree-close2 tree-opt tree-ws6
                                 tree-close tree-ws7 tree-e)))
          input16)))

  (define parse-ifun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 8)
    :short "Parse an @('ifun-bind')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "i-fun" input))
         ((when (reserrp tree-kw)) (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "ifun-bind: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1)) (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open)) (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2)) (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-id input5) (parse-identifier input4))
         ((when (reserrp tree-id)) (mv (reserrf-push tree-id) (nat-list-fix input)))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3)) (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-open2 input7) (abnf::parse-ichars "(" input6))
         ((when (reserrp tree-open2)) (mv (reserrf-push tree-open2) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4)) (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((mv trees-eps input9) (parse-repetition-*-ws-extent-param input8))
         ((mv tree-ws5 input10) (parse-ws input9))
         ((when (reserrp tree-ws5)) (mv (reserrf-push tree-ws5) (nat-list-fix input)))
         ((mv tree-close2 input11) (abnf::parse-ichars ")" input10))
         ((when (reserrp tree-close2)) (mv (reserrf-push tree-close2) (nat-list-fix input)))
         ((mv tree-opt input12) (parse-optional-type-annotation input11))
         ((when (reserrp tree-opt))
          (mv (reserrf-push tree-opt) (nat-list-fix input)))
         ((mv tree-ws6 input13) (parse-ws input12))
         ((when (reserrp tree-ws6)) (mv (reserrf-push tree-ws6) (nat-list-fix input)))
         ((mv tree-close input14) (abnf::parse-ichars ")" input13))
         ((when (reserrp tree-close)) (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws7 input15) (parse-ws input14))
         ((when (reserrp tree-ws7)) (mv (reserrf-push tree-ws7) (nat-list-fix input)))
         ((unless (mbt (< (len input15) (len input))))
          (mv (reserrf "ifun-bind: impossible") (nat-list-fix input)))
         ((mv tree-e input16) (parse-exp input15))
         ((when (reserrp tree-e)) (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "ifun-bind")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2 tree-id
                                 tree-ws3 tree-open2 tree-ws4)
                           trees-eps
                           (list tree-ws5 tree-close2 tree-opt tree-ws6
                                 tree-close tree-ws7 tree-e)))
          input16)))

  (define parse-at-fun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 7)
    :short "Parse an @('at-fun-bind')."
    (b* (((mv tree-kw input1) (abnf::parse-ichars "fun" input))
         ((when (reserrp tree-kw)) (mv (reserrf-push tree-kw) (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv (reserrf "at-fun-bind: impossible") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1)) (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv tree-open input3) (abnf::parse-ichars "(" input2))
         ((when (reserrp tree-open)) (mv (reserrf-push tree-open) (nat-list-fix input)))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2)) (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-at input5) (abnf::parse-ichars "@" input4))
         ((when (reserrp tree-at)) (mv (reserrf-push tree-at) (nat-list-fix input)))
         ((mv tree-ws3 input6) (parse-ws input5))
         ((when (reserrp tree-ws3)) (mv (reserrf-push tree-ws3) (nat-list-fix input)))
         ((mv tree-id input7) (parse-identifier input6))
         ((when (reserrp tree-id)) (mv (reserrf-push tree-id) (nat-list-fix input)))
         ((mv tree-ws4 input8) (parse-ws input7))
         ((when (reserrp tree-ws4)) (mv (reserrf-push tree-ws4) (nat-list-fix input)))
         ((mv tree-tps input9) (parse-type-params input8))
         ((when (reserrp tree-tps)) (mv (reserrf-push tree-tps) (nat-list-fix input)))
         ((mv tree-ws5 input10) (parse-ws input9))
         ((when (reserrp tree-ws5)) (mv (reserrf-push tree-ws5) (nat-list-fix input)))
         ((mv tree-ips input11) (parse-idx-params input10))
         ((when (reserrp tree-ips)) (mv (reserrf-push tree-ips) (nat-list-fix input)))
         ((mv trees-pats input12) (parse-repetition-*-ws-pat input11))
         ((mv tree-ws6 input13) (parse-ws input12))
         ((when (reserrp tree-ws6)) (mv (reserrf-push tree-ws6) (nat-list-fix input)))
         ((mv tree-colon input14) (abnf::parse-ichars ":" input13))
         ((when (reserrp tree-colon)) (mv (reserrf-push tree-colon) (nat-list-fix input)))
         ((mv tree-ws7 input15) (parse-ws input14))
         ((when (reserrp tree-ws7)) (mv (reserrf-push tree-ws7) (nat-list-fix input)))
         ((mv tree-te input16) (parse-type-exp input15))
         ((when (reserrp tree-te)) (mv (reserrf-push tree-te) (nat-list-fix input)))
         ((mv tree-ws8 input17) (parse-ws input16))
         ((when (reserrp tree-ws8)) (mv (reserrf-push tree-ws8) (nat-list-fix input)))
         ((mv tree-close input18) (abnf::parse-ichars ")" input17))
         ((when (reserrp tree-close)) (mv (reserrf-push tree-close) (nat-list-fix input)))
         ((mv tree-ws9 input19) (parse-ws input18))
         ((when (reserrp tree-ws9)) (mv (reserrf-push tree-ws9) (nat-list-fix input)))
         ((unless (mbt (< (len input19) (len input))))
          (mv (reserrf "at-fun-bind: impossible") (nat-list-fix input)))
         ((mv tree-e input20) (parse-exp input19))
         ((when (reserrp tree-e)) (mv (reserrf-push tree-e) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "at-fun-bind")
           :branches (list (list tree-kw tree-ws1 tree-open tree-ws2
                                 tree-at tree-ws3 tree-id tree-ws4
                                 tree-tps tree-ws5 tree-ips)
                           trees-pats
                           (list tree-ws6 tree-colon tree-ws7 tree-te
                                 tree-ws8 tree-close tree-ws9 tree-e)))
          input20)))

  ;; Repetition helpers for the mutual recursion.

  (define parse-*-ws-exp ((input nat-listp))
    :returns (mv (trees abnf::tree-listp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 30)
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-e input2) (parse-exp input1))
         ((when (reserrp tree-e)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-exp input2)))
      (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                 :branches (list (list tree-ws tree-e)))
                more)
          input3)))

  (define parse-*-ws-atom ((input nat-listp))
    :returns (mv (trees abnf::tree-listp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 29)
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-a input2) (parse-atom input1))
         ((when (reserrp tree-a)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-atom input2)))
      (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                 :branches (list (list tree-ws tree-a)))
                more)
          input3)))

  (define parse-*-ws-bind ((input nat-listp))
    :returns (mv (trees abnf::tree-listp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 28)
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-b input2) (parse-bind input1))
         ((when (reserrp tree-b)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-bind input2)))
      (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                 :branches (list (list tree-ws tree-b)))
                more)
          input3)))

  (define parse-*-extent-param-ws ((input nat-listp))
    :returns (mv (trees abnf::tree-listp) (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    :short "Parse @('*( extent-param ws )')."
    (b* (((mv tree-ep input1) (parse-extent-param input))
         ((when (reserrp tree-ep)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv tree-ws input2) (parse-ws input1))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-extent-param-ws input2)))
      (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                 :branches (list (list tree-ep tree-ws)))
                more)
          input3)))

  :prepwork ((local (defthm nfix-of-len
                      (equal (nfix (len x)) (len x))
                      :hints (("Goal" :in-theory (enable nfix)))))
             (defun parse-expressions-expand-hints (id clause world)
               (declare (ignore id world))
               (cond
                ((acl2::occur-lst '(acl2::flag-is 'parse-exp) clause)
                 '(:expand (parse-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-bracket-frame) clause)
                 '(:expand (parse-bracket-frame input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-paren-exp) clause)
                 '(:expand (parse-paren-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-paren-exp-body) clause)
                 '(:expand (parse-paren-exp-body input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-app-exp) clause)
                 '(:expand (parse-app-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-array-exp) clause)
                 '(:expand (parse-array-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-frame-exp) clause)
                 '(:expand (parse-frame-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-tapp-exp) clause)
                 '(:expand (parse-tapp-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-iapp-exp) clause)
                 '(:expand (parse-iapp-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-unbox-exp) clause)
                 '(:expand (parse-unbox-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-let-exp) clause)
                 '(:expand (parse-let-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-at-app-exp) clause)
                 '(:expand (parse-at-app-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-atom) clause)
                 '(:expand (parse-atom input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-atom-body) clause)
                 '(:expand (parse-atom-body input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-lambda) clause)
                 '(:expand (parse-lambda input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-type-lambda) clause)
                 '(:expand (parse-type-lambda input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-index-lambda) clause)
                 '(:expand (parse-index-lambda input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-box-expr) clause)
                 '(:expand (parse-box-expr input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-bind) clause)
                 '(:expand (parse-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-bind-body) clause)
                 '(:expand (parse-bind-body input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-val-bind) clause)
                 '(:expand (parse-val-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-fun-bind) clause)
                 '(:expand (parse-fun-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-tfun-bind) clause)
                 '(:expand (parse-tfun-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-ifun-bind) clause)
                 '(:expand (parse-ifun-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-at-fun-bind) clause)
                 '(:expand (parse-at-fun-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-*-ws-exp) clause)
                 '(:expand (parse-*-ws-exp input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-*-ws-atom) clause)
                 '(:expand (parse-*-ws-atom input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-*-ws-bind) clause)
                 '(:expand (parse-*-ws-bind input)))
                ((acl2::occur-lst '(acl2::flag-is 'parse-*-extent-param-ws) clause)
                 '(:expand (parse-*-extent-param-ws input))))))

  :returns-hints
  (("Goal"
    :in-theory
    (e/d (abnf::treep-when-tree-resultp-and-not-reserrp
          abnf::tree-listp-when-tree-list-resultp-and-not-reserrp)
         (parse-exp parse-bracket-frame parse-paren-exp
          parse-paren-exp-body parse-app-exp parse-array-exp
          parse-frame-exp parse-tapp-exp parse-iapp-exp
          parse-unbox-exp parse-let-exp parse-at-app-exp
          parse-atom parse-atom-body parse-lambda
          parse-type-lambda parse-index-lambda parse-box-expr
          parse-bind parse-bind-body parse-val-bind
          parse-fun-bind parse-tfun-bind parse-ifun-bind
          parse-at-fun-bind parse-*-ws-exp parse-*-ws-atom
          parse-*-ws-bind parse-*-extent-param-ws)))
   parse-expressions-expand-hints)

  :verify-guards nil

  ///
  (defret-mutual len-of-parse-expressions
    (defret len-of-parse-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-exp)
    (defret len-of-parse-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-exp)
    (defret len-of-parse-bracket-frame-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-bracket-frame)
    (defret len-of-parse-bracket-frame-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-bracket-frame)
    (defret len-of-parse-paren-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-paren-exp)
    (defret len-of-parse-paren-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-paren-exp)
    (defret len-of-parse-paren-exp-body-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-paren-exp-body)
    (defret len-of-parse-paren-exp-body-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-paren-exp-body)
    (defret len-of-parse-app-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-app-exp)
    (defret len-of-parse-app-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-app-exp)
    (defret len-of-parse-array-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-array-exp)
    (defret len-of-parse-array-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-array-exp)
    (defret len-of-parse-frame-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-frame-exp)
    (defret len-of-parse-frame-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-frame-exp)
    (defret len-of-parse-tapp-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-tapp-exp)
    (defret len-of-parse-tapp-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-tapp-exp)
    (defret len-of-parse-iapp-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-iapp-exp)
    (defret len-of-parse-iapp-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-iapp-exp)
    (defret len-of-parse-unbox-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-unbox-exp)
    (defret len-of-parse-unbox-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-unbox-exp)
    (defret len-of-parse-let-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-let-exp)
    (defret len-of-parse-let-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-let-exp)
    (defret len-of-parse-at-app-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-at-app-exp)
    (defret len-of-parse-at-app-exp-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-at-app-exp)
    (defret len-of-parse-atom-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-atom)
    (defret len-of-parse-atom-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-atom)
    (defret len-of-parse-atom-body-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-atom-body)
    (defret len-of-parse-atom-body-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-atom-body)
    (defret len-of-parse-lambda-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-lambda)
    (defret len-of-parse-lambda-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-lambda)
    (defret len-of-parse-type-lambda-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-type-lambda)
    (defret len-of-parse-type-lambda-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-type-lambda)
    (defret len-of-parse-index-lambda-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-index-lambda)
    (defret len-of-parse-index-lambda-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-index-lambda)
    (defret len-of-parse-box-expr-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-box-expr)
    (defret len-of-parse-box-expr-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-box-expr)
    (defret len-of-parse-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-bind)
    (defret len-of-parse-bind-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-bind)
    (defret len-of-parse-bind-body-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-bind-body)
    (defret len-of-parse-bind-body-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-bind-body)
    (defret len-of-parse-val-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-val-bind)
    (defret len-of-parse-val-bind-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-val-bind)
    (defret len-of-parse-fun-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-fun-bind)
    (defret len-of-parse-fun-bind-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-fun-bind)
    (defret len-of-parse-tfun-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-tfun-bind)
    (defret len-of-parse-tfun-bind-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-tfun-bind)
    (defret len-of-parse-ifun-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-ifun-bind)
    (defret len-of-parse-ifun-bind-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-ifun-bind)
    (defret len-of-parse-at-fun-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-at-fun-bind)
    (defret len-of-parse-at-fun-bind-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-at-fun-bind)
    (defret len-of-parse-*-ws-exp-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-ws-exp)
    (defret len-of-parse-*-ws-atom-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-ws-atom)
    (defret len-of-parse-*-ws-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-ws-bind)
    (defret len-of-parse-*-extent-param-ws-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-extent-param-ws)
    :hints (("Goal" :in-theory
             (disable parse-exp parse-bracket-frame parse-paren-exp
                      parse-paren-exp-body parse-app-exp parse-array-exp
                      parse-frame-exp parse-tapp-exp parse-iapp-exp
                      parse-unbox-exp parse-let-exp parse-at-app-exp
                      parse-atom parse-atom-body parse-lambda
                      parse-type-lambda parse-index-lambda parse-box-expr
                      parse-bind parse-bind-body parse-val-bind
                      parse-fun-bind parse-tfun-bind parse-ifun-bind
                      parse-at-fun-bind parse-*-ws-exp parse-*-ws-atom
                      parse-*-ws-bind parse-*-extent-param-ws))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-exp) clause)
                 '(:expand (parse-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-bracket-frame) clause)
                 '(:expand (parse-bracket-frame input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-paren-exp) clause)
                 '(:expand (parse-paren-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-paren-exp-body) clause)
                 '(:expand (parse-paren-exp-body input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-app-exp) clause)
                 '(:expand (parse-app-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-array-exp) clause)
                 '(:expand (parse-array-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-frame-exp) clause)
                 '(:expand (parse-frame-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-tapp-exp) clause)
                 '(:expand (parse-tapp-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-iapp-exp) clause)
                 '(:expand (parse-iapp-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-unbox-exp) clause)
                 '(:expand (parse-unbox-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-let-exp) clause)
                 '(:expand (parse-let-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-at-app-exp) clause)
                 '(:expand (parse-at-app-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-atom) clause)
                 '(:expand (parse-atom input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-atom-body) clause)
                 '(:expand (parse-atom-body input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-lambda) clause)
                 '(:expand (parse-lambda input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-type-lambda) clause)
                 '(:expand (parse-type-lambda input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-index-lambda) clause)
                 '(:expand (parse-index-lambda input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-box-expr) clause)
                 '(:expand (parse-box-expr input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-bind) clause)
                 '(:expand (parse-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-bind-body) clause)
                 '(:expand (parse-bind-body input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-val-bind) clause)
                 '(:expand (parse-val-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-fun-bind) clause)
                 '(:expand (parse-fun-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-tfun-bind) clause)
                 '(:expand (parse-tfun-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-ifun-bind) clause)
                 '(:expand (parse-ifun-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-at-fun-bind) clause)
                 '(:expand (parse-at-fun-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-exp) clause)
                 '(:expand (parse-*-ws-exp input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-atom) clause)
                 '(:expand (parse-*-ws-atom input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-bind) clause)
                 '(:expand (parse-*-ws-bind input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-extent-param-ws) clause)
                 '(:expand (parse-*-extent-param-ws input)))))
  (verify-guards parse-exp
    :hints (("Goal"
             :do-not-induct t
             :in-theory
             (e/d (abnf::treep-when-tree-resultp-and-not-reserrp
                   abnf::tree-listp-when-tree-list-resultp-and-not-reserrp)
                  (parse-exp parse-bracket-frame parse-paren-exp
                   parse-paren-exp-body parse-app-exp parse-array-exp
                   parse-frame-exp parse-tapp-exp parse-iapp-exp
                   parse-unbox-exp parse-let-exp parse-at-app-exp
                   parse-atom parse-atom-body parse-lambda
                   parse-type-lambda parse-index-lambda parse-box-expr
                   parse-bind parse-bind-body parse-val-bind
                   parse-fun-bind parse-tfun-bind parse-ifun-bind
                   parse-at-fun-bind parse-*-ws-exp parse-*-ws-atom
                   parse-*-ws-bind parse-*-extent-param-ws))))))

;; ---- Top-level ----

(define parse-program ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
  :short "Parse a @('program')."
  (b* (((mv tree-ws1 input1) (parse-ws input))
       ((when (reserrp tree-ws1))
        (mv (reserrf-push tree-ws1) (nat-list-fix input)))
       ((mv tree-e input2) (parse-exp input1))
       ((when (reserrp tree-e))
        (mv (reserrf-push tree-e) (nat-list-fix input)))
       ((mv tree-ws2 input3) (parse-ws input2))
       ((when (reserrp tree-ws2))
        (mv (reserrf-push tree-ws2) (nat-list-fix input))))
    (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "program")
         :branches (list (list tree-ws1 tree-e tree-ws2)))
        input3))
  :hooks (:fix)
  ///
  (defret len-of-parse-program-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear))

