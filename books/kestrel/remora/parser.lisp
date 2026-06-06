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
(include-book "identifier-syntax")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (concrete-syntax parsing-and-printing)
  :short "An executable parser for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "This source file defines a parser for the Remora grammar.
     It operates on lists of natural numbers representing
     Unicode code point integers (excluding surrogates),
     and produces @(tsee concrete-syntax-trees).")
   (xdoc::p
    "The source file is organized into three sections:")
   (xdoc::ol
    (xdoc::li
     "Generation of specialized generator macros for the parser.")
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

(local (in-theory (disable nfix)))

;; Since nfix is disabled globally, provide a rewrite rule so that
;; (nfix (len x)) simplifies to (len x).  This is needed for the
;; O<-OF-TWO-NATS-MEASURE rewrite rule to interact with linear
;; arithmetic on len in the measure proofs of mutually recursive parsers.
(local (defthm nfix-of-len
  (equal (nfix (len x)) (len x))
  :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; b* binders for parsing functions.
;; Adapted from the Leo/PFCS parsers for our 2-value (tree, rest-input)
;; signature.

(def-b*-binder pok
  :short "Check and propagate error results of parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Binds the result of a 2-value parsing function @('(mv tree rest-input)').
     If the result is a @(tsee reserrp), propagates the error immediately.
     Otherwise, binds the tree to the given variable and shadows @('input')
     with the remaining input."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* (((mv pok-fresh-var input)
         ,(car acl2::forms))
        ((when (reserrp pok-fresh-var))
         (mv (reserrf-push pok-fresh-var) input))
        (,(car args) pok-fresh-var))
     ,acl2::rest-expr))

(def-b*-binder pok<
  :short "Like @(tsee patbind-pok) but also ensures strict input decrease."
  :long
  (xdoc::topstring
   (xdoc::p
    "Like @(tsee patbind-pok), but also checks via @(tsee mbt) that
     the remaining input is strictly shorter than @('input') before
     the call.  Use this for any parse that is guaranteed to consume
     at least one character on success (keywords, delimiters,
     identifiers, expressions, etc.).  Use @(tsee patbind-pok) instead
     for parses that may consume zero characters (@('parse-ws'),
     optional forms)."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* (((mv pok-fresh-var input1)
         ,(car acl2::forms))
        ((when (reserrp pok-fresh-var))
         (mv (reserrf-push pok-fresh-var) input1))
        ((unless (mbt (< (len input1) (len input))))
         (mv (reserrf :impossible) input1))
        (input input1)
        (,(car args) pok-fresh-var))
     ,acl2::rest-expr))

(def-b*-binder try
  :short "Try a parsing alternative; return on success, continue on error."
  :long
  (xdoc::topstring
   (xdoc::p
    "Inverse of @(tsee patbind-pok).  Binds the result of a 2-value
     parsing function @('(mv tree rest-input)').  If the result is
     @em{not} a @(tsee reserrp), returns immediately with the tree and
     rest-input (exiting the enclosing @(tsee b*)).  If the result is
     an error, continues to the next binding (trying the next
     alternative).  Use this inside an inner @('b*') that tries
     multiple grammar alternatives for the same rule."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 2))))
  :body
  `(b* (((mv ,(car args) ,(cadr args)) ,(car acl2::forms))
        ((unless (reserrp ,(car args)))
         (mv ,(car args) ,(cadr args))))
     ,acl2::rest-expr))

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
    "( ws ispace )" group-ws-ispace
    "( ws atom )" group-ws-atom
    "( ws pat )" group-ws-pat
    "( ws bind )" group-ws-bind
    "( ws dim )" group-ws-dim
    "( ws shape )" group-ws-shape
    "( ws type-var )" group-ws-type-var
    "( ws ispace-var )" group-ws-ispace-var
    "( ws decimal )" group-ws-decimal

    ;; ---- Groups for keyword/operator alternatives ----
    ;; Keyword string-literals use %s (case-sensitive) per the grammar's
    ;; `keyword` rule.  "->" has no letters so %s would be redundant.
    ;; arrow-type
    "( \"->\" / %x2192 )" group-arrow
    ;; forall-type
    "( %s\"Forall\" / %x2200 )" group-forall
    ;; pi-type
    "( %s\"Pi\" / %x03A0 )" group-pi
    ;; sigma-type
    "( %s\"Sigma\" / %x03A3 )" group-sigma
    ;; lambda
    "( %s\"fn\" / %x03BB )" group-fn
    ;; type-lambda inner group
    "( %s\"t\" %x03BB )" group-t-lambda
    ;; type-lambda
    "( %s\"t-fn\" / ( %s\"t\" %x03BB ) )" group-t-fn
    ;; ispace-lambda inner group
    "( %s\"i\" %x03BB )" group-i-lambda
    ;; ispace-lambda
    "( %s\"i-fn\" / ( %s\"i\" %x03BB ) )" group-i-fn)

  (defparse-remora-option-table

    ;; num-val: [ "+" / "-" ]
    ;; also used in exponent
    "[ \"+\" / \"-\" ]" optional-sign

    ;; float-lit: [ exponent ]
    "[ exponent ]" optional-exponent

    ;; fun-sig, tfun-sig, ifun-sig: optional return-type annotation
    "[ ws colon-type ]" optional-type-annotation)

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

    ;; string-lit: *string-elem (= *( char-lit / empty-escape ))
    "*string-elem" repetition-*-string-elem

    ;; ---- Repetitions for ws-separated lists ----
    "*( ws exp )" repetition-*-ws-exp
    "*( ws type-exp )" repetition-*-ws-type-exp
    "*( ws ispace )" repetition-*-ws-ispace
    "*( ws atom )" repetition-*-ws-atom
    "*( ws pat )" repetition-*-ws-pat
    "*( ws bind )" repetition-*-ws-bind
    "*( ws dim )" repetition-*-ws-dim
    "*( ws shape )" repetition-*-ws-shape
    "*( ws type-var )" repetition-*-ws-type-var
    "*( ws ispace-var )" repetition-*-ws-ispace-var
    "*( ws decimal )" repetition-*-ws-decimal

    ;; unbox-exp: *( ispace-var ws )
    "*( ispace-var ws )" repetition-*-ispace-var-ws))

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

;; non-ascii, id-start, id-continue have their predicates factored
;; into identifier-syntax.lisp (xdoc topic identifier-syntax); the
;; per-character parsers below consult those predicates.  Hand-written
;; rather than auto-generated because each rule has 9-13 range
;; alternatives, which cause combinatorial proof blowup when generated
;; by ABNF tooling.

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

(define char-escape-codepoint-p ((nat natp))
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
       ((unless (char-escape-codepoint-p nat))
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
  (b* (((pok inner-tree)
        (b* (((try tree rest) (abnf::parse-ichars "NUL" input))
             ((try tree rest) (abnf::parse-ichars "SOH" input))
             ((try tree rest) (abnf::parse-ichars "STX" input))
             ((try tree rest) (abnf::parse-ichars "ETX" input))
             ((try tree rest) (abnf::parse-ichars "EOT" input))
             ((try tree rest) (abnf::parse-ichars "ENQ" input))
             ((try tree rest) (abnf::parse-ichars "ACK" input))
             ((try tree rest) (abnf::parse-ichars "BEL" input))
             ((try tree rest) (abnf::parse-ichars "BS" input))
             ((try tree rest) (abnf::parse-ichars "HT" input))
             ((try tree rest) (abnf::parse-ichars "LF" input))
             ((try tree rest) (abnf::parse-ichars "VT" input))
             ((try tree rest) (abnf::parse-ichars "FF" input))
             ((try tree rest) (abnf::parse-ichars "CR" input))
             ;; SOH already tried; SO is safe now
             ((try tree rest) (abnf::parse-ichars "SO" input))
             ((try tree rest) (abnf::parse-ichars "SI" input))
             ((try tree rest) (abnf::parse-ichars "DLE" input))
             ((try tree rest) (abnf::parse-ichars "DC1" input))
             ((try tree rest) (abnf::parse-ichars "DC2" input))
             ((try tree rest) (abnf::parse-ichars "DC3" input))
             ((try tree rest) (abnf::parse-ichars "DC4" input))
             ((try tree rest) (abnf::parse-ichars "NAK" input))
             ((try tree rest) (abnf::parse-ichars "SYN" input))
             ((try tree rest) (abnf::parse-ichars "ETB" input))
             ((try tree rest) (abnf::parse-ichars "CAN" input))
             ;; ESC before EM (longer prefix first)
             ((try tree rest) (abnf::parse-ichars "ESC" input))
             ((try tree rest) (abnf::parse-ichars "EM" input))
             ((try tree rest) (abnf::parse-ichars "SUB" input))
             ((try tree rest) (abnf::parse-ichars "FS" input))
             ((try tree rest) (abnf::parse-ichars "GS" input))
             ((try tree rest) (abnf::parse-ichars "RS" input))
             ((try tree rest) (abnf::parse-ichars "US" input))
             ((try tree rest) (abnf::parse-ichars "SP" input)))
          (abnf::parse-ichars "DEL" input))))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "ascii-escape")
         :branches (list (list inner-tree)))
        input))
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
  (b* (((pok< tree-caret) (abnf::parse-ichars "^" input))
       ((pok< tree-ctrl) (abnf::parse-range #x40 #x5F input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "caret-escape")
         :branches (list (list tree-caret) (list tree-ctrl)))
        input))
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

;; char-lit has 4 large ranges + escape; hand-written.

(define char-lit-nonescape-p ((nat natp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a non-escape char-lit."
  (b* ((nat (nfix nat)))
    (or (and (<= #x00 nat) (<= nat #x21))
        (and (<= #x23 nat) (<= nat #x5B))
        (and (<= #x5D nat) (<= nat #xD7FF))
        (and (<= #xE000 nat) (<= nat #x10FFFF))))
  :hooks (:fix))

(define parse-char-lit ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a @('char-lit')."
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "char-lit: end of input") nil))
       (nat (car input))
       ;; Non-escape case: any char except " (%x22) and \ (%x5C)
       ((when (char-lit-nonescape-p nat))
        (mv (abnf::make-tree-nonleaf
             :rulename? (abnf::rulename "char-lit")
             :branches (list (list (abnf::tree-leafterm (list nat)))))
            (cdr input)))
       ;; Escape case: "\" escape-char
       ((unless (eql nat #x5C))
        (mv (reserrf "char-lit: invalid char") input))
       (input (cdr input))
       ((pok< esc-tree) (parse-escape-char input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "char-lit")
         :branches (list (list (abnf::tree-leafterm (list #x5C)))
                         (list esc-tree)))
        input))
  :hooks (:fix)
  ///
  (defret len-of-parse-char-lit-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)
  (defret len-of-parse-char-lit-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;; string-lit = DQUOTE *string-elem DQUOTE
;; string-elem = char-lit / empty-escape
;; empty-escape = "\&"
(defparse-remora-rulename "empty-escape")
(defparse-remora-rulename "string-elem")
(defparse-remora-*-rulename "string-elem")
(defparse-remora-rulename "string-lit")

;; ---- Type and ispace parameters ----

(defparse-remora-rulename "atom-type-var")
(defparse-remora-rulename "array-type-var")
(defparse-remora-rulename "type-var")
(defparse-remora-rulename "dim-ispace-var")
(defparse-remora-rulename "shape-ispace-var")
(defparse-remora-rulename "ispace-var")

;; ---- Dimensions, shapes, ispaces ----
;; These rules are mutually recursive, so they must be hand-written
;; using defines. Two clusters:
;;   1. dim / dim-arith (dim-arith calls *dim)
;;   2. shape / shape-paren / ispace (shape ↔ ispace, shape ↔ shape-paren)

;; shape-lit is independent; auto-generate it first.
(defparse-remora-group "( ws decimal )")
(defparse-remora-*-group "( ws decimal )")
(defparse-remora-rulename "shape-lit")

;; Cluster 1: dim / dim-arith
;; dim = "$" identifier / decimal / "(" ws dim-arith ws ")"
;; dim-arith = "+" *( ws dim ) / "*" *( ws dim ) / "-" *( ws dim )

(defines parse-dim+dim-arith

  ;; Lexicographic measure: (len input, flag).
  ;; Flag 2 for parse-*-ws-dim, 1 for parse-dim, 0 for parse-dim-arith.
  ;; When parse-*-ws-dim calls parse-dim on post-ws input (same len),
  ;; the flag decreases from 2 to 1.
  (define parse-dim ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Parse a @('dim')."
    (b* (;; Try "$" identifier
         ((mv tree-dollar rest) (abnf::parse-ichars "$" input))
         ((when (not (reserrp tree-dollar)))
          (b* (((pok< tree-id) (parse-identifier rest)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "dim")
                 :branches (list (list tree-dollar) (list tree-id)))
                input)))
         ;; Try decimal
         ((mv tree-dec rest) (parse-decimal input))
         ((when (not (reserrp tree-dec)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "dim")
               :branches (list (list tree-dec)))
              rest))
         ;; Try "(" ws dim-arith ws ")"
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-da) (parse-dim-arith input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "dim")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-da)
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 1))

  (define parse-dim-arith ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Parse a @('dim-arith')."
    (b* (;; Try each operator: +, *, -
         ((pok< tree-op)
          (b* (((mv tree rest) (abnf::parse-ichars "+" input))
               ((unless (reserrp tree)) (mv tree rest))
               ((mv tree rest) (abnf::parse-ichars "*" input))
               ((unless (reserrp tree)) (mv tree rest))
               ((mv tree rest) (abnf::parse-ichars "-" input))
               ((unless (reserrp tree)) (mv tree rest)))
            (mv (reserrf "dim-arith: expected +, *, or -")
                (nat-list-fix input))))
         ;; Parse *( ws dim )
         ((mv trees-dims input) (parse-*-ws-dim input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "dim-arith")
           :branches (list (list tree-op) trees-dims))
          input))
    :measure (two-nats-measure (len input) 0))

  (define parse-*-ws-dim ((input nat-listp))
    :returns (mv (trees abnf::tree-listp)
                 (rest-input nat-listp))
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
                 :branches (list (list tree-ws) (list tree-dim)))
                more-trees)
          input3))
    :measure (two-nats-measure (len input) 2))

  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))

  :verify-guards nil   ; done later

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

;; Cluster 2: shape / shape-paren / ispace
;; shape = "@" identifier / dim / "(" ws shape-paren ws ")" / "[" ws *( ws ispace ) ws "]"
;; shape-paren = "dims" *( ws dim ) / "++" *( ws shape )
;; ispace = dim / shape

(defines parse-shape+ispace

  (define parse-shape ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Parse a @('shape')."
    (b* (;; Try "@" identifier
         ((mv tree-at input1) (abnf::parse-ichars "@" input))
         ((when (not (reserrp tree-at)))
          (b* (((mv tree-id input2) (parse-identifier input1))
               ((when (reserrp tree-id))
                (mv (reserrf-push tree-id) (nat-list-fix input))))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "shape")
                 :branches (list (list tree-at) (list tree-id)))
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
                 :branches (list (list tree-open)
                                 (list tree-ws1)
                                 (list tree-sp)
                                 (list tree-ws2)
                                 (list tree-close)))
                input5)))
         ;; Try "[" ws *( ws ispace ) ws "]"
         ((mv tree-open input1) (abnf::parse-ichars "[" input))
         ((when (reserrp tree-open))
          (mv (reserrf "shape: no match") (nat-list-fix input)))
         ((mv tree-ws1 input2) (parse-ws input1))
         ((when (reserrp tree-ws1))
          (mv (reserrf-push tree-ws1) (nat-list-fix input)))
         ((mv trees-exts input3) (parse-*-ws-ispace input2))
         ((mv tree-ws2 input4) (parse-ws input3))
         ((when (reserrp tree-ws2))
          (mv (reserrf-push tree-ws2) (nat-list-fix input)))
         ((mv tree-close input5) (abnf::parse-ichars "]" input4))
         ((when (reserrp tree-close))
          (mv (reserrf-push tree-close) (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "shape")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           trees-exts
                           (list tree-ws2)
                           (list tree-close)))
          input5))
    :measure (two-nats-measure (len input) 1))

  (define parse-shape-paren ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Parse a @('shape-paren')."
    (b* (;; Try "dims" *( ws dim )
         ((mv tree-kw input1) (abnf::parse-schars "dims" input))
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
          input2))
    :measure (two-nats-measure (len input) 0))

  (define parse-ispace ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :short "Parse an @('ispace')."
    ;; [SC5]: a shape under an ispace must not be a shape->dim.  We
    ;; satisfy this by trying dim first: if parse-dim succeeds we take
    ;; the dim branch directly, and if it fails then parse-shape's own
    ;; dim alternative (which just calls parse-dim) will also fail on
    ;; the same input, so parse-shape can only succeed via one of its
    ;; non-dim alternatives.
    (b* (;; Try dim first (per grammar ordering; also enforces [SC5])
         ((mv tree-dim input1) (parse-dim input))
         ((when (not (reserrp tree-dim)))
          (mv (abnf::make-tree-nonleaf
               :rulename? (abnf::rulename "ispace")
               :branches (list (list tree-dim)))
              input1))
         ;; Try shape
         ((mv tree-shape input1) (parse-shape input))
         ((when (reserrp tree-shape))
          (mv (reserrf "ispace: no match") (nat-list-fix input))))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "ispace")
           :branches (list (list tree-shape)))
          input1))
    :measure (two-nats-measure (len input) 2))

  (define parse-*-ws-shape ((input nat-listp))
    :returns (mv (trees abnf::tree-listp)
                 (rest-input nat-listp))
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-shape input2) (parse-shape input1))
         ((when (reserrp tree-shape)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-shape input2)))
      (mv (cons (abnf::make-tree-nonleaf
                 :rulename? nil
                 :branches (list (list tree-ws) (list tree-shape)))
                more)
          input3))
    :measure (two-nats-measure (len input) 4))

  (define parse-*-ws-ispace ((input nat-listp))
    :returns (mv (trees abnf::tree-listp)
                 (rest-input nat-listp))
    (b* (((mv tree-ws input1) (parse-ws input))
         ((when (reserrp tree-ws)) (mv nil (nat-list-fix input)))
         ((mv tree-ext input2) (parse-ispace input1))
         ((when (reserrp tree-ext)) (mv nil (nat-list-fix input)))
         ((unless (mbt (< (len input2) (len input))))
          (mv nil (nat-list-fix input)))
         ((mv more input3) (parse-*-ws-ispace input2)))
      (mv (cons (abnf::make-tree-nonleaf
                 :rulename? nil
                 :branches (list (list tree-ws) (list tree-ext)))
                more)
          input3))
    :measure (two-nats-measure (len input) 3))

  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))
  :ruler-extenders :all

  :verify-guards nil   ; done later

  ///

  (defret-mutual len-of-parse-shape+ispace
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
    (defret len-of-parse-ispace-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-ispace)
    (defret len-of-parse-ispace-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-ispace)
    (defret len-of-parse-*-ws-shape-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-*-ws-shape)
    (defret len-of-parse-*-ws-ispace-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear :fn parse-*-ws-ispace)
    :hints (("Goal" :in-theory
             (disable parse-shape parse-shape-paren parse-ispace
                      parse-*-ws-shape parse-*-ws-ispace))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-shape) clause)
                 '(:expand (parse-shape input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-shape-paren) clause)
                 '(:expand (parse-shape-paren input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-ispace) clause)
                 '(:expand (parse-ispace input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-shape) clause)
                 '(:expand (parse-*-ws-shape input)))
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ws-ispace) clause)
                 '(:expand (parse-*-ws-ispace input)))))

  (verify-guards parse-shape
    :hints (("Goal" :in-theory (disable parse-shape parse-shape-paren
                                        parse-ispace parse-*-ws-shape
                                        parse-*-ws-ispace)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ---- Types ----

;; Non-recursive type helpers (already-admitted dependencies only).
(defparse-remora-rulename "base-type")

;; Groups for keyword/operator alternatives in type rules.
(defparse-remora-group "( \"->\" / %x2192 )")
(defparse-remora-group "( %s\"Forall\" / %x2200 )")
(defparse-remora-group "( %s\"Pi\" / %x03A0 )")
(defparse-remora-group "( %s\"Sigma\" / %x03A3 )")

;; Repetitions for non-recursive params (type-var, ispace-var already defined).
(defparse-remora-group "( ws type-var )")
(defparse-remora-*-group "( ws type-var )")
(defparse-remora-group "( ws ispace-var )")
(defparse-remora-*-group "( ws ispace-var )")

;; Type rules are self-recursive: type-exp → bracket-type/array-type/etc → type-exp.
;; Hand-written using defines.

(defines parse-types

  (define parse-type-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('type-exp')."
    (b* (;; Try non-recursive alternatives
         ((mv tree input1)
          (b* (((try tree input1) (parse-type-var input))
               ((try tree input1) (parse-base-type input)))
            (parse-bracket-type input)))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
               :branches (list (list tree))) input1))
         ;; Try "(" ws type-exp-paren ws ")"
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-body) (parse-type-exp-paren input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-body)
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 3))

  (define parse-bracket-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('bracket-type')."
    (b* (((pok< tree-open) (abnf::parse-ichars "[" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-te) (parse-type-exp input))
         ((mv trees-exts input) (parse-*-ws-ispace input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars "]" input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bracket-type")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-te)
                           trees-exts
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 2))

  (define parse-type-exp-paren ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('type-exp-paren')."
    (b* (((pok tree)
          (b* (((try tree rest) (parse-array-type input))
               ((try tree rest) (parse-arrow-type input))
               ((try tree rest) (parse-forall-type input))
               ((try tree rest) (parse-pi-type input)))
            (parse-sigma-type input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-exp-paren")
           :branches (list (list tree))) input))
    :measure (two-nats-measure (len input) 1))

  (define parse-array-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('array-type')."
    (b* (((pok< tree-a) (abnf::parse-schars "A" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-te) (parse-type-exp input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-sh) (parse-shape input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "array-type")
           :branches (list (list tree-a)
                           (list tree-ws1)
                           (list tree-te)
                           (list tree-ws2)
                           (list tree-sh)))
          input))
    :measure (two-nats-measure (len input) 0))

  (define parse-arrow-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('arrow-type')."
    (b* ((orig-input input)
         ((pok< tree-kw) (parse-group-arrow input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok trees-tes) (parse-*-ws-type-exp input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((unless (mbt (< (len input) (len orig-input))))
          (mv (reserrf :impossible) (nat-list-fix orig-input)))
         ((pok< tree-te) (parse-type-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "arrow-type")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-tes
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-te)))
          input))
    :measure (two-nats-measure (len input) 0))

  (define parse-forall-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('forall-type')."
    (b* (((pok< tree-kw) (parse-group-forall input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-tps input) (parse-repetition-*-ws-type-var input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-te) (parse-type-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "forall-type")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-tps
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-te)))
          input))
    :measure (two-nats-measure (len input) 0))

  (define parse-pi-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('pi-type')."
    (b* (((pok< tree-kw) (parse-group-pi input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-eps input) (parse-repetition-*-ws-ispace-var input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-te) (parse-type-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "pi-type")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-eps
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-te)))
          input))
    :measure (two-nats-measure (len input) 0))

  (define parse-sigma-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('sigma-type')."
    (b* (((pok< tree-kw) (parse-group-sigma input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-eps input) (parse-repetition-*-ws-ispace-var input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-te) (parse-type-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "sigma-type")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-eps
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-te)))
          input))
    :measure (two-nats-measure (len input) 0))

  (define parse-*-ws-type-exp ((input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp) (rest-input nat-listp))
    :short "Parse @('*( ws type-exp )')."
    (b* ((start-input input)
         ((mv trees input)
          (b* (((pok tree-ws) (parse-ws input))
               ((pok< tree-te) (parse-type-exp input))
               ((unless (mbt (< (len input) (len start-input))))
                (mv (reserrf :impossible) (nat-list-fix start-input)))
               ((pok trees) (parse-*-ws-type-exp input)))
            (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                       :branches (list (list tree-ws) (list tree-te)))
                      trees)
                input)))
         ((when (reserrp trees))
          (mv nil (nat-list-fix start-input))))
      (mv trees input))
    :measure (two-nats-measure (len input) 4))

  :ruler-extenders :all

  :verify-guards nil   ; done later

  :returns-hints
  (("Goal"
    :in-theory
    (e/d (abnf::treep-when-result-not-error
          abnf::tree-listp-when-result-not-error)
         (parse-type-exp parse-bracket-type parse-type-exp-paren
          parse-array-type parse-arrow-type parse-forall-type
          parse-pi-type parse-sigma-type parse-*-ws-type-exp)))
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
        '(:expand (parse-*-ws-type-exp input))))

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
    (defret len-of-parse-*-ws-type-exp-<
      t
      :rule-classes nil :fn parse-*-ws-type-exp)
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

;; Generate groups/reps now that type-exp and ispace are defined.
(defparse-remora-group "( ws type-exp )")
(defparse-remora-*-group "( ws type-exp )")
(defparse-remora-group "( ws ispace )")
(defparse-remora-*-group "( ws ispace )")
;; *( ispace-var ws ) for unbox-spec is hand-written inside the defines
;; block (unusual reversed pattern).

(defparse-remora-rulename "type-args")
(defparse-remora-rulename "ispace-args")
(defparse-remora-rulename "type-vars")
(defparse-remora-rulename "ispace-vars")
(defparse-remora-rulename "type-bind")
(defparse-remora-rulename "ispace-bind")

;; Sub-rules factored out of *-fun-bind / val-bind alt 2 / unbox-exp so
;; that no rule has more than 10 ABNF concatenation elements (the abnf
;; library's tree-list-tupleN family stops at N=10).  These sub-rules
;; carry semantic content (function signatures, typed bindings) and
;; their inner abstractors keep slice 4-5 cluster member sizes manageable.

(defparse-remora-rulename "colon-type")
;; The inline option [ ws colon-type ] is used in fun-sig/tfun-sig/ifun-sig
;; for an optional return-type annotation.  We keep it as an inline option
;; rather than a rule because rulename auto-generation would attempt to
;; prove a strict-less-than measure lemma, which fails for nullable rules
;; (the empty match consumes no input).
(defparse-remora-option "[ ws colon-type ]")
(defparse-remora-rulename "fun-sig")
(defparse-remora-rulename "tfun-sig")
(defparse-remora-rulename "ifun-sig")
(defparse-remora-rulename "at-fun-sig")
(defparse-remora-rulename "val-typed-sig")

;; Lambda keyword groups (just literals, no recursion).
(defparse-remora-group "( %s\"fn\" / %x03BB )")
(defparse-remora-group "( %s\"t\" %x03BB )")
(defparse-remora-group "( %s\"t-fn\" / ( %s\"t\" %x03BB ) )")
(defparse-remora-group "( %s\"i\" %x03BB )")
(defparse-remora-group "( %s\"i-fn\" / ( %s\"i\" %x03BB ) )")

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
;; 6-3: lambda, type-lambda, ispace-lambda, box-expr
;; 1: unbox-spec
;; 0: *-ispace-var-ws

(defines parse-expressions

  (define parse-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('exp')."
    (b* (((pok tree)
          (b* (((try tree rest) (parse-atom input))
               ((try tree rest) (parse-bracket-frame input))
               ((try tree rest) (parse-identifier input))
               ((try tree rest) (parse-string-lit input)))
            (parse-paren-exp input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "exp")
           :branches (list (list tree))) input))
    :measure (two-nats-measure (len input) 18))

  (define parse-bracket-frame ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('bracket-frame')."
    (b* (((pok< tree-open) (abnf::parse-ichars "[" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-e) (parse-exp input))
         ((pok trees-more) (parse-*-ws-exp input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars "]" input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bracket-frame")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-e)
                           trees-more
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 16))

  (define parse-paren-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('paren-exp')."
    (b* (((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-body) (parse-paren-exp-body input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-body)
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 15))

  (define parse-paren-exp-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('paren-exp-body')."
    (b* (((pok tree)
          (b* (((try tree rest) (parse-array-exp input))
               ((try tree rest) (parse-frame-exp input))
               ((try tree rest) (parse-tapp-exp input))
               ((try tree rest) (parse-iapp-exp input))
               ((try tree rest) (parse-unbox-exp input))
               ((try tree rest) (parse-let-exp input))
               ((try tree rest) (parse-at-app-exp input)))
            ;; app-exp must be last [SC3]
            (parse-app-exp input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "paren-exp-body")
           :branches (list (list tree))) input))
    :measure (two-nats-measure (len input) 27))

  (define parse-app-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('app-exp')."
    (b* (((pok< tree-e) (parse-exp input))
         ((pok trees-more) (parse-*-ws-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "app-exp")
           :branches (list (list tree-e) trees-more))
          input))
    :measure (two-nats-measure (len input) 26))

  (define parse-array-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('array-exp')."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are two alternatives that share the @('array ws shape-lit')
       prefix.  We first try the empty-array alternative @('ws type-exp'),
       which gives the element type explicitly (since there are no atoms
       to carry it); if the @('type-exp') does not parse, we fall back to
       the @('*( ws atom )') alternative.  The two produce CSTs with
       distinct branch counts (5 vs. 4), which the abstractor dispatches
       on."))
    (b* (((pok< tree-kw) (abnf::parse-schars "array" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-sl) (parse-shape-lit input))
         ;; remember the input just after the shared prefix, for the
         ;; fallback to alternative 1 (which begins its own `ws`)
         (input-after-prefix input)
         ;; Alternative 2 (empty array): ws type-exp
         ;; parse-ws never errors, so `pok` here is always taken
         ((pok tree-ws2) (parse-ws input))
         ((mv tree-te input-b) (parse-type-exp input))
         ((unless (reserrp tree-te))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "array-exp")
               :branches (list (list tree-kw)
                               (list tree-ws1)
                               (list tree-sl)
                               (list tree-ws2)
                               (list tree-te)))
              input-b))
         ;; Alternative 1 (non-empty): *( ws atom )
         ;; (pok shadows `input` with the remaining input after the atoms)
         ((pok trees-more) (parse-*-ws-atom input-after-prefix)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "array-exp")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-sl)
                           trees-more))
          input))
    :measure (two-nats-measure (len input) 24))

  (define parse-frame-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('frame-exp')."
    :long
    (xdoc::topstring
     (xdoc::p
      "Like @(tsee parse-array-exp), there are two alternatives sharing the
       @('frame ws shape-lit') prefix.  We first try the empty-frame
       alternative @('ws type-exp'); if @('type-exp') does not parse, we
       fall back to @('*( ws exp )').  The CSTs have distinct branch counts
       (5 vs. 4)."))
    (b* (((pok< tree-kw) (abnf::parse-schars "frame" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-sl) (parse-shape-lit input))
         ;; remember the input just after the shared prefix, for the
         ;; fallback to alternative 1 (which begins its own `ws`)
         (input-after-prefix input)
         ;; Alternative 2 (empty frame): ws type-exp
         ;; parse-ws never errors, so `pok` here is always taken
         ((pok tree-ws2) (parse-ws input))
         ((mv tree-te input-b) (parse-type-exp input))
         ((unless (reserrp tree-te))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "frame-exp")
               :branches (list (list tree-kw)
                               (list tree-ws1)
                               (list tree-sl)
                               (list tree-ws2)
                               (list tree-te)))
              input-b))
         ;; Alternative 1 (non-empty): *( ws exp )
         ;; (pok shadows `input` with the remaining input after the exprs)
         ((pok trees-more) (parse-*-ws-exp input-after-prefix)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "frame-exp")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-sl)
                           trees-more))
          input))
    :measure (two-nats-measure (len input) 23))

  (define parse-tapp-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('tapp-exp')."
    (b* (((pok< tree-kw) (abnf::parse-schars "t-app" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-e) (parse-exp input))
         ((mv trees-tes input) (parse-repetition-*-ws-type-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "tapp-exp")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-e)
                           trees-tes))
          input))
    :measure (two-nats-measure (len input) 22))

  (define parse-iapp-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('iapp-exp')."
    (b* (((pok< tree-kw) (abnf::parse-schars "i-app" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-e) (parse-exp input))
         ((mv trees-exts input) (parse-repetition-*-ws-ispace input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "iapp-exp")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-e)
                           trees-exts))
          input))
    :measure (two-nats-measure (len input) 21))

  ;; unbox-exp = "unbox" ws "(" ws unbox-spec ws ")" ws exp
  (define parse-unbox-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('unbox-exp')."
    (b* (((pok< tree-kw) (abnf::parse-schars "unbox" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-spec) (parse-unbox-spec input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "unbox-exp")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           (list tree-ws2)
                           (list tree-spec)
                           (list tree-ws3)
                           (list tree-close)
                           (list tree-ws4)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 20))

  ;; [SC4] The Haskell parser guards each ispace-var (which it calls
  ;; extent-param) with notFollowedBy ")".  Our parser uses
  ;; greedy *( ispace-var ws ) without lookahead, which produces the
  ;; same result for well-formed input.
  ;;
  ;; unbox-spec = *( ispace-var ws ) identifier ws exp
  (define parse-unbox-spec ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('unbox-spec')."
    (b* ((orig-input input)
         ((pok trees-eps) (parse-*-ispace-var-ws input))
         ((pok< tree-id) (parse-identifier input))
         ((pok tree-ws) (parse-ws input))
         ((unless (mbt (< (len input) (len orig-input))))
          (mv (reserrf :impossible) (nat-list-fix orig-input)))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "unbox-spec")
           :branches (list trees-eps
                           (list tree-id)
                           (list tree-ws)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 1))

  (define parse-let-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('let-exp')."
    (b* ((orig-input input)
         ((pok< tree-kw) (abnf::parse-schars "let" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((unless (mbt (< (len input) (len orig-input))))
          (mv (reserrf :impossible) (nat-list-fix orig-input)))
         ((pok trees-binds) (parse-*-ws-bind input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((unless (mbt (< (len input) (len orig-input))))
          (mv (reserrf :impossible) (nat-list-fix orig-input)))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "let-exp")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-binds
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 19))

  (define parse-at-app-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('at-app-exp')."
    (b* (((pok< tree-at) (abnf::parse-ichars "@" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-e) (parse-exp input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-ta) (parse-type-args input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-ia) (parse-ispace-args input))
         ((pok trees-more) (parse-*-ws-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "at-app-exp")
           :branches (list (list tree-at)
                           (list tree-ws1)
                           (list tree-e)
                           (list tree-ws2)
                           (list tree-ta)
                           (list tree-ws3)
                           (list tree-ia)
                           trees-more))
          input))
    :measure (two-nats-measure (len input) 25))

  (define parse-atom ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('atom')."
    (b* (((mv tree rest) (parse-base-val input))
         ((unless (reserrp tree))
          (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom")
               :branches (list (list tree))) rest))
         ;; Try "(" ws atom-body ws ")"
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-body) (parse-atom-body input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-body)
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 17))

  (define parse-atom-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('atom-body')."
    (b* (((pok tree)
          (b* (((try tree rest) (parse-lambda input))
               ((try tree rest) (parse-type-lambda input))
               ((try tree rest) (parse-ispace-lambda input)))
            (parse-box-expr input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "atom-body")
           :branches (list (list tree))) input))
    :measure (two-nats-measure (len input) 14))

  (define parse-lambda ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('lambda')."
    (b* (((pok< tree-kw) (parse-group-fn input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-pats input) (parse-repetition-*-ws-pat input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "lambda")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-pats
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 6))

  (define parse-type-lambda ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('type-lambda')."
    (b* (((pok< tree-kw) (parse-group-t-fn input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-tps input) (parse-repetition-*-ws-type-var input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "type-lambda")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-tps
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 5))

  (define parse-ispace-lambda ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('ispace-lambda')."
    (b* (((pok< tree-kw) (parse-group-i-fn input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-eps input) (parse-repetition-*-ws-ispace-var input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "ispace-lambda")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-eps
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 4))

  (define parse-box-expr ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('box-expr')."
    (b* (((pok< tree-kw) (abnf::parse-schars "box" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((mv trees-exts input) (parse-repetition-*-ws-ispace input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-e) (parse-exp input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-te) (parse-type-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "box-expr")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           trees-exts
                           (list tree-ws2)
                           (list tree-close)
                           (list tree-ws3)
                           (list tree-e)
                           (list tree-ws4)
                           (list tree-te)))
          input))
    :measure (two-nats-measure (len input) 3))

  (define parse-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('bind')."
    (b* (((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-body) (parse-bind-body input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind")
           :branches (list (list tree-open)
                           (list tree-ws1)
                           (list tree-body)
                           (list tree-ws2)
                           (list tree-close)))
          input))
    :measure (two-nats-measure (len input) 12))

  (define parse-bind-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('bind-body')."
    (b* (((pok tree)
          (b* (((try tree rest) (parse-val-bind input))
               ((try tree rest) (parse-fun-bind input))
               ((try tree rest) (parse-tfun-bind input))
               ((try tree rest) (parse-ifun-bind input))
               ((try tree rest) (parse-type-bind input))
               ((try tree rest) (parse-ispace-bind input)))
            (parse-at-fun-bind input))))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "bind-body")
           :branches (list (list tree))) input))
    :measure (two-nats-measure (len input) 13))

  (define parse-val-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('val-bind')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The grammar has two alternatives:
       @({
         val-bind = \"val\" ws identifier ws exp
                  / \"val\" ws \"(\" ws val-typed-sig ws \")\" ws exp
       })
       The untyped form (alt 1) produces 5 tree-lists; the typed form
       (alt 2) produces 9 tree-lists.  The downstream abstractor
       dispatches on tree-list count."))
    (b* (((try tree rest)
          ;; Alt 1: "val" ws identifier ws exp
          (b* (((pok< tree-kw) (abnf::parse-schars "val" input))
               ((pok tree-ws1) (parse-ws input))
               ((pok< tree-id) (parse-identifier input))
               ((pok tree-ws2) (parse-ws input))
               ((pok< tree-e) (parse-exp input)))
            (mv (abnf::make-tree-nonleaf
                 :rulename? (abnf::rulename "val-bind")
                 :branches (list (list tree-kw)
                                 (list tree-ws1)
                                 (list tree-id)
                                 (list tree-ws2)
                                 (list tree-e)))
                input)))
         ;; Alt 2: "val" ws "(" ws val-typed-sig ws ")" ws exp
         ((pok< tree-kw) (abnf::parse-schars "val" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-sig) (parse-val-typed-sig input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf
           :rulename? (abnf::rulename "val-bind")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           (list tree-ws2)
                           (list tree-sig)
                           (list tree-ws3)
                           (list tree-close)
                           (list tree-ws4)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 11))

  ;; fun-bind = "fun" ws "(" ws fun-sig ws ")" ws exp
  (define parse-fun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('fun-bind')."
    (b* (((pok< tree-kw) (abnf::parse-schars "fun" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-sig) (parse-fun-sig input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "fun-bind")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           (list tree-ws2)
                           (list tree-sig)
                           (list tree-ws3)
                           (list tree-close)
                           (list tree-ws4)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 10))

  ;; tfun-bind = "t-fun" ws "(" ws tfun-sig ws ")" ws exp
  (define parse-tfun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse a @('tfun-bind')."
    (b* (((pok< tree-kw) (abnf::parse-schars "t-fun" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-sig) (parse-tfun-sig input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "tfun-bind")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           (list tree-ws2)
                           (list tree-sig)
                           (list tree-ws3)
                           (list tree-close)
                           (list tree-ws4)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 9))

  ;; ifun-bind = "i-fun" ws "(" ws ifun-sig ws ")" ws exp
  (define parse-ifun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('ifun-bind')."
    (b* (((pok< tree-kw) (abnf::parse-schars "i-fun" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-sig) (parse-ifun-sig input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "ifun-bind")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           (list tree-ws2)
                           (list tree-sig)
                           (list tree-ws3)
                           (list tree-close)
                           (list tree-ws4)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 8))

  ;; at-fun-bind = "fun" ws "(" ws at-fun-sig ws ")" ws exp
  (define parse-at-fun-bind ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
    :short "Parse an @('at-fun-bind')."
    (b* (((pok< tree-kw) (abnf::parse-schars "fun" input))
         ((pok tree-ws1) (parse-ws input))
         ((pok< tree-open) (abnf::parse-ichars "(" input))
         ((pok tree-ws2) (parse-ws input))
         ((pok< tree-sig) (parse-at-fun-sig input))
         ((pok tree-ws3) (parse-ws input))
         ((pok< tree-close) (abnf::parse-ichars ")" input))
         ((pok tree-ws4) (parse-ws input))
         ((pok< tree-e) (parse-exp input)))
      (mv (abnf::make-tree-nonleaf :rulename? (abnf::rulename "at-fun-bind")
           :branches (list (list tree-kw)
                           (list tree-ws1)
                           (list tree-open)
                           (list tree-ws2)
                           (list tree-sig)
                           (list tree-ws3)
                           (list tree-close)
                           (list tree-ws4)
                           (list tree-e)))
          input))
    :measure (two-nats-measure (len input) 7))

  ;; Repetition helpers for the mutual recursion.

  (define parse-*-ws-exp ((input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp) (rest-input nat-listp))
    (b* ((start-input input)
         ((mv trees input)
          (b* (((pok tree-ws) (parse-ws input))
               ((pok< tree-e) (parse-exp input))
               ((unless (mbt (< (len input) (len start-input))))
                (mv (reserrf :impossible) (nat-list-fix start-input)))
               ((pok trees) (parse-*-ws-exp input)))
            (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                       :branches (list (list tree-ws) (list tree-e)))
                      trees)
                input)))
         ((when (reserrp trees))
          (mv nil (nat-list-fix start-input))))
      (mv trees input))
    :measure (two-nats-measure (len input) 30))

  (define parse-*-ws-atom ((input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp) (rest-input nat-listp))
    (b* ((start-input input)
         ((mv trees input)
          (b* (((pok tree-ws) (parse-ws input))
               ((pok< tree-a) (parse-atom input))
               ((unless (mbt (< (len input) (len start-input))))
                (mv (reserrf :impossible) (nat-list-fix start-input)))
               ((pok trees) (parse-*-ws-atom input)))
            (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                       :branches (list (list tree-ws) (list tree-a)))
                      trees)
                input)))
         ((when (reserrp trees))
          (mv nil (nat-list-fix start-input))))
      (mv trees input))
    :measure (two-nats-measure (len input) 29))

  (define parse-*-ws-bind ((input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp) (rest-input nat-listp))
    (b* ((start-input input)
         ((mv trees input)
          (b* (((pok tree-ws) (parse-ws input))
               ((pok< tree-b) (parse-bind input))
               ((unless (mbt (< (len input) (len start-input))))
                (mv (reserrf :impossible) (nat-list-fix start-input)))
               ((pok trees) (parse-*-ws-bind input)))
            (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                       :branches (list (list tree-ws) (list tree-b)))
                      trees)
                input)))
         ((when (reserrp trees))
          (mv nil (nat-list-fix start-input))))
      (mv trees input))
    :measure (two-nats-measure (len input) 28))

  (define parse-*-ispace-var-ws ((input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp) (rest-input nat-listp))
    :short "Parse @('*( ispace-var ws )')."
    (b* ((start-input input)
         ((mv trees input)
          (b* (((pok< tree-ep) (parse-ispace-var input))
               ((unless (mbt (< (len input) (len start-input))))
                (mv (reserrf :impossible) (nat-list-fix start-input)))
               ((pok tree-ws) (parse-ws input))
               ((pok trees) (parse-*-ispace-var-ws input)))
            (mv (cons (abnf::make-tree-nonleaf :rulename? nil
                       :branches (list (list tree-ep) (list tree-ws)))
                      trees)
                input)))
         ((when (reserrp trees))
          (mv nil (nat-list-fix start-input))))
      (mv trees input))
    :measure (two-nats-measure (len input) 0))

  :prepwork ((defun parse-expressions-expand-hints (id clause world)
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
                ((acl2::occur-lst '(acl2::flag-is 'parse-unbox-spec) clause)
                 '(:expand (parse-unbox-spec input)))
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
                ((acl2::occur-lst '(acl2::flag-is 'parse-ispace-lambda) clause)
                 '(:expand (parse-ispace-lambda input)))
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
                ((acl2::occur-lst '(acl2::flag-is 'parse-*-ispace-var-ws) clause)
                 '(:expand (parse-*-ispace-var-ws input))))))

  :returns-hints
  (("Goal"
    :in-theory
    (e/d (abnf::treep-when-result-not-error
          abnf::tree-listp-when-result-not-error)
         (parse-exp parse-bracket-frame parse-paren-exp
          parse-paren-exp-body parse-app-exp parse-array-exp
          parse-frame-exp parse-tapp-exp parse-iapp-exp
          parse-unbox-exp parse-unbox-spec parse-let-exp parse-at-app-exp
          parse-atom parse-atom-body parse-lambda
          parse-type-lambda parse-ispace-lambda parse-box-expr
          parse-bind parse-bind-body parse-val-bind
          parse-fun-bind parse-tfun-bind parse-ifun-bind
          parse-at-fun-bind parse-*-ws-exp parse-*-ws-atom
          parse-*-ws-bind parse-*-ispace-var-ws)))
   parse-expressions-expand-hints)

  :ruler-extenders :all

  :verify-guards nil   ; done later

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
    (defret len-of-parse-unbox-spec-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-unbox-spec)
    (defret len-of-parse-unbox-spec-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-unbox-spec)
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
    (defret len-of-parse-ispace-lambda-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-ispace-lambda)
    (defret len-of-parse-ispace-lambda-<
      (implies (not (reserrp tree)) (< (len rest-input) (len input)))
      :rule-classes :linear :fn parse-ispace-lambda)
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
    (defret len-of-parse-*-ws-exp-<
      t :rule-classes nil :fn parse-*-ws-exp)
    (defret len-of-parse-*-ws-atom-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-ws-atom)
    (defret len-of-parse-*-ws-atom-<
      t :rule-classes nil :fn parse-*-ws-atom)
    (defret len-of-parse-*-ws-bind-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-ws-bind)
    (defret len-of-parse-*-ws-bind-<
      t :rule-classes nil :fn parse-*-ws-bind)
    (defret len-of-parse-*-ispace-var-ws-<=
      (<= (len rest-input) (len input)) :rule-classes :linear :fn parse-*-ispace-var-ws)
    (defret len-of-parse-*-ispace-var-ws-<
      t :rule-classes nil :fn parse-*-ispace-var-ws)
    :hints (("Goal" :in-theory
             (disable parse-exp parse-bracket-frame parse-paren-exp
                      parse-paren-exp-body parse-app-exp parse-array-exp
                      parse-frame-exp parse-tapp-exp parse-iapp-exp
                      parse-unbox-exp parse-unbox-spec parse-let-exp
                      parse-at-app-exp
                      parse-atom parse-atom-body parse-lambda
                      parse-type-lambda parse-ispace-lambda parse-box-expr
                      parse-bind parse-bind-body parse-val-bind
                      parse-fun-bind parse-tfun-bind parse-ifun-bind
                      parse-at-fun-bind parse-*-ws-exp parse-*-ws-atom
                      parse-*-ws-bind parse-*-ispace-var-ws))
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
            (and (acl2::occur-lst '(acl2::flag-is 'parse-unbox-spec) clause)
                 '(:expand (parse-unbox-spec input)))
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
            (and (acl2::occur-lst '(acl2::flag-is 'parse-ispace-lambda) clause)
                 '(:expand (parse-ispace-lambda input)))
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
            (and (acl2::occur-lst '(acl2::flag-is 'parse-*-ispace-var-ws) clause)
                 '(:expand (parse-*-ispace-var-ws input)))))

  (verify-guards parse-exp
    :hints (("Goal"
             :in-theory
             (e/d (abnf::treep-when-result-not-error
                   abnf::tree-listp-when-result-not-error)
                  (parse-exp parse-bracket-frame parse-paren-exp
                   parse-paren-exp-body parse-app-exp parse-array-exp
                   parse-frame-exp parse-tapp-exp parse-iapp-exp
                   parse-unbox-exp parse-unbox-spec parse-let-exp
                   parse-at-app-exp
                   parse-atom parse-atom-body parse-lambda
                   parse-type-lambda parse-ispace-lambda parse-box-expr
                   parse-bind parse-bind-body parse-val-bind
                   parse-fun-bind parse-tfun-bind parse-ifun-bind
                   parse-at-fun-bind parse-*-ws-exp parse-*-ws-atom
                   parse-*-ws-bind parse-*-ispace-var-ws))))))

;; ---- Top-level ----

(define parse-program ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp) (rest-input nat-listp))
  :short "Parse a @('program')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses a Remora program according to the ABNF grammar.
     The extra-grammatical constraint of keyword exclusion
     must be handled by the caller."))
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
         :branches (list (list tree-ws1)
                         (list tree-e)
                         (list tree-ws2)))
        input3))
  :hooks (:fix)
  ///
  (defret len-of-parse-program-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear))
