; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/utilities/strings/chars-codes" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)
(include-book "unicode/utf8-decode" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/typed-lists/nat-listp" :dir :system)

(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ printer-tokens
  :parents (parsing-and-printing)
  :short "Rendering of the tokens of Remora as code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "The text that the @(see printer) and the @(see pretty-printer) emit
     is assembled from code points (one nat per code point) of three
     kinds: ASCII literals from the printer sources (see @(tsee
     ascii-string=>codepoints)), identifiers from the AST, stored as
     UTF-8 byte strings (see @(tsee utf8-string=>codepoints)), and
     literals (see @(tsee nat-to-dec-codepoints), @(tsee
     int-lit-to-codepoints), @(tsee float-lit-to-codepoints), and
     @(tsee string-lit-to-codepoints)).  The functions here are shared
     by both printers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Code-point conversion.
;;

(define char-list-all-ascii-p ((chars character-listp))
  :returns (b booleanp)
  :short "True iff every character has @(tsee char-code) less than 128."
  (cond ((endp chars) t)
        ((< (char-code (car chars)) 128)
         (char-list-all-ascii-p (cdr chars)))
        (t nil)))

(define ascii-string=>codepoints ((s stringp))
  :returns (cps nat-listp)
  :short "Map an ASCII string to the nat-list of its char-codes.
          Caller must ensure @('s') contains only ASCII (codes
          @('< 128'))."
  :long
  (xdoc::topstring
   (xdoc::p
    "For ASCII strings, the ACL2 @(tsee char-code) of each character
     equals the Unicode code point.  This function is invoked at
     macro-expansion time by the @(tsee pdoc-ascii) and @(tsee
     pform-ascii) macros, and at runtime only for the few ASCII literals
     that are not written with those macros."))
  (chars=>nats (explode s)))


(define utf8-string=>codepoints ((s stringp))
  :returns (cps nat-listp)
  :short "Decode an ACL2 string of UTF-8 bytes to its code-point list.
          Returns the empty list on invalid UTF-8 (defensive)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifier names in the AST are stored as ACL2 strings whose
     bytes are the UTF-8 encoding of the original code-point sequence
     (see @(see abstract-syntax-trees)).  This function reverses that
     encoding."))
  (b* ((bytes (string=>nats (str-fix s)))
       ((unless (unsigned-byte-listp 8 bytes)) nil)
       (cps (utf8=>ustring bytes))
       ((unless (nat-listp cps)) nil))
    cps))

(define nat-to-dec-codepoints ((n natp))
  :returns (cps nat-listp)
  :short "Decimal digits of @('n') as a code-point list."
  (ascii-string=>codepoints (str::nat-to-dec-string (nfix n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Numeric literals.
;;

(define sign-to-codepoints ((s signp))
  :returns (cps nat-listp)
  (sign-case s :plus (list #x2B) :minus (list #x2D)))

(define sign-option-to-codepoints ((s? sign-optionp))
  :returns (cps nat-listp)
  (sign-option-case s?
                    :some (sign-to-codepoints s?.val)
                    :none nil))

(define expo-to-codepoints ((e expop))
  :returns (cps nat-listp)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable str::character-listp-when-dec-digit-char-listp)))
  (b* ((upcase (expo->upcase e))
       (sign? (expo->sign? e))
       (digits (expo->digits e)))
    (append (if upcase (list #x45) (list #x65))
            (append (sign-option-to-codepoints sign?)
                    (chars=>nats digits)))))

(define expo-option-to-codepoints ((e? expo-optionp))
  :returns (cps nat-listp)
  :hooks nil
  (expo-option-case e?
                    :some (expo-to-codepoints e?.val)
                    :none nil))

(define int-lit-to-codepoints ((il int-litp))
  :returns (cps nat-listp)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable str::character-listp-when-dec-digit-char-listp)))
  (b* ((sign? (int-lit->sign? il))
       (digits (int-lit->digits il)))
    (append (sign-option-to-codepoints sign?)
            (chars=>nats digits))))

(define float-lit-to-codepoints ((fl float-litp))
  :returns (cps nat-listp)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable str::character-listp-when-dec-digit-char-listp)))
  (b* ((sign? (float-lit->sign? fl))
       (whole (float-lit->whole-digits fl))
       (frac (float-lit->frac-digits fl))
       (expo? (float-lit->expo? fl))
       (dot/frac (cond ((consp frac) (cons #x2E (chars=>nats frac)))
                       (t nil))))
    (append (sign-option-to-codepoints sign?)
            (append (chars=>nats whole)
                    (append dot/frac
                            (expo-option-to-codepoints expo?))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; String literals: render @(tsee char-lit) values back to their
;; source-text form (printable code point vs.@ backslash escape).
;; Mirrors the @('char-lit') / @('escape-char') ABNF rules in
;; @('grammar.abnf').
;;

(define ascii-mnemonic-of-code ((code natp))
  :returns (cps nat-listp)
  :short "Map an ASCII control code (@('#x00')&ndash;@('#x20')) to its
          Remora source-form mnemonic (@('NUL')&ndash;@('SP'))
          as a code-point list."
  :guard (<= code #x20)
  (b* ((c (lnfix code)))
    (ascii-string=>codepoints
     (case c
       (0 "NUL") (1 "SOH") (2 "STX") (3 "ETX") (4 "EOT") (5 "ENQ")
       (6 "ACK") (7 "BEL") (8 "BS")  (9 "HT")  (10 "LF") (11 "VT")
       (12 "FF") (13 "CR") (14 "SO") (15 "SI") (16 "DLE") (17 "DC1")
       (18 "DC2") (19 "DC3") (20 "DC4") (21 "NAK") (22 "SYN") (23 "ETB")
       (24 "CAN") (25 "EM") (26 "SUB") (27 "ESC") (28 "FS") (29 "GS")
       (30 "RS") (31 "US") (32 "SP")
       (otherwise "")))))

(define char-escape-to-codepoints ((ce char-escapep))
  :returns (cps nat-listp)
  :short "Render a @(tsee char-escape) as the code-point list following
          the backslash (e.g. @(':n') &rarr; @('(#x6E)'))."
  (char-escape-case ce
    :a (list #x61)
    :b (list #x62)
    :f (list #x66)
    :n (list #x6E)
    :r (list #x72)
    :t (list #x74)
    :v (list #x76)
    :bslash (list #x5C)
    :dquote (list #x22)
    :squote (list #x27)))

(define ascii-escape-to-codepoints ((ae ascii-escapep))
  :returns (cps nat-listp)
  :short "Render an @(tsee ascii-escape) as the code-point list of its
          source-form mnemonic (e.g. @('NUL'), @('LF'), @('DEL'))."
  (ascii-escape-case ae
    :nul-to-sp (ascii-mnemonic-of-code ae.code)
    :del (ascii-string=>codepoints "DEL")))

(define caret-escape-to-codepoints ((ce caret-escapep))
  :returns (cps nat-listp)
  :short "Render a @(tsee caret-escape) as @('^') followed by the code
          point @('code+#x40')."
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable caret-escape->code)))
  (b* ((code (caret-escape->code ce)))
    (list #x5E (+ code #x40))))

(define dec-digit-char-list-to-codepoints ((digits str::dec-digit-char-listp))
  :returns (cps nat-listp)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable str::character-listp-when-dec-digit-char-listp)))
  (chars=>nats digits))

(define oct-digit-char-list-to-codepoints ((digits str::oct-digit-char-listp))
  :returns (cps nat-listp)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable str::character-listp-when-oct-digit-char-listp)))
  (chars=>nats digits))

(define hex-digit-char-list-to-codepoints ((digits str::hex-digit-char-listp))
  :returns (cps nat-listp)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable str::character-listp-when-hex-digit-char-listp)))
  (chars=>nats digits))

(define num-escape-to-codepoints ((ne num-escapep))
  :returns (cps nat-listp)
  :short "Render a @(tsee num-escape) to its source form (as code points):
          bare digits for decimal, prefixed by @('o') for octal, by
          @('x') for hexadecimal."
  (num-escape-case ne
    :dec (dec-digit-char-list-to-codepoints ne.digits)
    :oct (cons #x6F (oct-digit-char-list-to-codepoints ne.digits))
    :hex (cons #x78 (hex-digit-char-list-to-codepoints ne.digits))))

(define escape-to-codepoints ((e escapep))
  :returns (cps nat-listp)
  :short "Render the suffix of a @('\\\\')-escape; the leading @('\\\\')
          is added by @(tsee char-lit-to-codepoints)."
  (escape-case e
    :char (char-escape-to-codepoints e.escape)
    :ascii (ascii-escape-to-codepoints e.escape)
    :caret (caret-escape-to-codepoints e.escape)
    :num (num-escape-to-codepoints e.escape)))

(define char-lit-to-codepoints ((cl char-litp))
  :returns (cps nat-listp)
  :short "Render a single @(tsee char-lit) to its source-text form as
          a code-point list.  For @(':char') this is just the singleton
          @('(cl.code)'); for @(':escape') it is @('#x5C') (backslash)
          followed by the rendered escape suffix."
  (char-lit-case cl
    :char (list (lnfix cl.code))
    :escape (cons #x5C (escape-to-codepoints cl.escape))))

(define char-lit-list-to-codepoints ((chars char-lit-listp))
  :returns (cps nat-listp)
  :short "Render the contents of a Remora string literal: concatenation
          of @(tsee char-lit-to-codepoints) over @('chars').  Does NOT
          insert empty escapes; use @(tsee string-lit-to-codepoints) for
          a round-trip-safe rendering of a string literal."
  (cond ((endp chars) nil)
        (t (append (char-lit-to-codepoints (car chars))
                   (char-lit-list-to-codepoints (cdr chars))))))

;; ---- Disambiguation: insert "\&" empty-escapes where adjacent
;; char-lits would otherwise be merged on re-parse. ----
;;
;; The Remora grammar has two sources of round-trip ambiguity:
;;   1. num-escape is greedy (1*DIGIT, 1*OCTDIGIT, 1*HEXDIG), so
;;      :dec "5" followed by char '7' merges to "\57".
;;   2. ascii-escape :so is a prefix of :soh, so :so followed by 'H'
;;      or 'h' merges to "\SOH".
;; In both cases, the next char-lit is a :char.  Following an :escape
;; char-lit by another :escape always begins with '\', which never
;; extends a num-escape's digit run nor completes "SOH" after "SO".

(define char-lit-first-codepoint ((cl char-litp))
  :returns (cp natp)
  :short "First codepoint of @('cl')'s printed form."
  :hooks nil
  (char-lit-case cl
    :char (lnfix cl.code)
    :escape #x5C))

(define needs-empty-escape-between ((prev char-litp) (next char-litp))
  :returns (yes/no booleanp)
  :short "Whether to emit @('\\&') between @('prev') and @('next') so
          that re-parsing recovers the same two char-lits.  Returns
          @('t') when @('prev')'s greedy or prefix-ambiguous parse
          would otherwise consume part of @('next')."
  :hooks nil
  (b* ((next-cp (char-lit-first-codepoint next)))
    (char-lit-case prev
      :char nil  ; non-escape consumes exactly one codepoint
      :escape
      (escape-case prev.escape
        :char nil    ; \X mnemonic: 1 fixed codepoint
        :caret nil   ; \^X: caret consumes exactly 2 codepoints
        :ascii (ascii-escape-case prev.escape.escape
                 :nul-to-sp
                 ;; Only :so (code 14) has a prefix conflict (with :soh)
                 (and (eql prev.escape.escape.code 14)
                      (or (eql next-cp #x48)    ; 'H'
                          (eql next-cp #x68)))  ; 'h'
                 :del nil)
        :num (num-escape-case prev.escape.escape
               :dec (and (<= #x30 next-cp) (<= next-cp #x39))   ; 0-9
               :oct (and (<= #x30 next-cp) (<= next-cp #x37))   ; 0-7
               :hex (or (and (<= #x30 next-cp) (<= next-cp #x39))    ; 0-9
                        (and (<= #x41 next-cp) (<= next-cp #x46))    ; A-F
                        (and (<= #x61 next-cp) (<= next-cp #x66)))))))) ; a-f

(define char-lit-list-to-codepoints-disambig ((chars char-lit-listp))
  :returns (cps nat-listp)
  :short "Render @('chars') as the contents of a string literal,
          inserting @('\\&') (code points @('#x5C #x26')) between
          adjacent char-lits where the parser would otherwise re-merge
          them."
  (cond ((endp chars) nil)
        ((endp (cdr chars))
         (char-lit-to-codepoints (car chars)))
        (t (append
            (char-lit-to-codepoints (car chars))
            (append (if (needs-empty-escape-between (car chars)
                                                     (cadr chars))
                        (list #x5C #x26)
                      nil)
                    (char-lit-list-to-codepoints-disambig (cdr chars)))))))

(define string-lit-to-codepoints ((chars char-lit-listp))
  :returns (cps nat-listp)
  :short "Render a string literal: surround the disambig'd contents
          with double-quote code points (@('#x22'))."
  (cons #x22
        (append (char-lit-list-to-codepoints-disambig chars)
                (list #x22))))

