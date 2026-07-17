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
(include-book "abstract-syntax-well-formed")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)
(include-book "unicode/utf8-decode" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/typed-lists/nat-listp" :dir :system)

(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;; (acl2::controlled-configuration) is intentionally not used here:
;; the pdoc engine relies on standard acl2-count induction which the
;; controlled-configuration setup disables.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ printer
  :parents (parsing-and-printing)
  :short "A pretty-printer of Remora from the abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p "
 @({
 (print-file f)
 (print-expr e)
 })
 ")
   (xdoc::p
    "We provide a pretty-printer that turns @(see abstract-syntax) ASTs
     into Remora source text, according to the concrete syntax described
     by @(see grammar).  The printer is the AST-to-text counterpart of
     the @(see parser) and @(see syntax-abstraction) pipeline; together,
     they form a round-trip from text to AST back to text and back to
     the same AST.")
   (xdoc::p
    "The printer is built on a small @(tsee pdoc) combinator engine in
     the style of Wadler/Lindig (Lindig, "
    (xdoc::ahref "https://lindig.github.io/papers/strictly-pretty-2000.pdf"
                 "Strictly Pretty")
    ", 2000), rather than a port of the Common Lisp pretty-printer.
     The engine has six combinators &mdash; @(tsee pdoc-text),
     @(tsee pdoc-line), @(tsee pdoc-hardline), @(tsee pdoc-concat),
     @(tsee pdoc-nest), @(tsee pdoc-group) &mdash; and a single greedy
     @(tsee layout) function with one-line lookahead.  The whole engine
     is structurally recursive and small enough to formally verify.")
   (xdoc::p
    "We use the prefix @('pdoc') (`printer doc') for the document type
     because @('doc') is already taken by ACL2's built-in
     documentation system.")
   (xdoc::p
    "The Remora-specific layer (@(see expr-to-pdoc), @(see file-to-pdoc),
     etc.) walks the AST and builds the @(tsee pdoc).  The top-level
     entry points are @(tsee print-file) and @(tsee print-expr), which
     compose the walker and @(tsee layout) into single
     @('AST &rarr; string') functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; pdoc combinators (Wadler/Lindig style).
;;
;; A pdoc is a tree of layout instructions.  The layout function
;; recursively interprets the tree, choosing for each Group whether to
;; render it flat (all on one line) or broken (Lines become newlines
;; with indent).  The Group decision uses one-line lookahead via the
;; auxiliary fits function.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes pdocs
  :short "Mutually recursive types for the pretty-printer engine."

  (fty::deftagsum pdoc
    :parents (printer pdocs)
    :short "Pretty-printer document combinators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The six constructors:")
     (xdoc::ul
      (xdoc::li
       "@(':text') &mdash; literal text with no embedded newlines,
        stored as a list of Unicode code points (one nat per code point).
        Use the @(tsee pdoc-ascii) macro for ASCII string literals at
        call sites; for runtime UTF-8-byte-string input (identifier
        names) use @(tsee utf8-string=>codepoints).")
      (xdoc::li
       "@(':line') &mdash; soft newline: a single space when the
        enclosing @(':group') fits on the current line, otherwise a
        newline followed by the current indent.")
      (xdoc::li
       "@(':hardline') &mdash; forced newline (always breaks).")
      (xdoc::li
       "@(':concat') &mdash; sequence two documents.")
      (xdoc::li
       "@(':nest') &mdash; increase the current indent by @('amount')
        while rendering @('body').")
      (xdoc::li
       "@(':group') &mdash; render @('body') flat if it fits in the
        remaining columns of the current line; otherwise let its
        @(':line')s expand to newlines.")))
    (:text ((cps nat-list)))
    (:line ())
    (:hardline ())
    (:concat ((left pdoc) (right pdoc)))
    (:nest ((amount nat) (body pdoc)))
    (:group ((body pdoc)))
    :pred pdocp)

  (fty::deflist pdoc-list
    :parents (printer pdocs)
    :short "Lists of @(tsee pdoc)."
    :elt-type pdoc
    :true-listp t
    :elementp-of-nil nil
    :pred pdoc-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Helpers for building @(tsee pdoc-text) leaves at the code-point level.
;;
;; The pdoc :text leaf carries a nat-list of code points (not a string).
;; The printer assembles text from three sources:
;;
;;   (a) ASCII string literals embedded in printer source (e.g. "Bool",
;;       "(", "Forall").  Use the @(tsee pdoc-ascii) macro, which
;;       expands at read time to a quoted constant nat-list and signals
;;       a hard error on any non-ASCII character.
;;
;;   (b) Identifier names from the AST, stored as ACL2 strings of
;;       UTF-8 bytes (see @(see abstract-syntax-trees)).  Use
;;       @(tsee utf8-string=>codepoints), which decodes the bytes to
;;       code points.
;;
;;   (c) Numbers formatted as decimal text.  Use
;;       @(tsee nat-to-dec-codepoints) instead of @(tsee
;;       str::nat-to-dec-string).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     macro-expansion time by @(tsee pdoc-ascii) and at runtime nowhere
     in the printer (call sites use the macro)."))
  (chars=>nats (explode s)))

(defmacro+ pdoc-ascii (s)
  :parents (printer)
  :short "Wrap an ASCII string literal as a @(tsee pdoc-text) leaf
          whose code-point list is computed at admission time."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('(pdoc-ascii \"Bool\")') expands at read time to
     @('(pdoc-text (quote (66 111 111 108)))'), so the code-point list
     is a compile-time constant rather than something rebuilt on every
     call.  The expansion happens by calling @(tsee
     ascii-string=>codepoints) on the literal string.")
   (xdoc::p
    "The macro signals a hard error at admission time if its argument
     is not a string literal, or if the string contains any character
     with code @('>= 128').  This prevents silently emitting bogus
     code points (which the previous string-leaved printer's
     byte-counting would have hidden).")
   (xdoc::p
    "For non-ASCII literal text, write the code points explicitly,
     e.g. @('(pdoc-text (quote (#x3A0)))') for capital pi.  For
     runtime UTF-8-byte-string input (e.g., identifier names from
     the AST), use @(tsee utf8-string=>codepoints)."))
  (cond ((not (stringp s))
         (er hard 'pdoc-ascii
             "Expected a string literal, got ~x0." s))
        ((not (char-list-all-ascii-p (explode s)))
         (er hard 'pdoc-ascii
             "String ~x0 contains a non-ASCII character (code >= 128). ~
              For non-ASCII text, pass code points explicitly via ~
              (pdoc-text '(...))." s))
        (t (let ((cps (ascii-string=>codepoints s)))
             `(pdoc-text (quote ,cps))))))

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

(fty::deftagsum mode
  :short "Layout mode for a sub-document."
  :long
  (xdoc::topstring
   (xdoc::p
    "@(':flat') means render @(':line') as a space; @(':break') means
     render @(':line') as a newline followed by the current indent.
     The mode is decided by the enclosing @(':group') and threaded
     down through @(':concat')/@(':nest') unchanged."))
  (:flat ())
  (:break ())
  :pred modep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cmd
  :short "A pending-document command: a pdoc plus its indent and mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee fits) and @(tsee layout) functions process a list of
     such commands rather than recursing directly on the @(tsee pdoc)
     tree.  This is the standard trick that lets one-line lookahead
     across @(':concat') boundaries terminate cleanly."))
  ((indent nat)
   (mode mode)
   (pdoc pdoc))
  :pred cmdp)

(fty::deflist cmd-list
  :short "List of pending commands."
  :elt-type cmd
  :true-listp t
  :elementp-of-nil nil
  :pred cmd-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Termination measure for fits and layout.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce size
  :short "A positive size for @(tsee pdoc) values, used as a measure
          for @(tsee pdoc)-recursing functions."
  :types (pdocs)
  :result posp
  :default 1
  :combine binary-+
  :override
  ((pdoc :concat (+ 1
                    (pdoc-size (pdoc-concat->left pdoc))
                    (pdoc-size (pdoc-concat->right pdoc))))
   (pdoc :nest (+ 1 (pdoc-size (pdoc-nest->body pdoc))))
   (pdoc :group (+ 1 (pdoc-size (pdoc-group->body pdoc)))))
  :name abstract-syntax-size)

(define cmds-size ((cs cmd-listp))
  :returns (n natp :rule-classes (:rewrite :type-prescription))
  :short "Sum of @(tsee pdoc-size) across a command list."
  (if (endp cs)
      0
    (+ (pdoc-size (cmd->pdoc (car cs)))
       (cmds-size (cdr cs))))
  ///
  (defrule cmds-size-of-cons
    (equal (cmds-size (cons c cs))
           (+ (pdoc-size (cmd->pdoc c)) (cmds-size cs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; fits: does the command list, rendered flat, fit in the remaining
;; w columns of the current line?  Stops as soon as it sees a forced
;; break or runs out of width.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fits ((w integerp) (cs cmd-listp))
  :returns (yes booleanp)
  :short "One-line lookahead used by @(tsee layout) to decide
          @(':group') flat-vs-break.  Column width is measured in
          code points (one code point per column), not UTF-8 bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "@(tsee fits) and @(tsee layout) use a simple, pragmatic model:
     one code point in a @(':text') leaf counts as one display column.
     This is exact for ASCII, Latin Extended, Greek, Cyrillic, Hebrew,
     Arabic, and every other Basic Multilingual Plane script whose
     code points are single non-combining glyphs.  It is more correct
     than UTF-8 byte counting for identifiers that contain such characters.")
   (xdoc::p
    "The code-point-per-column model is still wrong, in opposite
     directions, for the following Unicode features.  None of these has been
     seen in Remora source, but they are listed here for future reference:")
   (xdoc::ul
    (xdoc::li
     "@('East-Asian-Wide') and @('Fullwidth') characters (most CJK
      ideographs, fullwidth punctuation): one code point but two
      display columns.  The printer under-counts, so lines with these
      characters may overflow @('width') without breaking.")
    (xdoc::li
     "Combining marks (e.g. @('U+0301') COMBINING ACUTE ACCENT):
      one code point but zero columns&mdash;they attach to the
      preceding base character.  The printer over-counts.  Precomposed
      forms (NFC) avoid this.")
    (xdoc::li
     "Zero-width characters (@('U+200B') ZERO WIDTH SPACE, @('U+200D')
      ZERO WIDTH JOINER, variation selectors @('U+FE00')&ndash;@('U+FE0F'),
      bidi controls): one code point, zero columns.")
    (xdoc::li
     "Emoji ZWJ sequences (e.g. family glyphs, skin-tone modifiers):
      multiple code points that the renderer collapses into a single
      glyph of one or two display columns.  The printer over-counts
      by however many code points the sequence contains.")
    (xdoc::li
     "Hangul jamo sequences in their decomposed form: leading +
      vowel + (optional) trailing jamo render as one syllable block
      of two columns but parse as 2&ndash;3 code points."))
   (xdoc::p
    "A fully Unicode-aware width function would consult the East-Asian
     Width property (UAX #11) and the General_Category for combining
     marks.  Implementing that is straightforward but adds a
     property-table dependency that is unwarranted for current uses
     of the printer."))
  (b* (((when (< (ifix w) 0)) nil)
       ((when (endp cs)) t)
       (c (car cs))
       (rest (cdr cs))
       (i (cmd->indent c))
       (m (cmd->mode c))
       (d (cmd->pdoc c)))
    (pdoc-case d
      :text (fits (- (ifix w) (len d.cps)) rest)
      :line (mode-case m
              :flat (fits (- (ifix w) 1) rest)
              :break t)
      :hardline t
      :concat (fits w
                    (cons (make-cmd :indent i :mode m :pdoc d.left)
                          (cons (make-cmd :indent i :mode m :pdoc d.right)
                                rest)))
      :nest (fits w
                  (cons (make-cmd :indent (+ i d.amount) :mode m :pdoc d.body)
                        rest))
      :group (fits w
                   (cons (make-cmd :indent i
                                   :mode (mode-flat)
                                   :pdoc d.body)
                         rest))))
  :measure (cmds-size cs)
  :hints (("Goal" :in-theory (enable pdoc-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; layout: render a command list to a string, given a target width
;; and a current column.  Newlines are emitted as #\Newline followed
;; by the current indent in spaces.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define spaces-codepoints ((n natp))
  :returns (cps nat-listp)
  :hooks nil
  :short "A list of @('n') space code points (each @('#x20'))."
  (if (zp n)
      nil
    (cons #x20 (spaces-codepoints (- n 1)))))

(define newline-and-indent-codepoints ((n natp))
  :returns (cps nat-listp)
  :hooks nil
  :short "Newline (@('#x0A')) followed by @('n') spaces, as code points."
  (cons #x0A (spaces-codepoints n)))

(define layout ((width natp) (col natp) (cs cmd-listp))
  :returns (cps nat-listp)
  :short "Render a command list to a code-point list."
  (b* (((when (endp cs)) nil)
       (c (car cs))
       (rest (cdr cs))
       (i (cmd->indent c))
       (m (cmd->mode c))
       (d (cmd->pdoc c)))
    (pdoc-case d
      :text (append d.cps
                    (layout width
                            (+ (lnfix col) (len d.cps))
                            rest))
      :line (mode-case m
              :flat (cons #x20
                          (layout width (+ (lnfix col) 1) rest))
              :break (append (newline-and-indent-codepoints i)
                             (layout width i rest)))
      :hardline (append (newline-and-indent-codepoints i)
                        (layout width i rest))
      :concat (layout width col
                      (cons (make-cmd :indent i :mode m :pdoc d.left)
                            (cons (make-cmd :indent i :mode m :pdoc d.right)
                                  rest)))
      :nest (layout width col
                    (cons (make-cmd :indent (+ i d.amount)
                                    :mode m :pdoc d.body)
                          rest))
      :group (b* ((flat-cmds
                   (cons (make-cmd :indent i
                                   :mode (mode-flat)
                                   :pdoc d.body)
                         rest)))
               (if (fits (- (lnfix width) (lnfix col)) flat-cmds)
                   (layout width col flat-cmds)
                 (layout width col
                         (cons (make-cmd :indent i
                                         :mode (mode-break)
                                         :pdoc d.body)
                               rest))))))
  :measure (cmds-size cs)
  :hints (("Goal" :in-theory (enable pdoc-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define layout-pdoc ((width natp) (d pdocp))
  :returns (cps nat-listp)
  :short "Render a single @(tsee pdoc) to a code-point list at column 0."
  (layout width 0
          (list (make-cmd :indent 0 :mode (mode-break) :pdoc d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Convenience constructors.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pdoc-empty ()
  :returns (d pdocp)
  :short "The empty document."
  (pdoc-text nil))

(define pdoc-seq ((ds pdoc-listp))
  :returns (d pdocp)
  :short "Concatenate a list of documents into a single document
          (right-fold via @(tsee pdoc-concat))."
  :measure (len ds)
  (cond ((endp ds) (pdoc-empty))
        ((endp (cdr ds)) (pdoc-fix (car ds)))
        (t (pdoc-concat (car ds) (pdoc-seq (cdr ds))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Convenience wrappers for common pdoc shapes.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pdoc-paren ((d pdocp))
  :returns (out pdocp)
  :short "Wrap a document in parentheses (no break)."
  (pdoc-concat (pdoc-ascii "(")
               (pdoc-concat d (pdoc-ascii ")"))))

(define pdoc-bracket ((d pdocp))
  :returns (out pdocp)
  :short "Wrap a document in square brackets (no break)."
  (pdoc-concat (pdoc-ascii "[")
               (pdoc-concat d (pdoc-ascii "]"))))

(define pdoc-space ()
  :returns (out pdocp)
  :short "A single literal space."
  (pdoc-ascii " "))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Standard Lisp-form layouts.  These wrap the head of a form (a
;; keyword string or a head-document) plus a body so that, when the
;; group breaks, the body sits on a new line indented two columns
;; under the head.  Lines emitted inside the body are also at the
;; nested indent.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pdoc-prefix-form ((keyword stringp) (body pdocp))
  :returns (out pdocp)
  :short "Standard prefix form: @('(keyword body)') on one line if it
          fits, otherwise @('keyword') on one line and @('body')
          indented two columns on subsequent lines.  Use this for the
          fixed-keyword forms like @('let'), @('fn'), @('A'),
          @('Forall').  @('keyword') is expected to be ASCII."
  (pdoc-group
   (pdoc-paren
    (pdoc-concat
     (pdoc-text (ascii-string=>codepoints keyword))
     (pdoc-nest 2 (pdoc-concat (pdoc-line) body))))))

(define pdoc-call-form ((head pdocp) (args pdocp))
  :returns (out pdocp)
  :short "Standard call-style form: @('(head args)') on one line if
          it fits, otherwise @('head') on one line and @('args')
          indented two columns.  Use this when the head is itself a
          document (e.g., the function expression of an application),
          not a fixed keyword."
  (pdoc-group
   (pdoc-paren
    (pdoc-concat
     head
     (pdoc-nest 2 (pdoc-concat (pdoc-line) args))))))

(define pdoc-head-only-form ((head pdocp))
  :returns (out pdocp)
  :short "A parenthesized form with no body: just @('(head)').
          Used by @(tsee expr-app) and friends when the argument list
          is empty."
  (pdoc-paren head))

(define pdoc-naked-form ((keyword stringp))
  :returns (out pdocp)
  :short "Bare parenthesized form @('(keyword)') with no body or
          trailing whitespace.  Used by list-bodied forms like
          @('(dims)') / @('(++)') / @('(+)') when the list is empty;
          @(tsee pdoc-prefix-form) would insert a stray @(tsee
          pdoc-line) before nothing, leaving a trailing space inside
          the parens.  @('keyword') is expected to be ASCII."
  (pdoc-paren (pdoc-text (ascii-string=>codepoints keyword))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; AST → pdoc walkers.  Bottom-up: simple types first, then composite
;; types, then the mutually recursive expr/atom/bind clique.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Base types: Bool, Int, Float.
;;

(define base-type-to-pdoc ((bt base-typep))
  :returns (d pdocp)
  :short "Render a @(tsee base-type) as a pdoc."
  (base-type-case bt
    :bool (pdoc-ascii "Bool")
    :int (pdoc-ascii "Int")
    :float (pdoc-ascii "Float")))

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

(define base-lit-to-pdoc ((bl base-litp))
  :returns (d pdocp)
  :short "Render a @(tsee base-lit) as a pdoc."
  (base-lit-case bl
    :bool (if bl.lit (pdoc-ascii "#t") (pdoc-ascii "#f"))
    :int (pdoc-text (int-lit-to-codepoints bl.lit))
    :float (pdoc-text (float-lit-to-codepoints bl.lit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Variable types: ispace-var ($name or @name), type-var (&name or *name).
;;

(define ispace-var-to-pdoc ((iv ispace-varp))
  :returns (d pdocp)
  :short "Render an @(tsee ispace-var) as a pdoc.
          Dimension variables are prefixed with @('$'); shape variables
          with @('@')."
  (ispace-var-case iv
    :dim (pdoc-text (cons #x24 (utf8-string=>codepoints iv.name)))
    :shape (pdoc-text (cons #x40 (utf8-string=>codepoints iv.name)))))

(define type-var-to-pdoc ((tv type-varp))
  :returns (d pdocp)
  :short "Render a @(tsee type-var) as a pdoc.
          Atom-kinded variables are prefixed with @('&'); array-kinded
          variables with @('*')."
  (type-var-case tv
    :atom (pdoc-text (cons #x26 (utf8-string=>codepoints tv.name)))
    :array (pdoc-text (cons #x2A (utf8-string=>codepoints tv.name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; List helpers: pdoc-intersperse-space and pdoc-list-from-list.
;;

(define pdoc-intersperse-space ((ds pdoc-listp))
  :returns (out pdocp)
  :short "Concatenate documents with spaces between."
  (cond ((endp ds) (pdoc-empty))
        ((endp (cdr ds)) (pdoc-fix (car ds)))
        (t (pdoc-concat (car ds)
                        (pdoc-concat (pdoc-ascii " ")
                                     (pdoc-intersperse-space (cdr ds)))))))

(define pdoc-intersperse-line ((ds pdoc-listp))
  :returns (out pdocp)
  :short "Concatenate documents with @(tsee pdoc-line) between
          (becomes space when group fits, newline+indent when it
          breaks)."
  (cond ((endp ds) (pdoc-empty))
        ((endp (cdr ds)) (pdoc-fix (car ds)))
        (t (pdoc-concat (car ds)
                        (pdoc-concat (pdoc-line)
                                     (pdoc-intersperse-line (cdr ds)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Dimensions and shapes (mutually recursive via dim-list / shape-list).
;;

(defines dim-shape-to-pdoc
  :short "Render @(tsee dim) and @(tsee shape) values as pdocs."
  :verify-guards :after-returns

  (define dim-to-pdoc ((d dimp))
    :returns (out pdocp)
    (dim-case d
      :var (pdoc-text (cons #x24 (utf8-string=>codepoints d.name)))
      :const (pdoc-text (nat-to-dec-codepoints d.val))
      :add (if (consp d.dims)
               (pdoc-prefix-form "+" (dim-list-to-pdoc d.dims))
             (pdoc-naked-form "+"))
      :mul (if (consp d.dims)
               (pdoc-prefix-form "*" (dim-list-to-pdoc d.dims))
             (pdoc-naked-form "*"))
      :sub (if (consp d.dims)
               (pdoc-prefix-form "-" (dim-list-to-pdoc d.dims))
             (pdoc-naked-form "-")))
    :measure (dim-count d))

  (define dim-list-to-pdoc ((ds dim-listp))
    :returns (out pdocp)
    (cond ((endp ds) (pdoc-empty))
          ((endp (cdr ds)) (dim-to-pdoc (car ds)))
          (t (pdoc-concat (dim-to-pdoc (car ds))
                          (pdoc-concat (pdoc-line)
                                       (dim-list-to-pdoc (cdr ds))))))
    :measure (dim-list-count ds)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Flat-form string printers for dim and dim-list.  These produce the
;; canonical compact form (single-space separators, no line breaks) that
;; the parser accepts.  They are intended as round-trip-provable
;; alternatives to dim-to-pdoc / dim-list-to-pdoc when pretty-printing
;; layout flexibility is not needed.
;;

(defines dim-shape-to-string
  :short "Render @(tsee dim) and @(tsee dim-list) values as flat strings."
  :verify-guards :after-returns

  (define dim-to-string ((d dimp))
    :returns (s stringp)
    (dim-case d
      :var (str::cat "$" d.name)
      :const (str::nat-to-dec-string d.val)
      :add (str::cat "(+" (str::cat (dim-list-to-string d.dims) ")"))
      :mul (str::cat "(*" (str::cat (dim-list-to-string d.dims) ")"))
      :sub (str::cat "(-" (str::cat (dim-list-to-string d.dims) ")")))
    :measure (dim-count d))

  (define dim-list-to-string ((ds dim-listp))
    :returns (s stringp)
    :short "Render a @(tsee dim-list) as a flat string with each dim
            preceded by a single space (so the empty list yields the
            empty string, and a non-empty list looks like
            @(' d1 d2 ...')).  Used by @(tsee dim-to-string) inside the
            parens of @('+'), @('*'), and @('-') forms."
    (cond ((endp ds) "")
          (t (str::cat " "
                       (str::cat (dim-to-string (car ds))
                                 (dim-list-to-string (cdr ds))))))
    :measure (dim-list-count ds)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Shapes and ispaces (mutually recursive clique).
;;

(defines shape/ispace-to-pdoc-defs
  :short "Render @(tsee shape), @(tsee ispace), and their list versions
          as pdocs."
  :verify-guards :after-returns

  (define shape-to-pdoc ((s shapep))
    :returns (out pdocp)
    (shape-case s
      :var (pdoc-text (cons #x40 (utf8-string=>codepoints s.name)))
      :dims (if (consp s.dims)
                (pdoc-prefix-form "dims" (dim-list-to-pdoc s.dims))
              (pdoc-naked-form "dims"))
      :append (if (consp s.shapes)
                  (pdoc-prefix-form "++" (shape-list-to-pdoc s.shapes))
                (pdoc-naked-form "++"))
      :splice (pdoc-group
               (pdoc-bracket
                (ispace-list-to-pdoc s.ispaces))))
    :measure (shape-count s))

  (define shape-list-to-pdoc ((ss shape-listp))
    :returns (out pdocp)
    (cond ((endp ss) (pdoc-empty))
          ((endp (cdr ss)) (shape-to-pdoc (car ss)))
          (t (pdoc-concat (shape-to-pdoc (car ss))
                          (pdoc-concat (pdoc-line)
                                       (shape-list-to-pdoc (cdr ss))))))
    :measure (shape-list-count ss))

  (define ispace-to-pdoc ((i ispacep))
    :returns (out pdocp)
    (ispace-case i
                 :dim (dim-to-pdoc i.dim)
                 :shape (shape-to-pdoc i.shape))
    :measure (ispace-count i))

  (define ispace-list-to-pdoc ((is ispace-listp))
    :returns (out pdocp)
    (cond ((endp is) (pdoc-empty))
          ((endp (cdr is)) (ispace-to-pdoc (car is)))
          (t (pdoc-concat (ispace-to-pdoc (car is))
                          (pdoc-concat (pdoc-line)
                                       (ispace-list-to-pdoc (cdr is))))))
    :measure (ispace-list-count is)))

(define ispace-list-option-to-pdoc ((io ispace-list-optionp))
  :returns (out pdocp)
  :short "Render @(tsee ispace-list-option): @(':none') prints as
          @('_'), @(':some') prints as parenthesized list."
  (ispace-list-option-case io
    :none (pdoc-ascii "_")
    :some (pdoc-paren (ispace-list-to-pdoc io.val))))

(define ispace-var-list-to-pdoc ((ivs ispace-var-listp))
  :returns (out pdocp)
  (cond ((endp ivs) (pdoc-empty))
        ((endp (cdr ivs)) (ispace-var-to-pdoc (car ivs)))
        (t (pdoc-concat (ispace-var-to-pdoc (car ivs))
                        (pdoc-concat (pdoc-line)
                                     (ispace-var-list-to-pdoc (cdr ivs)))))))

(define ispace-var-list-option-to-pdoc ((io ispace-var-list-optionp))
  :returns (out pdocp)
  :short "Render @(tsee ispace-var-list-option): @(':none') prints as
          @('_'), @(':some') prints as parenthesized list."
  (ispace-var-list-option-case io
    :none (pdoc-ascii "_")
    :some (pdoc-paren (ispace-var-list-to-pdoc io.val))))

(define type-var-list-to-pdoc ((tvs type-var-listp))
  :returns (out pdocp)
  (cond ((endp tvs) (pdoc-empty))
        ((endp (cdr tvs)) (type-var-to-pdoc (car tvs)))
        (t (pdoc-concat (type-var-to-pdoc (car tvs))
                        (pdoc-concat (pdoc-line)
                                     (type-var-list-to-pdoc (cdr tvs)))))))

(define type-var-list-option-to-pdoc ((io type-var-list-optionp))
  :returns (out pdocp)
  :short "Render @(tsee type-var-list-option): @(':none') prints as
          @('_'), @(':some') prints as parenthesized list."
  (type-var-list-option-case io
    :none (pdoc-ascii "_")
    :some (pdoc-paren (type-var-list-to-pdoc io.val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Types (mutually recursive: type, type-list).
;;

(defines type-to-pdoc-defs
  :short "Render @(tsee type) and @(tsee type-list) values as pdocs."
  :verify-guards :after-returns

  (define type-to-pdoc ((ty typep))
    :returns (out pdocp)
    (type-case ty
      :var (type-var-to-pdoc ty.var)
      :base (base-type-to-pdoc ty.type)
      :array (pdoc-prefix-form
              "A"
              (pdoc-concat (type-to-pdoc ty.elem)
                           (pdoc-concat (pdoc-line)
                                        (ispace-to-pdoc ty.ispace))))
      :bracket (pdoc-group
                (pdoc-bracket
                 (pdoc-concat (type-to-pdoc ty.elem)
                              (pdoc-concat (pdoc-line)
                                           (ispace-list-to-pdoc ty.ispaces)))))
      :fun (pdoc-prefix-form
            "->"
            (pdoc-concat (pdoc-paren (type-list-to-pdoc ty.in))
                         (pdoc-concat (pdoc-line)
                                      (type-to-pdoc ty.out))))
      :foralln (pdoc-prefix-form
               "Forall"
               (pdoc-concat (pdoc-paren (type-var-list-to-pdoc ty.params))
                            (pdoc-concat (pdoc-line)
                                         (type-to-pdoc ty.body))))
      :pi (pdoc-prefix-form
           "Pi"
           (pdoc-concat (pdoc-paren (ispace-var-to-pdoc ty.param))
                        (pdoc-concat (pdoc-line)
                                     (type-to-pdoc ty.body))))
      :pin (pdoc-prefix-form
            "Pi"
            (pdoc-concat (pdoc-paren (ispace-var-list-to-pdoc ty.params))
                         (pdoc-concat (pdoc-line)
                                      (type-to-pdoc ty.body))))
      :sigma (pdoc-prefix-form
              "Sigma"
              (pdoc-concat (pdoc-paren (ispace-var-list-to-pdoc ty.params))
                           (pdoc-concat (pdoc-line)
                                        (type-to-pdoc ty.body)))))
    :measure (type-count ty))

  (define type-list-to-pdoc ((tys type-listp))
    :returns (out pdocp)
    (cond ((endp tys) (pdoc-empty))
          ((endp (cdr tys)) (type-to-pdoc (car tys)))
          (t (pdoc-concat (type-to-pdoc (car tys))
                          (pdoc-concat (pdoc-line)
                                       (type-list-to-pdoc (cdr tys))))))
    :measure (type-list-count tys)))

(define type-option-to-pdoc ((to type-optionp))
  :returns (out pdocp)
  :short "Render @(tsee type-option): @('nil') prints as empty,
          some-type prints as the type."
  (if to (type-to-pdoc to) (pdoc-empty)))

(define type-list-option-to-pdoc ((to type-list-optionp))
  :returns (out pdocp)
  :short "Render @(tsee type-list-option): @(':none') prints as
          @('_'), @(':some') prints as parenthesized list."
  (type-list-option-case to
    :none (pdoc-ascii "_")
    :some (pdoc-paren (type-list-to-pdoc to.val))))

(fty::defresult pdoc-result
  :short "Fixtype of pdocs and errors."
  :ok pdoc
  :pred pdoc-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pat-to-pdoc ((vt var+type?-p))
  :returns (out pdoc-resultp)
  :short "Render a @(tsee var+type?) as the @('pat') grammar form
          @('(name type)') &mdash; no colon."
  :long
  (xdoc::topstring
   (xdoc::p
    "The AST @(tsee var+type?) fixtype is used by both
     @(tsee atom-lambda)/@(tsee bind-fun)/@(tsee bind-cfun) parameter
     lists and (potentially) other binders.  In every case where it
     appears in our AST, the corresponding concrete syntax is the
     @('pat') rule of @('grammar.abnf'), namely @('\"(\" ws identifier
     ws type ws \")\"') &mdash; with no separating colon.")
   (xdoc::p
    "The type is optional in the AST, but the @('pat') grammar rule
     requires it, and we do not perform type inference yet.
     So, when the type is absent, we fail:
     there is no concrete syntax that renders it.")
   (xdoc::p
    "The colon-style @('name : type') form (@('val-typed-sig'),
     @('colon-type') in the grammar) is used in @(tsee bind-val) for
     the variable+type signature and in fun-style binders for the
     optional return type.  Both store the type as a separate
     @(tsee type-option) field rather than as a @(tsee var+type?), so
     they don't go through this function."))
  (b* ((type? (var+type?->type? vt)))
    (type-option-case
     type?
     :none (reserr (list :pat-without-type (var+type?->var vt)))
     :some (pdoc-paren
            (pdoc-concat
             (pdoc-text (utf8-string=>codepoints (var+type?->var vt)))
             (pdoc-concat (pdoc-ascii " ")
                          (type-to-pdoc type?.val)))))))

(define pat-list-to-pdoc ((vts var+type?-listp))
  :returns (out pdoc-resultp)
  :short "Render a list of @('pat') forms separated by soft lines."
  (cond ((endp vts) (pdoc-empty))
        ((endp (cdr vts)) (pat-to-pdoc (car vts)))
        (t (b* (((ok first) (pat-to-pdoc (car vts)))
                ((ok rest) (pat-list-to-pdoc (cdr vts))))
             (pdoc-concat first
                          (pdoc-concat (pdoc-line) rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Helpers for nat-list (array/frame shape literals).
;;

(define nat-list-to-pdoc ((ns nat-listp))
  :returns (out pdocp)
  :short "Render a list of nats as space-separated decimal strings."
  (cond ((endp ns) (pdoc-empty))
        ((endp (cdr ns)) (pdoc-text (nat-to-dec-codepoints (nfix (car ns)))))
        (t (pdoc-concat (pdoc-text (nat-to-dec-codepoints (nfix (car ns))))
                        (pdoc-concat (pdoc-line)
                                     (nat-list-to-pdoc (cdr ns)))))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Expressions, atoms, and bindings (mutually recursive clique).
;;

(defines exprs/atoms/binds-to-pdoc
  :short "Render @(tsee expr), @(tsee atom), @(tsee bind), and their
          list versions as pdocs."
  :verify-guards :after-returns

  (define expr-to-pdoc ((e exprp))
    :returns (out pdoc-resultp)
    (expr-case e
      :var (pdoc-text (utf8-string=>codepoints e.name))
      :atom (atom-to-pdoc e.atom)
      :array (b* (((ok atoms) (atom-list-to-pdoc e.atoms)))
               (pdoc-prefix-form
                "array"
                (pdoc-concat (pdoc-bracket (nat-list-to-pdoc e.dims))
                             (pdoc-concat (pdoc-line) atoms))))
      :array-empty (pdoc-prefix-form
                    "array"
                    (pdoc-concat (pdoc-bracket (nat-list-to-pdoc e.dims))
                                 (pdoc-concat (pdoc-line)
                                              (type-to-pdoc e.type))))
      :frame (b* (((ok exprs) (expr-list-to-pdoc e.exprs)))
               (pdoc-prefix-form
                "frame"
                (pdoc-concat (pdoc-bracket (nat-list-to-pdoc e.dims))
                             (pdoc-concat (pdoc-line) exprs))))
      :frame-empty (pdoc-prefix-form
                    "frame"
                    (pdoc-concat (pdoc-bracket (nat-list-to-pdoc e.dims))
                                 (pdoc-concat (pdoc-line)
                                              (type-to-pdoc e.type))))
      :string (pdoc-text (string-lit-to-codepoints e.chars))
      :app (b* (((ok fun) (expr-to-pdoc e.fun)))
             (if (consp e.args)
                 (b* (((ok args) (expr-list-to-pdoc e.args)))
                   (pdoc-call-form fun args))
               (pdoc-head-only-form fun)))
      :tapp (b* (((ok fun) (expr-to-pdoc e.fun)))
              (pdoc-prefix-form
               "t-app"
               (pdoc-concat fun
                            (pdoc-concat (pdoc-line)
                                         (type-to-pdoc e.arg)))))
      :tappn (b* (((ok fun) (expr-to-pdoc e.fun)))
               (pdoc-prefix-form
                "t-app"
                (pdoc-concat fun
                             (if (consp e.args)
                                 (pdoc-concat (pdoc-line)
                                              (type-list-to-pdoc e.args))
                               (pdoc-empty)))))
      :iapp (b* (((ok fun) (expr-to-pdoc e.fun)))
              (pdoc-prefix-form
               "i-app"
               (pdoc-concat fun
                            (pdoc-concat (pdoc-line)
                                         (ispace-to-pdoc e.arg)))))
      :iappn (b* (((ok fun) (expr-to-pdoc e.fun)))
               (pdoc-prefix-form
                "i-app"
                (pdoc-concat fun
                             (if (consp e.args)
                                 (pdoc-concat (pdoc-line)
                                              (ispace-list-to-pdoc e.args))
                               (pdoc-empty)))))
      :capp (b* (((ok fun) (expr-to-pdoc e.fun))
                 ((ok args-doc)
                  (if (consp e.args)
                      (b* (((ok args) (expr-list-to-pdoc e.args)))
                        (pdoc-concat (pdoc-line) args))
                    (pdoc-empty))))
              (pdoc-prefix-form
               "@"
               (pdoc-concat
                fun
                (pdoc-concat
                 (pdoc-line)
                 (pdoc-concat
                  (type-list-option-to-pdoc e.targs)
                  (pdoc-concat
                   (pdoc-line)
                   (pdoc-concat
                    (ispace-list-option-to-pdoc e.iargs)
                    args-doc)))))))
      :unbox
      ;; Surface form (grammar unbox-spec):
      ;;   *( ispace-var ws ) identifier ws exp
      ;; The optional result type (e.type?) has no concrete syntax,
      ;; so it is not printed.
      ;; Suppress the leading pdoc-line / ispaces-doc when there are
      ;; zero ispace-vars; otherwise we get a stray space inside the
      ;; spec paren ("(unbox ( v target) body)").
      (b* ((ispaces-prefix (if (consp e.ispaces)
                               (pdoc-concat (ispace-var-list-to-pdoc e.ispaces)
                                            (pdoc-line))
                             (pdoc-empty)))
           ((ok target) (expr-to-pdoc e.target))
           ((ok body) (expr-to-pdoc e.body)))
        (pdoc-prefix-form
         "unbox"
         (pdoc-concat
          (pdoc-paren
           (pdoc-concat ispaces-prefix
                        (pdoc-concat (pdoc-text (utf8-string=>codepoints e.var))
                                     (pdoc-concat (pdoc-line) target))))
          (pdoc-concat (pdoc-line) body))))
      :bracket (b* (((ok exprs) (expr-list-to-pdoc e.exprs)))
                 (pdoc-group (pdoc-bracket exprs)))
      :let (b* (((ok binds) (bind-list-to-pdoc e.binds))
                ((ok body) (expr-to-pdoc e.body)))
             (pdoc-prefix-form
              "let"
              (pdoc-concat (pdoc-paren binds)
                           (pdoc-concat (pdoc-line) body)))))
    :measure (expr-count e))

  (define expr-list-to-pdoc ((es expr-listp))
    :returns (out pdoc-resultp)
    (cond ((endp es) (pdoc-empty))
          ((endp (cdr es)) (expr-to-pdoc (car es)))
          (t (b* (((ok first) (expr-to-pdoc (car es)))
                  ((ok rest) (expr-list-to-pdoc (cdr es))))
               (pdoc-concat first
                            (pdoc-concat (pdoc-line) rest)))))
    :measure (expr-list-count es))

  (define atom-to-pdoc ((a atomp))
    :returns (out pdoc-resultp)
    (atom-case a
      :base (base-lit-to-pdoc a.lit)
      ;; We do not print the optional body type (a.type?):
      ;; it has no concrete syntax (it is computed by type checking).
      :lambda (b* (((ok params) (pat-list-to-pdoc a.params))
                   ((ok body) (expr-to-pdoc a.body)))
                (pdoc-prefix-form
                 "fn"
                 (pdoc-concat (pdoc-paren params)
                              (pdoc-concat (pdoc-line) body))))
      :tlambda (b* (((ok body) (expr-to-pdoc a.body)))
                 (pdoc-prefix-form
                  "t-fn"
                  (pdoc-concat (pdoc-paren (type-var-to-pdoc a.param))
                               (pdoc-concat (pdoc-line) body))))
      :tlambdan (b* (((ok body) (expr-to-pdoc a.body)))
                  (pdoc-prefix-form
                   "t-fn"
                   (pdoc-concat (pdoc-paren (type-var-list-to-pdoc a.params))
                                (pdoc-concat (pdoc-line) body))))
      :ilambda (b* (((ok body) (expr-to-pdoc a.body)))
                 (pdoc-prefix-form
                  "i-fn"
                  (pdoc-concat (pdoc-paren (ispace-var-to-pdoc a.param))
                               (pdoc-concat (pdoc-line) body))))
      :ilambdan (b* (((ok body) (expr-to-pdoc a.body)))
                  (pdoc-prefix-form
                   "i-fn"
                   (pdoc-concat (pdoc-paren (ispace-var-list-to-pdoc a.params))
                                (pdoc-concat (pdoc-line) body))))
      :box (b* (((ok array) (expr-to-pdoc a.array)))
             (pdoc-prefix-form
              "box"
              (pdoc-concat
               (pdoc-paren (ispace-list-to-pdoc a.ispaces))
               (pdoc-concat
                (pdoc-line)
                (pdoc-concat
                 array
                 (pdoc-concat (pdoc-line)
                              (type-to-pdoc a.type))))))))
    :measure (atom-count a))

  (define atom-list-to-pdoc ((as atom-listp))
    :returns (out pdoc-resultp)
    (cond ((endp as) (pdoc-empty))
          ((endp (cdr as)) (atom-to-pdoc (car as)))
          (t (b* (((ok first) (atom-to-pdoc (car as)))
                  ((ok rest) (atom-list-to-pdoc (cdr as))))
               (pdoc-concat first
                            (pdoc-concat (pdoc-line) rest)))))
    :measure (atom-list-count as))

  (define bind-to-pdoc ((b bindp))
    :returns (out pdoc-resultp)
    (bind-case b
      :ispace (pdoc-paren
               (pdoc-concat (pdoc-ascii "ispace")
                            (pdoc-concat (pdoc-ascii " ")
                                         (pdoc-concat
                                          (ispace-var-to-pdoc b.var)
                                          (pdoc-concat (pdoc-ascii " ")
                                                       (ispace-to-pdoc b.ispace))))))
      :type (pdoc-paren
             (pdoc-concat (pdoc-ascii "type")
                          (pdoc-concat (pdoc-ascii " ")
                                       (pdoc-concat
                                        (type-var-to-pdoc b.var)
                                        (pdoc-concat (pdoc-ascii " ")
                                                     (type-to-pdoc b.type))))))
      :val
      ;; Two surface forms (grammar val-bind):
      ;;   "val" identifier exp                     -- when type? is :none
      ;;   "val" "(" val-typed-sig ")" exp          -- when type? is :some
      (b* ((sig-doc
            (type-option-case b.type?
              :some (pdoc-paren
                     (pdoc-concat (pdoc-text (utf8-string=>codepoints b.var))
                                  (pdoc-concat (pdoc-ascii " : ")
                                               (type-to-pdoc b.type?.val))))
              :none (pdoc-text (utf8-string=>codepoints b.var))))
           ((ok expr) (expr-to-pdoc b.expr)))
        (pdoc-prefix-form
         "val"
         (pdoc-concat sig-doc
                      (pdoc-concat (pdoc-line) expr))))
      :fun
      ;; Surface form (grammar fun-bind):
      ;;   "fun" "(" identifier *( ws pat ) [ ws colon-type ] ")" exp
      ;; The whole signature is parenthesized.
      (b* ((type-suffix (type-option-case b.type?
                          :some (pdoc-concat (pdoc-ascii " : ")
                                             (type-to-pdoc b.type?.val))
                          :none (pdoc-empty)))
           ((ok params-doc) (if (consp b.params)
                                (b* (((ok params) (pat-list-to-pdoc b.params)))
                                  (pdoc-concat (pdoc-line) params))
                              (pdoc-empty)))
           ((ok expr) (expr-to-pdoc b.expr))
           (sig-doc (pdoc-paren
                     (pdoc-concat (pdoc-text (utf8-string=>codepoints b.var))
                                  (pdoc-concat params-doc type-suffix)))))
        (pdoc-prefix-form
         "fun"
         (pdoc-concat sig-doc
                      (pdoc-concat (pdoc-line) expr))))
      :tfun
      ;; Surface form (grammar tfun-bind):
      ;;   "t-fun" "(" identifier "(" *( ws type-var ) ")" [ ws colon-type ] ")" exp
      (b* ((type-suffix (type-option-case b.type?
                          :some (pdoc-concat (pdoc-ascii " : ")
                                             (type-to-pdoc b.type?.val))
                          :none (pdoc-empty)))
           ((ok expr) (expr-to-pdoc b.expr))
           (sig-doc (pdoc-paren
                     (pdoc-concat
                      (pdoc-text (utf8-string=>codepoints b.var))
                      (pdoc-concat
                       (pdoc-line)
                       (pdoc-concat
                        (pdoc-paren (type-var-list-to-pdoc b.params))
                        type-suffix))))))
        (pdoc-prefix-form
         "t-fun"
         (pdoc-concat sig-doc
                      (pdoc-concat (pdoc-line) expr))))
      :ifun
      ;; Surface form (grammar ifun-bind):
      ;;   "i-fun" "(" identifier "(" *( ws ispace-var ) ")" [ ws colon-type ] ")" exp
      (b* ((type-suffix (type-option-case b.type?
                          :some (pdoc-concat (pdoc-ascii " : ")
                                             (type-to-pdoc b.type?.val))
                          :none (pdoc-empty)))
           ((ok expr) (expr-to-pdoc b.expr))
           (sig-doc (pdoc-paren
                     (pdoc-concat
                      (pdoc-text (utf8-string=>codepoints b.var))
                      (pdoc-concat
                       (pdoc-line)
                       (pdoc-concat
                        (pdoc-paren (ispace-var-list-to-pdoc b.params))
                        type-suffix))))))
        (pdoc-prefix-form
         "i-fun"
         (pdoc-concat sig-doc
                      (pdoc-concat (pdoc-line) expr))))
      :cfun
      ;; Surface form (grammar at-fun-bind / at-fun-sig):
      ;;   "fun" "(" "@" identifier type-vars ispace-vars *( ws pat ) ws colon-type ")" exp
      ;; Keyword is "fun" (the "@" lives inside the sig).  type-vars and
      ;; ispace-vars are each either "(" *( ws v ) ")" or "_".
      ;; colon-type is mandatory here.
      (b* (((ok params-doc) (if (consp b.params)
                                (b* (((ok params) (pat-list-to-pdoc b.params)))
                                  (pdoc-concat (pdoc-line) params))
                              (pdoc-empty)))
           ((ok expr) (expr-to-pdoc b.expr))
           (sig-doc (pdoc-paren
                     (pdoc-concat
                      (pdoc-ascii "@")
                      (pdoc-concat
                       (pdoc-line)
                       (pdoc-concat
                        (pdoc-text (utf8-string=>codepoints b.var))
                        (pdoc-concat
                         (pdoc-line)
                         (pdoc-concat
                          (type-var-list-option-to-pdoc b.tparams?)
                          (pdoc-concat
                           (pdoc-line)
                           (pdoc-concat
                            (ispace-var-list-option-to-pdoc b.iparams?)
                            (pdoc-concat
                             params-doc
                             (pdoc-concat
                              (pdoc-ascii " : ")
                              (type-to-pdoc b.type)))))))))))))
        (pdoc-prefix-form
         "fun"
         (pdoc-concat sig-doc
                      (pdoc-concat (pdoc-line) expr)))))
    :measure (bind-count b))

  (define bind-list-to-pdoc ((bs bind-listp))
    :returns (out pdoc-resultp)
    (cond ((endp bs) (pdoc-empty))
          ((endp (cdr bs)) (bind-to-pdoc (car bs)))
          (t (b* (((ok first) (bind-to-pdoc (car bs)))
                  ((ok rest) (bind-list-to-pdoc (cdr bs))))
               (pdoc-concat first
                            (pdoc-concat (pdoc-line) rest)))))
    :measure (bind-list-count bs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Standalone expressions: top-level printing entry points.
;;

(define print-expr-to-codepoints ((e exprp) &key ((width natp) '80))
  :returns (cps nat-listp)
  :short "Render an @(tsee expr) AST to a list of Unicode code points,
          wrapping at @('width') columns.  This is the codepoint-level
          entry point; @(tsee print-expr) is the string wrapper."
  :long
  (xdoc::topstring
   (xdoc::p
    "If rendering fails (e.g. a parameter has no type, which has no
     concrete syntax and which we do not infer yet), we return the
     empty list of code points, so that @(tsee print-expr) is total
     and yields the empty string in that case."))
  (b* ((pd (expr-to-pdoc e))
       ((when (reserrp pd)) nil))
    (layout-pdoc width pd)))

(define print-expr ((e exprp) &key ((width natp) '80))
  :returns (s stringp)
  :short "Render an @(tsee expr) AST (a standalone expression) to a
          UTF-8 encoded ACL2 string, wrapping at @('width') columns.
          Thin wrapper around @(tsee print-expr-to-codepoints) that
          UTF-8-encodes the code-point list into bytes and packs the
          bytes into an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "The defensive @(tsee ustring?) check guarantees the guard
     of @(tsee ustring=>utf8); for well-formed ASTs all emitted
     code points are valid Unicode scalars, so the @('unless') branch
     is unreachable."))
  (b* ((cps (print-expr-to-codepoints e :width width))
       ((unless (ustring? cps)) "")
       (bytes (ustring=>utf8 cps))
       ((unless (unsigned-byte-listp 8 bytes)) ""))
    (nats=>string bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Imports, declarations, and source files.
;;

(define import-to-pdoc ((imp importp))
  :returns (out pdocp)
  :short "Render an @(tsee import) as a pdoc."
  (pdoc-prefix-form
   "import"
   (pdoc-text (string-lit-to-codepoints (import->path imp)))))

(define import-list-to-pdoc ((imps import-listp))
  :returns (out pdocp)
  :short "Render an @(tsee import-list) as a pdoc,
          one import per line."
  (cond ((endp imps) (pdoc-empty))
        ((endp (cdr imps)) (import-to-pdoc (car imps)))
        (t (pdoc-concat (import-to-pdoc (car imps))
                        (pdoc-concat (pdoc-line)
                                     (import-list-to-pdoc (cdr imps)))))))

(define decl-to-pdoc ((d declp))
  :returns (out pdoc-resultp)
  :short "Render a @(tsee decl) as a pdoc."
  (decl-case d
    ;; Surface form (grammar def-decl):
    ;;   "def" ws bind
    :def
    (b* (((ok b-doc) (bind-to-pdoc d.bind)))
      (pdoc-prefix-form
       "def"
       b-doc))
    ;; Surface form (grammar entry-decl):
    ;;   "entry" ws "(" ws fun-sig ws ")" ws exp
    ;; Same signature shape as a fun binding's; see the :fun case of
    ;; @(tsee bind-to-pdoc), which this mirrors.
    :entry
    (b* ((type-suffix (type-option-case d.type?
                        :some (pdoc-concat (pdoc-ascii " : ")
                                           (type-to-pdoc d.type?.val))
                        :none (pdoc-empty)))
         ((ok params-doc) (if (consp d.params)
                              (b* (((ok params) (pat-list-to-pdoc d.params)))
                                (pdoc-concat (pdoc-line) params))
                            (pdoc-empty)))
         ((ok expr) (expr-to-pdoc d.expr))
         (sig-doc (pdoc-paren
                   (pdoc-concat (pdoc-text (utf8-string=>codepoints d.var))
                                (pdoc-concat params-doc type-suffix)))))
      (pdoc-prefix-form
       "entry"
       (pdoc-concat sig-doc
                    (pdoc-concat (pdoc-line) expr))))))

(define decl-list-to-pdoc ((ds decl-listp))
  :returns (out pdoc-resultp)
  :short "Render a @(tsee decl-list) as a pdoc,
          one declaration per line."
  (cond ((endp ds) (pdoc-empty))
        ((endp (cdr ds)) (decl-to-pdoc (car ds)))
        (t (b* (((ok first) (decl-to-pdoc (car ds)))
                ((ok rest) (decl-list-to-pdoc (cdr ds))))
             (pdoc-concat first
                          (pdoc-concat (pdoc-line) rest))))))

(define file-to-pdoc ((f filep))
  :returns (out pdoc-resultp)
  :short "Render a @(tsee file) (source file) as a pdoc:
          the imports, then the declarations, one per line."
  (b* (((file f) f)
       ((ok decls-doc) (if (consp f.decls)
                           (decl-list-to-pdoc f.decls)
                         (pdoc-empty))))
    (cond ((not (consp f.imports)) decls-doc)
          ((not (consp f.decls)) (import-list-to-pdoc f.imports))
          (t (pdoc-concat (import-list-to-pdoc f.imports)
                          (pdoc-concat (pdoc-line) decls-doc))))))

(define print-file-to-codepoints ((f filep) &key ((width natp) '80))
  :returns (cps nat-listp)
  :short "Render a @(tsee file) AST to a list of Unicode code points,
          wrapping at @('width') columns.  This is the codepoint-level
          entry point; @(tsee print-file) is the string wrapper."
  :long
  (xdoc::topstring
   (xdoc::p
    "If rendering fails (e.g. a parameter has no type, which has no
     concrete syntax and which we do not infer yet), we return the
     empty list of code points, so that @(tsee print-file) is total
     and yields the empty string in that case."))
  (b* ((pd (file-to-pdoc f))
       ((when (reserrp pd)) nil))
    (layout-pdoc width pd)))

(define print-file ((f filep) &key ((width natp) '80))
  :returns (s stringp)
  :short "Render a @(tsee file) AST to a UTF-8 encoded ACL2 string,
          wrapping at @('width') columns.  Thin wrapper around
          @(tsee print-file-to-codepoints), like @(tsee print-expr)
          is around @(tsee print-expr-to-codepoints)."
  (b* ((cps (print-file-to-codepoints f :width width))
       ((unless (ustring? cps)) "")
       (bytes (ustring=>utf8 cps))
       ((unless (unsigned-byte-listp 8 bytes)) ""))
    (nats=>string bytes)))
