; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "printer-tokens")
(include-book "abstract-syntax-well-formedness")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/strings/ascii-chars" :dir :system)
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
;; Documents: pdoc combinators (Wadler/Lindig style).
;;
;; A pdoc is a tree of layout instructions, which the layout function
;; below turns into code points.
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

(fty::defresult pdoc-result
  :short "Fixtype of pdocs and errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "The AST walkers that can fail return this type.  They fail when an
     optional part of the AST is absent but the concrete syntax
     requires it, e.g. the type of a parameter (see @(tsee
     pat-to-pdoc))."))
  :ok pdoc
  :pred pdoc-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The pdoc :text leaf carries a nat-list of code points (not a string);
;; see @(see printer-tokens) for how text of the three kinds (ASCII
;; literals, identifiers, literals) is converted to code points.  ASCII
;; literals in the printer source use the @(tsee pdoc-ascii) macro.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
        ((not (str::ascii-charlist-p (explode s)))
         (er hard 'pdoc-ascii
             "String ~x0 contains a non-ASCII character (code >= 128). ~
              For non-ASCII text, pass code points explicitly via ~
              (pdoc-text '(...))." s))
        (t (let ((cps (ascii-string=>codepoints s)))
             `(pdoc-text (quote ,cps))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Layout.
;;
;; The layout function recursively interprets a pdoc, choosing for
;; each Group whether to render it flat (all on one line) or broken
;; (Lines become newlines with indent).  The Group decision uses
;; one-line lookahead via the auxiliary fits function.
;;
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
  :name pdoc-size-measure)

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
;; layout: render a command list to a code-point list, given a target
;; width and a current column.  Newlines are emitted as #x0A followed
;; by the current indent in spaces.
;;

(define spaces-codepoints ((n natp))
  :returns (cps nat-listp)
  :short "A list of @('n') space code points (each @('#x20'))."
  (if (zp n)
      nil
    (cons #x20 (spaces-codepoints (- n 1)))))

(define newline-and-indent-codepoints ((n natp))
  :returns (cps nat-listp)
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

(define layout-pdoc ((width natp) (d pdocp))
  :returns (cps nat-listp)
  :short "Render a single @(tsee pdoc) to a code-point list at column 0."
  (layout width 0
          (list (make-cmd :indent 0 :mode (mode-break) :pdoc d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Document building blocks.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pdoc-empty ()
  :returns (d pdocp)
  :short "The empty document."
  (pdoc-text nil))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Standard Lisp-form layouts.  These wrap the head of a form (a
;; keyword string or a head-document) plus a body so that, when the
;; group breaks, the body sits on a new line indented two columns
;; under the head.  Lines emitted inside the body are also at the
;; nested indent.
;;

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
          Used by @(tsee expr-appn) and friends when the argument list
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
;; Base types (Bool, Int, Float) and base literals.
;;

(define base-type-to-pdoc ((bt base-typep))
  :returns (d pdocp)
  :short "Render a @(tsee base-type) as a pdoc."
  (base-type-case bt
    :bool (pdoc-ascii "Bool")
    :int (pdoc-ascii "Int")
    :float (pdoc-ascii "Float")))

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
;; Dimensions (mutually recursive: dim, dim-list), and the lists of
;; naturals that give the dimensions of array and frame expressions.
;;

(defines dim-to-pdoc-defs
  :short "Render @(tsee dim) and @(tsee dim-list) values as pdocs."
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Lists of variables, and optional lists (printed as _ when absent).
;;

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
            (pdoc-concat (type-to-pdoc ty.in)
                         (pdoc-concat (pdoc-line)
                                      (type-to-pdoc ty.out))))
      :funn (pdoc-prefix-form
             "->"
             (pdoc-concat (pdoc-paren (type-list-to-pdoc ty.in))
                          (pdoc-concat (pdoc-line)
                                       (type-to-pdoc ty.out))))
      :forall (pdoc-prefix-form
               "Forall"
               (pdoc-concat (pdoc-paren (type-var-to-pdoc ty.param))
                            (pdoc-concat (pdoc-line)
                                         (type-to-pdoc ty.body))))
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
              (pdoc-concat (pdoc-paren (ispace-var-to-pdoc ty.param))
                           (pdoc-concat (pdoc-line)
                                        (type-to-pdoc ty.body))))
      :sigman (pdoc-prefix-form
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Patterns (typed parameters).
;;

(define pat-to-pdoc ((vt var+type?-p))
  :returns (out pdoc-resultp)
  :short "Render a @(tsee var+type?) as the @('pat') grammar form
          @('(name type)') &mdash; no colon."
  :long
  (xdoc::topstring
   (xdoc::p
    "The AST @(tsee var+type?) fixtype is used by both
     @(tsee atom-lambdan)/@(tsee bind-fun)/@(tsee bind-cfun) parameter
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
      :app (b* (((ok fun) (expr-to-pdoc e.fun))
                ((ok arg) (expr-to-pdoc e.arg)))
             (pdoc-call-form fun arg))
      :appn (b* (((ok fun) (expr-to-pdoc e.fun)))
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
      :capp
      ;; Surface form (grammar at-app-exp):
      ;;   "@" exp ws type-args ws ispace-args *( ws exp )
      ;; The "@" is a prefix of the function expression, not a separate
      ;; head: it is written against it, with no space and no opportunity
      ;; to break the line between them.  So the head of the call form is
      ;; the "@" and the function concatenated, as in the :cfun sig.
      (b* (((ok fun) (expr-to-pdoc e.fun))
           ((ok args-doc)
            (if (consp e.args)
                (b* (((ok args) (expr-list-to-pdoc e.args)))
                  (pdoc-concat (pdoc-line) args))
              (pdoc-empty))))
        (pdoc-call-form
         (pdoc-concat (pdoc-ascii "@") fun)
         (pdoc-concat
          (type-list-option-to-pdoc e.targs)
          (pdoc-concat
           (pdoc-line)
           (pdoc-concat
            (ispace-list-option-to-pdoc e.iargs)
            args-doc)))))
      :unbox
      ;; Surface form (grammar unbox-spec):
      ;;   *( ispace-var ws ) identifier ws exp
      ;; The optional result type (e.type?) has no concrete syntax,
      ;; so it is not printed.
      ;; A unary unbox always has exactly one ispace var.
      (b* ((ispaces-prefix (pdoc-concat (ispace-var-list-to-pdoc
                                         (list e.ispace))
                                        (pdoc-line)))
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
      :unboxn
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
      :lambda (b* (((ok pat) (pat-to-pdoc a.param))
                   ((ok body) (expr-to-pdoc a.body)))
                (pdoc-prefix-form
                 "fn"
                 (pdoc-concat (pdoc-paren pat)
                              (pdoc-concat (pdoc-line) body))))
      :lambdan (b* (((ok params) (pat-list-to-pdoc a.params))
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
      ;; The box-expr grammar rule requires the type,
      ;; so we fail when the optional type is absent,
      ;; in both the unary and the n-ary form:
      ;; there is no concrete syntax that renders it.
      :box (type-option-case
            a.type?
            :none (reserr (list :box-without-type (atom-fix a)))
            :some (b* (((ok array) (expr-to-pdoc a.array)))
                    (pdoc-prefix-form
                     "box"
                     (pdoc-concat
                      (pdoc-paren (ispace-to-pdoc a.ispace))
                      (pdoc-concat
                       (pdoc-line)
                       (pdoc-concat
                        array
                        (pdoc-concat (pdoc-line)
                                     (type-to-pdoc a.type?.val))))))))
      :boxn (type-option-case
             a.type?
             :none (reserr (list :box-without-type (atom-fix a)))
             :some (b* (((ok array) (expr-to-pdoc a.array)))
                     (pdoc-prefix-form
                      "box"
                      (pdoc-concat
                       (pdoc-paren (ispace-list-to-pdoc a.ispaces))
                       (pdoc-concat
                        (pdoc-line)
                        (pdoc-concat
                         array
                         (pdoc-concat (pdoc-line)
                                      (type-to-pdoc a.type?.val)))))))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Entry points: standalone expressions and source files.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
