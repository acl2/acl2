; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

;; We reuse the token-level helpers of the pdoc-based printer (code-point
;; conversion of identifiers, numeric literals, string literals with their
;; disambiguating empty escapes, etc.).  Only the layout engine and the
;; AST walkers are new here.
(include-book "printer")

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pretty-printer
  :parents (parsing-and-printing)
  :short "A pretty-printer of Remora from the abstract syntax,
          in the style of the ACL2 prettyprinter (@('ppr1')/@('ppr2'))."
  :long
  (xdoc::topstring
   (xdoc::p "
 @({
 (pretty-print-file f :width 80 :flat-margin 60)
 (pretty-print-expr e :width 80 :flat-margin 60)
 })
 ")
   (xdoc::p
    "This is an alternative to the Wadler/Lindig-style @(see printer).
     That printer makes a one-line-lookahead decision at each group:
     either the whole group fits flat on the rest of the line, or
     @('every') soft line in it breaks.  The result tends to be either
     very wide or very tall.  ACL2's own prettyprinter (see the functions
     @('ppr1') and @('ppr2') in the ACL2 sources, file @('basis-a.lisp'))
     instead works bottom-up: it first lays out every subterm in the
     available width, records the width of the result, and then chooses,
     for the enclosing form, among several layouts based on the widths of
     the pieces.  We port that algorithm to a purely functional setting
     over a small language-neutral tree of print forms.")
   (xdoc::p
    "The pipeline is:")
   (xdoc::ol
    (xdoc::li
     "@(tsee expr-to-pform), @(tsee file-to-pforms), etc. map the AST
      to @(tsee pform)s, which are just atoms (token text), prefixed
      forms (a piece of text glued to a form, like @('@f') or
      @(': Int')), and bracketed lists of forms, each list optionally
      marked as a `special' form whose first @('n') arguments belong to
      the header line (as @('let') bindings or a @('fn') parameter list
      do).")
    (xdoc::li
     "@(tsee pform-to-ptuple) is the port of @('ppr1'): it chooses a
      layout for a form within a given width and returns a @(tsee
      ptuple) that records the choice together with the resulting
      width.  Lists of forms are assembled bottom-up by @(tsee
      pform-list-to-ptuples) and @(tsee cons-ptuple), the ports of
      @('ppr1-lst') and @('cons-ppr1'), which pack short atomic forms
      into rows.")
    (xdoc::li
     "@(tsee ptuple-print) is the port of @('ppr2'): it renders a
      tuple to code points, given the column at which it starts."))
   (xdoc::p
    "The available layouts for a list @('(head arg1 ... argn)') are:")
   (xdoc::ul
    (xdoc::li
     "@(':flat') &mdash; all on one line, if that fits both in the
      remaining width and within the @('flat-margin') (the analogue of
      ACL2's @('ppr-flat-right-margin'), default 60).  The flat margin
      keeps long flat forms from running all the way to the right
      margin, which makes structure easier to see.")
    (xdoc::li
     "@(':wide') &mdash; @('(head arg1') on the first line, with the
      remaining arguments in a column aligned under @('arg1').")
    (xdoc::li
     "@(':indent') &mdash; @('(head') on the first line, all arguments
      in a column indented by @('k'), where @('k') is chosen (up to 5)
      so that the widest argument ends as close as possible to the
      right margin.  Also used, with @('k = 1'), when the head is not
      atomic (e.g. an application of a lambda).")
    (xdoc::li
     "@(':special') &mdash; for @('let'), @('fn'), @('fun'),
      @('Forall'), @('unbox'), etc.: the header arguments go on the
      first line (or, if they do not fit, on their own lines), and the
      body arguments follow in a column indented by 2.  Unlike ACL2,
      the scoping forms (@('let'), @('fn'), function bindings,
      @('entry'), ...) are never printed flat: their body always starts
      on a new line, as one would write them by hand."))
   (xdoc::p
    "Widths include the right parentheses that will follow a form on its
     last line (the @('rpc') argument), as in @('ppr1'), so that closing
     brackets never push a line past the margin.  Column width is
     measured in code points, as in the @(see printer)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Print forms: the language-neutral input of the layout engine.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes pforms
  :short "Print forms: the tree the layout engine works on."

  (fty::deftagsum pform
    :parents (pretty-printer pforms)
    :short "A print form: an atom, a prefixed form, or a bracketed list."
    :long
    (xdoc::topstring
     (xdoc::ul
      (xdoc::li
       "@(':atom') &mdash; token text (as code points), printed as is.")
      (xdoc::li
       "@(':prefix') &mdash; text glued in front of a form, with no
        space and no possible line break between them; e.g. the @('@')
        of an @('@f') call whose function is a compound expression, or
        the @(': ') of a type ascription.  If the body breaks across
        lines, its continuation lines are laid out relative to the
        column after the prefix.")
      (xdoc::li
       "@(':list') &mdash; a list of forms between @('open') and
        @('close') brackets (code points, e.g. parentheses or square
        brackets).  @('special') is 0 for ordinary forms; a positive
        @('n') means the first @('n') elements after the head are header
        arguments (like the binding list of @('let')), treated as in
        ACL2's @('ppr-special-syms') table.  @('break-body') means the
        form is never printed flat when it has body arguments (arguments
        after the header ones), so its body always starts on a new
        line; this is set for the scoping forms @('let'), @('fn'),
        function bindings, @('entry'), etc.")))
    (:atom ((cps nat-list)))
    (:prefix ((cps nat-list) (body pform)))
    (:list ((open natp) (close natp) (special natp) (break-body booleanp)
            (elems pform-list)))
    :pred pformp)

  (fty::deflist pform-list
    :parents (pretty-printer pforms)
    :short "Lists of @(tsee pform)."
    :elt-type pform
    :true-listp t
    :elementp-of-nil nil
    :pred pform-listp))

(fty::defresult pform-result
  :short "Fixtype of pforms and errors."
  :ok pform
  :pred pform-resultp)

(fty::defresult pform-list-result
  :short "Fixtype of pform lists and errors."
  :ok pform-list
  :pred pform-list-resultp)

;; The AST walkers below build lists out of results checked with the
;; (ok ...) binder; these disabled-by-default rules let the return-type
;; and guard proofs see that a non-error result is a value.
(local (in-theory (enable pformp-when-result-not-error
                          pform-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Constructors.
;;

(defmacro+ pform-ascii (s)
  :parents (pretty-printer)
  :short "Wrap an ASCII string literal as a @(tsee pform-atom) whose
          code-point list is computed at admission time."
  (cond ((not (stringp s))
         (er hard 'pform-ascii "Expected a string literal, got ~x0." s))
        ((not (char-list-all-ascii-p (explode s)))
         (er hard 'pform-ascii
             "String ~x0 contains a non-ASCII character (code >= 128)." s))
        (t `(pform-atom (quote ,(ascii-string=>codepoints s))))))

(define pform-utf8 ((s stringp))
  :returns (x pformp)
  :short "Atom for an identifier stored as a UTF-8 byte string."
  (pform-atom (utf8-string=>codepoints s)))

(define pform-sigil-utf8 ((sigil natp) (s stringp))
  :returns (x pformp)
  :short "Atom for a sigil character (e.g. @('$'), @('&')) followed by an
          identifier."
  (pform-atom (cons (lnfix sigil) (utf8-string=>codepoints s))))

(define pform-paren ((elems pform-listp))
  :returns (x pformp)
  :short "Ordinary parenthesized form."
  (make-pform-list :open #x28 :close #x29 :special 0 :break-body nil :elems elems))

(define pform-special ((n natp) (elems pform-listp))
  :returns (x pformp)
  :short "Parenthesized form whose first @('n') arguments are header
          arguments (see @(tsee pform))."
  (make-pform-list :open #x28 :close #x29 :special n :break-body nil :elems elems))

(define pform-body-form ((elems pform-listp))
  :returns (x pformp)
  :short "Parenthesized form with one header argument whose body (the
          remaining arguments) always starts on a new line: the layout
          for @('let'), @('fn'), function bindings, @('entry'), and the
          like."
  (make-pform-list :open #x28 :close #x29 :special 1 :break-body t :elems elems))

(define pform-bracket ((elems pform-listp))
  :returns (x pformp)
  :short "Square-bracketed form."
  (make-pform-list :open #x5B :close #x5D :special 0 :break-body nil :elems elems))

(define pform-prefix-ascii ((s stringp) (body pformp))
  :returns (x pformp)
  :short "Glue an ASCII prefix onto a form."
  (make-pform-prefix :cps (ascii-string=>codepoints s) :body body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Flat size and flat printing of print forms.
;;

(define pform-atomic-p ((x pformp))
  :returns (yes booleanp)
  :short "Is @('x') an atom, possibly under prefixes?  Only such forms
          are packed together into rows by @(tsee cons-ptuple),
          mirroring the atom test in ACL2's @('cons-ppr1')."
  :measure (pform-count x)
  (pform-case x
    :atom t
    :prefix (pform-atomic-p x.body)
    :list nil))

(defines pform-must-break-p
  :short "Does @('x') contain a @('break-body') list with body arguments?
          Such a form, and anything containing it, is never printed flat."
  :verify-guards :after-returns

  (define pform-must-break-p ((x pformp))
    :returns (yes booleanp)
    :measure (pform-count x)
    (pform-case x
      :atom nil
      :prefix (pform-must-break-p x.body)
      :list (or (and x.break-body
                     (> (len x.elems) (+ 1 x.special)))
                (pform-list-must-break-p x.elems))))

  (define pform-list-must-break-p ((xs pform-listp))
    :returns (yes booleanp)
    :measure (pform-list-count xs)
    (and (consp xs)
         (or (pform-must-break-p (car xs))
             (pform-list-must-break-p (cdr xs))))))

(defines pform-flat-size
  :short "Number of columns a form takes when printed flat."
  :verify-guards :after-returns

  (define pform-flat-size ((x pformp))
    :returns (n natp :rule-classes :type-prescription)
    :measure (pform-count x)
    (pform-case x
      :atom (len x.cps)
      :prefix (+ (len x.cps) (pform-flat-size x.body))
      :list (+ 2 (pform-list-flat-size x.elems))))

  (define pform-list-flat-size ((xs pform-listp))
    :returns (n natp :rule-classes :type-prescription)
    :measure (pform-list-count xs)
    (cond ((endp xs) 0)
          ((endp (cdr xs)) (pform-flat-size (car xs)))
          (t (+ (pform-flat-size (car xs))
                1
                (pform-list-flat-size (cdr xs)))))))

;; Rendering functions below accumulate code points in reverse order,
;; consing onto acc; the final result is reversed once at the top.

(defines pform-flat-print
  :short "Print a form flat (single line), consing code points in
          reverse onto @('acc')."
  :verify-guards :after-returns

  (define pform-flat-print ((x pformp) (acc nat-listp))
    :returns (acc2 nat-listp)
    :measure (pform-count x)
    (pform-case x
      :atom (revappend x.cps (nat-list-fix acc))
      :prefix (pform-flat-print x.body (revappend x.cps (nat-list-fix acc)))
      :list (cons x.close
                  (pform-list-flat-print x.elems
                                         (cons x.open (nat-list-fix acc))))))

  (define pform-list-flat-print ((xs pform-listp) (acc nat-listp))
    :returns (acc2 nat-listp)
    :measure (pform-list-count xs)
    (cond ((endp xs) (nat-list-fix acc))
          ((endp (cdr xs)) (pform-flat-print (car xs) acc))
          (t (pform-list-flat-print (cdr xs)
                                    (cons #x20 (pform-flat-print (car xs) acc)))))))

(define pform-list-split ((n natp) (xs pform-listp))
  :returns (mv (init pform-listp) (rest pform-listp))
  :short "Split a list into its first @('n') elements and the rest."
  (cond ((or (zp n) (endp xs)) (mv nil (pform-list-fix xs)))
        (t (b* (((mv init rest) (pform-list-split (1- n) (cdr xs))))
             (mv (cons (pform-fix (car xs)) init) rest))))
  ///
  (defret pform-list-count-of-pform-list-split
    (and (<= (pform-list-count init) (pform-list-count xs))
         (<= (pform-list-count rest) (pform-list-count xs)))
    :hints (("Goal" :induct (pform-list-split n xs)
             :in-theory (enable pform-list-split pform-list-count)))
    :rule-classes :linear)
  (defret len-of-pform-list-split-init
    (equal (len init) (min (nfix n) (len xs))))
  (defret consp-of-pform-list-split-init
    (equal (consp init) (and (not (zp n)) (consp xs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Ppr tuples: layout decisions annotated with widths.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes ptuples
  :short "Layout tuples, the port of ACL2's ppr tuples."

  (fty::deftagsum ptuple
    :parents (pretty-printer ptuples)
    :short "A layout decision for a form (or a row of forms), with its
            width."
    :long
    (xdoc::topstring
     (xdoc::p
      "In every case @('width') is the number of columns from the
       start of the tuple to the end of its widest line, counting the
       right brackets that close enclosing forms on the last line
       (see the @('rpc') argument of @(tsee pform-to-ptuple)).")
     (xdoc::ul
      (xdoc::li
       "@(':flat') &mdash; a row of forms printed flat, separated by
        single spaces.  A row usually holds one form; @(tsee
        cons-ptuple) packs several short atomic forms into a row.")
      (xdoc::li
       "@(':prefix') &mdash; the prefix text followed by the body tuple.")
      (xdoc::li
       "@(':wide') &mdash; @('(head arg1') then the other args in a
        column aligned under @('arg1').")
      (xdoc::li
       "@(':indent') &mdash; @('(head') then all args in a column
        indented by @('indent') from the open bracket.")
      (xdoc::li
       "@(':special') &mdash; @('(head'), then the header args (on the
        first line after the head if @('init-break') is @('nil'),
        otherwise in a column at @('init-indent')), then the body args
        in a column at @('body-indent').")))
    (:flat ((width natp) (forms pform-list)))
    (:prefix ((width natp) (cps nat-list) (body ptuple)))
    (:wide ((width natp) (open natp) (close natp)
            (head ptuple) (args ptuple-list)))
    (:indent ((width natp) (indent natp) (open natp) (close natp)
              (head ptuple) (args ptuple-list)))
    (:special ((width natp) (open natp) (close natp)
               (head ptuple)
               (init-break booleanp) (init-indent natp) (init-args ptuple-list)
               (body-indent natp) (body-args ptuple-list)))
    :pred ptuplep)

  (fty::deflist ptuple-list
    :parents (pretty-printer ptuples)
    :short "Lists of @(tsee ptuple)."
    :elt-type ptuple
    :true-listp t
    :elementp-of-nil nil
    :pred ptuple-listp))

(define ptuple-width ((x ptuplep))
  :returns (w natp :rule-classes :type-prescription)
  :short "The width of any tuple."
  (ptuple-case x
    :flat x.width
    :prefix x.width
    :wide x.width
    :indent x.width
    :special x.width))

(define ptuple-list-max-width ((xs ptuple-listp))
  :returns (w natp :rule-classes :type-prescription)
  :short "Maximum width of the tuples in a list (0 for the empty list).
          Port of @('max-width')."
  (if (endp xs)
      0
    (max (ptuple-width (car xs))
         (ptuple-list-max-width (cdr xs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cons-ptuple ((x ptuplep)
                     (column ptuple-listp)
                     (width natp)
                     (flat-margin natp))
  :returns (column2 ptuple-listp)
  :short "Add the tuple @('x') for one form to a column of tuples for
          the forms that follow it.  Port of ACL2's @('cons-ppr1')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The default is to lengthen the column by putting @('x') on top.
     But if @('x') is a single atomic form and the top row of the column
     is flat, and the merged row fits within both @('width') and
     @('flat-margin'), we instead lengthen that top row: this is how
     sequences of short arguments (e.g. the elements of an array
     literal) are packed several per line.  Keyword pairing from
     @('cons-ppr1') is not needed for Remora: the only keyword-like
     token, the @(':') of a type ascription, is glued to its type as a
     @(':prefix') form."))
  (b* ((x (ptuple-fix x))
       (column (ptuple-list-fix column))
       ((unless (and (ptuple-case x :flat) (consp column)))
        (cons x column))
       (forms (ptuple-flat->forms x))
       ((unless (and (consp forms)
                     (endp (cdr forms))
                     (pform-atomic-p (car forms))))
        (cons x column))
       (row1 (car column))
       ((unless (ptuple-case row1 :flat)) (cons x column))
       (n (+ (ptuple-flat->width x) 1 (ptuple-flat->width row1)))
       ((unless (and (<= n (lnfix flat-margin)) (<= n (lnfix width))))
        (cons x column)))
    (cons (make-ptuple-flat :width n
                            :forms (cons (car forms) (ptuple-flat->forms row1)))
          (cdr column))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pform-to-ptuple
  :short "Choose a layout for a form within a width.  Port of ACL2's
          @('ppr1') and @('ppr1-lst')."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('width') is the number of columns available, starting at the
     column where the form will be printed.  @('rpc') (`right paren
     count') is the number of closing brackets of enclosing forms that
     will follow this form on its last line; the form must leave room
     for them.  @('flat-margin') is the maximum width of a form printed
     flat (unless it is an atom, which we never break)."))
  :verify-guards :after-returns

  (define pform-to-ptuple ((x pformp)
                           (width natp)
                           (rpc natp)
                           (flat-margin natp))
    :returns (tup ptuplep)
    :measure (pform-count x)
    (b* ((x (pform-fix x))
         (width (lnfix width))
         (rpc (lnfix rpc))
         (flat-margin (lnfix flat-margin))
         (sz (+ (pform-flat-size x) rpc))
         (flat (make-ptuple-flat :width sz :forms (list x)))
         (fits (and (<= sz width)
                    (<= sz flat-margin)
                    (not (pform-must-break-p x))))
         (width-1 (nfix (- width 1))))
      (pform-case x
        :atom flat
        :prefix
        (if fits
            flat
          (b* ((body (pform-to-ptuple x.body
                                      (nfix (- width (len x.cps)))
                                      rpc
                                      flat-margin)))
            (make-ptuple-prefix :width (+ (len x.cps) (ptuple-width body))
                                :cps x.cps
                                :body body)))
        :list
        (b* (((when (or fits (endp x.elems))) flat)
             ((when (endp (cdr x.elems)))
              ;; A singleton: nothing to lay out unless the element is
              ;; compound, in which case it is laid out (with room for
              ;; our close bracket) right after our open bracket.
              (if (pform-atomic-p (car x.elems))
                  flat
                (b* ((x1 (pform-to-ptuple (car x.elems) width-1 (+ rpc 1)
                                          flat-margin)))
                  (make-ptuple-indent :width (+ 1 (ptuple-width x1))
                                      :indent 1
                                      :open x.open :close x.close
                                      :head x1 :args nil))))
             (head (car x.elems))
             (args (cdr x.elems))
             ;; The head is followed by args, so it has 0 right parens.
             (x1 (pform-to-ptuple head width-1 0 flat-margin))
             (hd-sz (and (pform-atomic-p head) (ptuple-width x1)))
             ((unless hd-sz)
              ;; Non-atomic head (e.g. a lambda being applied): the head
              ;; and all args go in one column indented by 1.
              (b* ((xc (pform-list-to-ptuples args width-1 (+ rpc 1) flat-margin))
                   (maximum (max (ptuple-width x1) (ptuple-list-max-width xc))))
                (make-ptuple-indent :width (+ 1 maximum)
                                    :indent 1
                                    :open x.open :close x.close
                                    :head x1 :args xc)))
             (special (if (<= x.special (len args)) x.special 0))
             ((mv init-args rest-args) (pform-list-split special args))
             ;; Each body arg gets the full width minus 1 (for the
             ;; minimal indentation).
             (xc (pform-list-to-ptuples rest-args width-1 (+ rpc 1) flat-margin))
             (maximum (ptuple-list-max-width xc))
             ((when (> special 0))
              ;; Port of the SPECIAL-TERM case.  If the first header
              ;; arg is atomic and short, glue it to the head on the
              ;; first line (like the name in `(defun name ...)').
              (b* ((name (car init-args))
                   (name-sz (pform-flat-size name))
                   (opt-name (and (pform-atomic-p name)
                                  (<= (+ hd-sz 1 name-sz) width-1)))
                   (opt-name-sz (if opt-name (+ 1 name-sz) 0))
                   (x1 (if opt-name
                           (make-ptuple-flat :width (+ hd-sz opt-name-sz)
                                             :forms (list head name))
                         x1))
                   (init-forms (if opt-name (cdr init-args) init-args))
                   (init-pp (pform-list-to-ptuples init-forms
                                                   width-1
                                                   (if (endp xc) (+ rpc 1) 0)
                                                   flat-margin))
                   (max-init (ptuple-list-max-width init-pp))
                   ;; Header args go on the first line unless too wide.
                   (init-break (and (consp init-pp)
                                    (>= (+ hd-sz opt-name-sz max-init) width-1)))
                   (init-indent (cond ((not init-break) 0)
                                      ((>= (+ hd-sz max-init) width-1)
                                       (max 1 (- width-1 max-init)))
                                      (t (+ hd-sz 2))))
                   (rest-indent (if (or (>= maximum width-1)
                                        (and init-break (eql init-indent 1)))
                                    1
                                  2))
                   (maximum (max (max (ptuple-width x1)
                                      (+ maximum rest-indent -1))
                                 (if init-break
                                     (+ init-indent -1 max-init)
                                   (+ hd-sz opt-name-sz 1 max-init)))))
                (make-ptuple-special :width (+ 1 maximum)
                                     :open x.open :close x.close
                                     :head x1
                                     :init-break init-break
                                     :init-indent init-indent
                                     :init-args init-pp
                                     :body-indent rest-indent
                                     :body-args xc)))
             ;; WIDE if there is room for the open bracket, the head, a
             ;; space, and the widest argument.
             ((when (<= (+ hd-sz 2 maximum) width))
              (make-ptuple-wide :width (+ hd-sz 2 maximum)
                                :open x.open :close x.close
                                :head x1 :args xc))
             ;; Otherwise indent the args so that the widest one ends at
             ;; the right margin, but by at most 5.
             ((when (< maximum width))
              (b* ((ind (min 5 (- width maximum))))
                (make-ptuple-indent :width (+ maximum ind)
                                    :indent ind
                                    :open x.open :close x.close
                                    :head x1 :args xc))))
          (make-ptuple-indent :width (+ 1 maximum)
                              :indent 1
                              :open x.open :close x.close
                              :head x1 :args xc)))))

  (define pform-list-to-ptuples ((xs pform-listp)
                                 (width natp)
                                 (rpc natp)
                                 (flat-margin natp))
    :returns (tups ptuple-listp)
    :measure (pform-list-count xs)
    (cond ((endp xs) nil)
          ;; The last element is followed by the enclosing right parens.
          ((endp (cdr xs))
           (list (pform-to-ptuple (car xs) width rpc flat-margin)))
          (t (cons-ptuple (pform-to-ptuple (car xs) width 0 flat-margin)
                          (pform-list-to-ptuples (cdr xs) width rpc flat-margin)
                          width
                          flat-margin)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Rendering tuples to code points.  Port of ppr2 / ppr2-column.
;;

(define spaces-acc ((n natp) (acc nat-listp))
  :returns (acc2 nat-listp)
  :short "Cons @('n') space code points onto @('acc')."
  (if (zp n)
      (nat-list-fix acc)
    (spaces-acc (1- n) (cons #x20 acc))))

(defines ptuple-print
  :short "Render a tuple to code points (in reverse, consed onto
          @('acc')), given the column @('col') at which it starts.
          Port of ACL2's @('ppr2') and @('ppr2-column')."
  :verify-guards :after-returns

  (define ptuple-print ((x ptuplep) (col natp) (acc nat-listp))
    :returns (acc2 nat-listp)
    :measure (ptuple-count x)
    (ptuple-case x
      :flat (pform-list-flat-print x.forms acc)
      :prefix (ptuple-print x.body
                            (+ (lnfix col) (len x.cps))
                            (revappend x.cps (nat-list-fix acc)))
      :wide (b* ((acc (cons x.open (nat-list-fix acc)))
                 (acc (ptuple-print x.head (+ (lnfix col) 1) acc))
                 (hd (ptuple-width x.head))
                 (acc (ptuple-list-print-column x.args
                                                (+ (lnfix col) 1 hd)
                                                (+ (lnfix col) 2 hd)
                                                acc)))
              (cons x.close acc))
      :indent (b* ((acc (cons x.open (nat-list-fix acc)))
                   (acc (ptuple-print x.head (+ (lnfix col) 1) acc))
                   (acc (if (consp x.args)
                            (ptuple-list-print-column x.args
                                                      0
                                                      (+ (lnfix col) x.indent)
                                                      (cons #x0A acc))
                          acc)))
                (cons x.close acc))
      :special (b* ((acc (cons x.open (nat-list-fix acc)))
                    (acc (ptuple-print x.head (+ (lnfix col) 1) acc))
                    (hd (ptuple-width x.head))
                    (acc (cond ((endp x.init-args) acc)
                               (x.init-break
                                (ptuple-list-print-column x.init-args
                                                          0
                                                          (+ (lnfix col) x.init-indent)
                                                          (cons #x0A acc)))
                               (t (ptuple-list-print-column x.init-args
                                                            (+ (lnfix col) 1 hd)
                                                            (+ (lnfix col) 2 hd)
                                                            acc))))
                    (acc (if (consp x.body-args)
                             (ptuple-list-print-column x.body-args
                                                       0
                                                       (+ (lnfix col) x.body-indent)
                                                       (cons #x0A acc))
                           acc)))
                 (cons x.close acc))))

  (define ptuple-list-print-column ((xs ptuple-listp)
                                    (loc natp)
                                    (col natp)
                                    (acc nat-listp))
    :returns (acc2 nat-listp)
    :short "Print tuples in a column at @('col'), one per line, with the
            print head currently at @('loc').  If @('loc') is already at
            or past @('col'), print a single space instead."
    :measure (ptuple-list-count xs)
    (b* (((when (endp xs)) (nat-list-fix acc))
         (loc (lnfix loc))
         (col (lnfix col))
         (acc (spaces-acc (if (> col loc) (- col loc) 1) acc))
         (acc (ptuple-print (car xs) (if (> col loc) col (+ loc 1)) acc))
         ((when (endp (cdr xs))) acc))
      (ptuple-list-print-column (cdr xs) 0 col (cons #x0A acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pform-print ((x pformp) (width natp) (flat-margin natp) (acc nat-listp))
  :returns (acc2 nat-listp)
  :short "Lay out and render a form starting at column 0."
  (ptuple-print (pform-to-ptuple x width 0 flat-margin) 0 acc))

(define pform-list-print-separated ((xs pform-listp)
                                    (width natp)
                                    (flat-margin natp)
                                    (blank-line booleanp)
                                    (acc nat-listp))
  :returns (acc2 nat-listp)
  :short "Render top-level forms, each starting at column 0, separated
          by a newline (or a blank line if @('blank-line'))."
  (b* (((when (endp xs)) (nat-list-fix acc))
       (acc (pform-print (car xs) width flat-margin acc))
       ((when (endp (cdr xs))) acc)
       (acc (if blank-line (list* #x0A #x0A acc) (cons #x0A acc))))
    (pform-list-print-separated (cdr xs) width flat-margin blank-line acc)))

(define codepoints-acc-to-string ((acc nat-listp))
  :returns (s stringp)
  :short "Reverse an accumulated code-point list and UTF-8 encode it
          into an ACL2 string.  Returns the empty string on invalid
          code points (unreachable for well-formed ASTs)."
  (b* ((cps (rev (nat-list-fix acc)))
       ((unless (ustring? cps)) "")
       (bytes (ustring=>utf8 cps))
       ((unless (unsigned-byte-listp 8 bytes)) ""))
    (nats=>string bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; AST -> pform.  Mirrors the walkers of the pdoc printer (see there for
;; the correspondence with the grammar rules), producing print forms.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base-type-to-pform ((bt base-typep))
  :returns (x pformp)
  (base-type-case bt
    :bool (pform-ascii "Bool")
    :int (pform-ascii "Int")
    :float (pform-ascii "Float")))

(define base-lit-to-pform ((bl base-litp))
  :returns (x pformp)
  (base-lit-case bl
    :bool (if bl.lit (pform-ascii "#t") (pform-ascii "#f"))
    :int (pform-atom (int-lit-to-codepoints bl.lit))
    :float (pform-atom (float-lit-to-codepoints bl.lit))))

(define ispace-var-to-pform ((iv ispace-varp))
  :returns (x pformp)
  :short "@('$name') for dimension variables, @('@name') for shape
          variables."
  (ispace-var-case iv
    :dim (pform-sigil-utf8 #x24 iv.name)
    :shape (pform-sigil-utf8 #x40 iv.name)))

(define type-var-to-pform ((tv type-varp))
  :returns (x pformp)
  :short "@('&name') for atom-kinded variables, @('*name') for
          array-kinded variables."
  (type-var-case tv
    :atom (pform-sigil-utf8 #x26 tv.name)
    :array (pform-sigil-utf8 #x2A tv.name)))

(define ispace-var-list-to-pforms ((ivs ispace-var-listp))
  :returns (xs pform-listp)
  (if (endp ivs)
      nil
    (cons (ispace-var-to-pform (car ivs))
          (ispace-var-list-to-pforms (cdr ivs)))))

(define type-var-list-to-pforms ((tvs type-var-listp))
  :returns (xs pform-listp)
  (if (endp tvs)
      nil
    (cons (type-var-to-pform (car tvs))
          (type-var-list-to-pforms (cdr tvs)))))

(define ispace-var-list-option-to-pform ((io ispace-var-list-optionp))
  :returns (x pformp)
  :short "@('_') when absent, a parenthesized list otherwise."
  (ispace-var-list-option-case io
    :none (pform-ascii "_")
    :some (pform-paren (ispace-var-list-to-pforms io.val))))

(define type-var-list-option-to-pform ((io type-var-list-optionp))
  :returns (x pformp)
  :short "@('_') when absent, a parenthesized list otherwise."
  (type-var-list-option-case io
    :none (pform-ascii "_")
    :some (pform-paren (type-var-list-to-pforms io.val))))

(define nat-list-to-pforms ((ns nat-listp))
  :returns (xs pform-listp)
  (if (endp ns)
      nil
    (cons (pform-atom (nat-to-dec-codepoints (lnfix (car ns))))
          (nat-list-to-pforms (cdr ns)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dim-to-pform
  :short "Print forms for @(tsee dim) and @(tsee dim-list)."
  :verify-guards :after-returns

  (define dim-to-pform ((d dimp))
    :returns (x pformp)
    :measure (dim-count d)
    (dim-case d
      :var (pform-sigil-utf8 #x24 d.name)
      :const (pform-atom (nat-to-dec-codepoints d.val))
      :add (pform-paren (cons (pform-ascii "+") (dim-list-to-pforms d.dims)))
      :mul (pform-paren (cons (pform-ascii "*") (dim-list-to-pforms d.dims)))
      :sub (pform-paren (cons (pform-ascii "-") (dim-list-to-pforms d.dims)))))

  (define dim-list-to-pforms ((ds dim-listp))
    :returns (xs pform-listp)
    :measure (dim-list-count ds)
    (if (endp ds)
        nil
      (cons (dim-to-pform (car ds))
            (dim-list-to-pforms (cdr ds))))))

(defines shape-to-pform
  :short "Print forms for @(tsee shape), @(tsee ispace), and their lists."
  :verify-guards :after-returns

  (define shape-to-pform ((s shapep))
    :returns (x pformp)
    :measure (shape-count s)
    (shape-case s
      :var (pform-sigil-utf8 #x40 s.name)
      :dims (pform-paren (cons (pform-ascii "dims") (dim-list-to-pforms s.dims)))
      :append (pform-paren (cons (pform-ascii "++") (shape-list-to-pforms s.shapes)))
      :splice (pform-bracket (ispace-list-to-pforms s.ispaces))))

  (define shape-list-to-pforms ((ss shape-listp))
    :returns (xs pform-listp)
    :measure (shape-list-count ss)
    (if (endp ss)
        nil
      (cons (shape-to-pform (car ss))
            (shape-list-to-pforms (cdr ss)))))

  (define ispace-to-pform ((i ispacep))
    :returns (x pformp)
    :measure (ispace-count i)
    (ispace-case i
      :dim (dim-to-pform i.dim)
      :shape (shape-to-pform i.shape)))

  (define ispace-list-to-pforms ((is ispace-listp))
    :returns (xs pform-listp)
    :measure (ispace-list-count is)
    (if (endp is)
        nil
      (cons (ispace-to-pform (car is))
            (ispace-list-to-pforms (cdr is))))))

(define ispace-list-option-to-pform ((io ispace-list-optionp))
  :returns (x pformp)
  (ispace-list-option-case io
    :none (pform-ascii "_")
    :some (pform-paren (ispace-list-to-pforms io.val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-to-pform
  :short "Print forms for @(tsee type) and @(tsee type-list)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The binder forms @('Forall'), @('Pi'), and @('Sigma') are special
     forms with one header argument (the binder list)."))
  :verify-guards :after-returns

  (define type-to-pform ((ty typep))
    :returns (x pformp)
    :measure (type-count ty)
    (type-case ty
      :var (type-var-to-pform ty.var)
      :base (base-type-to-pform ty.type)
      :array (pform-paren (list (pform-ascii "A")
                                (type-to-pform ty.elem)
                                (ispace-to-pform ty.ispace)))
      :bracket (pform-bracket (cons (type-to-pform ty.elem)
                                    (ispace-list-to-pforms ty.ispaces)))
      :fun (pform-paren (list (pform-ascii "->")
                              (type-to-pform ty.in)
                              (type-to-pform ty.out)))
      :funn (pform-paren (list (pform-ascii "->")
                               (pform-paren (type-list-to-pforms ty.in))
                               (type-to-pform ty.out)))
      :forall (pform-special 1 (list (pform-ascii "Forall")
                                     (pform-paren (list (type-var-to-pform ty.param)))
                                     (type-to-pform ty.body)))
      :foralln (pform-special 1 (list (pform-ascii "Forall")
                                      (pform-paren (type-var-list-to-pforms ty.params))
                                      (type-to-pform ty.body)))
      :pi (pform-special 1 (list (pform-ascii "Pi")
                                 (pform-paren (list (ispace-var-to-pform ty.param)))
                                 (type-to-pform ty.body)))
      :pin (pform-special 1 (list (pform-ascii "Pi")
                                  (pform-paren (ispace-var-list-to-pforms ty.params))
                                  (type-to-pform ty.body)))
      :sigma (pform-special 1 (list (pform-ascii "Sigma")
                                    (pform-paren (list (ispace-var-to-pform ty.param)))
                                    (type-to-pform ty.body)))
      :sigman (pform-special 1 (list (pform-ascii "Sigma")
                                     (pform-paren (ispace-var-list-to-pforms ty.params))
                                     (type-to-pform ty.body)))))

  (define type-list-to-pforms ((tys type-listp))
    :returns (xs pform-listp)
    :measure (type-list-count tys)
    (if (endp tys)
        nil
      (cons (type-to-pform (car tys))
            (type-list-to-pforms (cdr tys))))))

(define type-list-option-to-pform ((to type-list-optionp))
  :returns (x pformp)
  (type-list-option-case to
    :none (pform-ascii "_")
    :some (pform-paren (type-list-to-pforms to.val))))

(define colon-type-to-pform ((ty typep))
  :returns (x pformp)
  :short "A type ascription @(': type'), with the colon glued to the type."
  (pform-prefix-ascii ": " (type-to-pform ty)))

(define type-option-to-pforms ((to type-optionp))
  :returns (xs pform-listp)
  :short "An optional trailing type ascription: nothing, or one
          @(tsee colon-type-to-pform)."
  (type-option-case to
    :none nil
    :some (list (colon-type-to-pform to.val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pat-to-pform ((vt var+type?-p))
  :returns (x pform-resultp)
  :short "The @('pat') form @('(name type)'); fails if the type is absent,
          since the concrete syntax requires it."
  (b* ((type? (var+type?->type? vt)))
    (type-option-case type?
      :none (reserr (list :pat-without-type (var+type?->var vt)))
      :some (pform-paren (list (pform-utf8 (var+type?->var vt))
                               (type-to-pform type?.val))))))

(define pat-list-to-pforms ((vts var+type?-listp))
  :returns (xs pform-list-resultp)
  (b* (((when (endp vts)) nil)
       ((ok first) (pat-to-pform (car vts)))
       ((ok rest) (pat-list-to-pforms (cdr vts))))
    (cons first rest)))

(define fun-sig-to-pform ((var stringp)
                          (params var+type?-listp)
                          (type? type-optionp))
  :returns (x pform-resultp)
  :short "The @('fun-sig') form @('(name pat ... [: type])'), shared by
          @('fun') bindings and @('entry') declarations."
  (b* (((ok pats) (pat-list-to-pforms params)))
    (pform-paren (cons (pform-utf8 var)
                       (append pats (type-option-to-pforms type?))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-to-pform
  :short "Print forms for @(tsee expr), @(tsee atom), @(tsee bind), and
          their lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Binding and abstraction forms are special forms with one header
     argument, so that their body goes on its own lines indented by 2.
     For the scoping forms (@('let'), @('fn'), @('t-fn'), @('i-fn'),
     @('unbox'), and the @('fun'), @('t-fun'), @('i-fun') bindings) the
     body always starts on a new line (@(tsee pform-body-form)); for
     @('val'), @('type'), and @('ispace') bindings and for @('box') the
     form is printed flat when it fits (@(tsee pform-special)).
     Applications, @('array'), @('frame'), @('t-app'), @('i-app'), and
     @('@f') calls are ordinary forms, laid out wide or indented.")
   (xdoc::p
    "See the @(see printer) for the correspondence between AST cases and
     grammar rules, and for which AST information has no concrete
     syntax (and so is not printed or causes an error)."))
  :verify-guards :after-returns

  (define expr-to-pform ((e exprp))
    :returns (x pform-resultp)
    :measure (expr-count e)
    (expr-case e
      :var (pform-utf8 e.name)
      :atom (atom-to-pform e.atom)
      :array (b* (((ok atoms) (atom-list-to-pforms e.atoms)))
               (pform-paren (list* (pform-ascii "array")
                                   (pform-bracket (nat-list-to-pforms e.dims))
                                   atoms)))
      :array-empty (pform-paren (list (pform-ascii "array")
                                      (pform-bracket (nat-list-to-pforms e.dims))
                                      (type-to-pform e.type)))
      :frame (b* (((ok exprs) (expr-list-to-pforms e.exprs)))
               (pform-paren (list* (pform-ascii "frame")
                                   (pform-bracket (nat-list-to-pforms e.dims))
                                   exprs)))
      :frame-empty (pform-paren (list (pform-ascii "frame")
                                      (pform-bracket (nat-list-to-pforms e.dims))
                                      (type-to-pform e.type)))
      :string (pform-atom (string-lit-to-codepoints e.chars))
      :app (b* (((ok fun) (expr-to-pform e.fun))
                ((ok arg) (expr-to-pform e.arg)))
             (pform-paren (list fun arg)))
      :appn (b* (((ok fun) (expr-to-pform e.fun))
                 ((ok args) (expr-list-to-pforms e.args)))
              (pform-paren (cons fun args)))
      :tapp (b* (((ok fun) (expr-to-pform e.fun)))
              (pform-paren (list (pform-ascii "t-app") fun (type-to-pform e.arg))))
      :tappn (b* (((ok fun) (expr-to-pform e.fun)))
               (pform-paren (list* (pform-ascii "t-app") fun
                                   (type-list-to-pforms e.args))))
      :iapp (b* (((ok fun) (expr-to-pform e.fun)))
              (pform-paren (list (pform-ascii "i-app") fun (ispace-to-pform e.arg))))
      :iappn (b* (((ok fun) (expr-to-pform e.fun)))
               (pform-paren (list* (pform-ascii "i-app") fun
                                   (ispace-list-to-pforms e.args))))
      :capp
      ;; "@" exp type-args ispace-args exp*: the "@" is glued to the
      ;; function expression.
      (b* (((ok fun) (expr-to-pform e.fun))
           ((ok args) (expr-list-to-pforms e.args)))
        (pform-paren (list* (pform-prefix-ascii "@" fun)
                            (type-list-option-to-pform e.targs)
                            (ispace-list-option-to-pform e.iargs)
                            args)))
      :unbox
      ;; The optional result type has no concrete syntax.
      (b* (((ok target) (expr-to-pform e.target))
           ((ok body) (expr-to-pform e.body)))
        (pform-body-form (list (pform-ascii "unbox")
                               (pform-paren (list (ispace-var-to-pform e.ispace)
                                                  (pform-utf8 e.var)
                                                  target))
                               body)))
      :unboxn
      (b* (((ok target) (expr-to-pform e.target))
           ((ok body) (expr-to-pform e.body)))
        (pform-body-form (list (pform-ascii "unbox")
                               (pform-paren (append (ispace-var-list-to-pforms e.ispaces)
                                                    (list (pform-utf8 e.var)
                                                          target)))
                               body)))
      :bracket (b* (((ok exprs) (expr-list-to-pforms e.exprs)))
                 (pform-bracket exprs))
      :let (b* (((ok binds) (bind-list-to-pforms e.binds))
                ((ok body) (expr-to-pform e.body)))
             (pform-body-form (list (pform-ascii "let")
                                    (pform-paren binds)
                                    body)))))

  (define expr-list-to-pforms ((es expr-listp))
    :returns (xs pform-list-resultp)
    :measure (expr-list-count es)
    (b* (((when (endp es)) nil)
         ((ok first) (expr-to-pform (car es)))
         ((ok rest) (expr-list-to-pforms (cdr es))))
      (cons first rest)))

  (define atom-to-pform ((a atomp))
    :returns (x pform-resultp)
    :measure (atom-count a)
    (atom-case a
      :base (base-lit-to-pform a.lit)
      ;; The optional body type of lambdas has no concrete syntax.
      :lambda (b* (((ok pat) (pat-to-pform a.param))
                   ((ok body) (expr-to-pform a.body)))
                (pform-body-form (list (pform-ascii "fn")
                                       (pform-paren (list pat))
                                       body)))
      :lambdan (b* (((ok pats) (pat-list-to-pforms a.params))
                    ((ok body) (expr-to-pform a.body)))
                 (pform-body-form (list (pform-ascii "fn")
                                        (pform-paren pats)
                                        body)))
      :tlambda (b* (((ok body) (expr-to-pform a.body)))
                 (pform-body-form (list (pform-ascii "t-fn")
                                        (pform-paren (list (type-var-to-pform a.param)))
                                        body)))
      :tlambdan (b* (((ok body) (expr-to-pform a.body)))
                  (pform-body-form (list (pform-ascii "t-fn")
                                         (pform-paren (type-var-list-to-pforms a.params))
                                         body)))
      :ilambda (b* (((ok body) (expr-to-pform a.body)))
                 (pform-body-form (list (pform-ascii "i-fn")
                                        (pform-paren (list (ispace-var-to-pform a.param)))
                                        body)))
      :ilambdan (b* (((ok body) (expr-to-pform a.body)))
                  (pform-body-form (list (pform-ascii "i-fn")
                                         (pform-paren (ispace-var-list-to-pforms a.params))
                                         body)))
      ;; The box-expr grammar rule requires the type.
      :box (type-option-case a.type?
             :none (reserr (list :box-without-type (atom-fix a)))
             :some (b* (((ok array) (expr-to-pform a.array)))
                     (pform-special 1 (list (pform-ascii "box")
                                            (pform-paren (list (ispace-to-pform a.ispace)))
                                            array
                                            (type-to-pform a.type?.val)))))
      :boxn (type-option-case a.type?
              :none (reserr (list :box-without-type (atom-fix a)))
              :some (b* (((ok array) (expr-to-pform a.array)))
                      (pform-special 1 (list (pform-ascii "box")
                                             (pform-paren (ispace-list-to-pforms a.ispaces))
                                             array
                                             (type-to-pform a.type?.val)))))))

  (define atom-list-to-pforms ((as atom-listp))
    :returns (xs pform-list-resultp)
    :measure (atom-list-count as)
    (b* (((when (endp as)) nil)
         ((ok first) (atom-to-pform (car as)))
         ((ok rest) (atom-list-to-pforms (cdr as))))
      (cons first rest)))

  (define bind-to-pform ((b bindp))
    :returns (x pform-resultp)
    :measure (bind-count b)
    (bind-case b
      :ispace (pform-special 1 (list (pform-ascii "ispace")
                                     (ispace-var-to-pform b.var)
                                     (ispace-to-pform b.ispace)))
      :type (pform-special 1 (list (pform-ascii "type")
                                   (type-var-to-pform b.var)
                                   (type-to-pform b.type)))
      :val
      ;; "val" identifier exp, or "val" "(" identifier : type ")" exp.
      (b* ((sig (type-option-case b.type?
                  :some (pform-paren (list (pform-utf8 b.var)
                                           (colon-type-to-pform b.type?.val)))
                  :none (pform-utf8 b.var)))
           ((ok expr) (expr-to-pform b.expr)))
        (pform-special 1 (list (pform-ascii "val") sig expr)))
      :fun
      (b* (((ok sig) (fun-sig-to-pform b.var b.params b.type?))
           ((ok expr) (expr-to-pform b.expr)))
        (pform-body-form (list (pform-ascii "fun") sig expr)))
      :tfun
      ;; "t-fun" "(" identifier "(" type-var* ")" [: type] ")" exp
      (b* (((ok expr) (expr-to-pform b.expr))
           (sig (pform-paren (list* (pform-utf8 b.var)
                                    (pform-paren (type-var-list-to-pforms b.params))
                                    (type-option-to-pforms b.type?)))))
        (pform-body-form (list (pform-ascii "t-fun") sig expr)))
      :ifun
      ;; "i-fun" "(" identifier "(" ispace-var* ")" [: type] ")" exp
      (b* (((ok expr) (expr-to-pform b.expr))
           (sig (pform-paren (list* (pform-utf8 b.var)
                                    (pform-paren (ispace-var-list-to-pforms b.params))
                                    (type-option-to-pforms b.type?)))))
        (pform-body-form (list (pform-ascii "i-fun") sig expr)))
      :cfun
      ;; "fun" "(" "@" identifier type-vars ispace-vars pat* : type ")" exp
      (b* (((ok pats) (pat-list-to-pforms b.params))
           ((ok expr) (expr-to-pform b.expr))
           (sig (pform-paren (list* (pform-sigil-utf8 #x40 b.var)
                                    (type-var-list-option-to-pform b.tparams?)
                                    (ispace-var-list-option-to-pform b.iparams?)
                                    (append pats
                                            (list (colon-type-to-pform b.type)))))))
        (pform-body-form (list (pform-ascii "fun") sig expr)))))

  (define bind-list-to-pforms ((bs bind-listp))
    :returns (xs pform-list-resultp)
    :measure (bind-list-count bs)
    (b* (((when (endp bs)) nil)
         ((ok first) (bind-to-pform (car bs)))
         ((ok rest) (bind-list-to-pforms (cdr bs))))
      (cons first rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define import-to-pform ((imp importp))
  :returns (x pformp)
  (pform-paren (list (pform-ascii "import")
                     (pform-atom (string-lit-to-codepoints (import->path imp))))))

(define import-list-to-pforms ((imps import-listp))
  :returns (xs pform-listp)
  (if (endp imps)
      nil
    (cons (import-to-pform (car imps))
          (import-list-to-pforms (cdr imps)))))

(define decl-to-pform ((d declp))
  :returns (x pform-resultp)
  (decl-case d
    ;; "def" bind: an ordinary form, so a short binding stays on the
    ;; `def' line and a long one is laid out wide, e.g.
    ;;   (def (fun (f (x Int) : Int)
    ;;          (+ x 1)))
    :def (b* (((ok bind) (bind-to-pform d.bind)))
           (pform-paren (list (pform-ascii "def") bind)))
    ;; "entry" "(" fun-sig ")" exp
    :entry (b* (((ok sig) (fun-sig-to-pform d.var d.params d.type?))
                ((ok expr) (expr-to-pform d.expr)))
             (pform-body-form (list (pform-ascii "entry") sig expr)))))

(define decl-list-to-pforms ((ds decl-listp))
  :returns (xs pform-list-resultp)
  (b* (((when (endp ds)) nil)
       ((ok first) (decl-to-pform (car ds)))
       ((ok rest) (decl-list-to-pforms (cdr ds))))
    (cons first rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Entry points.
;;

(define pretty-print-expr-to-codepoints ((e exprp)
                                         &key
                                         ((width natp) '80)
                                         ((flat-margin natp) '60))
  :returns (cps nat-listp)
  :short "Render an @(tsee expr) to a list of Unicode code points.
          Returns the empty list if the AST has no concrete syntax
          (e.g. an untyped parameter)."
  (b* ((x (expr-to-pform e))
       ((when (reserrp x)) nil))
    (rev (pform-print x width flat-margin nil))))

(define pretty-print-expr ((e exprp)
                           &key
                           ((width natp) '80)
                           ((flat-margin natp) '60))
  :returns (s stringp)
  :short "Render an @(tsee expr) to a UTF-8 encoded ACL2 string, wrapping
          at @('width') columns and printing flat only forms at most
          @('flat-margin') columns wide."
  (b* ((x (expr-to-pform e))
       ((when (reserrp x)) ""))
    (codepoints-acc-to-string (pform-print x width flat-margin nil))))

(define file-to-pforms ((f filep))
  :returns (mv (imports pform-listp) (decls pform-list-resultp))
  :short "Print forms for the imports and the declarations of a file."
  (b* (((file f) f))
    (mv (import-list-to-pforms f.imports)
        (decl-list-to-pforms f.decls))))

(define pretty-print-file-acc ((f filep) (width natp) (flat-margin natp))
  :returns (acc nat-listp)
  :short "Render a file to reversed code points: the imports one per line,
          then a blank line, then the declarations separated by blank
          lines.  Returns @('nil') if the AST has no concrete syntax."
  (b* (((mv imports decls) (file-to-pforms f))
       ((when (reserrp decls)) nil)
       (acc (pform-list-print-separated imports width flat-margin nil nil))
       (acc (if (and (consp imports) (consp decls))
                (list* #x0A #x0A acc)
              acc)))
    (pform-list-print-separated decls width flat-margin t acc)))

(define pretty-print-file-to-codepoints ((f filep)
                                         &key
                                         ((width natp) '80)
                                         ((flat-margin natp) '60))
  :returns (cps nat-listp)
  :short "Render a @(tsee file) to a list of Unicode code points."
  (rev (pretty-print-file-acc f width flat-margin)))

(define pretty-print-file ((f filep)
                           &key
                           ((width natp) '80)
                           ((flat-margin natp) '60))
  :returns (s stringp)
  :short "Render a @(tsee file) to a UTF-8 encoded ACL2 string, wrapping
          at @('width') columns and printing flat only forms at most
          @('flat-margin') columns wide."
  (codepoints-acc-to-string (pretty-print-file-acc f width flat-margin)))
