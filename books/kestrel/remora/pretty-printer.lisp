; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

;; For the token-level helpers (identifiers, literals).
(include-book "printer")

(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pretty-printer
  :parents (parsing-and-printing)
  :short "A pretty-printer of Remora from the abstract syntax,
          in the style of the ACL2 prettyprinter (@('ppr1')/@('ppr2'))."
  :long
  (xdoc::topstring
   (xdoc::codeblock
    "(pretty-print-file f :width 80 :flat-margin 60)"
    "(pretty-print-expr e :width 80 :flat-margin 60)")
   (xdoc::p
    "This is a port of ACL2's prettyprinter (@('ppr1') and @('ppr2') in
     @('basis-a.lisp')).  It works bottom-up: each subform is laid out
     in the available width, and the enclosing form chooses its layout
     from the widths of the results.  The output is more compact than
     that of the @(see printer), which either fits a group on one line
     or breaks all of it.")
   (xdoc::p
    "There are three steps:")
   (xdoc::ol
    (xdoc::li
     "@(tsee expr-to-pform), @(tsee decl-to-pform), etc. map the AST to
      @(tsee pform)s, a small tree of tokens and bracketed lists.")
    (xdoc::li
     "@(tsee pform-to-ptuple) chooses a layout for each form,
      as a @(tsee ptuple).")
    (xdoc::li
     "@(tsee ptuple-print) renders the tuples to code points."))
   (xdoc::p
    "A list @('(head arg ...)') is laid out in one of these ways:")
   (xdoc::ul
    (xdoc::li
     "Flat: on one line, if no wider than @('flat-margin').")
    (xdoc::li
     "Wide: the arguments in a column after the head.")
    (xdoc::li
     "Indented: the arguments in a column under the head,
      indented by up to 5.")
    (xdoc::li
     "Header: for @('let'), @('fn'), @('fun'), @('Forall'), etc.
      The first argument stays on the line of the head,
      and the body is indented by 2.
      The body of a scoping form, such as @('let') or @('fn'),
      always starts on a new line."))
   (xdoc::p
    "Widths are in code points, and include the closing brackets
     that follow a form on its last line."))
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
       "@(':atom'): token text, as code points.")
      (xdoc::li
       "@(':prefix'): text glued to the front of a form, like the
        @('@') of an @('@f') call or the @(': ') of a type ascription.")
      (xdoc::li
       "@(':list'): forms between an open and a close bracket.
        With @('headerp'), the first argument is a header,
        like the bindings of @('let').
        With @('breakp'), the arguments after the header
        always start on a new line.")))
    (:atom ((cps nat-list)))
    (:prefix ((cps nat-list) (body pform)))
    (:list ((open natp) (close natp) (headerp booleanp) (breakp booleanp)
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

(define pform-paren ((elems pform-listp)
                     &key
                     ((headerp booleanp) 'nil)
                     ((breakp booleanp) 'nil))
  :returns (x pformp)
  :short "Parenthesized form."
  (make-pform-list :open #x28 :close #x29
                   :headerp headerp :breakp breakp :elems elems))

(define pform-bracket ((elems pform-listp))
  :returns (x pformp)
  :short "Square-bracketed form."
  (make-pform-list :open #x5B :close #x5D
                   :headerp nil :breakp nil :elems elems))

(define pform-prefix-ascii ((s stringp) (body pformp))
  :returns (x pformp)
  :short "Glue an ASCII prefix onto a form."
  (make-pform-prefix :cps (ascii-string=>codepoints s) :body body))

(defmacro+ pform-op (keyword &rest args)
  :parents (pretty-printer)
  :short "Parenthesized form starting with a keyword,
          given as an ASCII string literal."
  `(pform-paren (list (pform-ascii ,keyword) ,@args)))

(defmacro+ pform-op* (keyword &rest args)
  :parents (pretty-printer)
  :short "Like @(tsee pform-op), but the last argument is a list of
          forms."
  `(pform-paren (list* (pform-ascii ,keyword) ,@args)))

(defmacro+ pform-header-op (keyword header &rest body)
  :parents (pretty-printer)
  :short "Parenthesized form with a header argument."
  `(pform-paren (list (pform-ascii ,keyword) ,header ,@body)
                :headerp t))

(defmacro+ pform-scope-op (keyword header body)
  :parents (pretty-printer)
  :short "Parenthesized form with a header argument,
          whose body always starts on a new line."
  `(pform-paren (list (pform-ascii ,keyword) ,header ,body)
                :headerp t :breakp t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Flat size and flat printing of print forms.
;;

(define pform-atomic-p ((x pformp))
  :returns (yes booleanp)
  :short "Is @('x') an atom, possibly under prefixes?"
  :measure (pform-count x)
  (pform-case x
    :atom t
    :prefix (pform-atomic-p x.body)
    :list nil))

(defines pform-must-break-p
  :short "Does @('x') contain a form that cannot be printed flat?"
  :verify-guards :after-returns

  (define pform-must-break-p ((x pformp))
    :returns (yes booleanp)
    :measure (pform-count x)
    (pform-case x
      :atom nil
      :prefix (pform-must-break-p x.body)
      :list (or (and x.breakp (consp (cddr x.elems)))
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

;; Printing functions cons code points onto acc, in reverse order.

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
      "The @('width') is that of the widest line, including the closing
       brackets that follow the form on its last line.")
     (xdoc::ul
      (xdoc::li
       "@(':flat'): a row of forms on one line.")
      (xdoc::li
       "@(':prefix'): prefix text followed by a tuple.")
      (xdoc::li
       "@(':block'): a head followed by up to two columns of rows,
        each at its indent from the open bracket.
        The first column starts on the line of the head
        unless @('break1') holds;
        the second always starts on a new line.
        The wide and indented layouts use one column;
        the header layout puts the header in the first
        and the body in the second.")))
    (:flat ((width natp) (forms pform-list)))
    (:prefix ((width natp) (cps nat-list) (body ptuple)))
    (:block ((width natp) (open natp) (close natp)
             (head ptuple)
             (break1 booleanp) (indent1 natp) (rows1 ptuple-list)
             (indent2 natp) (rows2 ptuple-list)))
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
    :block x.width))

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
  :short "Add a tuple to the front of a column.
          Port of ACL2's @('cons-ppr1')."
  :long
  (xdoc::topstring
   (xdoc::p
    "An atomic form is merged into the top row of the column if that row
     is flat and the result fits in @('width') and @('flat-margin').
     This packs short arguments, like the elements of an array literal,
     several per line."))
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
    "@('width') is the number of columns available.
     @('rpc') is the number of closing brackets
     that will follow the form on its last line.
     @('flat-margin') is the maximum width of a form printed flat."))
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
             (head (car x.elems))
             (args (cdr x.elems))
             (atomicp (pform-atomic-p head))
             ;; There is nothing to lay out in `(atom)'.
             ((when (and atomicp (endp args))) flat)
             ;; The head is followed by our close bracket only if it is
             ;; the last element.
             (head-tup (pform-to-ptuple head
                                        width-1
                                        (if (consp args) 0 (+ rpc 1))
                                        flat-margin))
             (head-sz (ptuple-width head-tup))
             ((when (and x.headerp atomicp))
              ;; Port of the SPECIAL-TERM case.  A short atomic header
              ;; is glued to the head, like the name in `(defun name'.
              (b* ((header (car args))
                   (body (pform-list-to-ptuples (cdr args)
                                                width-1
                                                (+ rpc 1)
                                                flat-margin))
                   (body-max (ptuple-list-max-width body))
                   (header-sz (pform-flat-size header))
                   (gluep (and (pform-atomic-p header)
                               (<= (+ head-sz 1 header-sz) width-1)))
                   (head-tup (if gluep
                                 (make-ptuple-flat
                                  :width (+ head-sz 1 header-sz)
                                  :forms (list head header))
                               head-tup))
                   (head-sz (ptuple-width head-tup))
                   (rows1 (and (not gluep)
                               (list (pform-to-ptuple header
                                                      width-1
                                                      (if (endp body)
                                                          (+ rpc 1)
                                                        0)
                                                      flat-margin))))
                   (max1 (ptuple-list-max-width rows1))
                   (break1 (and (not gluep)
                                (>= (+ head-sz max1) width-1)))
                   (indent1 (if break1
                                (max 1 (- width-1 max1))
                              (+ head-sz 2)))
                   (indent2 (if (or (>= body-max width-1)
                                    (and break1 (eql indent1 1)))
                                1
                              2)))
                (make-ptuple-block
                 :width (+ 1 (max (max head-sz (+ body-max indent2 -1))
                                  (+ indent1 -1 max1)))
                 :open x.open :close x.close
                 :head head-tup
                 :break1 break1 :indent1 indent1 :rows1 rows1
                 :indent2 indent2 :rows2 body)))
             ;; Each arg gets the full width minus 1 (for the minimal
             ;; indentation).
             (rows (pform-list-to-ptuples args width-1 (+ rpc 1) flat-margin))
             ;; A non-atomic head (e.g. a lambda being applied) is
             ;; treated as one more row of the column, indented by 1.
             (rows-max (if atomicp
                           (ptuple-list-max-width rows)
                         (max head-sz (ptuple-list-max-width rows))))
             ;; Wide if there is room for the open bracket, the head, a
             ;; space, and the widest argument.
             (widep (and atomicp
                         (<= (+ head-sz 2 rows-max) width)))
             ;; Otherwise indent the args so that the widest one ends at
             ;; the right margin, but by at most 5.
             (indent (cond (widep (+ head-sz 2))
                           ((and atomicp (< rows-max width))
                            (min 5 (- width rows-max)))
                           (t 1))))
          (make-ptuple-block :width (+ rows-max indent)
                             :open x.open :close x.close
                             :head head-tup
                             :break1 (not widep) :indent1 indent :rows1 rows
                             :indent2 0 :rows2 nil)))))

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

(define newline-acc ((col natp) (acc nat-listp))
  :returns (acc2 nat-listp)
  :short "Cons a newline and then @('col') spaces onto @('acc')."
  :verify-guards nil
  (if (zp col)
      (cons #x0A (nat-list-fix acc))
    (cons #x20 (newline-acc (1- col) acc)))
  ///
  (verify-guards newline-acc))

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
      :block (b* ((col1 (+ (lnfix col) x.indent1))
                  (col2 (+ (lnfix col) x.indent2))
                  (acc (cons x.open (nat-list-fix acc)))
                  (acc (ptuple-print x.head (+ (lnfix col) 1) acc))
                  (acc (if (consp x.rows1)
                           (ptuple-list-print-column
                            x.rows1
                            col1
                            (if x.break1
                                (newline-acc col1 acc)
                              (cons #x20 acc)))
                         acc))
                  (acc (if (consp x.rows2)
                           (ptuple-list-print-column x.rows2
                                                     col2
                                                     (newline-acc col2 acc))
                         acc)))
               (cons x.close acc))))

  (define ptuple-list-print-column ((xs ptuple-listp) (col natp) (acc nat-listp))
    :returns (acc2 nat-listp)
    :short "Print tuples in a column at @('col'), one per line, with the
            print head already at @('col')."
    :measure (ptuple-list-count xs)
    (b* (((when (endp xs)) (nat-list-fix acc))
         (acc (ptuple-print (car xs) col acc))
         ((when (endp (cdr xs))) acc))
      (ptuple-list-print-column (cdr xs) col (newline-acc col acc)))))

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

(define codepoints-to-utf8-string ((cps nat-listp))
  :returns (s stringp)
  :short "UTF-8 encode a code-point list into an ACL2 string.  Returns
          the empty string on invalid code points (unreachable for
          well-formed ASTs)."
  (b* (((unless (ustring? cps)) "")
       (bytes (ustring=>utf8 cps))
       ((unless (unsigned-byte-listp 8 bytes)) ""))
    (nats=>string bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; AST -> pform.
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

(define nat-to-pform ((n natp))
  :returns (x pformp)
  (pform-atom (nat-to-dec-codepoints n)))

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

(std::defprojection nat-list-to-pforms ((x nat-listp))
  :returns (xs pform-listp)
  (nat-to-pform x))

(std::defprojection ispace-var-list-to-pforms ((x ispace-var-listp))
  :returns (xs pform-listp)
  (ispace-var-to-pform x))

(std::defprojection type-var-list-to-pforms ((x type-var-listp))
  :returns (xs pform-listp)
  (type-var-to-pform x))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dim-to-pform
  :short "Print forms for @(tsee dim) and @(tsee dim-list)."
  :verify-guards :after-returns

  (define dim-to-pform ((d dimp))
    :returns (x pformp)
    :measure (dim-count d)
    (dim-case d
      :var (pform-sigil-utf8 #x24 d.name)
      :const (nat-to-pform d.val)
      :add (pform-op* "+" (dim-list-to-pforms d.dims))
      :mul (pform-op* "*" (dim-list-to-pforms d.dims))
      :sub (pform-op* "-" (dim-list-to-pforms d.dims))))

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
      :dims (pform-op* "dims" (dim-list-to-pforms s.dims))
      :append (pform-op* "++" (shape-list-to-pforms s.shapes))
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
  :verify-guards :after-returns

  (define type-to-pform ((ty typep))
    :returns (x pformp)
    :measure (type-count ty)
    (type-case ty
      :var (type-var-to-pform ty.var)
      :base (base-type-to-pform ty.type)
      :array (pform-op "A"
                       (type-to-pform ty.elem)
                       (ispace-to-pform ty.ispace))
      :bracket (pform-bracket (cons (type-to-pform ty.elem)
                                    (ispace-list-to-pforms ty.ispaces)))
      :fun (pform-op "->"
                     (type-to-pform ty.in)
                     (type-to-pform ty.out))
      :funn (pform-op "->"
                      (pform-paren (type-list-to-pforms ty.in))
                      (type-to-pform ty.out))
      :forall (pform-header-op "Forall"
                               (pform-paren (list (type-var-to-pform ty.param)))
                               (type-to-pform ty.body))
      :foralln (pform-header-op "Forall"
                                (pform-paren (type-var-list-to-pforms ty.params))
                                (type-to-pform ty.body))
      :pi (pform-header-op "Pi"
                           (pform-paren (list (ispace-var-to-pform ty.param)))
                           (type-to-pform ty.body))
      :pin (pform-header-op "Pi"
                            (pform-paren (ispace-var-list-to-pforms ty.params))
                            (type-to-pform ty.body))
      :sigma (pform-header-op "Sigma"
                              (pform-paren (list (ispace-var-to-pform ty.param)))
                              (type-to-pform ty.body))
      :sigman (pform-header-op "Sigma"
                               (pform-paren (ispace-var-list-to-pforms ty.params))
                               (type-to-pform ty.body))))

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
    "The scoping forms (@('let'), @('fn'), @('t-fn'), @('i-fn'),
     @('unbox'), and function bindings) use @(tsee pform-scope-op).
     The other binding forms and @('box') use @(tsee pform-header-op).
     The rest are ordinary forms.")
   (xdoc::p
    "AST information with no concrete syntax is not printed,
     or causes an error; see the @(see printer)."))
  :verify-guards :after-returns

  (define expr-to-pform ((e exprp))
    :returns (x pform-resultp)
    :measure (expr-count e)
    (expr-case e
      :var (pform-utf8 e.name)
      :atom (atom-to-pform e.atom)
      :array (b* (((ok atoms) (atom-list-to-pforms e.atoms)))
               (pform-op* "array"
                          (pform-bracket (nat-list-to-pforms e.dims))
                          atoms))
      :array-empty (pform-op "array"
                             (pform-bracket (nat-list-to-pforms e.dims))
                             (type-to-pform e.type))
      :frame (b* (((ok exprs) (expr-list-to-pforms e.exprs)))
               (pform-op* "frame"
                          (pform-bracket (nat-list-to-pforms e.dims))
                          exprs))
      :frame-empty (pform-op "frame"
                             (pform-bracket (nat-list-to-pforms e.dims))
                             (type-to-pform e.type))
      :string (pform-atom (string-lit-to-codepoints e.chars))
      :app (b* (((ok fun) (expr-to-pform e.fun))
                ((ok arg) (expr-to-pform e.arg)))
             (pform-paren (list fun arg)))
      :appn (b* (((ok fun) (expr-to-pform e.fun))
                 ((ok args) (expr-list-to-pforms e.args)))
              (pform-paren (cons fun args)))
      :tapp (b* (((ok fun) (expr-to-pform e.fun)))
              (pform-op "t-app" fun (type-to-pform e.arg)))
      :tappn (b* (((ok fun) (expr-to-pform e.fun)))
               (pform-op* "t-app" fun (type-list-to-pforms e.args)))
      :iapp (b* (((ok fun) (expr-to-pform e.fun)))
              (pform-op "i-app" fun (ispace-to-pform e.arg)))
      :iappn (b* (((ok fun) (expr-to-pform e.fun)))
               (pform-op* "i-app" fun (ispace-list-to-pforms e.args)))
      :capp
      ;; "@" exp type-args ispace-args exp*: the "@" is glued to the
      ;; function expression.
      (b* (((ok fun) (expr-to-pform e.fun))
           ((ok args) (expr-list-to-pforms e.args)))
        (pform-paren (list* (pform-prefix-ascii "@" fun)
                            (type-list-option-to-pform e.targs)
                            (ispace-list-option-to-pform e.iargs)
                            args)))
      ;; The optional result type of unbox has no concrete syntax.
      :unbox (b* (((ok target) (expr-to-pform e.target))
                  ((ok body) (expr-to-pform e.body)))
               (pform-scope-op "unbox"
                               (pform-paren (list (ispace-var-to-pform e.ispace)
                                                  (pform-utf8 e.var)
                                                  target))
                               body))
      :unboxn (b* (((ok target) (expr-to-pform e.target))
                   ((ok body) (expr-to-pform e.body)))
                (pform-scope-op "unbox"
                                (pform-paren
                                 (append (ispace-var-list-to-pforms e.ispaces)
                                         (list (pform-utf8 e.var) target)))
                                body))
      :bracket (b* (((ok exprs) (expr-list-to-pforms e.exprs)))
                 (pform-bracket exprs))
      :let (b* (((ok binds) (bind-list-to-pforms e.binds))
                ((ok body) (expr-to-pform e.body)))
             (pform-scope-op "let" (pform-paren binds) body))))

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
                (pform-scope-op "fn" (pform-paren (list pat)) body))
      :lambdan (b* (((ok pats) (pat-list-to-pforms a.params))
                    ((ok body) (expr-to-pform a.body)))
                 (pform-scope-op "fn" (pform-paren pats) body))
      :tlambda (b* (((ok body) (expr-to-pform a.body)))
                 (pform-scope-op "t-fn"
                                 (pform-paren (list (type-var-to-pform a.param)))
                                 body))
      :tlambdan (b* (((ok body) (expr-to-pform a.body)))
                  (pform-scope-op "t-fn"
                                  (pform-paren (type-var-list-to-pforms a.params))
                                  body))
      :ilambda (b* (((ok body) (expr-to-pform a.body)))
                 (pform-scope-op "i-fn"
                                 (pform-paren (list (ispace-var-to-pform a.param)))
                                 body))
      :ilambdan (b* (((ok body) (expr-to-pform a.body)))
                  (pform-scope-op "i-fn"
                                  (pform-paren (ispace-var-list-to-pforms a.params))
                                  body))
      ;; The box-expr grammar rule requires the type.
      :box (type-option-case a.type?
             :none (reserr (list :box-without-type (atom-fix a)))
             :some (b* (((ok array) (expr-to-pform a.array)))
                     (pform-header-op "box"
                                      (pform-paren (list (ispace-to-pform a.ispace)))
                                      array
                                      (type-to-pform a.type?.val))))
      :boxn (type-option-case a.type?
              :none (reserr (list :box-without-type (atom-fix a)))
              :some (b* (((ok array) (expr-to-pform a.array)))
                      (pform-header-op "box"
                                       (pform-paren (ispace-list-to-pforms a.ispaces))
                                       array
                                       (type-to-pform a.type?.val))))))

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
      :ispace (pform-header-op "ispace"
                               (ispace-var-to-pform b.var)
                               (ispace-to-pform b.ispace))
      :type (pform-header-op "type"
                             (type-var-to-pform b.var)
                             (type-to-pform b.type))
      :val
      ;; "val" identifier exp, or "val" "(" identifier : type ")" exp.
      (b* ((sig (type-option-case b.type?
                  :some (pform-paren (list (pform-utf8 b.var)
                                           (colon-type-to-pform b.type?.val)))
                  :none (pform-utf8 b.var)))
           ((ok expr) (expr-to-pform b.expr)))
        (pform-header-op "val" sig expr))
      :fun
      (b* (((ok sig) (fun-sig-to-pform b.var b.params b.type?))
           ((ok expr) (expr-to-pform b.expr)))
        (pform-scope-op "fun" sig expr))
      :tfun
      ;; "t-fun" "(" identifier "(" type-var* ")" [: type] ")" exp
      (b* (((ok expr) (expr-to-pform b.expr))
           (sig (pform-paren (list* (pform-utf8 b.var)
                                    (pform-paren (type-var-list-to-pforms b.params))
                                    (type-option-to-pforms b.type?)))))
        (pform-scope-op "t-fun" sig expr))
      :ifun
      ;; "i-fun" "(" identifier "(" ispace-var* ")" [: type] ")" exp
      (b* (((ok expr) (expr-to-pform b.expr))
           (sig (pform-paren (list* (pform-utf8 b.var)
                                    (pform-paren (ispace-var-list-to-pforms b.params))
                                    (type-option-to-pforms b.type?)))))
        (pform-scope-op "i-fun" sig expr))
      :cfun
      ;; "fun" "(" "@" identifier type-vars ispace-vars pat* : type ")" exp
      (b* (((ok pats) (pat-list-to-pforms b.params))
           ((ok expr) (expr-to-pform b.expr))
           (sig (pform-paren (list* (pform-sigil-utf8 #x40 b.var)
                                    (type-var-list-option-to-pform b.tparams?)
                                    (ispace-var-list-option-to-pform b.iparams?)
                                    (append pats
                                            (list (colon-type-to-pform b.type)))))))
        (pform-scope-op "fun" sig expr))))

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
  (pform-op "import"
            (pform-atom (string-lit-to-codepoints (import->path imp)))))

(std::defprojection import-list-to-pforms ((x import-listp))
  :returns (xs pform-listp)
  (import-to-pform x))

(define decl-to-pform ((d declp))
  :returns (x pform-resultp)
  (decl-case d
    ;; "def" bind
    :def (b* (((ok bind) (bind-to-pform d.bind)))
           (pform-op "def" bind))
    ;; "entry" "(" fun-sig ")" exp
    :entry (b* (((ok sig) (fun-sig-to-pform d.var d.params d.type?))
                ((ok expr) (expr-to-pform d.expr)))
             (pform-scope-op "entry" sig expr))))

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
  (codepoints-to-utf8-string
   (pretty-print-expr-to-codepoints e :width width :flat-margin flat-margin)))

(define pretty-print-file-to-codepoints ((f filep)
                                         &key
                                         ((width natp) '80)
                                         ((flat-margin natp) '60))
  :returns (cps nat-listp)
  :short "Render a @(tsee file) to a list of Unicode code points:
          the imports one per line, then a blank line, then the
          declarations separated by blank lines.  Returns the empty list
          if the AST has no concrete syntax."
  (b* (((file f) f)
       (imports (import-list-to-pforms f.imports))
       (decls (decl-list-to-pforms f.decls))
       ((when (reserrp decls)) nil)
       (acc (pform-list-print-separated imports width flat-margin nil nil))
       (acc (if (and (consp imports) (consp decls))
                (list* #x0A #x0A acc)
              acc)))
    (rev (pform-list-print-separated decls width flat-margin t acc))))

(define pretty-print-file ((f filep)
                           &key
                           ((width natp) '80)
                           ((flat-margin natp) '60))
  :returns (s stringp)
  :short "Render a @(tsee file) to a UTF-8 encoded ACL2 string, wrapping
          at @('width') columns and printing flat only forms at most
          @('flat-margin') columns wide."
  (codepoints-to-utf8-string
   (pretty-print-file-to-codepoints f :width width :flat-margin flat-margin)))
