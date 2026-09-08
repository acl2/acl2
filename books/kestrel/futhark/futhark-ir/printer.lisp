; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "../codepoint-utilities")
(include-book "abstract-syntax")
(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/strings/cat-base" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/typed-lists/nat-listp" :dir :system)

(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ printer
  :parents (parsing-and-printing)
  :short "Pretty-printer for the supported Futhark IR ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The main entry point is @(tsee print-fut-program), which turns the
     abstract syntax accepted by the parser into textual Futhark SOACS IR.
     The output is intended to be accepted by @(tsee parse-ir-from-string).")
   (xdoc::p
    "The printer is built on a small Wadler/Lindig-style @(tsee pdoc)
     document language, following the organization of the Remora printer.
     The AST-specific functions build documents, and @(tsee layout-pdoc)
     chooses between flat and broken layouts at a requested width.")
   (xdoc::p
    "The recursive expression, statement, body, and declaration ASTs are
     fixtypes, so the printer follows their generated case structure and
     structural counts.  It does not use fuel; recursive calls are justified
     by the FTY-generated measures.")
   (xdoc::p
    "The printer emits ACL2 strings whose bytes are UTF-8.  String-literal
     contents are decoded from the AST string to code points, escaped as
     Futhark IR string literal text, and encoded back to an ACL2 string."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *default-print-width*
  80)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; pdoc combinators.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes pdocs
  :short "Mutually recursive types for the pretty-printer engine."

  (fty::deftagsum pdoc
    :parents (printer pdocs)
    :short "Pretty-printer document combinators."
    (:text ((cps acl2::nat-list)))
    (:line ())
    (:hardline ())
    (:concat ((left pdoc) (right pdoc)))
    (:nest ((amount acl2::nat) (body pdoc)))
    (:group ((body pdoc)))
    :pred pdocp)

  (fty::deflist pdoc-list
    :parents (printer pdocs)
    :short "Lists of @(tsee pdoc)."
    :elt-type pdoc
    :true-listp t
    :elementp-of-nil nil
    :pred pdoc-listp))

(define char-list-all-ascii-p ((chars character-listp))
  :returns (yes booleanp)
  :short "True iff every character has @(tsee char-code) less than 128."
  (cond ((endp chars) t)
        ((< (char-code (car chars)) 128)
         (char-list-all-ascii-p (cdr chars)))
        (t nil)))

(define ascii-string=>codepoints ((str stringp))
  :returns (cps nat-listp)
  :short "Map an ASCII string to its Unicode code points."
  (acl2::chars=>nats (acl2::explode (str-fix str))))

(defmacro pdoc-ascii (str)
  (cond ((not (stringp str))
         (er hard 'pdoc-ascii
             "Expected a string literal, got ~x0." str))
        ((not (char-list-all-ascii-p (acl2::explode str)))
         (er hard 'pdoc-ascii
             "String ~x0 contains a non-ASCII character." str))
        (t `(pdoc-text (quote ,(ascii-string=>codepoints str))))))

(define string-to-pdoc ((str stringp))
  :returns (d pdocp)
  :short "Decode a UTF-8 ACL2 string and wrap the code points as text."
  (pdoc-text (string=>codepoints str)))

(define nat-to-dec-codepoints ((n natp))
  :returns (codepoints nat-listp)
  (ascii-string=>codepoints (str::nat-to-dec-string (nfix n))))

(fty::deftagsum mode
  :short "Layout mode for a sub-document."
  (:flat ())
  (:break ())
  :pred modep)

(fty::defprod cmd
  :short "A pending-document command: a pdoc plus its indent and mode."
  ((indent acl2::nat)
   (mode mode)
   (pdoc pdoc))
  :pred cmdp)

(fty::deflist cmd-list
  :short "List of pending commands."
  :elt-type cmd
  :true-listp t
  :elementp-of-nil nil
  :pred cmd-listp)

(fty::deffold-reduce size
  :short "A positive size for @(tsee pdoc) values."
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

(define cmds-size ((cmds cmd-listp))
  :returns (n natp :rule-classes (:rewrite :type-prescription))
  :short "Sum of @(tsee pdoc-size) across a command list."
  (if (endp cmds)
      0
    (+ (pdoc-size (cmd->pdoc (car cmds)))
       (cmds-size (cdr cmds))))
  ///
  (defrule cmds-size-of-cons
    (equal (cmds-size (cons cmd cmds))
           (+ (pdoc-size (cmd->pdoc cmd))
              (cmds-size cmds)))))

(define fits ((width-left integerp) (cmds cmd-listp))
  :returns (yes booleanp)
  :short "One-line lookahead used by @(tsee layout)."
  (b* (((when (< (ifix width-left) 0)) nil)
       ((when (endp cmds)) t)
       (cmd (car cmds))
       (rest (cdr cmds))
       (indent (cmd->indent cmd))
       (mode (cmd->mode cmd))
       (doc (cmd->pdoc cmd)))
    (pdoc-case doc
      :text (fits (- (ifix width-left) (len doc.cps)) rest)
      :line (mode-case mode
              :flat (fits (- (ifix width-left) 1) rest)
              :break t)
      :hardline t
      :concat (fits width-left
                    (cons (make-cmd :indent indent
                                    :mode mode
                                    :pdoc doc.left)
                          (cons (make-cmd :indent indent
                                          :mode mode
                                          :pdoc doc.right)
                                rest)))
      :nest (fits width-left
                  (cons (make-cmd :indent (+ indent doc.amount)
                                  :mode mode
                                  :pdoc doc.body)
                        rest))
      :group (fits width-left
                   (cons (make-cmd :indent indent
                                   :mode (mode-flat)
                                   :pdoc doc.body)
                         rest))))
  :measure (cmds-size cmds)
  :hints (("Goal" :in-theory (enable pdoc-size))))

(define spaces-codepoints ((n natp))
  :returns (cps nat-listp)
  :hooks nil
  :short "A list of @('n') space code points."
  (if (zp n)
      nil
    (cons #x20 (spaces-codepoints (- n 1)))))

(define newline-and-indent-codepoints ((n natp))
  :returns (cps nat-listp)
  :hooks nil
  :short "Newline followed by @('n') spaces."
  (cons #x0A (spaces-codepoints n)))

(define layout ((width natp) (col natp) (cmds cmd-listp))
  :returns (cps nat-listp)
  :short "Render a command list to a code-point list."
  (b* (((when (endp cmds)) nil)
       (cmd (car cmds))
       (rest (cdr cmds))
       (indent (cmd->indent cmd))
       (mode (cmd->mode cmd))
       (doc (cmd->pdoc cmd)))
    (pdoc-case doc
      :text (append doc.cps
                    (layout width
                            (+ (acl2::lnfix col) (len doc.cps))
                            rest))
      :line (mode-case mode
              :flat (cons #x20
                          (layout width (+ (acl2::lnfix col) 1) rest))
              :break (append (newline-and-indent-codepoints indent)
                             (layout width indent rest)))
      :hardline (append (newline-and-indent-codepoints indent)
                        (layout width indent rest))
      :concat (layout width col
                      (cons (make-cmd :indent indent
                                      :mode mode
                                      :pdoc doc.left)
                            (cons (make-cmd :indent indent
                                            :mode mode
                                            :pdoc doc.right)
                                  rest)))
      :nest (layout width col
                    (cons (make-cmd :indent (+ indent doc.amount)
                                    :mode mode
                                    :pdoc doc.body)
                          rest))
      :group (b* ((flat-cmds
                   (cons (make-cmd :indent indent
                                   :mode (mode-flat)
                                   :pdoc doc.body)
                         rest)))
               (if (fits (- (acl2::lnfix width) (acl2::lnfix col)) flat-cmds)
                   (layout width col flat-cmds)
                 (layout width col
                         (cons (make-cmd :indent indent
                                         :mode (mode-break)
                                         :pdoc doc.body)
                               rest))))))
  :measure (cmds-size cmds)
  :hints (("Goal" :in-theory (enable pdoc-size))))

(define layout-pdoc ((width natp) (doc pdocp))
  :returns (cps nat-listp)
  :short "Render a single @(tsee pdoc) to a code-point list."
  (layout width 0
          (list (make-cmd :indent 0 :mode (mode-break) :pdoc doc))))

(define pdoc-empty ()
  :returns (doc pdocp)
  (pdoc-text nil))

(define pdoc-seq ((docs pdoc-listp))
  :returns (doc pdocp)
  :measure (len docs)
  (cond ((endp docs) (pdoc-empty))
        ((endp (cdr docs)) (pdoc-fix (car docs)))
        (t (pdoc-concat (car docs)
                        (pdoc-seq (cdr docs))))))

(define pdoc-space ()
  :returns (doc pdocp)
  (pdoc-ascii " "))

(define pdoc-bracket ((doc pdocp))
  :returns (out pdocp)
  (pdoc-seq (list (pdoc-ascii "[") doc (pdoc-ascii "]"))))

(define pdoc-paren ((doc pdocp))
  :returns (out pdocp)
  (pdoc-seq (list (pdoc-ascii "(") doc (pdoc-ascii ")"))))

(define pdoc-brace ((doc pdocp))
  :returns (out pdocp)
  (pdoc-seq (list (pdoc-ascii "{") doc (pdoc-ascii "}"))))

(define pdoc-delimited ((open pdocp)
                        (doc pdocp)
                        (close pdocp)
                        (amount natp))
  :returns (out pdocp)
  :short "Group delimited text and nest continuations under the opener."
  (pdoc-group
   (pdoc-seq
    (list (pdoc-fix open)
          (pdoc-nest amount doc)
          (pdoc-fix close)))))

(define pdoc-paren-nest ((doc pdocp) (amount natp))
  :returns (out pdocp)
  (pdoc-delimited (pdoc-ascii "(") doc (pdoc-ascii ")") amount))

(define pdoc-bracket-nest ((doc pdocp) (amount natp))
  :returns (out pdocp)
  (pdoc-delimited (pdoc-ascii "[") doc (pdoc-ascii "]") amount))

(define pdoc-brace-nest ((doc pdocp) (amount natp))
  :returns (out pdocp)
  (pdoc-delimited (pdoc-ascii "{") doc (pdoc-ascii "}") amount))

(define string-codepoint-width ((str stringp))
  :returns (width natp)
  :short "The printer's display width model for a UTF-8 ACL2 string."
  (len (string=>codepoints str)))

(define pdoc-call-like ((prefix pdocp)
                        (prefix-width natp)
                        (args pdocp))
  :returns (out pdocp)
  :short "Group a call and align broken arguments after the opening paren."
  (pdoc-group
   (pdoc-seq
    (list (pdoc-fix prefix)
          (pdoc-ascii "(")
          (pdoc-nest (+ 1 (nfix prefix-width)) args)
          (pdoc-ascii ")")))))

(define pdoc-call-name ((name stringp) (args pdocp))
  :returns (out pdocp)
  (pdoc-call-like (string-to-pdoc name)
                  (string-codepoint-width name)
                  args))

(define pdoc-apply-name ((name stringp) (args pdocp))
  :returns (out pdocp)
  (pdoc-call-like (pdoc-seq (list (pdoc-ascii "apply ")
                                  (string-to-pdoc name)))
                  (+ 6 (string-codepoint-width name))
                  args))

(define pdoc-render-string ((doc pdocp) (width natp))
  :returns (text stringp)
  :short "Render a document as a UTF-8 ACL2 string."
  (b* ((text (codepoints=>string (layout-pdoc width doc)))
       ((when (reserrp text)) ""))
    text))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; String literals.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-string-literal-codepoint ((codepoint natp))
  :returns (codepoints nat-listp)
  :short "Print one decoded string-literal code point as source code points."
  (b* ((codepoint (nfix codepoint)))
    (cond ((eql codepoint #x07) '(#x5C #x61)) ; \a
          ((eql codepoint #x08) '(#x5C #x62)) ; \b
          ((eql codepoint #x09) '(#x5C #x74)) ; \t
          ((eql codepoint #x0A) '(#x5C #x6E)) ; \n
          ((eql codepoint #x0B) '(#x5C #x76)) ; \v
          ((eql codepoint #x0C) '(#x5C #x66)) ; \f
          ((eql codepoint #x0D) '(#x5C #x72)) ; \r
          ((eql codepoint #x22) '(#x5C #x22)) ; \"
          ((eql codepoint #x5C) '(#x5C #x5C)) ; \\
          ((or (< codepoint #x20)
               (eql codepoint #x7F))
           (append (list #x5C)
                   (append (nat-to-dec-codepoints codepoint)
                           (list #x5C #x26))))
          (t (list codepoint)))))

(define print-string-literal-codepoints ((codepoints nat-listp))
  :returns (printed nat-listp)
  (if (endp codepoints)
      nil
    (append (print-string-literal-codepoint (car codepoints))
            (print-string-literal-codepoints (cdr codepoints)))))

(define string-literal-to-codepoints ((str stringp))
  :returns (codepoints nat-listp)
  :short "Print an ACL2 UTF-8 byte string as quoted string code points."
  (cons #x22
        (append (print-string-literal-codepoints (string=>codepoints str))
                (list #x22))))

(define print-string-literal ((str stringp))
  :returns (text stringp)
  :short "Print an ACL2 UTF-8 byte string as a quoted Futhark IR string."
  (b* ((text (codepoints=>string (string-literal-to-codepoints str)))
       ((when (reserrp text)) "\"\""))
    text))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; AST-to-pdoc walkers.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ir-type-to-pdoc-defs
  :verify-guards :after-returns

  (define fut-type-to-pdoc ((type fut-typep))
    :returns (doc pdocp)
    (fut-type-case type
      :prim (string-to-pdoc type.name)
      :array (pdoc-seq
              (list (pdoc-ascii "[")
                    (if type.size
                        (string-to-pdoc type.size)
                      (pdoc-empty))
                    (pdoc-ascii "]")
                    (fut-type-to-pdoc type.elem))))
    :measure (fut-type-count type))

  (define fut-type-list-to-pdoc ((types fut-type-listp))
    :returns (doc pdocp)
    (cond ((endp types) (pdoc-empty))
          ((endp (cdr types)) (fut-type-to-pdoc (car types)))
          (t (pdoc-seq
              (list (fut-type-to-pdoc (car types))
                    (pdoc-ascii ",")
                    (pdoc-line)
                    (fut-type-list-to-pdoc (cdr types))))))
    :measure (fut-type-list-count types)))

(define result-types-to-pdoc ((types fut-type-listp))
  :returns (doc pdocp)
  (pdoc-brace-nest (fut-type-list-to-pdoc types) 1))

(define entry-result-types-to-pdoc ((types fut-type-listp))
  :returns (doc pdocp)
  (if (and (consp types)
           (endp (cdr types)))
      (fut-type-to-pdoc (car types))
    (result-types-to-pdoc types)))

(define print-fut-type ((type fut-typep) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (fut-type-to-pdoc type) width))

(define print-fut-type-list ((types fut-type-listp)
                             &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (fut-type-list-to-pdoc types) width))

(define print-result-types ((types fut-type-listp)
                            &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (result-types-to-pdoc types) width))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-to-pdoc ((param paramp))
  :returns (doc pdocp)
  (b* ((param (param-fix param)))
    (pdoc-group
     (pdoc-seq (list (string-to-pdoc (param->name param))
                     (pdoc-ascii " : ")
                     (fut-type-to-pdoc (param->type param)))))))

(define param-list-to-pdoc ((params param-listp))
  :returns (doc pdocp)
  :measure (len params)
  (cond ((endp params) (pdoc-empty))
        ((endp (cdr params)) (param-to-pdoc (car params)))
        (t (pdoc-seq (list (param-to-pdoc (car params))
                           (pdoc-ascii ",")
                           (pdoc-line)
                           (param-list-to-pdoc (cdr params)))))))

(define params-to-pdoc ((params param-listp))
  :returns (doc pdocp)
  (pdoc-paren-nest (param-list-to-pdoc params) 1))

(define pattern-to-pdoc ((params param-listp))
  :returns (doc pdocp)
  (pdoc-brace-nest (param-list-to-pdoc params) 1))

(define print-param ((param paramp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (param-to-pdoc param) width))

(define print-param-list ((params param-listp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (param-list-to-pdoc params) width))

(define print-params ((params param-listp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (params-to-pdoc params) width))

(define print-pattern ((params param-listp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (pattern-to-pdoc params) width))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm <-of-+-1-and-+-1
   (implies (< x y)
            (< (+ 1 x) (+ 1 y)))))

(local
 (defthm not-equal-of-+-1-and-+-1-when-<
   (implies (< x y)
            (not (equal (+ 1 x) (+ 1 y))))))

(local
 (defthm expr-count-of-stmt-let->expr-linear
   (< (expr-count (stmt-let->expr stmt))
      (stmt-count (stmt-fix stmt)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable stmt-count)))))

(local
 (defthm stmt-list-count-of-body-block->stmts-linear
   (< (stmt-list-count (body-block->stmts body))
      (body-count (body-fix body)))
   :rule-classes :linear
   :hints (("Goal"
            :expand ((body-count body))
            :in-theory (enable body-count)))))

(local
 (defthm expr-list-count-of-body-block->results-linear
   (< (expr-list-count (body-block->results body))
      (body-count (body-fix body)))
   :rule-classes :linear
   :hints (("Goal"
            :expand ((body-count body))
            :in-theory (enable body-count)))))

(defines ir-form-to-pdoc-defs
  :verify-guards :after-returns
  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))

  (define expr-to-pdoc ((expr exprp))
    :returns (doc pdocp)
    (expr-case expr
      :var (string-to-pdoc expr.name)
      :literal (string-to-pdoc expr.text)
      :array (b* ((base (pdoc-group
                         (pdoc-bracket-nest
                          (expr-list-to-pdoc expr.elems) 1))))
               (pdoc-group
                (pdoc-seq (list base
                                (pdoc-line)
                                (pdoc-ascii ": []")
                                (fut-type-to-pdoc expr.type)))))
      :brace (pdoc-brace-nest (expr-list-to-pdoc expr.elems) 1)
      :call (pdoc-call-name expr.fun
                            (expr-list-to-pdoc expr.args))
      :apply (b* ((base (pdoc-apply-name expr.fun
                                         (expr-list-to-pdoc expr.args))))
               (pdoc-group
                (pdoc-seq
                 (list base
                       (pdoc-line)
                       (pdoc-ascii ": ")
                       (result-types-to-pdoc expr.result-types)))))
      :map (pdoc-call-name "map"
                           (expr-list-to-pdoc expr.args))
      :lambda (pdoc-seq
               (list (pdoc-ascii "\\ ")
                     (pattern-to-pdoc expr.params)
                     (pdoc-ascii " : ")
                     (result-types-to-pdoc expr.result-types)
                     (pdoc-ascii " ->")
                     (pdoc-nest 2
                                (pdoc-seq
                                 (list (pdoc-hardline)
                                       (lambda-body-core-to-pdoc expr.body))))))
      :paren (pdoc-paren (expr-to-pdoc expr.expr))
      :raw (string-to-pdoc expr.text))
    :measure (two-nats-measure (expr-count (expr-fix expr)) 0))

  (define expr-list-to-pdoc ((exprs expr-listp))
    :returns (doc pdocp)
    (cond ((endp exprs) (pdoc-empty))
          ((endp (cdr exprs)) (expr-to-pdoc (car exprs)))
          (t (pdoc-seq
              (list (expr-to-pdoc (car exprs))
                    (pdoc-ascii ",")
                    (pdoc-line)
                    (expr-list-to-pdoc (cdr exprs))))))
    :measure (two-nats-measure (expr-list-count exprs) 0))

  (define stmt-to-pdoc ((stmt stmtp))
    :returns (doc pdocp)
    (stmt-case stmt
      :let (pdoc-seq
            (list (pdoc-ascii "let ")
                  (pattern-to-pdoc stmt.pattern)
                  (pdoc-ascii " =")
                  (pdoc-nest 2
                             (pdoc-seq
                              (list (pdoc-hardline)
                                    (expr-to-pdoc stmt.expr)))))))
    :measure (two-nats-measure (stmt-count (stmt-fix stmt)) 1))

  (define stmt-list-to-pdoc ((stmts stmt-listp))
    :returns (doc pdocp)
    (cond ((endp stmts) (pdoc-empty))
          ((endp (cdr stmts)) (stmt-to-pdoc (car stmts)))
          (t (pdoc-seq
              (list (stmt-to-pdoc (car stmts))
                    (pdoc-hardline)
                    (stmt-list-to-pdoc (cdr stmts))))))
    :measure (two-nats-measure (stmt-list-count stmts) 0))

  (define body-core-to-pdoc ((body bodyp))
    :returns (doc pdocp)
    (body-case body
      :block (if (endp body.stmts)
                 (pdoc-seq
                  (list (pdoc-ascii "in ")
                        (pdoc-brace
                         (expr-list-to-pdoc body.results))))
               (pdoc-seq
                (list (stmt-list-to-pdoc body.stmts)
                      (pdoc-hardline)
                      (pdoc-ascii "in ")
                      (pdoc-brace
                       (expr-list-to-pdoc body.results))))))
    :measure (two-nats-measure (body-count (body-fix body)) 0))

  (define lambda-body-core-to-pdoc ((body bodyp))
    :returns (doc pdocp)
    (body-case body
      :block (if (endp body.stmts)
                 (pdoc-brace
                  (expr-list-to-pdoc body.results))
               (body-core-to-pdoc body)))
    :measure (two-nats-measure (body-count (body-fix body)) 1))

  (define body-to-pdoc ((body bodyp))
    :returns (doc pdocp)
    (body-case body
      :block (pdoc-seq
              (list (pdoc-ascii "{")
                    (pdoc-nest 2
                               (pdoc-seq
                                (list (pdoc-hardline)
                                      (if (endp body.stmts)
                                          (pdoc-brace
                                           (expr-list-to-pdoc body.results))
                                        (body-core-to-pdoc body)))))
                    (pdoc-hardline)
                    (pdoc-ascii "}"))))
    :measure (two-nats-measure (body-count (body-fix body)) 2))

  (define decl-to-pdoc ((decl declp))
    :returns (doc pdocp)
    (decl-case decl
      :fun (pdoc-seq
            (list (pdoc-ascii "fun")
                  (pdoc-nest 2
                             (pdoc-seq
                              (list (pdoc-hardline)
                                    (string-to-pdoc decl.name)
                                    (pdoc-space)
                                    (params-to-pdoc decl.params)
                                    (pdoc-hardline)
                                    (pdoc-ascii ": ")
                                    (result-types-to-pdoc decl.result-types)
                                    (pdoc-ascii " = ")
                                    (body-to-pdoc decl.body))))))
      :entry (pdoc-seq
              (list (pdoc-ascii "entry(")
                    (pdoc-text
                     (string-literal-to-codepoints decl.external-name))
                    (pdoc-ascii ",")
                    (pdoc-nest 6
                               (pdoc-seq
                                (list (pdoc-hardline)
                                      (pdoc-ascii "{},")
                                      (pdoc-hardline)
                                      (entry-result-types-to-pdoc
                                       decl.entry-result-types)
                                      (if decl.doc
                                          (pdoc-seq
                                           (list (pdoc-ascii ",")
                                                 (pdoc-hardline)
                                                 (pdoc-text
                                                  (string-literal-to-codepoints
                                                   decl.doc))))
                                        (pdoc-empty)))))
                    (pdoc-ascii ")")
                    (pdoc-nest 2
                               (pdoc-seq
                                (list (pdoc-hardline)
                                      (string-to-pdoc decl.name)
                                      (pdoc-space)
                                      (params-to-pdoc decl.params)
                                      (pdoc-hardline)
                                      (pdoc-ascii ": ")
                                      (result-types-to-pdoc decl.result-types)
                                      (pdoc-ascii " = ")
                                      (body-to-pdoc decl.body)))))))
    :measure (two-nats-measure (decl-count (decl-fix decl)) 3))

  (define decl-list-to-pdoc ((decls decl-listp))
    :returns (doc pdocp)
    (cond ((endp decls) (pdoc-empty))
          ((endp (cdr decls)) (decl-to-pdoc (car decls)))
          (t (pdoc-seq
              (list (decl-to-pdoc (car decls))
                    (pdoc-hardline)
                    (pdoc-hardline)
                    (decl-list-to-pdoc (cdr decls))))))
    :measure (two-nats-measure (decl-list-count decls) 0)))

(define print-expr ((expr exprp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (expr-to-pdoc expr) width))

(define print-expr-list ((exprs expr-listp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (expr-list-to-pdoc exprs) width))

(define print-stmt ((stmt stmtp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (stmt-to-pdoc stmt) width))

(define print-stmt-list ((stmts stmt-listp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (stmt-list-to-pdoc stmts) width))

(define print-body ((body bodyp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (body-to-pdoc body) width))

(define print-decl ((decl declp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (decl-to-pdoc decl) width))

(define print-decl-list ((decls decl-listp) &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (decl-list-to-pdoc decls) width))

(define fut-program-to-pdoc ((program fut-programp))
  :returns (doc pdocp)
  (b* ((program (fut-program-fix program))
       (name-source (fut-program->name-source program))
       (decls (fut-program->decls program))
       (name-doc (if name-source
                     (pdoc-seq
                      (list (pdoc-ascii "name_source {")
                            (string-to-pdoc name-source)
                            (pdoc-ascii "}")
                            (pdoc-hardline)
                            (pdoc-hardline)))
                   (pdoc-empty)))
       (types-doc (pdoc-seq
                   (list (pdoc-ascii "types {")
                         (pdoc-hardline)
                         (pdoc-hardline)
                         (pdoc-ascii "}")
                         (pdoc-hardline)
                         (pdoc-hardline)))))
    (pdoc-seq
     (list name-doc
           types-doc
           (decl-list-to-pdoc decls)))))

(define print-fut-program ((program fut-programp)
                           &key ((width natp) '*default-print-width*))
  :returns (text stringp)
  (pdoc-render-string (fut-program-to-pdoc program) width))
