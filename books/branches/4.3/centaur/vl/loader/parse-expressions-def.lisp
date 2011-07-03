; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(include-book "parse-utils")
(local (include-book "../util/arithmetic"))


(local (in-theory (disable consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr)))


(defsection vl-mixed-binop-list-p

; All of the binary operators in Verilog are left-associative, but it is
; difficult to directly build a left-associative structure in straightforward
; recursive descent parsing.
;
; So instead, our expression parsers build MIXED BINOP LISTS which we then
; left-associate later.
;
; Ignoring attributes for a moment, the idea is that these lists look like the
; following: (EXPR OP EXPR OP EXPR OP EXPR ... EXPR).  So for instance, to
; parse the Verilog source code "1 + 2 + 3 + 4", the plan is first to build a
; mixed list which looks like (1 + 2 + 3 + 4), and then to fully left-associate
; this list into the expected form, (+ (+ (+ 1 2) 3) 4).
;
; Attributes only make this slightly more complex.  The actual format of our
; mixed list is (EXPR OP ATTS EXPR OP ATTS ... EXPR, where each ATTS belongs to
; the OP immediately preceeding it.

  (defund vl-mixed-binop-list-p (x)
    (declare (xargs :guard t))
    (and (consp x)
         (vl-expr-p (car x))
         (or (not (consp (cdr x)))
             (and (consp (cddr x))
                  (consp (cdddr x))
                  (let ((op   (second x))
                        (atts (third x))
                        (rest (cdddr x)))
                    (and (vl-op-p op)
                         (equal (vl-op-arity op) 2)
                         (vl-atts-p atts)
                         (vl-mixed-binop-list-p rest)))))))

  (local (in-theory (enable vl-mixed-binop-list-p)))

  (defthm vl-mixed-binop-list-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-mixed-binop-list-p x)
                    nil)))

  (defthm vl-mixed-binop-list-p-of-singleton
    (equal (vl-mixed-binop-list-p (list x))
           (vl-expr-p x)))

  (defthm vl-mixed-binop-list-p-of-list*
    (equal (vl-mixed-binop-list-p (list* x y z w))
           (and (vl-expr-p x)
                (vl-op-p y)
                (equal (vl-op-arity y) 2)
                (vl-atts-p z)
                (vl-mixed-binop-list-p w)))))



(defsection vl-left-associate-mixed-binop-list

  (defund vl-left-associate-mixed-binop-list (x)
    (declare (xargs :guard (vl-mixed-binop-list-p x)
                    :measure (len x)
                    :verify-guards nil))
    (if (consp (cdr x))
        (let ((e1      (first x))
              (op      (second x))
              (atts    (third x))
              (e2      (fourth x))
              (rest    (cddddr x)))
          ;; At each step, we just merge the first two expressions using the op
          ;; and attributes between them.
          (vl-left-associate-mixed-binop-list
           (cons (make-vl-nonatom :op op
                                  :atts atts
                                  :args (list e1 e2))
                 rest)))
      (car x)))

  (local (in-theory (enable vl-mixed-binop-list-p
                            vl-left-associate-mixed-binop-list)))

  (defthm vl-expr-p-of-vl-left-associate-mixed-binop-list
    (implies (vl-mixed-binop-list-p x)
             (vl-expr-p (vl-left-associate-mixed-binop-list x)))
    :hints(("Goal" :induct (vl-left-associate-mixed-binop-list x))))

  (verify-guards vl-left-associate-mixed-binop-list))



; Another operation which we want to left-associate is bit/part selection,
; which might also be called array or memory indexing.  The idea is that for
; "foo[1][2][3]", we want to build an expression of the form:
;
;     (bitselect (bitselect (bitselect foo 1)
;                           2)
;                3)
;
; This is easier because we are only dealing with one operation and no
; attributes, so we can just read the list of selects and then left-associate
; them.  We also add some support for dealing with part selects from ranges.

(defund vl-build-bitselect-nest (expr bitselects)
  (declare (xargs :guard (and (vl-expr-p expr)
                              (vl-exprlist-p bitselects))))
  (if (consp bitselects)
      (vl-build-bitselect-nest
       (make-vl-nonatom :op :vl-bitselect
                        :args (list expr (car bitselects)))
       (cdr bitselects))
    expr))

(defthm vl-expr-p-of-vl-build-bitselect-nest
  (implies (and (force (vl-expr-p expr))
                (force (vl-exprlist-p bitselects)))
           (vl-expr-p (vl-build-bitselect-nest expr bitselects)))
  :hints(("Goal" :in-theory (enable vl-build-bitselect-nest))))


(defenum vl-erangetype-p
  (:vl-bitselect
   :vl-colon
   :vl-pluscolon
   :vl-minuscolon)
  :parents (parser))

(deflist vl-erangetypelist-p (x)
  (vl-erangetype-p x)
  :elementp-of-nil nil)

(defthm vl-erangetype-p-of-vl-type-of-matched-token
  ;; ugly, but effective.
  (implies (vl-erangetypelist-p types)
           (equal (vl-erangetype-p (vl-type-of-matched-token types tokens))
                  (if (vl-type-of-matched-token types tokens)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token))))



(defaggregate vl-erange
  ;; For bit selects, we just set left and right to the same expression.
  (type left right)
  :tag :vl-erange
  :legiblep nil
  :require ((vl-erangetype-p-of-vl-erange->type (vl-erangetype-p type))
            (vl-expr-p-of-vl-erange->left       (vl-expr-p left))
            (vl-expr-p-of-vl-erange->right      (vl-expr-p right)))
  :parents (parser))


(defsection vl-build-range-select

  (defund vl-build-range-select (expr range)
    (declare (xargs :guard (and (vl-expr-p expr)
                                (vl-erange-p range))))
    (let ((type  (vl-erange->type range))
          (left  (vl-erange->left range))
          (right (vl-erange->right range)))
      (case type
        (:vl-bitselect
         (make-vl-nonatom :op :vl-bitselect
                          :args (list expr left)))
        (:vl-colon
         (make-vl-nonatom :op :vl-partselect-colon
                          :args (list expr left right)))
        (:vl-pluscolon
         (make-vl-nonatom :op :vl-partselect-pluscolon
                          :args (list expr left right)))
        (:vl-minuscolon
         (make-vl-nonatom :op :vl-partselect-minuscolon
                          :args (list expr left right))))))

  (local (in-theory (enable vl-build-range-select)))

  (local (defthm lemma
           (implies (and (vl-erange-p range)
                         (not (equal (vl-erange->type range) :vl-bitselect))
                         (not (equal (vl-erange->type range) :vl-colon))
                         (not (equal (vl-erange->type range) :vl-pluscolon)))
                    (equal (vl-erange->type range)
                           :vl-minuscolon))
           :hints(("Goal"
                   :in-theory (e/d (vl-erangetype-p)
                                   (vl-erangetype-p-of-vl-erange->type))
                   :use ((:instance vl-erangetype-p-of-vl-erange->type (x range)))))))

  (defthm vl-expr-p-of-vl-build-range-select
    (implies (and (force (vl-expr-p expr))
                  (force (vl-erange-p range)))
             (vl-expr-p (vl-build-range-select expr range)))))



(defsection vl-make-guts-from-inttoken

  (defund vl-make-guts-from-inttoken (x)
    (declare (xargs :guard (vl-inttoken-p x)))
    (b* (((vl-inttoken x) x))
      (if x.value
          (make-vl-constint :origwidth  x.width
                            :origtype   (if x.signedp :vl-signed :vl-unsigned)
                            :value      x.value
                            :wasunsized x.wasunsized)
        (make-vl-weirdint :origwidth  x.width
                          :origtype   (if x.signedp :vl-signed :vl-unsigned)
                          :bits       x.bits
                          :wasunsized x.wasunsized))))

  (local (in-theory (enable vl-make-guts-from-inttoken)))

  (defthm vl-atomguts-p-of-make-guts-from-inttoken
    (implies (force (vl-inttoken-p x))
             (vl-atomguts-p (vl-make-guts-from-inttoken x)))))




; We are now ready to introduce our parsing functions.
;
; Everything about expressions is mutually recursive, so this is complicated.
; I have put the grammar rules in front of the functions that parse them, but
; note that the productions found below are not exactly the same as those in
; the Verilog standard:
;
;    1. I have removed any "bare aliases" which only served to complicate
;       the grammar, such as "base_expression ::= expression" and
;       "attr_name ::= identifier".
;
;    2. I do not support the notion of "constant expressions" -- I just use
;       plain expressions instead.

(vl-mutual-recursion

; attr_spec ::= identifier [ '=' expression ]
;
; attribute_instance ::= '(*' attr_spec { ',' attr_spec } '*)'
;
; We parse attributes_instance into a vl-atts-p, which is just an alist that
; map names to expressions (or nil).  It's common for other grammar rules that
; use attributes to write "{ attribute_instance }" --- that is, any number of
; attribute_instances.  In this case, we merge the alists using append, so
; that for instance
;
;    (* foo *) (* bar *)
;
; Is treated in just the same way as
;
;    (* foo bar *).
;
; Shadowed pairs are allowed to remain in the alist, so you can detect whether
; an attribute has occurred multiple times, etc.

 (defparser vl-parse-attr-spec (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)
                   :verify-guards nil
                   :hints(("Goal"
                           :do-not '(generalize fertilize)
                           :do-not-induct t))))
   (seqw tokens warnings
         (id := (vl-match-token :vl-idtoken))
         (when (vl-is-token? :vl-equalsign)
           (:= (vl-match-token :vl-equalsign))
           (expr := (vl-parse-expression)))
         (return (cons (vl-idtoken->name id) expr))))

 (defparser vl-parse-attribute-instance-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   (seqw tokens warnings
         (first :s= (vl-parse-attr-spec))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match-token :vl-comma))
           (rest := (vl-parse-attribute-instance-aux)))
         (return (cons first rest))))

 (defparser vl-parse-attribute-instance (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (:= (vl-match-token :vl-beginattr))
         (data := (vl-parse-attribute-instance-aux))
         (:= (vl-match-token :vl-endattr))
         (return data)))

 (defparser vl-parse-0+-attribute-instances (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   (seqw tokens warnings
         (when (not (vl-is-token? :vl-beginattr))
           (return nil))
         (first :s= (vl-parse-attribute-instance))
         (rest := (vl-parse-0+-attribute-instances))
         (return (append first rest))))


; system_function_call ::=
;    system_identifier [ '(' expression { ',' expression } ')' ]
;
; Strangely, system calls are not allowed to have attributes even though
; regular function calls are allowed to.

 (defparser vl-parse-1+-expressions-separated-by-commas (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 27)))
   (seqw tokens warnings
         (first :s= (vl-parse-expression))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match-token :vl-comma))
           (rest := (vl-parse-1+-expressions-separated-by-commas)))
         (return (cons first rest))))

 (defparser vl-parse-system-function-call (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (fn := (vl-match-token :vl-sysidtoken))
         (when (vl-is-token? :vl-lparen)
           (:= (vl-match-token :vl-lparen))
           (args := (vl-parse-1+-expressions-separated-by-commas))
           (:= (vl-match-token :vl-rparen)))
         (return
          (let ((fname (make-vl-sysfunname :name (vl-sysidtoken->name fn))))
            (make-vl-nonatom :op :vl-syscall
                             :args (cons (make-vl-atom :guts fname) args))))))


; mintypmax_expression ::=
;    expression
;  | expression ':' expression ':' expression

 (defparser vl-parse-mintypmax-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 27)))
   (seqw tokens warnings
         (min :s= (vl-parse-expression))
         (unless (vl-is-token? :vl-colon)
           (return min))
         (:= (vl-match-token :vl-colon))
         (typ :s= (vl-parse-expression))
         (:= (vl-match-token :vl-colon))
         (max := (vl-parse-expression))
         (return (make-vl-nonatom :op :vl-mintypmax
                                  :args (list min typ max)))))


; range_expression ::=
;    expression
;  | expression ':' expression
;  | expression '+:' expression
;  | expression '-:' expression

 (defparser vl-parse-range-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 27)))
   (let ((range-separators '(:vl-colon :vl-pluscolon :vl-minuscolon)))
     (seqw tokens warnings
           (e1 :s= (vl-parse-expression))
           (unless (vl-is-some-token? range-separators)
             (return (vl-erange :vl-bitselect e1 e1)))
           (sep := (vl-match-some-token range-separators))
           (e2 := (vl-parse-expression))
           (return (vl-erange (vl-token->type sep) e1 e2)))))



; concatenation ::= '{' expression { ',' expression } '}'
;
; multiple_concatenation ::= '{' expression concatenation '}'
;
; Unfortunately, we don't know which of these is being parsed until we have
; read the character which follows "'{' expression".  If we find a comma, or a
; closing brace, we know it is a concatenation.  Otherwise, if we find an
; opening brace, we know it is a multiple concatenation.

 (defparser vl-parse-concatenation (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (:= (vl-match-token :vl-lcurly))
         (args := (vl-parse-1+-expressions-separated-by-commas))
         (:= (vl-match-token :vl-rcurly))
         (return (make-vl-nonatom :op :vl-concat :args args))))

 (defparser vl-parse-concatenation-or-multiple-concatenation (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (:= (vl-match-token :vl-lcurly))
         (e1 :s= (vl-parse-expression))

         (when (vl-is-token? :vl-lcurly)
           ;; A multiple concatenation
           (concat := (vl-parse-concatenation))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-nonatom :op :vl-multiconcat
                                    :args (list e1 concat))))

         ;; Otherwise, a regular concat -- does it have extra args?
         (when (vl-is-token? :vl-comma)
           (:= (vl-match-token :vl-comma))
           (rest := (vl-parse-1+-expressions-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-nonatom :op :vl-concat
                                    :args (cons e1 rest))))

         ;; Nope, just a concat of one expression.
         (:= (vl-match-token :vl-rcurly))
         (return (make-vl-nonatom :op :vl-concat
                                  :args (list e1)))))




; hierarchial_identifier ::=
;   { identifier [ '[' expression ']' ] '.' } identifier

 (defparser vl-parse-hierarchial-identifier (recursivep tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)))

; It should be easy to convince yourself that the above is equivalent to:
;
;    identifier
;  | identifier '.' hierarchial_identifier
;  | identifier '[' expression ']' '.' hierarchial_identifier
;
; And this function is more easily understood by looking at these three rules.
; Even so, it is a little tricky.  Because bracketed expressions can
; legitimately follow HIDs (e.g., see "primary"), it is not until we have read
; the dot that we are sure this expression, in the third production, belongs to
; this HID.  So if there is no dot, we will actually backtrack and only take
; the first identifier we have seen.
;
; The recursivep argument is used to determine, in the base case, whether the
; atom we build should be a hidpiece or an idtoken.  Basically, if we have not
; yet seen a dot then recursivep is nil and we want to just build a regular id
; token.  But otherwise, this id is just part of a hierarchial identifier, so
; we convert it into a hidpiece.

   (seqw tokens warnings
         (id := (vl-match-token :vl-idtoken))

         (when (vl-is-token? :vl-dot)
           (:= (vl-match-token :vl-dot))
           (tail :s= (vl-parse-hierarchial-identifier t))
           (return
            (let ((part (make-vl-hidpiece :name (vl-idtoken->name id))))
              (make-vl-nonatom :op :vl-hid-dot
                               :args (list (make-vl-atom :guts part) tail)))))

         (when (vl-is-token? :vl-lbrack)
           (expr := (mv-let (err expr explore new-warnings)
                            (seqw tokens warnings
                                  (:= (vl-match-token :vl-lbrack))
                                  (expr :s= (vl-parse-expression))
                                  (:= (vl-match-token :vl-rbrack))
                                  (:= (vl-match-token :vl-dot))
                                  (return expr))
                            (if err
                                (mv nil nil tokens warnings)
                              (mv nil expr explore new-warnings)))))

         (when expr
           (tail := (vl-parse-hierarchial-identifier t)))

         (return (cond (tail
                        (let ((part1 (make-vl-hidpiece :name (vl-idtoken->name id))))
                          (make-vl-nonatom :op :vl-hid-arraydot
                                           :args (list (make-vl-atom :guts part1)
                                                       expr tail))))
                       (recursivep
                        (make-vl-atom
                         :guts (make-vl-hidpiece :name (vl-idtoken->name id))))
                       (t
                        (make-vl-atom
                         :guts (make-vl-id :name (vl-idtoken->name id))))))))


; function_call ::=
;    hierarchial_identifier { attribute_instance }
;      '(' expression { ',' expression } ')'

 (defparser vl-parse-function-call (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   (seqw tokens warnings
         (id :s= (vl-parse-hierarchial-identifier nil))
         (atts :w= (vl-parse-0+-attribute-instances))
         (:= (vl-match-token :vl-lparen))
         (args := (vl-parse-1+-expressions-separated-by-commas))
         (:= (vl-match-token :vl-rparen))
         (return (cond ((and (vl-fast-atom-p id)
                             (vl-fast-id-p (vl-atom->guts id)))
                        ;; The function's name is a non-hierarchial identifier.  We
                        ;; convert it into a funname atom, instead, so that there is
                        ;; no confusion that it is not a variable.
                        (let ((fname (make-vl-funname
                                      :name (vl-id->name (vl-atom->guts id)))))
                          (make-vl-nonatom :op :vl-funcall
                                           :atts atts
                                           :args (cons (make-vl-atom :guts fname) args))))
                       (t
                        ;; Otherwise, a hierarchial identifier.  We just use it as is.
                        (make-vl-nonatom :op :vl-funcall
                                         :atts atts
                                         :args (cons id args)))))))




; primary ::=
;    number
;  | hierarchial_identifier [ { '[' expression ']' } '[' range_expression ']' ]
;  | concatenation
;  | multiple_concatenation
;  | function_call
;  | system_function_call
;  | '(' mintypmax_expression ')'
;  | string

 (defparser vl-parse-0+-bracketed-expressions (tokens warnings)
   ;; This is for { '[' expression ']' }.  We just return them as a list.
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   (if (not (vl-is-token? :vl-lbrack)) ;; For termination, this needs to be a ruler.
       (mv nil nil tokens warnings)
     (mv-let (err first explore new-warnings)
             (seqw tokens warnings
                   (:= (vl-match-token :vl-lbrack))
                   (expr := (vl-parse-expression))
                   (:= (vl-match-token :vl-rbrack))
                   (return expr))
             (cond ((or err (not first))
                    ;; No initial expression; okay.
                    (mv nil nil tokens warnings))
                   ((not (mbt (< (acl2-count explore) (acl2-count tokens))))
                    (prog2$ (er hard? 'vl-parse-0+-bracketed-expressions "termination failure")
                            (vl-parse-error "termination failure")))
                   (t
                    (mv-let (erp rest tokens warnings)
                            (vl-parse-0+-bracketed-expressions explore new-warnings)
                            (declare (ignore erp))
                            (mv nil (cons first rest) tokens warnings)))))))

 (defparser vl-parse-indexed-id (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   ;; This is for:
   ;;   hierarchial_identifier [ { '[' expression ']' } '[' range_expression ']' ]
   (seqw tokens warnings
         (hid :s= (vl-parse-hierarchial-identifier nil))
         (bexprs :w= (vl-parse-0+-bracketed-expressions))
         (when (vl-is-token? :vl-lbrack)
           (:= (vl-match-token :vl-lbrack))
           (range := (vl-parse-range-expression))
           (:= (vl-match-token :vl-rbrack)))
         (return (let ((main (vl-build-bitselect-nest hid bexprs)))
                   (if range
                       (vl-build-range-select main range)
                     main)))))

 (defparser vl-parse-primary (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 2)))
   (if (not (consp tokens))
       (vl-parse-error "Unexpected EOF.")
     (let ((type (vl-token->type (car tokens))))
       (case type
         ((:vl-inttoken)
          (mv nil
              (make-vl-atom
               :guts (vl-make-guts-from-inttoken (car tokens)))
              (cdr tokens)
              warnings))

         ((:vl-realtoken)
          (mv nil
              (make-vl-atom
               :guts (make-vl-real
                      :value (vl-echarlist->string
                              (vl-realtoken->etext (car tokens)))))
              (cdr tokens)
              warnings))

         ((:vl-stringtoken)
          (mv nil
              (make-vl-atom
               :guts (make-vl-string
                      :value (vl-stringtoken->expansion (car tokens))))
              (cdr tokens)
              warnings))

         (:vl-lcurly
          ;; It's either a concatenation or a multiconcatenation
          (vl-parse-concatenation-or-multiple-concatenation))

         (:vl-idtoken
          ;; Its either an hindex or a function call.  We need to check for
          ;; function call first, since, e.g.,our hindex would accept just the
          ;; hierarchial identifier, "foo", if given "foo(x, y, z)."
          (mv-let (err funcall explore new-warnings)
                  (vl-parse-function-call)
                  (if err
                      (vl-parse-indexed-id)
                    (mv err funcall explore new-warnings))))

         (:vl-sysidtoken
          ;; It can only be a system function call.
          (vl-parse-system-function-call))

         (:vl-lparen ;; '(' mintypmax_expression ')'
          (seqw tokens warnings
                (:= (vl-match-token :vl-lparen))
                (expr := (vl-parse-mintypmax-expression))
                (:= (vl-match-token :vl-rparen))
                (return expr)))

         (t
          (vl-parse-error (str::cat "Expected a primary, but found a "
                                    (symbol-name type)
                                    " token with text "
                                    (vl-echarlist->string (vl-token->etext (car tokens))))))))))


; expression ::=
;    primary
;  | unary_operator { attribute_instance } primary
;  | expression binary_operator { attribute_instance } expression
;  | conditional_expression
;
; conditional_expression ::=
;    expression '?' { attribute_instance } expression ':' expression
;
; Note also the precedence rules from Page 44.
;
;               Table 5-4 --- Precedence rules for operators
;
;   Highest Precedence      +  -  !  ~  &  ~&  |  ~|  ^  ~^  ^~    (unary)
;                           **
;                           *  /  %
;                           +  -               (binary)
;                           <<  >>  <<<  >>>
;                           <   <=  >    >=
;                           ==  !=  ===  !==
;                           &                  (binary)
;                           ^  ^~  ~^          (binary)
;                           |                  (binary)
;                           &&
;                           ||
;                           ?:                 (conditional operator)
;   Lowest Precedence       {} {{}}            (concatenations)
;
; And note also the associativity rule from 5.1.2: all operators shall
; associate left to right with the exception of the conditional operator, which
; shall associate right to left.
;
; Just to refresh our memory, this is how we might write a grammar where '*' is
; to have higher precedence than '-':
;
;    expr ::= term { '-' term }
;    term ::= number { '*' number }
;
; In other words, the higher precedence an operator is, the closer to "number"
; it should occur.  Incorporating these precedence rules into the grammar, we
; come up with the following, new definition for expression:
;
; unary_expression ::=
;    unary_operator { attribute_instance } primary
;  | primary
;
; power_expression ::=
;    unary_expression { '**' { attribute_instance } unary_expression }
;
; mult_op ::= '*' | '/' | '%'
; mult_expression ::=
;    power_expression { mult_op { attribute_instance } power_expression }
;
; add_op ::= '+' | '-'
; add_expression ::=
;    mult_expression { add_op { attribute_instance } mult_expression }
;
; shift_op ::= '<<' | '>>' | '<<<' | '>>>'
; shift_expression ::=
;    add_expression { shift_op { attribute_instance } add_expression }
;
; compare_op ::= '<' | '<=' | '>' | '>='
; compare_expression ::=
;    shift_expression { compare_op { attribute_instance } shift_expression }
;
; equality_op ::= '==' | '!=' | '===' | '!=='
; equality_expression ::=
;    compare_expression { equality_op { attribute_instance } compare_expression }
;
; bitand_expression ::=
;     equality_expression { '&' { attribute_instance } equality_expression }
;
; bitxor_op ::= '^' | '^~' | '~^'
; bitxor_expression ::=
;    bitand_expression { bitxor_op { attribute_instance } bitand_expression }
;
; bitor_expression ::=
;    bitxor_expression { '|' { attribute_instance } bitxor_expression }
;
; logand_expression ::=
;    bitor_expression { '&&' { attribute_instance } bitor_expression }
;
; logor_expression ::=
;    logand_expression { '||' { attribute_instance } logand_expression }
;
; expression ::=
;    logor_expression { '?' { attribute_instance } expression ':' expression }






; unary_expression ::=
;    unary_operator { attribute_instance } primary
;  | primary

 (defparser vl-parse-unary-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 3)))
   (let ((unary-operators '(:vl-plus     ;;; +
                            :vl-minus    ;;; -
                            :vl-lognot   ;;; !
                            :vl-bitnot   ;;; ~
                            :vl-bitand   ;;; &
                            :vl-nand     ;;; ~&
                            :vl-bitor    ;;; |
                            :vl-nor      ;;; ~|
                            :vl-xor      ;;; ^
                            :vl-xnor     ;;; ~^ or ^~
                            )))
     (seqw tokens warnings
           (unless (vl-is-some-token? unary-operators)
             (primary :s= (vl-parse-primary))
             (return primary))
           (op := (vl-match-some-token unary-operators))
           (atts :w= (vl-parse-0+-attribute-instances))
           (primary := (vl-parse-primary))
           (return (make-vl-nonatom
                    :op (case (vl-token->type op)
                          (:vl-plus   :vl-unary-plus)
                          (:vl-minus  :vl-unary-minus)
                          (:vl-lognot :vl-unary-lognot)
                          (:vl-bitnot :vl-unary-bitnot)
                          (:vl-bitand :vl-unary-bitand)
                          (:vl-nand   :vl-unary-nand)
                          (:vl-bitor  :vl-unary-bitor)
                          (:vl-nor    :vl-unary-nor)
                          (:vl-xor    :vl-unary-xor)
                          (:vl-xnor   :vl-unary-xnor))
                    :atts atts
                    :args (list primary))))))


; power_expression ::=
;    unary_expression { '**' { attribute_instance } unary_expression }

 (defparser vl-parse-power-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 4)))
   (seqw tokens warnings
         (first :s= (vl-parse-unary-expression))
         (unless (vl-is-token? :vl-power)
           (return (list first)))
         (:= (vl-match-token :vl-power))
         (atts :w= (vl-parse-0+-attribute-instances))
         (tail := (vl-parse-power-expression-aux))
         (return (list* first :vl-binary-power atts tail))))

 (defparser vl-parse-power-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 5)))
   (seqw tokens warnings
         (mixed := (vl-parse-power-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))




; mult_op ::= '*' | '/' | '%'
; mult_expression ::=
;    power_expression { mult_op { attribute_instance } power_expression }

 (defparser vl-parse-mult-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 6)))
   (let ((mult-ops '(:vl-times :vl-div :vl-rem)))
     (seqw tokens warnings
           (first :s= (vl-parse-power-expression))
           (unless (vl-is-some-token? mult-ops)
             (return (list first)))
           (op := (vl-match-some-token mult-ops))
           (atts :w= (vl-parse-0+-attribute-instances))
           (tail := (vl-parse-mult-expression-aux))
           (return (list* first (case (vl-token->type op)
                                  (:vl-times :vl-binary-times)
                                  (:vl-div   :vl-binary-div)
                                  (:vl-rem   :vl-binary-rem))
                          atts tail)))))

 (defparser vl-parse-mult-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 7)))
   (seqw tokens warnings
         (mixed := (vl-parse-mult-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; add_op ::= '+' | '-'
; add_expression ::=
;    mult_expression { add_op { attribute_instance } mult_expression }

 (defparser vl-parse-add-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 8)))
   (let ((add-ops '(:vl-plus :vl-minus)))
     (seqw tokens warnings
           (first :s= (vl-parse-mult-expression))
           (unless (vl-is-some-token? add-ops)
             (return (list first)))
           (op := (vl-match-some-token add-ops))
           (atts :w= (vl-parse-0+-attribute-instances))
           (tail := (vl-parse-add-expression-aux))
           (return (list* first (case (vl-token->type op)
                                  (:vl-plus :vl-binary-plus)
                                  (:vl-minus :vl-binary-minus))
                          atts tail)))))

 (defparser vl-parse-add-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 9)))
   (seqw tokens warnings
         (mixed := (vl-parse-add-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; shift_op ::= '<<' | '>>' | '<<<' | '>>>'
; shift_expression ::=
;    add_expression { shift_op { attribute_instance } add_expression }

 (defparser vl-parse-shift-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 10)))
   (let ((shift-ops '(:vl-shl :vl-shr :vl-ashl :vl-ashr)))
     (seqw tokens warnings
           (first :s= (vl-parse-add-expression))
           (unless (vl-is-some-token? shift-ops)
             (return (list first)))
           (op := (vl-match-some-token shift-ops))
           (atts :w= (vl-parse-0+-attribute-instances))
           (tail := (vl-parse-shift-expression-aux))
           (return (list* first (case (vl-token->type op)
                                  (:vl-shl :vl-binary-shl)
                                  (:vl-shr :vl-binary-shr)
                                  (:vl-ashl :vl-binary-ashl)
                                  (:vl-ashr :vl-binary-ashr))
                          atts tail)))))

 (defparser vl-parse-shift-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 11)))
   (seqw tokens warnings
         (mixed := (vl-parse-shift-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; compare_op ::= '<' | '<=' | '>' | '>='
; compare_expression ::=
;    shift_expression { compare_op { attribute_instance } shift_expression }

 (defparser vl-parse-compare-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 12)))
   (let ((compare-ops '(:vl-lt :vl-lte :vl-gt :vl-gte)))
     (seqw tokens warnings
           (first :s= (vl-parse-shift-expression))
           (unless (vl-is-some-token? compare-ops)
             (return (list first)))
           (op := (vl-match-some-token compare-ops))
           (atts :w= (vl-parse-0+-attribute-instances))
           (tail := (vl-parse-compare-expression-aux))
           (return (list* first (case (vl-token->type op)
                                  (:vl-lt  :vl-binary-lt)
                                  (:vl-lte :vl-binary-lte)
                                  (:vl-gt  :vl-binary-gt)
                                  (:vl-gte :vl-binary-gte))
                          atts tail)))))

 (defparser vl-parse-compare-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 13)))
   (seqw tokens warnings
         (mixed := (vl-parse-compare-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; equality_op ::= '==' | '!=' | '===' | '!=='
; equality_expression ::=
;    compare_expression { equality_op { attribute_instance } compare_expression }

 (defparser vl-parse-equality-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 14)))
   (let ((equality-ops '(:vl-eq :vl-neq :vl-ceq :vl-cne)))
     (seqw tokens warnings
           (first :s= (vl-parse-compare-expression))
           (unless (vl-is-some-token? equality-ops)
             (return (list first)))
           (op := (vl-match-some-token equality-ops))
           (atts :w= (vl-parse-0+-attribute-instances))
           (tail := (vl-parse-equality-expression-aux))
           (return (list* first (case (vl-token->type op)
                                  (:vl-eq  :vl-binary-eq)
                                  (:vl-neq :vl-binary-neq)
                                  (:vl-ceq :vl-binary-ceq)
                                  (:vl-cne :vl-binary-cne))
                          atts tail)))))

 (defparser vl-parse-equality-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 15)))
   (seqw tokens warnings
         (mixed := (vl-parse-equality-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; bitand_expression ::=
;     equality_expression { '&' { attribute_instance } equality_expression }

 (defparser vl-parse-bitand-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 16)))
   (seqw tokens warnings
         (first :s= (vl-parse-equality-expression))
         (unless (vl-is-token? :vl-bitand)
           (return (list first)))
         (:= (vl-match-token :vl-bitand))
         (atts :w= (vl-parse-0+-attribute-instances))
         (tail := (vl-parse-bitand-expression-aux))
         (return (list* first :vl-binary-bitand atts tail))))

 (defparser vl-parse-bitand-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 17)))
   (seqw tokens warnings
         (mixed := (vl-parse-bitand-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; bitxor_op ::= '^' | '^~' | '~^'
; bitxor_expression ::=
;    bitand_expression { bitxor_op { attribute_instance } bitand_expression }

 (defparser vl-parse-bitxor-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 18)))
   (let ((bitxor-ops '(:vl-xor :vl-xnor)))
     (seqw tokens warnings
           (first :s= (vl-parse-bitand-expression))
           (unless (vl-is-some-token? bitxor-ops)
             (return (list first)))
           (op := (vl-match-some-token bitxor-ops))
           (atts :w= (vl-parse-0+-attribute-instances))
           (tail := (vl-parse-bitxor-expression-aux))
           (return (list* first (case (vl-token->type op)
                                  (:vl-xor :vl-binary-xor)
                                  (:vl-xnor :vl-binary-xnor))
                          atts tail)))))

 (defparser vl-parse-bitxor-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 19)))
   (seqw tokens warnings
         (mixed := (vl-parse-bitxor-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; bitor_expression ::=
;    bitxor_expression { '|' { attribute_instance } bitxor_expression }

 (defparser vl-parse-bitor-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 20)))
   (seqw tokens warnings
         (first :s= (vl-parse-bitxor-expression))
         (unless (vl-is-token? :vl-bitor)
           (return (list first)))
         (:= (vl-match-token :vl-bitor))
         (atts :w= (vl-parse-0+-attribute-instances))
         (tail := (vl-parse-bitor-expression-aux))
         (return (list* first :vl-binary-bitor atts tail))))

 (defparser vl-parse-bitor-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 21)))
   (seqw tokens warnings
         (mixed := (vl-parse-bitor-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; logand_expression ::=
;    bitor_expression { '&&' { attribute_instance } bitor_expression }

 (defparser vl-parse-logand-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 22)))
   (seqw tokens warnings
         (first :s= (vl-parse-bitor-expression))
         (unless (vl-is-token? :vl-logand)
           (return (list first)))
         (:= (vl-match-token :vl-logand))
         (atts :w= (vl-parse-0+-attribute-instances))
         (tail := (vl-parse-logand-expression-aux))
         (return (list* first :vl-binary-logand atts tail))))

 (defparser vl-parse-logand-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 23)))
   (seqw tokens warnings
         (mixed := (vl-parse-logand-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))



; logor_expression ::=
;    logand_expression { '||' { attribute_instance } logand_expression }

 (defparser vl-parse-logor-expression-aux (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 24)))
   (seqw tokens warnings
         (first :s= (vl-parse-logand-expression))
         (unless (vl-is-token? :vl-logor)
           (return (list first)))
         (:= (vl-match-token :vl-logor))
         (atts :w= (vl-parse-0+-attribute-instances))
         (tail := (vl-parse-logor-expression-aux))
         (return (list* first :vl-binary-logor atts tail))))

 (defparser vl-parse-logor-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 25)))
   (seqw tokens warnings
         (mixed := (vl-parse-logor-expression-aux))
         (return (vl-left-associate-mixed-binop-list mixed))))


; expression ::=
;    logor_expression { '?' { attribute_instance } expression ':' expression }
;
; Note that the conditional operator associates to the right, so for
; example
;    1 ? 2 : 3 ? 4 : 5
;
; Should be interpreted as:  1 ? 2 : (3 ? 4 : 5)   =  2
;
; Rather than as:            (1 ? 2 : 3) ? 4 : 5   =  4

 (defparser vl-parse-expression (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 26)))
   (seqw tokens warnings
         (first :s= (vl-parse-logor-expression))
         (unless (vl-is-token? :vl-qmark)
           (return first))
         (:= (vl-match-token :vl-qmark))
         (atts :w= (vl-parse-0+-attribute-instances))
         (second :s= (vl-parse-expression))
         (:= (vl-match-token :vl-colon))
         (third := (vl-parse-expression))
         (return (make-vl-nonatom :op :vl-qmark
                                  :atts atts
                                  :args (list first second third))))))




(with-output
 :off prove :gag-mode :goals
 (FLAG::make-flag vl-flag-parse-expression
                  vl-parse-expression-fn))
