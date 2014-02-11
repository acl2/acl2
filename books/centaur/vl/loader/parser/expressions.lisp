; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "utils")
(include-book "../../expr")
(local (include-book "../../util/arithmetic"))
(local (non-parallel-book))


; BOZO we can probably speed this up quite a bit by getting rid of the big
; case-splits in parse-unary-expression and the smaller, similar case splits in
; the other functions that deal with several operators.

(defsection parse-expressions
  :parents (parser)
  :short "Routines for expression parsing.")

(local (xdoc::set-default-parents parse-expressions))

(local (defthm nfix-of-len
         (equal (nfix (len x)) (len x))))

;; Dumb accumulated persistence hacking
(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ACL2::LEN-WHEN-PREFIXP
                           double-containment
                           CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P
                           CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                           acl2::consp-by-len
                           VL-WARNINGLIST-P-WHEN-NOT-CONSP
                           ACL2::PREFIXP-WHEN-EQUAL-LENGTHS
                           ACL2::SUBLISTP-WHEN-PREFIXP
                           ACL2::LOWER-BOUND-OF-LEN-WHEN-SUBLISTP
                           ACL2::INDEX-OF-<-LEN
                           default-<-1
                           default-<-2
                           ACL2::CANCEL_TIMES-EQUAL-CORRECT
                           ACL2::CANCEL_PLUS-EQUAL-CORRECT
                           VL-WARNINGLIST-P-WHEN-SUBSETP-EQUAL
                           VL-TOKENLIST-P-WHEN-SUBSETP-EQUAL
                           ACL2::LISTPOS-UPPER-BOUND-STRONG-2
                           VL-TOKENLIST-P-WHEN-MEMBER-EQUAL-OF-VL-TOKENLISTLIST-P
                           ACL2::ALISTP-OF-CDR
                           ACL2::CONSP-OF-CAR-WHEN-ALISTP
                           ALISTP-WHEN-ALL-HAVE-LEN
                           (tau-system)
                           nfix
                           ;(:rules-of-class :type-prescription :here)
                           )))

(define vl-mixed-binop-list-p (x)
  :short "A list of alternating expressions, operators, and attributes."

  :long "<p>All of the binary operators in Verilog are left-associative, but it
is difficult to directly build a left-associative structure in straightforward
recursive descent parsing.</p>

<p>So instead, our expression parsers build <i>mixed binop lists</i> which we
then left-associate later.</p>

<p>Ignoring attributes for a moment, the idea is that these lists look like the
 following:</p>

@({
    (EXPR OP EXPR OP EXPR OP EXPR ... EXPR)
})

<p>So for instance, to parse the Verilog source code @('\"1 + 2 + 3 + 4\"'),
the plan is first to build a mixed list which looks like</p>

@({
    (1 + 2 + 3 + 4)
})

<p>and then to fully left-associate this list into the expected form,</p>

@({
    (+ (+ (+ 1 2) 3) 4)
})

<p>Attributes only make this slightly more complex.  The actual format of our
 mixed list is</p>

@({
    (EXPR OP ATTS EXPR OP ATTS ... EXPR)
})

<p>Where each ATTS belongs to the OP immediately preceeding it.</p>"

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
                       (vl-mixed-binop-list-p rest))))))

  ///
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



(define vl-left-associate-mixed-binop-list ((x vl-mixed-binop-list-p))
  :returns (expr vl-expr-p :hyp :guard)
  :measure (len x)
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
    (car x))
  :prepwork ((local (in-theory (enable vl-mixed-binop-list-p)))))


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

(define vl-build-bitselect-nest ((expr vl-expr-p)
                                 (bitselects vl-exprlist-p))
  :returns (expr vl-expr-p :hyp :fguard)
  (if (atom bitselects)
      expr
    (vl-build-bitselect-nest
     (make-vl-nonatom :op :vl-bitselect
                      :args (list expr (car bitselects)))
     (cdr bitselects))))


(defenum vl-erangetype-p
  (:vl-bitselect
   :vl-colon
   :vl-pluscolon
   :vl-minuscolon)
  :parents (parser))

(deflist vl-erangetypelist-p (x)
  (vl-erangetype-p x)
  :elementp-of-nil nil
  ///
  (defthm vl-erangetype-p-of-vl-type-of-matched-token
    ;; ugly, but effective.
    (implies (vl-erangetypelist-p types)
             (equal (vl-erangetype-p (vl-type-of-matched-token types tokens))
                    (if (vl-type-of-matched-token types tokens)
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable vl-type-of-matched-token)))))


(defaggregate vl-erange
  ;; For bit selects, we just set left and right to the same expression.
  ((type vl-erangetype-p)
   (left vl-expr-p)
   (right vl-expr-p))
  :tag :vl-erange
  :legiblep nil)


(define vl-build-range-select ((expr vl-expr-p)
                               (range vl-erange-p))
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
                        :args (list expr left right)))))
  ///
  (local (defthm lemma
           (implies (and (vl-erange-p range)
                         (not (equal (vl-erange->type range) :vl-bitselect))
                         (not (equal (vl-erange->type range) :vl-colon))
                         (not (equal (vl-erange->type range) :vl-pluscolon)))
                    (equal (vl-erange->type range)
                           :vl-minuscolon))
           :hints(("Goal"
                   :in-theory (e/d (vl-erangetype-p)
                                   (return-type-of-vl-erange->type))
                   :use ((:instance return-type-of-vl-erange->type (x range)))))))

  (defthm vl-expr-p-of-vl-build-range-select
    (implies (and (force (vl-expr-p expr))
                  (force (vl-erange-p range)))
             (vl-expr-p (vl-build-range-select expr range)))))



(define vl-make-guts-from-inttoken ((x vl-inttoken-p))
  :returns (guts vl-atomguts-p :hyp :fguard)
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


(define vl-mark-as-explicit-parens
  :short "Annotate an expression as having explicit parentheses."
  ((x vl-expr-p))
  :returns (new-x vl-expr-p :hyp :guard)

  :long "<p>For some kinds of linting checks, we may want to know whether the
original expression had any parens, e.g., we might want to warn the user if
they have typed</p>

@({
     a & b < c
})

<p>Because this gets parsed as @('a & (b < c)'), which seems strange and may
catch the user by surprise.  On the other hand, if they've typed</p>

@({
     a & (b < c)
})

<p>Then, as strange as this is, it seems to be what they want, and we probably
don't want to complain about it.</p>

<p>But these expressions will be identical after parsing unless we somehow
remember where explicit parens were.  To facilitate this, we set the
@('VL_EXPLICIT_PARENS') attribute on non-atoms that have explicit parens.</p>

<p>Note that we don't bother to set @('VL_EXPLICIT_PARENS') on atoms, e.g., the
following really are still parsed equivalently:</p>

@({
    (a) & b      vs.    a & b
})

<p>This is possibly unfortunate, but atoms don't have attributes so what else
would we do?</p>"

  (b* (((when (vl-fast-atom-p x))
        x)
       (atts (vl-nonatom->atts x))
       (atts (acons "VL_EXPLICIT_PARENS" nil atts)))
    (change-vl-nonatom x :atts atts)))


(defines has-any-atts-p
  :flag nil
  :parents (vl-parse-attr-spec)

  (define vl-expr-has-any-atts-p ((x vl-expr-p))
    :returns (bool booleanp :rule-classes :type-prescription)
    :measure (vl-expr-count x)
    (b* (((when (vl-fast-atom-p x))
          nil)
         ((vl-nonatom x) x))
      (or (consp x.atts)
          (vl-exprlist-has-any-atts-p x.args))))

  (define vl-exprlist-has-any-atts-p ((x vl-exprlist-p))
    :returns (bool booleanp :rule-classes :type-prescription)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (or (vl-expr-has-any-atts-p (car x))
          (vl-exprlist-has-any-atts-p (cdr x))))))


(defparsers parse-expressions
   :parents (parser)
   :short "Parser for Verilog and SystemVerilog expressions."

  :long "<p>This is very complicated because everything about expressions is
mutually recursive.  Most of the functions here correspond to particular
productions in the grammars of the Verilog-2005 or SystemVerilog-2012.  A
few high-level notes:</p>

<ul>

<li>The documentation for each function generally describes the grammar
productions that are being implemented.</li>

<li>We generally simplify the grammar rules by removing any bare \"aliases\"
such as @('base_expression ::= expression') and @('attr_name ::=
identifier').</li>

<li>We do not try to implement any separation between \"ordinary\" expressions
and \"constant\" expressions.  I think the whole treatment of constant
expressions as a syntactic construct is somewhat misguided.  It is difficult to
imagine truly handling constant expressions at parse time.  For instance, in a
parameterized module with, say, a @('width') parameter, you really want to
resolve expressions like @('width-1') into constants and treat them as constant
indexes.  But you can't do this until you know the values for these parameters,
which you don't know until you've read all the instances of the module,
etc.</li>

</ul>"

  (defparser vl-parse-attr-spec ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match a single @('attr_spec'), return a singleton @(see vl-atts-p)."
    :long "<p>Verilog-2005 and SystemVerilog-2012 agree exactly about the
definition of @('attr_spec'):</p>

@({
attr_spec ::= attr_name [ '=' constant_expression ]
attr_name ::= identifier
})"
    :measure (two-nats-measure (len tokens) 0)
    :verify-guards nil
    (seqw tokens warnings
          (id := (vl-match-token :vl-idtoken))
          (when (vl-is-token? :vl-equalsign)
            (:= (vl-match-token :vl-equalsign))
            (expr := (vl-parse-expression)))
          (when (and expr (vl-expr-has-any-atts-p expr))
            (return-raw
             (vl-parse-error "Nested attributes are illegal.")))
          (return (list (cons (vl-idtoken->name id) expr)))))

  (defparser vl-parse-attribute-instance-aux ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match @(' attr_spec { ',' attr_spec' } '), return a @(see vl-atts-p)."
    :measure (two-nats-measure (len tokens) 1)
    (seqw tokens warnings
          (first :s= (vl-parse-attr-spec))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match-token :vl-comma))
            (rest := (vl-parse-attribute-instance-aux)))
          (return (append first rest))))

  (defparser vl-parse-attribute-instance ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match (* ... *), return a @(see vl-atts-p)."
    :long "<p>Verilog-2005 and SystemVerilog-2012 agree exactly about the
definition of @('attribute_instance'):</p>

@({
    attribute_instance ::= '(*' attr_spec { ',' attr_spec } '*)'
})"
    :measure (two-nats-measure (len tokens) 0)
    (seqw tokens warnings
          (:= (vl-match-token :vl-beginattr))
          (data := (vl-parse-attribute-instance-aux))
          (:= (vl-match-token :vl-endattr))
          (return data)))

  (defparser vl-parse-0+-attribute-instances-aux ()
    :parents (vl-parse-0+-attribute-instances)
    :short "Match @('{ attribute_instance }'), collecting all attributes in
the order they were seen, without proper duplicity checking."
    :long "<p>We convert each individual @('attribute_instance') into an
@('vl-atts-p') alist, and then merge these together using @(see append), so
that for instance:</p>

@({
    (* foo *) (* bar *)
})

<p>Is treated in just the same way as:</p>

@({
     (* foo, bar *)
})"
    :measure (two-nats-measure (len tokens) 1)
    (seqw tokens warnings
          (when (not (vl-is-token? :vl-beginattr))
            (return nil))
          (first :s= (vl-parse-attribute-instance))
          (rest := (vl-parse-0+-attribute-instances-aux))
          (return (append first rest))))

  (defparser vl-parse-0+-attribute-instances ()
    :short "Top level parser for @('{ attribute_instance }') with proper
duplicity checking and warnings.  Returns a @(see vl-atts-p)."

    :long "<p>This is a wrapper.  Almost all of the work is done by the aux
function, @(see vl-parse-0+-attribute-instances-aux).  The aux function gathers
up an @(see vl-atts-p) that has all the attributes in the order they were seen
in.  For instance, it would produce:</p>

@({
       (* foo = 1 *)  (* bar = 2, foo = 2 *)
          --->
       (( \"foo\" . <1> )     ; Where <1> means, a proper vl-expr-p with
        ( \"bar\" . <2> )     ; the number 1.
        ( \"foo\" . <2> ))
})

<p>This isn't quite right.  We want any later attributes to shadow the previous
attributes, and we want to warn about any attributes like \"foo\" that occur
multiple times.  So, in this wrapper, we check for duplicates and issue
warnings, and we fix up the alists to get unique keys bound to the right
values.</p>"
    :measure (two-nats-measure (len tokens) 2)
    (seqw tokens warnings
          (when (not (vl-is-token? :vl-beginattr))
            ;; Stupid hack for performance.  Usually there are no attributes,
            ;; so we don't need to do anything more.
            (return nil))
          (loc := (vl-current-loc))
          (original-atts := (vl-parse-0+-attribute-instances-aux))
          (return-raw
           (b* ((atts
                 ;; The original-atts are in the order seen.
                 ;;  - Reversing them puts the later occurrences first, which
                 ;;    is good because these are the occurrences we want to keep
                 ;;  - Shrinking gets rid of any earlier occurrences, and also
                 ;;    re-reverses the list so we get them in the right order.
                 (fast-alist-free (hons-shrink-alist (rev original-atts) nil)))
                (warnings
                 (if (same-lengthp atts original-atts)
                     ;; No dupes, nothing to warn about
                     warnings
                   (warn :type :vl-warn-shadowed-atts
                         :msg "~l0: Found multiple occurrences of ~&1 in ~
                               attributes.  Later occurrences take precedence."
                         :args (list loc
                                     (duplicated-members
                                      (alist-keys original-atts)))))))
             (mv nil atts tokens warnings)))))


; system_function_call ::=
;    system_identifier [ '(' expression { ',' expression } ')' ]
;
; Strangely, system calls are not allowed to have attributes even though
; regular function calls are allowed to.

  (defparser vl-parse-1+-expressions-separated-by-commas ()
    :measure (two-nats-measure (len tokens) 27)
    (seqw tokens warnings
          (first :s= (vl-parse-expression))
          (when (vl-is-token? :vl-comma)
            (:= (vl-match-token :vl-comma))
            (rest := (vl-parse-1+-expressions-separated-by-commas)))
          (return (cons first rest))))

  (defparser vl-parse-system-function-call ()
    :measure (two-nats-measure (len tokens) 0)
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

  (defparser vl-parse-mintypmax-expression ()
    :measure (two-nats-measure (len tokens) 27)
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

  (defparser vl-parse-range-expression ()
    :measure (two-nats-measure (len tokens) 27)
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

  (defparser vl-parse-concatenation ()
    :measure (two-nats-measure (len tokens) 0)
    (seqw tokens warnings
          (:= (vl-match-token :vl-lcurly))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rcurly))
          (return (make-vl-nonatom :op :vl-concat :args args))))

  (defparser vl-parse-concatenation-or-multiple-concatenation ()
    :measure (two-nats-measure (len tokens) 0)
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

  (defparser vl-parse-hierarchial-identifier (recursivep)
    :measure (two-nats-measure (len tokens) 0)

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

  (defparser vl-parse-function-call ()
    :measure (two-nats-measure (len tokens) 1)
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

  (defparser vl-parse-0+-bracketed-expressions ()
    ;; This is for { '[' expression ']' }.  We just return them as a list.
    :measure (two-nats-measure (len tokens) 1)
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
              ((not (mbt (< (len explore) (len tokens))))
               (prog2$ (er hard? 'vl-parse-0+-bracketed-expressions "termination failure")
                       (vl-parse-error "termination failure")))
              (t
               (mv-let (erp rest tokens warnings)
                 (vl-parse-0+-bracketed-expressions
                  :tokens explore
                  :warnings new-warnings)
                 ;;(declare (ignore erp))
                 ;;(mv nil (cons first rest) tokens warnings)
                 (if erp
                     (mv erp rest tokens warnings)
                   (mv nil (cons first rest) tokens warnings))))))))

  (defparser vl-parse-indexed-id ()
    :measure (two-nats-measure (len tokens) 1)
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

  (defparser vl-parse-primary ()
    :measure (two-nats-measure (len tokens) 2)
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
                 (return (vl-mark-as-explicit-parens expr))))

          (t
           (vl-parse-error (cat "Expected a primary, but found a "
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

  (defparser vl-parse-unary-expression ()
    :measure (two-nats-measure (len tokens) 3)
    (let ((unary-operators '(:vl-plus  ;;; +
                             :vl-minus ;;; -
                             :vl-lognot ;;; !
                             :vl-bitnot ;;; ~
                             :vl-bitand ;;; &
                             :vl-nand   ;;; ~&
                             :vl-bitor  ;;; |
                             :vl-nor    ;;; ~|
                             :vl-xor    ;;; ^
                             :vl-xnor   ;;; ~^ or ^~
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

  (defparser vl-parse-power-expression-aux ()
    :measure (two-nats-measure (len tokens) 4)
    (seqw tokens warnings
          (first :s= (vl-parse-unary-expression))
          (unless (vl-is-token? :vl-power)
            (return (list first)))
          (:= (vl-match-token :vl-power))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-power-expression-aux))
          (return (list* first :vl-binary-power atts tail))))

  (defparser vl-parse-power-expression ()
    :measure (two-nats-measure (len tokens) 5)
    (seqw tokens warnings
          (mixed := (vl-parse-power-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))




; mult_op ::= '*' | '/' | '%'
; mult_expression ::=
;    power_expression { mult_op { attribute_instance } power_expression }

  (defparser vl-parse-mult-expression-aux ()
    :measure (two-nats-measure (len tokens) 6)
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

  (defparser vl-parse-mult-expression ()
    :measure (two-nats-measure (len tokens) 7)
    (seqw tokens warnings
          (mixed := (vl-parse-mult-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; add_op ::= '+' | '-'
; add_expression ::=
;    mult_expression { add_op { attribute_instance } mult_expression }

  (defparser vl-parse-add-expression-aux ()
    :measure (two-nats-measure (len tokens) 8)
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

  (defparser vl-parse-add-expression ()
    :measure (two-nats-measure (len tokens) 9)
    (seqw tokens warnings
          (mixed := (vl-parse-add-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; shift_op ::= '<<' | '>>' | '<<<' | '>>>'
; shift_expression ::=
;    add_expression { shift_op { attribute_instance } add_expression }

  (defparser vl-parse-shift-expression-aux ()
    :measure (two-nats-measure (len tokens) 10)
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

  (defparser vl-parse-shift-expression ()
    :measure (two-nats-measure (len tokens) 11)
    (seqw tokens warnings
          (mixed := (vl-parse-shift-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; compare_op ::= '<' | '<=' | '>' | '>='
; compare_expression ::=
;    shift_expression { compare_op { attribute_instance } shift_expression }

  (defparser vl-parse-compare-expression-aux ()
    :measure (two-nats-measure (len tokens) 12)
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

  (defparser vl-parse-compare-expression ()
    :measure (two-nats-measure (len tokens) 13)
    (seqw tokens warnings
          (mixed := (vl-parse-compare-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; equality_op ::= '==' | '!=' | '===' | '!=='
; equality_expression ::=
;    compare_expression { equality_op { attribute_instance } compare_expression }

  (defparser vl-parse-equality-expression-aux ()
    :measure (two-nats-measure (len tokens) 14)
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

  (defparser vl-parse-equality-expression ()
    :measure (two-nats-measure (len tokens) 15)
    (seqw tokens warnings
          (mixed := (vl-parse-equality-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; bitand_expression ::=
;     equality_expression { '&' { attribute_instance } equality_expression }

  (defparser vl-parse-bitand-expression-aux ()
    :measure (two-nats-measure (len tokens) 16)
    (seqw tokens warnings
          (first :s= (vl-parse-equality-expression))
          (unless (vl-is-token? :vl-bitand)
            (return (list first)))
          (:= (vl-match-token :vl-bitand))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitand-expression-aux))
          (return (list* first :vl-binary-bitand atts tail))))

  (defparser vl-parse-bitand-expression ()
    :measure (two-nats-measure (len tokens) 17)
    (seqw tokens warnings
          (mixed := (vl-parse-bitand-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; bitxor_op ::= '^' | '^~' | '~^'
; bitxor_expression ::=
;    bitand_expression { bitxor_op { attribute_instance } bitand_expression }

  (defparser vl-parse-bitxor-expression-aux ()
    :measure (two-nats-measure (len tokens) 18)
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

  (defparser vl-parse-bitxor-expression ()
    :measure (two-nats-measure (len tokens) 19)
    (seqw tokens warnings
          (mixed := (vl-parse-bitxor-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; bitor_expression ::=
;    bitxor_expression { '|' { attribute_instance } bitxor_expression }

  (defparser vl-parse-bitor-expression-aux ()
    :measure (two-nats-measure (len tokens) 20)
    (seqw tokens warnings
          (first :s= (vl-parse-bitxor-expression))
          (unless (vl-is-token? :vl-bitor)
            (return (list first)))
          (:= (vl-match-token :vl-bitor))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-bitor-expression-aux))
          (return (list* first :vl-binary-bitor atts tail))))

  (defparser vl-parse-bitor-expression ()
    :measure (two-nats-measure (len tokens) 21)
    (seqw tokens warnings
          (mixed := (vl-parse-bitor-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; logand_expression ::=
;    bitor_expression { '&&' { attribute_instance } bitor_expression }

  (defparser vl-parse-logand-expression-aux ()
    :measure (two-nats-measure (len tokens) 22)
    (seqw tokens warnings
          (first :s= (vl-parse-bitor-expression))
          (unless (vl-is-token? :vl-logand)
            (return (list first)))
          (:= (vl-match-token :vl-logand))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-logand-expression-aux))
          (return (list* first :vl-binary-logand atts tail))))

  (defparser vl-parse-logand-expression ()
    :measure (two-nats-measure (len tokens) 23)
    (seqw tokens warnings
          (mixed := (vl-parse-logand-expression-aux))
          (return (vl-left-associate-mixed-binop-list mixed))))



; logor_expression ::=
;    logand_expression { '||' { attribute_instance } logand_expression }

  (defparser vl-parse-logor-expression-aux ()
    :measure (two-nats-measure (len tokens) 24)
    (seqw tokens warnings
          (first :s= (vl-parse-logand-expression))
          (unless (vl-is-token? :vl-logor)
            (return (list first)))
          (:= (vl-match-token :vl-logor))
          (atts :w= (vl-parse-0+-attribute-instances))
          (tail := (vl-parse-logor-expression-aux))
          (return (list* first :vl-binary-logor atts tail))))

  (defparser vl-parse-logor-expression ()
    :measure (two-nats-measure (len tokens) 25)
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

  (defparser vl-parse-expression ()
    :measure (two-nats-measure (len tokens) 26)
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




(defun vl-val-when-error-claim-fn (name args)
  `'(,name (implies (mv-nth 0 (,name . ,args))
                    (equal (mv-nth 1 (,name . ,args))
                           nil))))

(defmacro vl-val-when-error-claim (name &key args)
  (vl-val-when-error-claim-fn name args))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (disable (force))))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-val-when-error
      ,(vl-val-when-error-claim vl-parse-attr-spec)
      ,(vl-val-when-error-claim vl-parse-attribute-instance-aux)
      ,(vl-val-when-error-claim vl-parse-attribute-instance)
      ,(vl-val-when-error-claim vl-parse-0+-attribute-instances-aux)
      ,(vl-val-when-error-claim vl-parse-0+-attribute-instances)
      ,(vl-val-when-error-claim vl-parse-1+-expressions-separated-by-commas)
      ,(vl-val-when-error-claim vl-parse-system-function-call)
      ,(vl-val-when-error-claim vl-parse-mintypmax-expression)
      ,(vl-val-when-error-claim vl-parse-range-expression)
      ,(vl-val-when-error-claim vl-parse-concatenation)
      ,(vl-val-when-error-claim vl-parse-concatenation-or-multiple-concatenation)
      ,(vl-val-when-error-claim vl-parse-hierarchial-identifier :args (recursivep))
      ,(vl-val-when-error-claim vl-parse-function-call)
      ,(vl-val-when-error-claim vl-parse-0+-bracketed-expressions)
      ,(vl-val-when-error-claim vl-parse-indexed-id)
      ,(vl-val-when-error-claim vl-parse-primary)
      ,(vl-val-when-error-claim vl-parse-unary-expression)
      ,(vl-val-when-error-claim vl-parse-power-expression-aux)
      ,(vl-val-when-error-claim vl-parse-power-expression)
      ,(vl-val-when-error-claim vl-parse-mult-expression-aux)
      ,(vl-val-when-error-claim vl-parse-mult-expression)
      ,(vl-val-when-error-claim vl-parse-add-expression-aux)
      ,(vl-val-when-error-claim vl-parse-add-expression)
      ,(vl-val-when-error-claim vl-parse-shift-expression-aux)
      ,(vl-val-when-error-claim vl-parse-shift-expression)
      ,(vl-val-when-error-claim vl-parse-compare-expression-aux)
      ,(vl-val-when-error-claim vl-parse-compare-expression)
      ,(vl-val-when-error-claim vl-parse-equality-expression-aux)
      ,(vl-val-when-error-claim vl-parse-equality-expression)
      ,(vl-val-when-error-claim vl-parse-bitand-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitand-expression)
      ,(vl-val-when-error-claim vl-parse-bitxor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitxor-expression)
      ,(vl-val-when-error-claim vl-parse-bitor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitor-expression)
      ,(vl-val-when-error-claim vl-parse-logand-expression-aux)
      ,(vl-val-when-error-claim vl-parse-logand-expression)
      ,(vl-val-when-error-claim vl-parse-logor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-logor-expression)
      ,(vl-val-when-error-claim vl-parse-expression)
      :hints((and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))


(defun vl-tokenlist-claim-fn (name args)
  `'(,name (vl-tokenlist-p (mv-nth 2 (,name . ,args)))))

(defmacro vl-tokenlist-claim (name &key args)
  (vl-tokenlist-claim-fn name args))

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-parse-expressions-flag vl-parse-expression-tokenlist
     ,(vl-tokenlist-claim vl-parse-attr-spec)
     ,(vl-tokenlist-claim vl-parse-attribute-instance-aux)
     ,(vl-tokenlist-claim vl-parse-attribute-instance)
     ,(vl-tokenlist-claim vl-parse-0+-attribute-instances-aux)
     ,(vl-tokenlist-claim vl-parse-0+-attribute-instances)
     ,(vl-tokenlist-claim vl-parse-1+-expressions-separated-by-commas)
     ,(vl-tokenlist-claim vl-parse-system-function-call)
     ,(vl-tokenlist-claim vl-parse-mintypmax-expression)
     ,(vl-tokenlist-claim vl-parse-range-expression)
     ,(vl-tokenlist-claim vl-parse-concatenation)
     ,(vl-tokenlist-claim vl-parse-concatenation-or-multiple-concatenation)
     ,(vl-tokenlist-claim vl-parse-hierarchial-identifier :args (recursivep))
     ,(vl-tokenlist-claim vl-parse-function-call)
     ,(vl-tokenlist-claim vl-parse-0+-bracketed-expressions)
     ,(vl-tokenlist-claim vl-parse-indexed-id)
     ,(vl-tokenlist-claim vl-parse-primary)
     ,(vl-tokenlist-claim vl-parse-unary-expression)
     ,(vl-tokenlist-claim vl-parse-power-expression-aux)
     ,(vl-tokenlist-claim vl-parse-power-expression)
     ,(vl-tokenlist-claim vl-parse-mult-expression-aux)
     ,(vl-tokenlist-claim vl-parse-mult-expression)
     ,(vl-tokenlist-claim vl-parse-add-expression-aux)
     ,(vl-tokenlist-claim vl-parse-add-expression)
     ,(vl-tokenlist-claim vl-parse-shift-expression-aux)
     ,(vl-tokenlist-claim vl-parse-shift-expression)
     ,(vl-tokenlist-claim vl-parse-compare-expression-aux)
     ,(vl-tokenlist-claim vl-parse-compare-expression)
     ,(vl-tokenlist-claim vl-parse-equality-expression-aux)
     ,(vl-tokenlist-claim vl-parse-equality-expression)
     ,(vl-tokenlist-claim vl-parse-bitand-expression-aux)
     ,(vl-tokenlist-claim vl-parse-bitand-expression)
     ,(vl-tokenlist-claim vl-parse-bitxor-expression-aux)
     ,(vl-tokenlist-claim vl-parse-bitxor-expression)
     ,(vl-tokenlist-claim vl-parse-bitor-expression-aux)
     ,(vl-tokenlist-claim vl-parse-bitor-expression)
     ,(vl-tokenlist-claim vl-parse-logand-expression-aux)
     ,(vl-tokenlist-claim vl-parse-logand-expression)
     ,(vl-tokenlist-claim vl-parse-logor-expression-aux)
     ,(vl-tokenlist-claim vl-parse-logor-expression)
     ,(vl-tokenlist-claim vl-parse-expression)
     :hints((and acl2::stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  acl2::clause
                  ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))))))

(defun vl-warninglist-claim-fn (name args)
  `'(,name (vl-warninglist-p (mv-nth 3 (,name . ,args)))))

(defmacro vl-warninglist-claim (name &key args)
  (vl-warninglist-claim-fn name args))

(with-output
  :off prove
  :gag-mode :goals
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-warninglist
      ,(vl-warninglist-claim vl-parse-attr-spec)
      ,(vl-warninglist-claim vl-parse-attribute-instance-aux)
      ,(vl-warninglist-claim vl-parse-attribute-instance)
      ,(vl-warninglist-claim vl-parse-0+-attribute-instances-aux)
      ,(vl-warninglist-claim vl-parse-0+-attribute-instances)
      ,(vl-warninglist-claim vl-parse-1+-expressions-separated-by-commas)
      ,(vl-warninglist-claim vl-parse-system-function-call)
      ,(vl-warninglist-claim vl-parse-mintypmax-expression)
      ,(vl-warninglist-claim vl-parse-range-expression)
      ,(vl-warninglist-claim vl-parse-concatenation)
      ,(vl-warninglist-claim vl-parse-concatenation-or-multiple-concatenation)
      ,(vl-warninglist-claim vl-parse-hierarchial-identifier :args (recursivep))
      ,(vl-warninglist-claim vl-parse-function-call)
      ,(vl-warninglist-claim vl-parse-0+-bracketed-expressions)
      ,(vl-warninglist-claim vl-parse-indexed-id)
      ,(vl-warninglist-claim vl-parse-primary)
      ,(vl-warninglist-claim vl-parse-unary-expression)
      ,(vl-warninglist-claim vl-parse-power-expression-aux)
      ,(vl-warninglist-claim vl-parse-power-expression)
      ,(vl-warninglist-claim vl-parse-mult-expression-aux)
      ,(vl-warninglist-claim vl-parse-mult-expression)
      ,(vl-warninglist-claim vl-parse-add-expression-aux)
      ,(vl-warninglist-claim vl-parse-add-expression)
      ,(vl-warninglist-claim vl-parse-shift-expression-aux)
      ,(vl-warninglist-claim vl-parse-shift-expression)
      ,(vl-warninglist-claim vl-parse-compare-expression-aux)
      ,(vl-warninglist-claim vl-parse-compare-expression)
      ,(vl-warninglist-claim vl-parse-equality-expression-aux)
      ,(vl-warninglist-claim vl-parse-equality-expression)
      ,(vl-warninglist-claim vl-parse-bitand-expression-aux)
      ,(vl-warninglist-claim vl-parse-bitand-expression)
      ,(vl-warninglist-claim vl-parse-bitxor-expression-aux)
      ,(vl-warninglist-claim vl-parse-bitxor-expression)
      ,(vl-warninglist-claim vl-parse-bitor-expression-aux)
      ,(vl-warninglist-claim vl-parse-bitor-expression)
      ,(vl-warninglist-claim vl-parse-logand-expression-aux)
      ,(vl-warninglist-claim vl-parse-logand-expression)
      ,(vl-warninglist-claim vl-parse-logor-expression-aux)
      ,(vl-warninglist-claim vl-parse-logor-expression)
      ,(vl-warninglist-claim vl-parse-expression)
      :hints(("Goal" :in-theory (disable (force)))
             (and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))))))

(defun vl-progress-claim-fn (name strongp args)
  `'(,name (and (<= (len (mv-nth 2 (,name . ,args)))
                    (len tokens))
                ,@(if strongp
                      `((implies (not (mv-nth 0 (,name . ,args)))
                                 (< (len (mv-nth 2 (,name . ,args)))
                                    (len tokens))))
                    nil))
           :rule-classes ((:rewrite) (:linear))))

(defmacro vl-progress-claim (name &key
                                  (strongp 't)
                                  args)
  (vl-progress-claim-fn name strongp args))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (disable (force))))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-progress
      ,(vl-progress-claim vl-parse-attr-spec)
      ,(vl-progress-claim vl-parse-attribute-instance-aux)
      ,(vl-progress-claim vl-parse-attribute-instance)
      ,(vl-progress-claim vl-parse-0+-attribute-instances-aux :strongp nil)
      ,(vl-progress-claim vl-parse-0+-attribute-instances :strongp nil)
      ,(vl-progress-claim vl-parse-1+-expressions-separated-by-commas)
      ,(vl-progress-claim vl-parse-system-function-call)
      ,(vl-progress-claim vl-parse-mintypmax-expression)
      ,(vl-progress-claim vl-parse-range-expression)
      ,(vl-progress-claim vl-parse-concatenation)
      ,(vl-progress-claim vl-parse-concatenation-or-multiple-concatenation)
      ,(vl-progress-claim vl-parse-hierarchial-identifier :args (recursivep))
      ,(vl-progress-claim vl-parse-function-call)
      ,(vl-progress-claim vl-parse-0+-bracketed-expressions :strongp nil)
      ,(vl-progress-claim vl-parse-indexed-id)
      ,(vl-progress-claim vl-parse-primary)
      ,(vl-progress-claim vl-parse-unary-expression)
      ,(vl-progress-claim vl-parse-power-expression-aux)
      ,(vl-progress-claim vl-parse-power-expression)
      ,(vl-progress-claim vl-parse-mult-expression-aux)
      ,(vl-progress-claim vl-parse-mult-expression)
      ,(vl-progress-claim vl-parse-add-expression-aux)
      ,(vl-progress-claim vl-parse-add-expression)
      ,(vl-progress-claim vl-parse-shift-expression-aux)
      ,(vl-progress-claim vl-parse-shift-expression)
      ,(vl-progress-claim vl-parse-compare-expression-aux)
      ,(vl-progress-claim vl-parse-compare-expression)
      ,(vl-progress-claim vl-parse-equality-expression-aux)
      ,(vl-progress-claim vl-parse-equality-expression)
      ,(vl-progress-claim vl-parse-bitand-expression-aux)
      ,(vl-progress-claim vl-parse-bitand-expression)
      ,(vl-progress-claim vl-parse-bitxor-expression-aux)
      ,(vl-progress-claim vl-parse-bitxor-expression)
      ,(vl-progress-claim vl-parse-bitor-expression-aux)
      ,(vl-progress-claim vl-parse-bitor-expression)
      ,(vl-progress-claim vl-parse-logand-expression-aux)
      ,(vl-progress-claim vl-parse-logand-expression)
      ,(vl-progress-claim vl-parse-logor-expression-aux)
      ,(vl-progress-claim vl-parse-logor-expression)
      ,(vl-progress-claim vl-parse-expression)
      :hints((and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))

(defun vl-eof-claim-fn (name args type)
  `'(,name (implies (not (consp tokens))
                    ,(cond ((eq type :error)
                            `(mv-nth 0 (,name . ,args)))
                           ((eq type nil)
                            `(equal (mv-nth 1 (,name . ,args))
                                    nil))
                           (t
                            (er hard? 'vl-eof-claim-fn
                                "Bad type: ~x0." type))))))

(defmacro vl-eof-claim (name type &key args)
  (vl-eof-claim-fn name args type))

(with-output
  :off prove
  :gag-mode :goals
  (encapsulate
    ()
    (local (in-theory (disable (force))))
    (make-event
     `(defthm-parse-expressions-flag vl-parse-expression-eof
        ,(vl-eof-claim vl-parse-attr-spec :error)
        ,(vl-eof-claim vl-parse-attribute-instance-aux :error)
        ,(vl-eof-claim vl-parse-attribute-instance :error)
        ,(vl-eof-claim vl-parse-0+-attribute-instances-aux nil)
        ,(vl-eof-claim vl-parse-0+-attribute-instances nil)
        ,(vl-eof-claim vl-parse-1+-expressions-separated-by-commas :error)
        ,(vl-eof-claim vl-parse-system-function-call :error)
        ,(vl-eof-claim vl-parse-mintypmax-expression :error)
        ,(vl-eof-claim vl-parse-range-expression :error)
        ,(vl-eof-claim vl-parse-concatenation :error)
        ,(vl-eof-claim vl-parse-concatenation-or-multiple-concatenation :error)
        ,(vl-eof-claim vl-parse-hierarchial-identifier :error :args (recursivep))
        ,(vl-eof-claim vl-parse-function-call :error)
        ,(vl-eof-claim vl-parse-0+-bracketed-expressions nil)
        ,(vl-eof-claim vl-parse-indexed-id :error)
        ,(vl-eof-claim vl-parse-primary :error)
        ,(vl-eof-claim vl-parse-unary-expression :error)
        ,(vl-eof-claim vl-parse-power-expression-aux :error)
        ,(vl-eof-claim vl-parse-power-expression :error)
        ,(vl-eof-claim vl-parse-mult-expression-aux :error)
        ,(vl-eof-claim vl-parse-mult-expression :error)
        ,(vl-eof-claim vl-parse-add-expression-aux :error)
        ,(vl-eof-claim vl-parse-add-expression :error)
        ,(vl-eof-claim vl-parse-shift-expression-aux :error)
        ,(vl-eof-claim vl-parse-shift-expression :error)
        ,(vl-eof-claim vl-parse-compare-expression-aux :error)
        ,(vl-eof-claim vl-parse-compare-expression :error)
        ,(vl-eof-claim vl-parse-equality-expression-aux :error)
        ,(vl-eof-claim vl-parse-equality-expression :error)
        ,(vl-eof-claim vl-parse-bitand-expression-aux :error)
        ,(vl-eof-claim vl-parse-bitand-expression :error)
        ,(vl-eof-claim vl-parse-bitxor-expression-aux :error)
        ,(vl-eof-claim vl-parse-bitxor-expression :error)
        ,(vl-eof-claim vl-parse-bitor-expression-aux :error)
        ,(vl-eof-claim vl-parse-bitor-expression :error)
        ,(vl-eof-claim vl-parse-logand-expression-aux :error)
        ,(vl-eof-claim vl-parse-logand-expression :error)
        ,(vl-eof-claim vl-parse-logor-expression-aux :error)
        ,(vl-eof-claim vl-parse-logor-expression :error)
        ,(vl-eof-claim vl-parse-expression :error)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))



(defun vl-expression-claim-fn (name args type)
  `'(,name (implies (force (not (mv-nth 0 (,name . ,args))))
                    ,(cond ((eq type :expr)
                            `(vl-expr-p (mv-nth 1 (,name . ,args))))
                           ((eq type :exprlist)
                            `(vl-exprlist-p (mv-nth 1 (,name . ,args))))
                           ((eq type :atts)
                            `(vl-atts-p (mv-nth 1 (,name . ,args))))
                           ((eq type :erange)
                            `(vl-erange-p (mv-nth 1 (,name . ,args))))
                           ((eq type :mixed)
                            `(vl-mixed-binop-list-p (mv-nth 1 (,name . ,args))))
                           (t
                            (er hard? 'vl-expression-claim-fn
                                "Bad type: ~x0." type))))))

(defmacro vl-expression-claim (name type &key args)
  (vl-expression-claim-fn name args type))

(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           vl-atom-p-by-tag-when-vl-expr-p)))


(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (enable vl-maybe-expr-p)))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-value
      ,(vl-expression-claim vl-parse-attr-spec :atts)
      ,(vl-expression-claim vl-parse-attribute-instance-aux :atts)
      ,(vl-expression-claim vl-parse-attribute-instance :atts)
      ,(vl-expression-claim vl-parse-0+-attribute-instances-aux :atts)
      ,(vl-expression-claim vl-parse-0+-attribute-instances :atts)
      ,(vl-expression-claim vl-parse-1+-expressions-separated-by-commas :exprlist)
      ,(vl-expression-claim vl-parse-system-function-call :expr)
      ,(vl-expression-claim vl-parse-mintypmax-expression :expr)
      ,(vl-expression-claim vl-parse-range-expression :erange)
      ,(vl-expression-claim vl-parse-concatenation :expr)
      ,(vl-expression-claim vl-parse-concatenation-or-multiple-concatenation :expr)
      ,(vl-expression-claim vl-parse-hierarchial-identifier :expr :args (recursivep))
      ,(vl-expression-claim vl-parse-function-call :expr)
      ,(vl-expression-claim vl-parse-0+-bracketed-expressions :exprlist)
      ,(vl-expression-claim vl-parse-indexed-id :expr)
      ,(vl-expression-claim vl-parse-primary :expr)
      ,(vl-expression-claim vl-parse-unary-expression :expr)
      ,(vl-expression-claim vl-parse-power-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-power-expression :expr)
      ,(vl-expression-claim vl-parse-mult-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-mult-expression :expr)
      ,(vl-expression-claim vl-parse-add-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-add-expression :expr)
      ,(vl-expression-claim vl-parse-shift-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-shift-expression :expr)
      ,(vl-expression-claim vl-parse-compare-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-compare-expression :expr)
      ,(vl-expression-claim vl-parse-equality-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-equality-expression :expr)
      ,(vl-expression-claim vl-parse-bitand-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-bitand-expression :expr)
      ,(vl-expression-claim vl-parse-bitxor-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-bitxor-expression :expr)
      ,(vl-expression-claim vl-parse-bitor-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-bitor-expression :expr)
      ,(vl-expression-claim vl-parse-logand-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-logand-expression :expr)
      ,(vl-expression-claim vl-parse-logor-expression-aux :mixed)
      ,(vl-expression-claim vl-parse-logor-expression :expr)
      ,(vl-expression-claim vl-parse-expression :expr)
      :hints(("Goal"
              :do-not '(generalize fertilize))
             (and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))


(local (defthm true-listp-when-alistp
         (implies (alistp x)
                  (true-listp x))))

(with-output
 :off prove :gag-mode :goals
 (verify-guards vl-parse-expression-fn))

