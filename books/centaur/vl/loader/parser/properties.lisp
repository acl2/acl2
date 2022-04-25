; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
; Copyright (C) 2022 Intel Corporation
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "expressions")
(include-book "eventctrl")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defxdoc parse-property
  :parents (parser)
  :short "Functions for parsing SystemVerilog assertion sequence and property
expressions."

  :long "<p><b>Note:</b> see also @('vl/loader/parser/notes/properties.txt')
for considerably discussion of how we want to parse sequences and properties,
and for a description of the modified grammar that we target.</p>")

(local (xdoc::set-default-parents parse-property))

(defval *vl-trivially-true-property-expr*
  :parents (vl-propexpr)
  :short "A @(see vl-propexpr) that is just <i>true</i>."

  :long "<p>This is useful as the implicit first step in a @(see vl-propthen)
that a user might write without a leading expression.  That is, if the user
writes something like:</p>

@({
    ##1 foo ##1 bar
})

<p>Then this is equivalent to having written:</p>

@({
    1 ##1 foo ##1 bar
})

<p>To simplify our internal representation, we always make this leading @('1')
explicit as the head of the sequence.</p>

<p>Similarly, our internal form of @('if')/@('else') property expressions
always has an @('else') branch, even though they are optional in the grammar.
But such expressions are equivalent to just having an else branch of
@('1').</p>"

  (make-vl-propcore :guts
                   (make-vl-exprdist :expr (vl-make-index 1))))


(defparser vl-parse-dist-item ()
  :short "Matches @('dist_item')."
  :result (vl-distitem-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :long "<p>See @(see vl-distitem).  Grammar rules:</p>

@({
     dist_item ::= value_range [ dist_weight ]

     dist_weight ::= ':=' expression
                   | ':/' expression

     value_range ::= expression
                   | [ expression : expression ]
})"

  (seq tokstream
       (when (vl-is-token? :vl-lbrack)
         (lbrack := (vl-match)))
       (left := (vl-parse-expression))
       (when lbrack
         (:= (vl-match-token :vl-colon))
         (right := (vl-parse-expression))
         (:= (vl-match-token :vl-rbrack)))
       (when (vl-is-some-token? '(:vl-coloneq :vl-colonslash))
         (type := (vl-match))
         (weight := (vl-parse-expression)))
       (return (make-vl-distitem
                :left  left
                :right right
                ;; The default type and weight are := 1.
                :type  (cond ((not type)                                :vl-weight-each)
                             ((eq (vl-token->type type) :vl-coloneq)    :vl-weight-each)
                             ((eq (vl-token->type type) :vl-colonslash) :vl-weight-total)
                             (t
                              (progn$ (impossible)
                                      :vl-weight-each)))
                :weight (or weight (vl-make-index 1))))))

(defparser vl-parse-dist-list ()
  :short "Matches @('dist_list ::= dist_item { ',' dist_item }')."
  :result (vl-distlist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-dist-item))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-dist-list)))
       (return (cons first rest))))

(defparser vl-parse-expression-or-dist ()
  :short "Matches @('expression_or_dist ::= expression [ 'dist' '{' dist_list '}' ]')."
  :result (vl-exprdist-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (expr := (vl-parse-expression))
       (when (vl-is-token? :vl-kwd-dist)
         (:= (vl-match))
         (:= (vl-match-token :vl-lcurly))
         (dist := (vl-parse-dist-list))
         (:= (vl-match-token :vl-rcurly)))
       (return (make-vl-exprdist :expr expr :dist dist))))

(defparser vl-parse-1+-expression-or-dists-separated-by-commas ()
  :short "Matches @(' expression_or_dist { ',' expression_or_dist } ')."
  :result (vl-exprdistlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-expression-or-dist))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-expression-or-dists-separated-by-commas)))
       (return (cons first rest))))


(defval *vl-end-of-sequence-$*
  :parents (vl-parse-cycledelayrange)
  (make-vl-special :key :vl-$))

(assert! (vl-expr-p *vl-end-of-sequence-$*))

(defparser vl-parse-cycledelayrange ()
  :short "Matches @('cycle_delay_range')."
  :result (vl-range-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :long "<p>Grammar rules are as follows:</p>

@({
    cycle_delay_range ::= '##' constant_primary
                        | '##' '[' cycle_delay_const_range_expression ']'
                        | '##[*]'
                        | '##[+]'

    cycle_delay_const_range_expression ::= constant_expression ':' constant_expression
                                         | constant_expression ':' '$'

})

<p>But @('##[*]') just means @('##[0:$]') and @('##[+]') just means
@('##[1:$]').  Note also that @('$') is a valid expression, so there's nothing
special we need to do to recognize @('$') tokens here.</p>"
  (seq tokstream
       (:= (vl-match-token :vl-poundpound))

       (unless (vl-is-token? :vl-lbrack)  ;; constant_primary case
         (left := (vl-parse-primary))
         (return (make-vl-range :msb left
                                :lsb left)))

       (:= (vl-match))  ;; Eat [

       (when (vl-is-token? :vl-times)
         (:= (vl-match))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-range :msb (vl-make-index 0)
                                :lsb *vl-end-of-sequence-$*)))

       (when (vl-is-token? :vl-plus)
         (:= (vl-match))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-range :msb (vl-make-index 1)
                                :lsb *vl-end-of-sequence-$*)))

       ;; Otherwise we should have two expressions.  We don't have to do anything
       ;; special in case the right one is a $.

       (left := (vl-parse-expression))
       (:= (vl-match-token :vl-colon))
       (right := (vl-parse-expression))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-range :msb left
                              :lsb right))))


(defparser vl-parse-boolean-abbrev ()
  :short "Matches @('boolean_abbrev')."
  :result (vl-repetition-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :guard-debug t
  :long "<p>Relevant grammar rules:</p>

@({
    boolean_abbrev ::= consecutive_repetition
                     | non_consecutive_repetition
                     | goto_repetition

    consecutive_repetition ::= '[*' const_or_range_expression ']'
                             | '[*]'
                             | '[+]'

    non_consecutive_repetition ::= ['=' const_or_range_expression ]

    goto_repetition ::= ['->' const_or_range_expression ]

    const_or_range_expression ::= constant_expression
                                | cycle_delay_const_range_expression

    cycle_delay_const_range_expression ::= constant_expression ':' constant_expression
                                         | constant_expression ':' '$'
})"

  (seq tokstream
       (:= (vl-match-token :vl-lbrack))

       (when (vl-is-token? :vl-plus)           ;; [+] is equivalent to [1:$]
         (:= (vl-match))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-repetition :type :vl-repetition-consecutive
                                     :left (vl-make-index 1)
                                     :right *vl-end-of-sequence-$*)))

       (type := (vl-match-some-token '(:vl-times :vl-arrow :vl-equalsign)))

       (when (and (eq (vl-token->type type) :vl-times)
                  (vl-is-token? :vl-rbrack)) ;; [*] is equivalent to [0:$]
         (:= (vl-match))
         (return (make-vl-repetition :type :vl-repetition-consecutive
                                     :left (vl-make-index 0)
                                     :right *vl-end-of-sequence-$*)))

       (left := (vl-parse-expression))
       (when (vl-is-token? :vl-colon)
         (:= (vl-match))
         (right := (vl-parse-expression)))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-repetition :type (case (vl-token->type type)
                                           (:vl-times     :vl-repetition-consecutive)
                                           (:vl-arrow     :vl-repetition-goto)
                                           (:vl-equalsign :vl-repetition-nonconsecutive))
                                   :left left
                                   :right right))))

(defparser vl-parse-sequence-abbrev ()
  :short "Matches @('sequence_abbrev')."
  :result (vl-repetition-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :guard-debug t
  :long "<p>This is just a subset of @('boolean_abbrev').  We basically just
adapt @(see vl-parse-boolean-abbrev) and exclude the arrow/equal cases.
Relevant grammar rules:</p>

@({
    sequence_abbrev ::= consecutive_repetition

    consecutive_repetition ::= '[*' const_or_range_expression ']'
                             | '[*]'
                             | '[+]'

    const_or_range_expression ::= constant_expression
                                | cycle_delay_const_range_expression

    cycle_delay_const_range_expression ::= constant_expression ':' constant_expression
                                         | constant_expression ':' '$'
})"

  (seq tokstream
       (:= (vl-match-token :vl-lbrack))

       (when (vl-is-token? :vl-plus)           ;; [+] is equivalent to [1:$]
         (:= (vl-match))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-repetition :type :vl-repetition-consecutive
                                     :left (vl-make-index 1)
                                     :right *vl-end-of-sequence-$*)))

       (:= (vl-match-token :vl-times))

       (when (vl-is-token? :vl-rbrack) ;; [*] is equivalent to [0:$]
         (:= (vl-match))
         (return (make-vl-repetition :type :vl-repetition-consecutive
                                     :left (vl-make-index 0)
                                     :right *vl-end-of-sequence-$*)))

       (left := (vl-parse-expression))
       (when (vl-is-token? :vl-colon)
         (:= (vl-match))
         (right := (vl-parse-expression)))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-repetition :type :vl-repetition-consecutive
                                   :left left
                                   :right right))))

(defparser vl-parse-scoped-or-hierarchical-identifier ()
  :short "Matches @('ps_or_hierarchical_sequence_identifier') or @('ps_or_hierarchical_tf_identifier')."
  :result (vl-scopeexpr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :verify-guards nil
  :long "<p>These seem to be a subset of scoped identifiers, so that's what
I'll return.</p>

<p>Relevant grammar rules for @('ps_or_hierarchical_sequence_identifier')</p>

@({
    ps_or_hierarchical_sequence_identifier ::= [package_scope] sequence_identifier
                                             | hierarchical_sequence_identifier

    package_scope ::= package_identifier '::'
                    | '$unit' '::'

    sequence_identifier ::= identifier
    package_identifier ::= identifier

    hierarchical_sequence_identifier ::= hierarchical_identifier

    hierarchical_identifier ::= [ '$root' '.' ] { identifier constant_bit_select '.'} identifier
})

<p>Analogous rules for @('ps_or_hierarchical_tf_identifier')</p>

@({
    ps_or_hierarchical_tf_identifier ::= [package_scope] tf_identifier
                                       | hierarchical_tf_identifier

    hierarchical_tf_identifier ::= hierarchical_identifier

    tf_identifier ::= identifier
})"

  (seq tokstream

       (when (and (vl-is-token? :vl-idtoken)
                  (vl-lookahead-is-token? :vl-scope (cdr (vl-tokstream->tokens))))
         ;; Package-scope case.  Must be of the form foo::bar.  Match it and
         ;; make a suitable scopeexpr.
         (id1 := (vl-match))
         (:= (vl-match))
         (id2 := (vl-match-token :vl-idtoken))
         (return (make-vl-scopeexpr-colon
                  :first (vl-idtoken->name id1)
                  :rest (make-vl-scopeexpr-end
                         :hid (make-vl-hidexpr-end :name (vl-idtoken->name id2))))))

       ;; The only other possibility is that this is an ordinary
       ;; hierarchical_identifier with no scoping.  Since we haven't eaten any
       ;; tokens we can just use vl-parse-hierarchical-identifier to do all the
       ;; work.
       (hid := (vl-parse-hierarchical-identifier nil))
       (return (make-vl-scopeexpr-end :hid hid)))
  ///
  (verify-guards vl-parse-scoped-or-hierarchical-identifier-fn
    :hints(("Goal" :in-theory (enable vl-lookahead-is-token?
                                      vl-is-token?
                                      vl-match)))))

(defparser vl-parse-sequence-match-item ()
  :short "Matches @('sequence_match_item')."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :long "<p>After reviewing the grammar, I think sequence_match_items are
essentially just a subset of expressions and can probably be best represented
just as expressions.  The main grammar rule is:</p>

@({
     sequence_match_item ::= operator_assignment
                           | inc_or_dec_expression
                           | subroutine_call
})

<p>If you dive down into this, the complexity really explodes.  The details of
@('inc_or_dec_expression') and @('operator_assignment') involve
@('variable_lvalue') terms which are really complex and which we haven't tried
to entirely support yet in our expressions.  Meanwhile @('subroutine_call') can
include @('randomize_call') which leads to a huge bunch of
@('constraint_block') stuff and there are also other parts of
@('subroutine_call') like @('array_manipulation_call') that we haven't tried to
implement at all.</p>

<p>But all of this stuff is also a problem in our ordinary expressions; we
have</p>

@({
     expression ::= primary
                  | '(' operator_assignment ')'
                  | inc_or_dec_expression
                  | ...

     primary ::= function_subroutine_call
               | ...

     function_subroutine_call ::= subroutine_call
})

<p>So all of these kinds of things can directly be expressions.</p>"

  ;; One difference between sequence_match_item and expression is that
  ;; operator_assignment has to be in parens when used in expression, but need
  ;; not be in parens in a sequence_match_item.  So for now I think the most
  ;; expedient thing to do is just:
  ;;
  ;;  1. Try to parse a mintypmax exprssion.
  ;;  2. Check to see if it was a valid sequence_match_item.
  ;;
  ;; In the future we might want to make this more restrictive and generally
  ;; expand upon the kinds of subroutine_calls that our expression parsing code
  ;; supports, etc.

  (seq tokstream
       (expr := (vl-parse-mintypmax-expression))
       (when (and expr
                  (vl-expr-case expr
                    (:vl-call t)
                    (:vl-unary (member expr.op '(:vl-unary-preinc
                                                 :vl-unary-predec
                                                 :vl-unary-postinc
                                                 :vl-unary-postdec)))
                    (:vl-binary (member expr.op '(:vl-binary-assign
                                                  :vl-binary-plusassign
                                                  :vl-binary-minusassign
                                                  :vl-binary-timesassign
                                                  :vl-binary-divassign
                                                  :vl-binary-remassign
                                                  :vl-binary-andassign
                                                  :vl-binary-orassign
                                                  :vl-binary-xorassign
                                                  :vl-binary-shlassign
                                                  :vl-binary-shrassign
                                                  :vl-binary-ashlassign
                                                  :vl-binary-ashrassign)))
                    (& nil)))
         (return expr))
       (return-raw
        (vl-parse-error "Illegal expression for sequence_match_item."))))

(defparser vl-parse-sequence-match-item-list ()
  :short "Matches @(' { ',' sequence_match_item } '), possibly empty."
  :result (vl-exprlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (unless (vl-is-token? :vl-comma)
         (return nil))
       (:= (vl-match))
       (first := (vl-parse-sequence-match-item))
       (rest  := (vl-parse-sequence-match-item-list))
       (return (cons first rest))))


(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag consp-of-vl-parse-event-expression-2012
    (defthm consp-of-vl-parse-event-expression-2012
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2012)))
        (equal (consp val)
               (not err)))
      :flag vl-parse-event-expression-2012)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression-2012)))))))

(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag consp-of-vl-parse-event-expression-2005
    (defthm consp-of-vl-parse-event-expression-2005
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2005)))
        (equal (consp val)
               (not err)))
      :flag vl-parse-event-expression-2005)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression-2005)))))))

(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag consp-of-vl-parse-event-expression
    (defthm consp-of-vl-parse-event-expression
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression)))
        (equal (consp val)
               (not err)))
      :flag vl-parse-event-expression)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression)))))))


(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag vl-evatomlist-p-of-vl-parse-event-expression-2005
    (defthm vl-evatomlist-p-of-vl-parse-event-expression-2005
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2005)))
        (vl-evatomlist-p val))
      :flag vl-parse-event-expression-2005)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression-2005)))))))

(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag vl-evatomlist-p-of-vl-parse-event-expression-2012
    (defthm vl-evatomlist-p-of-vl-parse-event-expression-2012
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2012)))
        (vl-evatomlist-p val))
      :flag vl-parse-event-expression-2012)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression-2012)))))))

(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag vl-evatomlist-p-of-vl-parse-event-expression
    (defthm vl-evatomlist-p-of-vl-parse-event-expression
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression)))
        (vl-evatomlist-p val))
      :flag vl-parse-event-expression)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression)))))))



(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag true-listp-of-vl-parse-event-expression-2005
    (defthm true-listp-of-vl-parse-event-expression-2005
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2005)))
        (true-listp val))
      :rule-classes :type-prescription
      :flag vl-parse-event-expression-2005)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression-2005)))))))

(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag true-listp-of-vl-parse-event-expression-2012
    (defthm true-listp-of-vl-parse-event-expression-2012
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2012)))
        (true-listp val))
      :rule-classes :type-prescription
      :flag vl-parse-event-expression-2012)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression-2012)))))))

(local (with-output :off (prove proof-tree)
  (defthm-parse-expressions-flag true-listp-of-vl-parse-event-expression
    (defthm true-listp-of-vl-parse-event-expression
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression)))
        (true-listp val))
      :rule-classes :type-prescription
      :flag vl-parse-event-expression)
    :skip-others t
    :hints(("Goal" :expand ((vl-parse-event-expression)))))))

(local (in-theory (disable (force))))

(defparser vl-parse-event-expression-fragment ()
  :parents (vl-parse-property-list-of-arguments)
  :short "Special subset of @('event_expression') for use only in
@('sequence_list_of_actuals')."

  :long "<p>This is similar to @(see vl-parse-event-expression) except that our
goal is to avoid ambiguity with @('sequence_expr').  In particular, we don't
allow:</p>

<ul>
<li>Top-level bare expressions without even an edge identifier,</li>
<li>Top-level @('or') expressions</li>
<li>Top-level comma-separated expressions</li>
<li>Parentheses expressions like @('(foo)') where there's only a single
expression in the parens without any edge specifier.</li>
</ul>"

  :result (vl-evatomlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-lparen)
         ;; Try to match any arbitrary event expression inside the parens.
         ;; This expression is free to use ORs, commas, and so forth.
         (:= (vl-match))
         (evatoms := (vl-parse-event-expression))
         (:= (vl-match-token :vl-rparen))
         (when (and (eql (len evatoms) 1)
                    (equal (vl-evatom->type (car evatoms)) :vl-noedge))
           (return-raw
            (vl-parse-error "Want to backtrack to treat a lone expression (foo) like
                             a sequence expression instead of an event expression.")))
         (return evatoms))

       ;; If there are no explicit parens, require an edge or else we just want
       ;; to treat this like a sequence expression.
       (edge := (vl-match-some-token '(:vl-kwd-posedge :vl-kwd-negedge :vl-kwd-edge)))
       (expr := (vl-parse-expression))
       (when (vl-is-token? :vl-kwd-iff)
         ;; We don't have anywhere in our parse tree structures yet to put the
         ;; IFF part yet.
         (return-raw
          (vl-parse-error "BOZO need to implement event_expressions with 'iff' clauses.")))

       ;; Do not match commas or OR expressions, we'll try to handle them
       ;; separately in sequence_list_of_actuals.
       (return
        (let ((edgetype (case (vl-token->type edge)
                          (:vl-kwd-posedge :vl-posedge)
                          (:vl-kwd-negedge :vl-negedge)
                          (:vl-kwd-edge    :vl-edge)
                          (t (impossible)))))
          (list (vl-evatom edgetype expr)))))
  ///
  (defthm vl-parse-event-expression-fragment-errors-on-eof
    (implies (atom (vl-tokstream->tokens))
             (mv-nth 0 (vl-parse-event-expression-fragment)))
    :hints(("Goal" :in-theory (enable vl-parse-event-expression-fragment)))))



(define vl-alternating-propexpr/op-list-p (x)
  :short "Temporary structure to support parsing left-associative sequence expressions."
  (and (consp x)
       (vl-propexpr-p (first x))
       (or (not (consp (cdr x)))
           (and (consp (cddr x))
                (let ((op (second x))
                      (rest (cddr x)))
                  (and (vl-property-binaryop-p op)
                       (vl-alternating-propexpr/op-list-p rest))))))
  ///
  (defthm vl-alternating-propexpr/op-list-p-when-atom
    (implies (atom x)
             (equal (vl-alternating-propexpr/op-list-p x)
                    nil)))

  (defthm vl-alternating-propexpr/op-list-p-of-singleton
    (equal (vl-alternating-propexpr/op-list-p (list x))
           (vl-propexpr-p x)))

  (defthm vl-alternating-propexpr/op-list-p-of-list*
    (equal (vl-alternating-propexpr/op-list-p (list* x y z))
           (and (vl-propexpr-p x)
                (vl-property-binaryop-p y)
                (vl-alternating-propexpr/op-list-p z)))))

(define vl-left-associate-alternating-propexpr/op-list ((x vl-alternating-propexpr/op-list-p))
  :returns (propexpr vl-propexpr-p)
  :measure (len x)
  (if (atom (cdr x))
      (vl-propexpr-fix (first x))
    (b* (((list* left op right rest) x))
      (vl-left-associate-alternating-propexpr/op-list
       (cons (make-vl-propbinary :left left
                                 :op op
                                 :right right)
             rest))))
  :prepwork ((local (in-theory (enable vl-alternating-propexpr/op-list-p)))))


(define vl-delay-se-tail-p (x)
  :short "Temporary structure to support left-associative parsing of @('{ cycle_delay_range repeat_se }')."
  (if (atom x)
      (not x)
    (and (consp x)
         (consp (cdr x))
         (and (vl-range-p (first x))
              (vl-propexpr-p (second x))
              (vl-delay-se-tail-p (cddr x)))))
  ///
  (defthm vl-delay-se-tail-p-when-atom
    (implies (atom x)
             (equal (vl-delay-se-tail-p x)
                    (not x))))

  (defthm vl-delay-se-tail-p-of-list*
    (equal (vl-delay-se-tail-p (list* delay expr rest))
           (and (vl-range-p delay)
                (vl-propexpr-p expr)
                (vl-delay-se-tail-p rest)))))

(define vl-left-associate-delay-se-tail ((head vl-propexpr-p)
                                         (tail vl-delay-se-tail-p))
  :returns (propexpr vl-propexpr-p)
  (b* (((when (atom tail))
        (vl-propexpr-fix head))
       ((list* delay expr rest) tail)
       (new-head (make-vl-propthen :left head
                                   :delay delay
                                   :right expr)))
    (vl-left-associate-delay-se-tail new-head rest))
  :prepwork ((local (in-theory (enable vl-delay-se-tail-p)))))


(defparser vl-parse-property-acceptop ()
  :short "Matches @('accept_on'), @('reject_on'), @('sync_accept_on'), or @('sync_reject_on')."
  :result (vl-property-acceptop-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (tok := (vl-match-some-token '(:vl-kwd-accept_on
                                      :vl-kwd-reject_on
                                      :vl-kwd-sync_accept_on
                                      :vl-kwd-sync_reject_on)))
       (return (case (vl-token->type tok)
                 (:vl-kwd-accept_on :vl-prop-accepton)
                 (:vl-kwd-reject_on :vl-prop-rejecton)
                 (:vl-kwd-sync_accept_on :vl-prop-syncaccepton)
                 (:vl-kwd-sync_reject_on :vl-prop-syncrejecton)
                 (otherwise (progn$ (impossible)
                                    :vl-prop-accepton))))))

(defparser vl-parse-impl-prop-expr-op ()
  :short "Matches @('|->'), @('|=>'), @('#-#'), and @('#=#')."
  :result (vl-property-binaryop-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (tok := (vl-match-some-token '(:vl-bararrow    ;; |->
                                      :vl-bareqarrow  ;; |=>
                                      :vl-pounddash   ;; #-#
                                      :vl-poundequal  ;; #=#
                                      )))
       (return (case (vl-token->type tok)
                 (:vl-bararrow   :vl-prop-thin-implies)
                 (:vl-bareqarrow :vl-prop-fat-implies)
                 (:vl-pounddash  :vl-prop-thin-follows)
                 (:vl-poundequal :vl-prop-fat-follows)
                 (otherwise (progn$ (impossible) :vl-prop-thin-implies))))))

(defconst *lower-precedence-unary-operators*
  '(:vl-atsign
    :vl-kwd-always
    :vl-kwd-s_always
    :vl-kwd-s_eventually
    :vl-kwd-eventually
    :vl-kwd-accept_on
    :vl-kwd-reject_on
    :vl-kwd-sync_accept_on
    :vl-kwd-sync_reject_on
    :vl-kwd-if
    :vl-kwd-case))

(defparsers parse-property-expr
  :verify-guards nil
  :flag-local nil
  ;; :ruler-extenders :all
  ;; :measure-debug t

  ;; NOTE NOTE NOTE --- See notes/properties.txt to understand the grammar that
  ;; we are implementing here!!

  (defparser vl-parse-property-low-prec-unary ()
    :short "Match a property expr beginning with a low precedence unary operator 
            -- i.e. those with lower precedence than impl operators such as @('|->')"
    ;; NOTE: Before this change (and the user of this below in vl-parse-not-property-expr)
    ;; we could't parse e.g.  'foo |-> s_eventually bar'.
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :guard (vl-is-some-token? *lower-precedence-unary-operators*)
    (cond ((vl-is-token? :vl-atsign)
           ;; property_expr ::= clocking_event property_expr
           (seq tokstream
                (trigger := (vl-parse-clocking-event))
                (then    := (vl-parse-property-expr))
                (return (make-vl-propclock :trigger trigger :then then))))

          ((vl-is-token? :vl-kwd-always)
           ;; property_expr ::= 'always' property_expr
           ;;                 | 'always' '[' cycle_delay_const_range_expression ']' property_expr
           (seq tokstream
                (:= (vl-match))
                (when (vl-is-token? :vl-lbrack)
                  (range := (vl-parse-range)))
                (prop := (vl-parse-property-expr))
                (return (make-vl-propalways :strongp nil :range range :prop prop))))

          ((vl-is-token? :vl-kwd-s_always)
           ;; property_expr ::= 's_always' '[' constant_range ']' property_expr
           (seq tokstream
                (:= (vl-match))
                (range := (vl-parse-range))
                (prop :=  (vl-parse-property-expr))
                (return (make-vl-propalways :strongp t :range range :prop prop))))

          ((vl-is-token? :vl-kwd-s_eventually)
           ;; property_expr ::= 's_eventually' property_expr
           ;;                 | 's_eventually' '[' cycle_delay_const_range_expression ']' property_expr
           (seq tokstream
                (:= (vl-match))
                (when (vl-is-token? :vl-lbrack)
                  (range := (vl-parse-range)))
                (prop := (vl-parse-property-expr))
                (return (make-vl-propeventually :strongp t :range range :prop prop))))

          ((vl-is-token? :vl-kwd-eventually)
           ;; property_expr ::= 'eventually' '[' constant_range ']' property_expr
           (seq tokstream
                (:= (vl-match))
                (range := (vl-parse-range))
                (prop := (vl-parse-property-expr))
                (return (make-vl-propeventually :strongp nil :range range :prop prop))))

          ((vl-is-some-token? '(:vl-kwd-accept_on
                                :vl-kwd-reject_on
                                :vl-kwd-sync_accept_on
                                :vl-kwd-sync_reject_on))
           ;; property_expr ::= 'accept_on'      '(' expression_or_dist ')' property_expr
           ;;                 | 'reject_on'      '(' expression_or_dist ')' property_expr
           ;;                 | 'sync_accept_on' '(' expression_or_dist ')' property_expr
           ;;                 | 'sync_reject_on' '(' expression_or_dist ')' property_expr
           (seq tokstream
                (op := (vl-parse-property-acceptop))
                (:= (vl-match-token :vl-lparen))
                (condition := (vl-parse-expression-or-dist))
                (:= (vl-match-token :vl-rparen))
                (prop := (vl-parse-property-expr))
                (return (make-vl-propaccept :op op :condition condition :prop prop))))

          ((vl-is-token? :vl-kwd-if)
           ;; property_expr ::= 'if' '(' expression_or_dist ')' property_expr [ 'else' property_expr ]
           (seq tokstream
                (:= (vl-match-token :vl-kwd-if))
                (:= (vl-match-token :vl-lparen))
                (condition := (vl-parse-expression-or-dist))
                (:= (vl-match-token :vl-rparen))
                (then :s= (vl-parse-property-expr))
                (when (vl-is-token? :vl-kwd-else)
                  (:= (vl-match))
                  (else := (vl-parse-property-expr)))
                (return (make-vl-propif :condition condition
                                        :then then
                                        :else (or else *vl-trivially-true-property-expr*)))))

          ((vl-is-token? :vl-kwd-case)
           ;; property_expr ::= 'case' '(' expression_or_dist ')' property_case_item { property_case_item } 'endcase'
           (seq tokstream
                (:= (vl-match-token :vl-kwd-case))
                (:= (vl-match-token :vl-lparen))
                (condition := (vl-parse-expression-or-dist))
                (:= (vl-match-token :vl-rparen))
                (cases := (vl-parse-1+-property-case-items))
                (:= (vl-match-token :vl-kwd-endcase))
                (return (make-vl-propcase :condition condition :cases cases))))

          (t (prog2$ (impossible)
                     (vl-parse-error "not a low-precedence unary op in property expr")))))
            
  (defparser vl-parse-property-expr ()
    :short "Match @('property_expr')."
    :measure (two-nats-measure (vl-tokstream-measure) 200)
    (if (vl-is-some-token? *lower-precedence-unary-operators*)
        (vl-parse-property-low-prec-unary)
      ;; property_expr ::= impl_pe
      (vl-parse-impl-property-expr)))


  (defparser vl-parse-property-case-item ()
    :short "Match @('property_case_item')."
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    (seq tokstream
         ;; property_case_item ::= default [ ':' ] property_expr [ ';' ]
         (when (vl-is-token? :vl-kwd-default)
           (:= (vl-match))
           (when (vl-is-token? :vl-colon)
             (:= (vl-match)))
           (prop := (vl-parse-property-expr))
           (when (vl-is-token? :vl-semi)
             (:= (vl-match)))
           (return (make-vl-propcaseitem :match nil :prop prop)))
         ;; Otherwise,
         ;; property_case_item ::= expression_or_dist { ',' expression_or_dist } ':' property_expr [ ';' ]
         (match := (vl-parse-1+-expression-or-dists-separated-by-commas))
         (:= (vl-match-token :vl-colon))
         (prop := (vl-parse-property-expr))
         (when (vl-is-token? :vl-semi)
           (:= (vl-match)))
         (return (make-vl-propcaseitem :match match :prop prop))))

  (defparser vl-parse-1+-property-case-items ()
    :short "Match property_case_item { property_case_item }."
    :long "<p>We assume we need to do this until we see @('endcase').</p>"
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    (seq tokstream
         (first :s= (vl-parse-property-case-item))
         (when (vl-is-token? :vl-kwd-endcase)
           (return (list first)))
         (rest := (vl-parse-1+-property-case-items))
         (return (cons first rest))))


  (defparser vl-parse-impl-property-expr ()
    :short "Match @('impl_pe')."
    :measure (two-nats-measure (vl-tokstream-measure) 190)
    ;; ((Right Associative))
    ;; impl_pe ::= until_pe '|->' impl_pe
    ;;           | until_pe '|=>' impl_pe
    ;;           | until_pe '#-#' impl_pe
    ;;           | until_pe '#=#' impl_pe
    ;;           | until_pe
    (seq tokstream
         (left :s= (vl-parse-until-property-expr))
         (when (vl-is-some-token? '(:vl-bararrow    ;; |->
                                    :vl-bareqarrow  ;; |=>
                                    :vl-pounddash   ;; #-#
                                    :vl-poundequal  ;; #=#
                                    ))
           (op := (vl-parse-impl-prop-expr-op))
           (right := (vl-parse-impl-property-expr))
           (return (make-vl-propbinary :op op :left left :right right)))
         ;; Else, just the initial until_pe.
         (return left)))

  (defparser vl-parse-until-property-expr ()
    :short "Match @('until_pe')."
    :measure (two-nats-measure (vl-tokstream-measure) 180)
    ;; ((Right Associative))
    ;; until_pe ::= iff_pe { 'until' iff_pe }
    ;;            | iff_pe { 's_until' iff_pe }
    ;;            | iff_pe { 'until_with' iff_pe }
    ;;            | iff_pe { 's_until_with' iff_pe }
    ;;            | iff_pe { 'implies' iff_pe }
    ;;            | iff_pe
    (seq tokstream
         (left :s= (vl-parse-iff-property-expr))
         (unless (vl-is-some-token? '(:vl-kwd-until
                                      :vl-kwd-s_until
                                      :vl-kwd-until_with
                                      :vl-kwd-s_until_with
                                      :vl-kwd-implies))
           (return left))
         (op := (vl-match))
         (right := (vl-parse-until-property-expr))
         (return (make-vl-propbinary :op (case (vl-token->type op)
                                           (:vl-kwd-until        :vl-prop-until)
                                           (:vl-kwd-s_until      :vl-prop-suntil)
                                           (:vl-kwd-until_with   :vl-prop-untilwith)
                                           (:vl-kwd-s_until_with :vl-prop-suntilwith)
                                           (:vl-kwd-implies      :vl-prop-word-implies))
                                     :left left
                                     :right right))))

  (defparser vl-parse-iff-property-expr ()
    :short "Match @('iff_pe ::= or_pe { 'iff' or_pe }').  Right associative."
    :measure (two-nats-measure (vl-tokstream-measure) 170)
    (seq tokstream
         (left :s= (vl-parse-or-property-expr))
         (unless (vl-is-token? :vl-kwd-iff)
           (return left))
         (:= (vl-match))
         (right := (vl-parse-iff-property-expr))
         (return (make-vl-propbinary :op :vl-prop-iff :left left :right right))))


  (defparser vl-parse-or-property-expr ()
    :short "Match @('or_pe ::= and_pe { 'or' and_pe }').  Left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 165)
    (seq tokstream
         (mixed := (vl-parse-or-property-expr-aux))
         (return (vl-left-associate-alternating-propexpr/op-list mixed))))

  (defparser vl-parse-or-property-expr-aux ()
    :short "Parse @('or_pe ::= and_pe { 'or' and_pe }') into a @(see vl-alternating-propexpr/op-list-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 160)
    (seq tokstream
         (first :s= (vl-parse-and-property-expr))
         (unless (vl-is-token? :vl-kwd-or)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-or-property-expr-aux))
         (return (list* first :vl-prop-or tail))))


  (defparser vl-parse-and-property-expr ()
    :short "Match @('and_pe ::= not_pe { 'and' not_pe }').  Left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 155)
    (seq tokstream
         (mixed := (vl-parse-and-property-expr-aux))
         (return (vl-left-associate-alternating-propexpr/op-list mixed))))

  (defparser vl-parse-and-property-expr-aux ()
    :short "Parse @('and_pe ::= not_pe { 'and' not_pe }') into a @(see vl-alternating-propexpr/op-list-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 150)
    (seq tokstream
         (first :s= (vl-parse-not-property-expr))
         (unless (vl-is-token? :vl-kwd-and)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-and-property-expr-aux))
         (return (list* first :vl-prop-and tail))))


  (defparser vl-parse-not-property-expr ()
    :short "Match @('not_pe')."
    :measure (two-nats-measure (vl-tokstream-measure) 140)
    (let ((lower-precedence-unary-operators
           ;; Horrible godwaful hack to try to handle things like `not always
           ;; r1 until r2` parse like they do in NCVerilog.  See "Handling of
           ;; Not" in notes/properties.txt for additional discussion.
           *lower-precedence-unary-operators*))
      (cond ((vl-is-token? :vl-kwd-not)
             ;; not_pe ::= 'not' not_pe
             (seq tokstream
                  (:= (vl-match))
                  (prop := (if (vl-is-some-token? lower-precedence-unary-operators)
                               (vl-parse-property-expr)
                             (vl-parse-not-property-expr)))
                  (return (make-vl-propunary :op :vl-prop-not :arg prop))))
            ((vl-is-some-token? '(:vl-kwd-nexttime :vl-kwd-s_nexttime))
             ;; not_pe ::= 'nexttime' not_pe
             ;;          | 'nexttime' '[' constant_expression ']' not_pe
             ;;          | 's_nexttime' not_pe
             ;;          | 's_nexttime' '[' constant_expression ']' not_pe
             (seq tokstream
                  (op := (vl-match))
                  (when (vl-is-token? :vl-lbrack)
                    (:= (vl-match))
                    (expr := (vl-parse-expression))
                    (:= (vl-match-token :vl-rbrack)))
                  (prop := (if (vl-is-some-token? lower-precedence-unary-operators)
                               (vl-parse-property-expr)
                             (vl-parse-not-property-expr)))
                  (return (make-vl-propnexttime :strongp (case (vl-token->type op)
                                                           (:vl-kwd-nexttime nil)
                                                           (:vl-kwd-s_nexttime t))
                                                :expr expr
                                                :prop prop))))
            ((vl-is-some-token? lower-precedence-unary-operators)
             (vl-parse-property-low-prec-unary))
            (t
             ;; not_pe ::= strength_pe
             (vl-parse-strength-property-expr)))))

  (defparser vl-parse-strength-property-expr ()
    :short "Match @('strength_pe')."
    :measure (two-nats-measure (vl-tokstream-measure) 130)
    (cond ((vl-is-some-token? '(:vl-kwd-strong :vl-kwd-weak))
           ;; strength_pe ::= 'strong' '(' property_expr ')'
           ;;               | 'weak'   '(' property_expr ')'
           (seq tokstream
                (op := (vl-match))
                (:= (vl-match-token :vl-lparen))
                (seq := (vl-parse-property-expr))
                (:= (vl-match-token :vl-rparen))
                (return (make-vl-propunary :op (case (vl-token->type op)
                                                 (:vl-kwd-strong :vl-prop-strong)
                                                 (:vl-kwd-weak   :vl-prop-weak))
                                           :arg seq))))
          (t
           ;; strength_pe ::= isect_se
           (vl-parse-intersect-sequence-expr))))


  ;; --- isect_se ::= within_se { 'intersect' within_se }  ((Left Associative))

  (defparser vl-parse-intersect-sequence-expr ()
    :short "Parse @('isect_se ::= within_se { 'intersect' within_se }'), left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 75)
    (seq tokstream
         (mixed := (vl-parse-intersect-sequence-expr-aux))
         (return (vl-left-associate-alternating-propexpr/op-list mixed))))

  (defparser vl-parse-intersect-sequence-expr-aux ()
    :short "Parse @('isect_se ::= within_se { 'intersect' within_se }') into a @(see vl-alternating-propexpr/op-list-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 70)
    (seq tokstream
         (first :s= (vl-parse-within-sequence-expr))
         (unless (vl-is-token? :vl-kwd-intersect)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-intersect-sequence-expr-aux))
         (return (list* first :vl-prop-intersect tail))))


  ;; --- within_se ::= thout_se { 'within' thout_se }   ((Left Associative))

  (defparser vl-parse-within-sequence-expr ()
    :short "Parse @('within_se ::= thout_se { 'within' thout_se }'), left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 65)
    (seq tokstream
         (mixed := (vl-parse-within-sequence-expr-aux))
         (return (vl-left-associate-alternating-propexpr/op-list mixed))))

  (defparser vl-parse-within-sequence-expr-aux ()
    :short "Parse @('within_se ::= thout_se { 'within' thout_se }') into a @(see vl-alternating-propexpr/op-list-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 60)
    (seq tokstream
         (first :s= (vl-parse-throughout-sequence-expr))
         (unless (vl-is-token? :vl-kwd-within)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-within-sequence-expr-aux))
         (return (list* first :vl-prop-within tail))))


  ;; --- thout_se ::= expression_or_dist 'throughout' thout_se
  ;;                | delay_se

  (defparser vl-parse-throughout-sequence-expr ()
    :short "Parse @('thout_se ::= expression_or_dist 'throughout' thout_se | delay_se')."
    :measure (two-nats-measure (vl-tokstream-measure) 50)
    ;; Either form can have an expression_or_dist; we won't know which we're
    ;; parsing until we get to the 'throughout' keyword or not, so use
    ;; backtracking.
    (b* ((backup (vl-tokstream-save))
         ((mv err exprdist tokstream)
          (vl-parse-expression-or-dist))
         ((when (and (not err)
                     (vl-is-token? :vl-kwd-throughout)))
          ;; Looks like the first form.
          (seq tokstream
               (:= (vl-match))
               (right := (vl-parse-throughout-sequence-expr))
               (return (make-vl-propthroughout :left exprdist :right right))))
         ;; Didn't find throughout or just started at some non-expression in
         ;; the first place, so let's give up and try to just match a delay_se.
         ;; If exprdist is a good expression_or_dist, this may be some extra
         ;; work, but that seems fine and it's better to keep this simpler than
         ;; trying to figure out how to salvage it.
         (tokstream (vl-tokstream-restore backup)))
      (seq tokstream
           (delay := (vl-parse-delay-sequence-expr))
           (return delay))))

  ;; ((Left Associative))
  ;; delay_se ::= [cycle_range] firstmatch_se { cycle_delay_range firstmatch_se }

  (defparser vl-parse-delay-sequence-expr ()
    :short "Matches @('delay_se ::= [cycle_range] firstmatch_se { cycle_delay_range firstmatch_se }')."
    :measure (two-nats-measure (vl-tokstream-measure) 45)
    (seq tokstream
         (when (vl-is-token? :vl-poundpound)
           ;; Something like ##2 bar ##3 baz with no leading expression.
           ;; Pretend like we actually saw 1 ##2 bar ##3 baz instead.
           (tail := (vl-parse-delay-sequence-expr-tail))
           (return (vl-left-associate-delay-se-tail *vl-trivially-true-property-expr* tail)))
         (head :s= (vl-parse-firstmatch-sequence-expr))
         (when (vl-is-token? :vl-poundpound)
           ;; Something like foo ##2 bar ##3 baz.
           (tail := (vl-parse-delay-sequence-expr-tail))
           (return (vl-left-associate-delay-se-tail head tail)))
         ;; Just a foo with no ##2 bar ##3 baz style stuff after it.
         (return head)))

  (defparser vl-parse-delay-sequence-expr-tail ()
    :short "Match @('{ cycle_delay_range firstmatch_se }') constructs, may be empty."
    :measure (two-nats-measure (vl-tokstream-measure) 40)
    (seq tokstream
         (when (vl-is-token? :vl-poundpound)
           (del := (vl-parse-cycledelayrange))
           (expr :s= (vl-parse-firstmatch-sequence-expr))
           (rest := (vl-parse-delay-sequence-expr-tail))
           (return (list* del expr rest)))
         (return nil)))


  (defparser vl-parse-firstmatch-sequence-expr ()
    :short "Match @('firstmatch_se')."
    :measure (two-nats-measure (vl-tokstream-measure) 30)
    (cond ((vl-is-token? :vl-kwd-first_match)
           ;; firstmatch_se ::= 'first_match' '(' property_expr {',' sequence_match_item} ')'
           (seq tokstream
                (:= (vl-match))
                (:= (vl-match-token :vl-lparen))
                (seq :s= (vl-parse-property-expr))
                (items := (vl-parse-sequence-match-item-list))
                (:= (vl-match-token :vl-rparen))
                (return
                 ;; Basically what we're doing here is converting
                 ;;    first_match(foo, x++)
                 ;; Into the equivalent:
                 ;;    first_match((foo, x++))
                 ;; Which keeps our internal representation of vl-seqfirstmatch very simple.
                 (let ((fixup (if (atom items)
                                  ;; No assignments so we can just the sequence directly.
                                  seq
                                ;; Build the internal (foo, x++) assignment.
                                (make-vl-propassign :seq seq :items items))))
                   (make-vl-propunary :op :vl-prop-firstmatch :arg fixup)))))
          (t
           ;; firstmatch_se ::= repeat_se
           (vl-parse-repeat-sequence-expr))))

  (defparser vl-parse-repeat-sequence-expr ()
    :short "Matches @('repeat_se')."
    :measure (two-nats-measure (vl-tokstream-measure) 25)
    ;;   repeat_se ::= expression_or_dist [boolean_abbrev]
    ;;               | property_instance [sequence_abbrev]
    ;;               | '(' property_expr { ',' sequence_match_item } ')' [sequence_abbrev]

    ;; See the notes in notes/properties.txt about resolving ambiguities.  Any
    ;; of these can start with an open paren except for property_instance but
    ;; we need to try expression_or_dist first because property_instance can
    ;; match partial expressions like foo.
    (b* ((backup (vl-tokstream-save))
         ((mv err exprdist tokstream)
          (vl-parse-expression-or-dist))

         ((when (and (not err)
                     (vl-is-token? :vl-lparen)
                     (not (vl-exprdist->dist exprdist))
                     (let ((expr (vl-exprdist->expr exprdist)))
                       (vl-expr-case expr
                         (:vl-index t)
                         (:otherwise nil)))))
          ;; We hit the bad ambiguity between the expression_or_dist case and
          ;; the property_instance case.  Try to parse this as a
          ;; property_instance instead, because it doesn't seem like it can be
          ;; a valid expression any other way.
          (let ((tokstream (vl-tokstream-restore backup)))
            (vl-parse-instance-property-expr)))

         ((when err)
          ;; Failed to match expr_or_dist, so we also can't be in the
          ;; property_inst case because its identifier would have been a valid
          ;; expression.  Remaining possibility:
          ;;   repeat_se ::= '(' property_expr { ',' sequence_match_item } ')' [sequence_abbrev]
          (b* ((tokstream (vl-tokstream-restore backup))
               ((unless (vl-is-token? :vl-lparen))
                ;; Doesn't seem sensible.  I think it's better to give the
                ;; error message right here, rather than where an expression
                ;; parse failed, because we don't know whether this is supposed
                ;; to be an expression or not anyway.
                (vl-parse-error "Expected a valid property/sequence expression.")))
            (vl-parse-assign-sequence-expr)))

         ;; If we get here, we matched a exprdist successfully and we think
         ;; it's what we really wanted.  Don't backtrack, just try to match the
         ;; rest.
         (core (make-vl-propcore :guts exprdist))
         ((unless (vl-is-token? :vl-lbrack))
          (mv nil core tokstream)))
      (seq tokstream
           (reps := (vl-parse-boolean-abbrev))
           (return (make-vl-proprepeat :seq core :reps reps)))))

  (defparser vl-parse-assign-sequence-expr ()
    :short "Matches @(' '(' property_expr { ',' sequence_match_item } ')' [sequence_abbrev] ')"
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    (seq tokstream
         (:= (vl-match-token :vl-lparen))
         (seq := (vl-parse-property-expr))
         (items := (vl-parse-sequence-match-item-list))
         (:= (vl-match-token :vl-rparen))
         (when (vl-is-token? :vl-lbrack)
           (reps := (vl-parse-sequence-abbrev)))
         (return
          (b* ((core (if (atom items)
                         ;; No assignments so just collapse (foo) down to foo.
                         seq
                       ;; Build the internal (foo, x++) assignment
                       (make-vl-propassign :seq seq :items items)))
               (ret  (if (not reps)
                         ;; No repetition part, so just return the core
                         core
                       (make-vl-proprepeat :seq core :reps reps))))
            ret))))

  (defparser vl-parse-instance-property-expr ()
    :short "Matches @('property_instance [sequence_abbrev]')."
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    ;; property_instance ::= ps_or_hierarchical_sequence_identifier [ '(' [property_list_of_arguments] ')' ]
    (seq tokstream
         (name := (vl-parse-scoped-or-hierarchical-identifier))
         (when (vl-is-token? :vl-lparen)
           (:= (vl-match))
           (args := (vl-parse-property-list-of-arguments))
           (:= (vl-match-token :vl-rparen)))
         (when (vl-is-token? :vl-lbrack)
           (reps := (vl-parse-sequence-abbrev)))
         (return
          (b* ((core (make-vl-propinst :ref name :args args))
               (ret  (if (not reps)
                         core
                       (make-vl-proprepeat :seq core :reps reps))))
            ret))))


  (defparser vl-parse-property-actual-arg ((name stringp))
    :measure (two-nats-measure (vl-tokstream-measure) 250)
    :short "Match a single @('sequence_actual_arg')."
    :long "<p>This is used in the special case where we know that we want to
match exactly one (perhaps optional) @('property_actual_arg') followed by a
right paren, e.g., we are matching @('bar') in @('.foo(bar)') or similar.</p>

<p>The basic grammar rule here is:</p>

@({
    property_actual_arg ::= property_expr
                          | sequence_actual_arg

    sequence_actual_arg ::= event_expression
                          | sequence_expr
})

<p>We don't really distinguish between @('property_expr') and
@('sequence_expr').  But even without the vast ambiguity between them, this is
also ambiguous in a couple of ways.</p>

<p>First, any ordinary expression is simultaneously an @('event_expression')
and also a @('sequence_expr'), e.g., via @('expression_or_dist').  So if we
just see an identifier like @('foo') or some other expression, it may be an
event expression or a sequence expression, and it isn't clear what we should
prefer.  Furthermore, the keyword @('or') makes it so that an event expression
such as @('a or b') might instead be interpreted as a sequence expression.</p>

<p>In the special case where we know that we're expecting a single
@('property_actual_arg') followed by a right-paren, e.g., @('.foo(bar)'), it
seems fairly reasonable to just use backtracking to try both possibilities and
see which (if any) leads us to the right place.  If both succeed, e.g., perhaps
@('bar') is an ordinary expression, we arbitrarily choose to prefer a
@('property_expr') over an @('event_expression').</p>"
    (b* (((when (vl-is-token? :vl-rparen))
          (mv nil (make-vl-propactual-blank :name name) tokstream))
         (backup (vl-tokstream-save))
         ((mv err prop tokstream)
          (vl-parse-property-expr))
         ((when (and (not err)
                     (vl-is-token? :vl-rparen)))
          ;; Parsing property_expr seems to work, so call it good.
          (mv err
              (make-vl-propactual-prop :name name
                                       :prop prop)
              tokstream))
         (tokstream (vl-tokstream-restore backup))

         ((mv err evatoms tokstream) (vl-parse-event-expression))
         ((when (and (not err)
                     (vl-is-token? :vl-rparen)))
          ;; Parsing event_expression  seems to work, so call it good.
          (mv err
              (make-vl-propactual-event :name name
                                        :evatoms evatoms)
              tokstream)))
      (vl-parse-error
       "Expected lone event_expression or property_expr followed by ')'.")))

  (defparser vl-parse-1+-named-property-list-of-arguments ()
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :short "Match the named list portion of @('property_list_of_arguments')."
    :long "<p>See @(see vl-parse-property-list-of-arguments).  Our goal here is
to parse the named arguments in the tail of a @('property_list_of_arguments').
That is, we want to match:</p>

@({
      '.' identifier ( [property_actual_arg] )
           { ',' '.' identifier ( [property_actual_arg] ) }
})"

    (seq tokstream
         (:= (vl-match-token :vl-dot))
         (name := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-lparen))
         (first :w= (vl-parse-property-actual-arg (vl-idtoken->name name)))
         (:= (vl-match-token :vl-rparen))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-named-property-list-of-arguments))
           (return (cons first rest)))
         (return (list first))))

  (defparser vl-parse-property-list-of-arguments ()
    :measure (two-nats-measure (vl-tokstream-measure) 250)
    :short "Heuristically match a @('property_list_of_arguments')."
    :long "<p>Our goal is to match @('property_list_of_arguments'), defined in
the SystemVerilog-2012 grammar as follows:</p>

@({
    property_list_of_arguments ::=

        [property_actual_arg] { ',' [property_actual_arg] }
                              { ',' '.' identifier '(' [property_actual_arg] ')' }

      | '.' identifier ( [property_actual_arg] )
           { ',' '.' identifier ( [property_actual_arg] ) }
})

<p>Here is a slightly revised, equivalent grammar:</p>

@({
     named_property_list_of_arguments ::=
                    '.' identifier ( [property_actual_arg] )
              { ',' '.' identifier ( [property_actual_arg] ) }

     property_list_of_arguments ::=
         [property_actual_arg] { ',' [property_actual_arg] } [named_property_list_of_arguments]
       | named_property_list_of_arguments
})

<p>Note that we can match @('named_property_list_of_arguments') with @(see
vl-parse-1+-named-property-list-of-arguments) and we know that such a thing
always starts with a dot.  Note also that by inspecting the grammar, we can see
that @('property_list_of_arguments') always occurs within parens, so we know
that we should end on a right paren.</p>

<p>Distressingly this rule is quite ambiguous.  We describe some of the basic
@('property_actual_arg') ambiguities in @(see vl-parse-property-actual-arg).
But beyond that, here we have @('property_actual_arg')s being separated by
commas, which is even more ambiguous because an @('event_expression') can
itself be a comma-delimited list of expressions!</p>

<p>So how can we handle this.  One option would be to try to aggressively use
backtracking to find a match.  But even then we have to make rather arbitrary
distinctions for expressions like @('a or b')---is it an event expression or
is it a property expression?</p>

<p>So I think something I like better is to be a little more restrictive.
Suppose that instead of the full @('event_expression') grammar, we only support
edge expressions that have an explicit posedge or negedge, and otherwise we
require a property expression.  This will still allow us to match most of the
grammar and will probably lead to mostly correct interpretations.</p>

<p>Coming up with a proper solution to this would probably require a lot of
experimentation.  This language is so awful...</p>"

    (seq tokstream
         (when (vl-is-token? :vl-rparen)
           (return nil))
         (when (vl-is-token? :vl-dot)
           ;; Switch to parsing a named_property_of_arguments, hooray.
           (rest := (vl-parse-1+-named-property-list-of-arguments))
           (return rest))
         (when (vl-is-token? :vl-comma)
           ;; Blank argument I guess.
           (:= (vl-match))
           (rest := (vl-parse-property-list-of-arguments))
           (return (cons (make-vl-propactual-blank) rest)))
         (return-raw
          ;; Try backtracking to match a "proper" event_expression or a
          ;; property expression.
          (b* ((backup (vl-tokstream-save))
               ((mv err evatoms tokstream) (vl-parse-event-expression-fragment))
               ((unless err)
                ;; This really looks like an edge expression or a compound
                ;; event expression involving more than one event, so we want
                ;; to go ahead and make an event actual for it, rather than a
                ;; property actual.
                (seq tokstream
                     (when (vl-is-token? :vl-comma)
                       (:= (vl-match))
                       (rest := (vl-parse-property-list-of-arguments)))
                     (return
                      (cons (make-vl-propactual-event :name nil
                                                      :evatoms evatoms)
                            rest))))
               ;; Otherwise, and probably far more common, just try to match a
               ;; property expression.
               (tokstream (vl-tokstream-restore backup)))
            (seq tokstream
                 (first :s= (vl-parse-property-expr))
                 (when (vl-is-token? :vl-comma)
                   (:= (vl-match))
                   (rest := (vl-parse-property-list-of-arguments)))
                 (return (cons (make-vl-propactual-prop :name nil
                                                        :prop first)
                               rest)))))))

    )


(local (in-theory (disable acl2::lower-bound-of-len-when-sublistp
                           acl2::sublistp-when-prefixp
                           acl2::len-when-prefixp
                           acl2::len-when-atom
                           acl2::prefixp-when-equal-lengths
                           acl2::prefixp-when-not-consp-right
                           ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                           ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP
                           (tau-system)
                           default-<-1
                           default-<-2
                           double-containment)))

(make-event
 `(defthm-parse-property-expr-flag vl-parse-property-expr-when-error
    ;; Whenever there's an error, the main return value is NIL.
    ,(vl-val-when-error-claim vl-parse-property-low-prec-unary)
    ,(vl-val-when-error-claim vl-parse-property-expr)
    ,(vl-val-when-error-claim vl-parse-property-case-item)
    ,(vl-val-when-error-claim vl-parse-1+-property-case-items)
    ,(vl-val-when-error-claim vl-parse-impl-property-expr)
    ,(vl-val-when-error-claim vl-parse-until-property-expr)
    ,(vl-val-when-error-claim vl-parse-iff-property-expr)
    ,(vl-val-when-error-claim vl-parse-or-property-expr)
    ,(vl-val-when-error-claim vl-parse-or-property-expr-aux)
    ,(vl-val-when-error-claim vl-parse-and-property-expr)
    ,(vl-val-when-error-claim vl-parse-and-property-expr-aux)
    ,(vl-val-when-error-claim vl-parse-not-property-expr)
    ,(vl-val-when-error-claim vl-parse-strength-property-expr)
    ,(vl-val-when-error-claim vl-parse-intersect-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-intersect-sequence-expr-aux)
    ,(vl-val-when-error-claim vl-parse-within-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-within-sequence-expr-aux)
    ,(vl-val-when-error-claim vl-parse-throughout-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-delay-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-delay-sequence-expr-tail)
    ,(vl-val-when-error-claim vl-parse-firstmatch-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-repeat-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-assign-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-instance-property-expr)
    ,(vl-val-when-error-claim vl-parse-property-actual-arg :args (name))
    ,(vl-val-when-error-claim vl-parse-1+-named-property-list-of-arguments)
    ,(vl-val-when-error-claim vl-parse-property-list-of-arguments)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-property-expr-fn (w state)))))))

(make-event
 `(defthm-parse-property-expr-flag vl-parse-property-expr-warning
    ,(vl-warning-claim vl-parse-property-low-prec-unary)
    ,(vl-warning-claim vl-parse-property-expr)
    ,(vl-warning-claim vl-parse-property-case-item)
    ,(vl-warning-claim vl-parse-1+-property-case-items)
    ,(vl-warning-claim vl-parse-impl-property-expr)
    ,(vl-warning-claim vl-parse-until-property-expr)
    ,(vl-warning-claim vl-parse-iff-property-expr)
    ,(vl-warning-claim vl-parse-or-property-expr)
    ,(vl-warning-claim vl-parse-or-property-expr-aux)
    ,(vl-warning-claim vl-parse-and-property-expr)
    ,(vl-warning-claim vl-parse-and-property-expr-aux)
    ,(vl-warning-claim vl-parse-not-property-expr)
    ,(vl-warning-claim vl-parse-strength-property-expr)
    ,(vl-warning-claim vl-parse-intersect-sequence-expr)
    ,(vl-warning-claim vl-parse-intersect-sequence-expr-aux)
    ,(vl-warning-claim vl-parse-within-sequence-expr)
    ,(vl-warning-claim vl-parse-within-sequence-expr-aux)
    ,(vl-warning-claim vl-parse-throughout-sequence-expr)
    ,(vl-warning-claim vl-parse-delay-sequence-expr)
    ,(vl-warning-claim vl-parse-delay-sequence-expr-tail)
    ,(vl-warning-claim vl-parse-firstmatch-sequence-expr)
    ,(vl-warning-claim vl-parse-repeat-sequence-expr)
    ,(vl-warning-claim vl-parse-assign-sequence-expr)
    ,(vl-warning-claim vl-parse-instance-property-expr)
    ,(vl-warning-claim vl-parse-property-actual-arg :args (name))
    ,(vl-warning-claim vl-parse-1+-named-property-list-of-arguments)
    ,(vl-warning-claim vl-parse-property-list-of-arguments)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-property-expr-fn (w state)))))))

(make-event
 `(defthm-parse-property-expr-flag vl-parse-property-expr-progress
    ,(vl-progress-claim vl-parse-property-low-prec-unary)
    ,(vl-progress-claim vl-parse-property-expr)
    ,(vl-progress-claim vl-parse-property-case-item)
    ,(vl-progress-claim vl-parse-1+-property-case-items)
    ,(vl-progress-claim vl-parse-impl-property-expr)
    ,(vl-progress-claim vl-parse-until-property-expr)
    ,(vl-progress-claim vl-parse-iff-property-expr)
    ,(vl-progress-claim vl-parse-or-property-expr)
    ,(vl-progress-claim vl-parse-or-property-expr-aux)
    ,(vl-progress-claim vl-parse-and-property-expr)
    ,(vl-progress-claim vl-parse-and-property-expr-aux)
    ,(vl-progress-claim vl-parse-not-property-expr)
    ,(vl-progress-claim vl-parse-strength-property-expr)
    ,(vl-progress-claim vl-parse-intersect-sequence-expr)
    ,(vl-progress-claim vl-parse-intersect-sequence-expr-aux)
    ,(vl-progress-claim vl-parse-within-sequence-expr)
    ,(vl-progress-claim vl-parse-within-sequence-expr-aux)
    ,(vl-progress-claim vl-parse-throughout-sequence-expr)
    ,(vl-progress-claim vl-parse-delay-sequence-expr)
    (vl-parse-delay-sequence-expr-tail
     ;; Special... strong when we know it's a poundpound.
     (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-delay-sequence-expr-tail)))
              (vl-tokstream-measure))
          (implies (and (not (mv-nth 0 (vl-parse-delay-sequence-expr-tail)))
                        (vl-is-token? :vl-poundpound))
                   (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-delay-sequence-expr-tail)))
                      (vl-tokstream-measure))))
     :rule-classes ((:rewrite) (:linear)))
    ,(vl-progress-claim vl-parse-firstmatch-sequence-expr)
    ,(vl-progress-claim vl-parse-repeat-sequence-expr)
    ,(vl-progress-claim vl-parse-assign-sequence-expr)
    ,(vl-progress-claim vl-parse-instance-property-expr)
    ,(vl-progress-claim vl-parse-property-actual-arg :args (name) :strongp nil)
    ,(vl-progress-claim vl-parse-1+-named-property-list-of-arguments)
    ,(vl-progress-claim vl-parse-property-list-of-arguments :strongp nil)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-property-expr-fn (w state)))))))


(defun vl-propexpr-claim-fn (name args type)
  `'(,name (implies (force (not (mv-nth 0 (,name . ,args))))
                    (,(case type
                        (:propexpr  'vl-propexpr-p)
                        (:mixed     'vl-alternating-propexpr/op-list-p)
                        (:delaytail 'vl-delay-se-tail-p)
                        (:actual    'vl-propactual-p)
                        (:actuals   'vl-propactuallist-p)
                        (:caseitem  'vl-propcaseitem-p)
                        (:caseitems 'vl-propcaseitemlist-p)
                        (otherwise
                         (er hard? 'vl-propexpr-claim-fn "Bad type ~x0~%" type)))
                     (mv-nth 1 (,name . ,args))))))

(defmacro vl-propexpr-claim (name type &key args)
  (vl-propexpr-claim-fn name args type))

(make-event
 `(defthm-parse-property-expr-flag vl-parse-property-expr-value
    ,(vl-propexpr-claim vl-parse-property-low-prec-unary :propexpr)
    ,(vl-propexpr-claim vl-parse-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-property-case-item :caseitem)
    ,(vl-propexpr-claim vl-parse-1+-property-case-items :caseitems)
    ,(vl-propexpr-claim vl-parse-impl-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-until-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-iff-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-or-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-or-property-expr-aux :mixed)
    ,(vl-propexpr-claim vl-parse-and-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-and-property-expr-aux :mixed)
    ,(vl-propexpr-claim vl-parse-not-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-strength-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-intersect-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-intersect-sequence-expr-aux :mixed)
    ,(vl-propexpr-claim vl-parse-within-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-within-sequence-expr-aux :mixed)
    ,(vl-propexpr-claim vl-parse-throughout-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-delay-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-delay-sequence-expr-tail :delaytail)
    ,(vl-propexpr-claim vl-parse-firstmatch-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-repeat-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-assign-sequence-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-instance-property-expr :propexpr)
    ,(vl-propexpr-claim vl-parse-property-actual-arg :actual :args (name))
    ,(vl-propexpr-claim vl-parse-1+-named-property-list-of-arguments :actuals)
    ,(vl-propexpr-claim vl-parse-property-list-of-arguments :actuals)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-property-expr-fn (w state)))))))

(verify-guards vl-parse-property-expr-fn
  ;; :guard-debug t
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable vl-type-of-matched-token
                                    vl-is-token?)))))


(defparser vl-parse-property-spec ()
  :short "Parse @('property_spec')."
  :long "@({
               property_spec ::= [clocking_event] [ 'disable' 'iff' '(' expression_or_dist ')' ] property_expr
         })"
  :result (vl-propspec-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       (when (vl-is-token? :vl-atsign)
         (evatoms := (vl-parse-clocking-event)))
       (when (vl-is-token? :vl-kwd-disable)
         (:= (vl-match))
         (:= (vl-match-token :vl-kwd-iff))
         (:= (vl-match-token :vl-lparen))
         (exprdist := (vl-parse-expression-or-dist))
         (:= (vl-match-token :vl-rparen)))
       (prop := (vl-parse-property-expr))
       (return (make-vl-propspec :evatoms evatoms :disable exprdist :prop prop :loc loc))))
