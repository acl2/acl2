; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "statements")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defxdoc parse-sequence
  :parents (parser)
  :short "Functions for parsing SystemVerilog assertion sequence expressions.")

(local (xdoc::set-default-parents parse-sequence))


(defval *vl-trivially-true-sequence-expr*
  :parents (vl-seqthen)
  :short "A @(see vl-seqexpr) that is always true."

  :long "<p>This is useful as the implicit first step in a @(see vl-seqthen)
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
explicit as the head of the sequence.</p>"

  (make-vl-seqcore :guts
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

(defval *vl-end-of-sequence-$*
  :parents (vl-parse-cycledelayrange)
  (make-vl-special :key :vl-$))

(assert! (vl-expr-p *vl-end-of-sequence-$*))

(defparser vl-parse-cycledelayrange ()
  :short "Matches @('cycle_delay_range')."
  :result (vl-cycledelayrange-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :long "<p>See @(see vl-cycledelayrange).  Grammar rules are as follows:</p>

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
         (return (make-vl-cycledelayrange :left left :right nil)))

       (:= (vl-match))  ;; Eat [

       (when (vl-is-token? :vl-times)
         (:= (vl-match))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-cycledelayrange :left (vl-make-index 0)
                                          :right *vl-end-of-sequence-$*)))

       (when (vl-is-token? :vl-plus)
         (:= (vl-match))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-cycledelayrange :left (vl-make-index 1)
                                          :right *vl-end-of-sequence-$*)))

       ;; Otherwise should have two expressions.  We don't have to do anything
       ;; special in case the right one is a $.
       (left := (vl-parse-expression))
       (:= (vl-match-token :vl-colon))
       (right := (vl-parse-expression))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-cycledelayrange :left left
                                        :right right))))

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
  ;; not be in parens in a sequence_match_item.  Fortunately our expression
  ;; parsing code doesn't currently enforce that restriction.  So for now I think
  ;; the most expedient thing to do is just:
  ;;
  ;;  1. Try to parse an ordinary expression.
  ;;  2. Check to see if it was a valid sequence_match_item.
  ;;
  ;; In the future we might want to make this more restrictive and generally
  ;; expand upon the kinds of subroutine_calls that our expression parsing code
  ;; supports, etc.

  (seq tokstream
       (expr := (vl-parse-expression))
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

(defparser vl-parse-event-expression-fragment ()
  :parents (vl-parse-sequence-list-of-arguments)
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


; -----------------------------------------------------------------------------
;
; Precedence
;
; Basic grammar rule per the SystemVerilog-2012 standard:
;
; sequence_expr ::= cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;                 | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;                 | expression_or_dist [boolean_abbrev]
;                 | sequence_instance [sequence_abbrev]
;                 | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;                 | sequence_expr 'and' sequence_expr
;                 | sequence_expr 'intersect' sequence_expr
;                 | sequence_expr 'or' sequence_expr
;                 | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
;                 | expression_or_dist 'throughout' sequence_expr
;                 | sequence_expr 'within' sequence_expr
;                 | clocking_event sequence_expr
;
; To make any sense of this we need to know the precedences of these operators.
; The SystemVerilog-2012 standard almost tells us what we need to know in Table
; 16-1, Page 356.
;
;            Operators        Associativity       Precedence
;     --------------------------------------------------------
;       [* ]  [= ]  [-> ]     ---                   highest
;       ##                    Left
;       throughout            Right
;       within                Left
;       intersect             Left
;       and                   Left
;       or                    Left                  lowest
;     --------------------------------------------------------
;
; So this almost covers everything.  Just running through the rules again:
;
;    (ok) A cycle_delay_range is a ## thing, so these are basically covered:
;
;                    cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;                 | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;
;    (ok) A boolean_abbrev or sequence_abbrev is a [*], [+], [=], or [->] kind of
;         thing, so these are covered (modulo the omission of [+], but it seems
;         safe to assume that's supposed to be treated like the others.)
;
;                 | expression_or_dist [boolean_abbrev]
;                 | sequence_instance [sequence_abbrev]
;
;    (ok) This rule seems fine because the explicit parens mean there's not
;         really any interaction with any other rules.
;
;                 | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;
;    (ok) These are explicitly covered in the table:
;
;                 | sequence_expr 'and' sequence_expr
;                 | sequence_expr 'intersect' sequence_expr
;                 | sequence_expr 'or' sequence_expr
;
;    (ok) This one isn't a problem because the explicit parens mean we can't really have
;         any confusion about interactions with other operators.
;
;                 | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
;
;    (ok) This is covered in the table but is slightly weird/special because of the
;         right associativity.
;
;                 | expression_or_dist 'throughout' sequence_expr
;
;    (ok) This one is covered in the table above.
;
;                 | sequence_expr 'within' sequence_expr
;
;   (bad) This one is not covered in the table and unfortunately commercial
;         simulators do not seem to agree what its precedence should be.
;
;                 | clocking_event sequence_expr
;
; Experiments with NCVerilog and VCS (see vl/loader/parser/notes/seqprec.sv)
; suggest that NCV treats a clocking_event as having lower precedence than OR,
; but that VCS does the opposite.  That's too bad because it means we don't
; have any real basis for making a decision other than whatever we like better.
; Fortunately, I have arbitrarily decreed that NCVerilog's behavior is nicer,
; and that's what I'm going to implement.
;
; OK, so now to do the usual thing and convert these precedences into a grammar
; that we can implement in recursive descent style.  The lowest priority rules
; need to come first, and the very lowest priority rule is going to be a the
; rule for clocking events.  Here's an updated table with my rule names:
;
;            Operators        Associativity       Precedence         MyName
;     -----------------------------------------------------------------------------------------
;       [* ]  [= ]  [-> ]     ---                   highest        repeat_se
;       ##                    Left                                 delay_se
;       throughout            Right                                thout_se
;       within                Left                                 within_se
;       intersect             Left                                 isect_se
;       and                   Left                                 and_se
;       or                    Left                                 or_se
;       clocking events       ---                   lowest         sequence_expression
;     -----------------------------------------------------------------------------------------
;
; Working from the top-down:
;
;   sequence_expression  ::= [clocking_event] or_se
;   or_se                ::= and_se { 'or' and_se }               ((Left Associative))
;   and_se               ::= isect_se { 'and' isect_se }          ((Left Associative))
;   isect_se             ::= within_se { 'intersect' within_se }  ((Left Associative))
;   within_se            ::= thout_se { 'within' thout_se }       ((Left Associative))
;
; Throughout expressions things are a little trickier.  I want to write
; something like:
;
;   thout_se  ::= delay_se { 'throughout' delay_se } ((Right Associative))
;
; But that doesn't seem quite right because we're only supposed to have an
; expression_or_dist on the left hand side.  So maybe a better way to write
; this is:
;
;    thout_se ::= expression_or_dist 'throughout' thout_se
;               | delay_se
;
; This is ambiguous, but it seems straightforward to try to match the
; 'throughout' form first and then backtrack if that wasn't right.  The
; right-associative style of the rule is a natural fit for recursive descent,
; so that should work well.
;
; Moving along to ## operators.  The original grammar rules to consider here
; are:
;
;    sequence_expr ::=               cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;                    | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;
; Supposing that we're going to introduce a repeat_se for higher-precedence
; sequence expressions, I think what we want here is:
;
;    delay_se ::=           cycle_delay_range repeat_se { cycle_delay_range repeat_se }
;               | repeat_se cycle_delay_range repeat_se { cycle_delay_range repeat_se }
;
; But of course we also want a way for higher precedence sequence expressions
; to be used as delay expressions directly, so I think really our starting
; point should be:
;
;    delay_se ::=           cycle_delay_range repeat_se { cycle_delay_range repeat_se }
;               | repeat_se cycle_delay_range repeat_se { cycle_delay_range repeat_se }
;               | repeat_se
;
; Obviously the second rule collapses as follows:
;
;    delay_se ::=           cycle_delay_range repeat_se { cycle_delay_range repeat_se }
;               | repeat_se { cycle_delay_range repeat_se }
;               | repeat_se
;
; Now just adjusting spacing we have:
;
;    delay_se ::= cycle_delay_range repeat_se { cycle_delay_range repeat_se }
;               |                   repeat_se { cycle_delay_range repeat_se }
;               |                   repeat_se
;
; Which I think reduces to simply:
;
;    delay_se ::= [cycle_range] repeat_se { cycle_delay_range repeat_se }  ((Left Associative))
;
; That gets us down to repeat expressions for the [*], [+], [=], and [->]
; constructs.  Let's review how much of the original grammar we haven't
; covered yet:
;
;       DONE        cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;       DONE      | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;       TODO      | expression_or_dist [boolean_abbrev]
;       TODO      | sequence_instance [sequence_abbrev]
;       TODO      | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;       DONE      | sequence_expr 'and' sequence_expr
;       DONE      | sequence_expr 'intersect' sequence_expr
;       DONE      | sequence_expr 'or' sequence_expr
;       TODO      | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
;       DONE      | expression_or_dist 'throughout' sequence_expr
;       DONE      | sequence_expr 'within' sequence_expr
;       DONE      | clocking_event sequence_expr
;
; So just collecting up the TODO part we're left with:
;
;   repeat_se ::= expression_or_dist [boolean_abbrev]
;               | sequence_instance [sequence_abbrev]
;               | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;               | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
;
; Some of this is easy and unambiguous:
;
;   - The first_match case is really easy because it has a unique keyword that
;     obviously distinguishes it from the other cases.
;
;   - The leading paren in the third case clearly distinguishes it from the
;     sequence_instance case.
;
; However, there are two ambiguities which make this trickier.  Note the
; following supporting productions:
;
;   expression_or_dist ::= expression [ 'dist' '{' dist_list '}' ]
;   sequence_instance ::= ps_or_hierarchical_sequence_identifier [ '(' [sequence_list_of_arguments] ')' ]
;   boolean_abbrevs are things like:  [* ...], [+], [= ...], or [-> ...]
;   sequence_abbrevs are similar but slightly more restrictive: [* ...], [+] are OK, but not [= ...] or [-> ...]
;
; Ambiguity 1. Any ps_or_hierarchical_sequence_identifier is a valid
; expression, so if we just see a ps_or_hierarchical_sequence_identifier, with
; or without arguments, it's not clear whether we're in the sequence_instance
; or expression_or_dist case.
;
; We sometimes face similar ambiguities and need to know whether something is a
; user-defined type, and we track those in the parse state.  But I don't think
; that's an approach that we can use here, because the SystemVerilog standard
; (Section 16.8, Page 350) explicitly says: "A named sequence may be
; instantiated anywhere that a sequence_expr may be written, including prior to
; its declaration."  So it seems like we can just "know" that we're dealing
; with a sequence identifier, because even if we are, we may not have seen its
; declaration yet.
;
; So how deep is this ambiguity?  A lone identifier might be fine as an
; expression.  But a sequence instance can optionally have this very subtle
; sequence_list_of_arguments.  So it seems to me that an ordinary looking
; function call like foo(1,2,3) could match both expression and
; sequence_instance.
;
; Can we resolve this via backtracking?  We might try:
;
;   1. Try to match sequence_instance [sequence_abbrev]
;   2. If unsuccessful, backtrack and match expression_or_dist [boolean_abbrev]
;
; I think this is clearly broken because there are expressions that have tails
; after the sequence_instance part.  For instance, consider an expression such
; as `foo + bar`.  Here `foo` is a perfectly valid sequence_instance, so we will
; succeed in step 1 and think we've matched a whole sequence_expression, but
; there's more stuff there that we should have consumed.
;
; So we might try the reverse, i.e.:
;
;   1. Try to match expression_or_dist [boolean_abbrev]
;   2. If unsuccessful, backtrack and match sequence_instance [sequence_abbrev]
;
; I think this has a similar problem.  In particular, there are some sequence
; instances such as `foo(1,2,3)` that are valid expressions, but there are also
; sequence instances that are not, such as `foo(a within b)`.  So if we
; encounter such a thing, then our expression_or_dist parser would still match
; part of this: it will tell us that `foo` is a valid expression, but it will
; have failed to match the sequence_list_of_arguments.
;
; On the other hand, this is salvageable because, unlike expressions where a
; partial match might be followed by many different kinds of tokens, it seems
; possible to straightforwardly identify when we are in this bad situation.  In
; particular, the only way that a sequence_instance can be a non-expression is
; if there is something about its arguments that makes them non-expressions.
; And in that case, it seems like:
;
;   - Our expression parser will produce an identifier
;   - The next token in the input stream will be '(', i.e., the start of the
;     argument list.
;
; So: is there any way for us to encounter a ( after parsing a valid
; sequence_expr?  It takes awhile to follow through the grammar, but after
; tracing through it a bunch, I don't believe this is possible.  So I think the
; following is a valid heuristic:
;
;    1. Try to match expression_or_dist [boolean_abbrev]
;    2. If you arrive at an open paren, you have done the wrong thing,
;       backtrack and try to match sequence_instance [sequence_abbrev]
;       instead.
;
; Ambiguity 2.  How can we differentiate between:
;
;      expression_or_dist [boolean_abbrev]
;      '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;
; Note that a sequence_match_item is basically just a restricted subset of
; expression.  This seems like a more run of the mill ambiguity that we can
; probably easily solve with backtracking.  There are expressions like `(foo)`
; which are also valid sequence expressions, but in that case I think we
; probably prefer to just treat them as plain expressions.  If we run into
; something fancier like `(foo, bar)`, it won't be a valid expression anyway,
; so we can just start with expression_or_dist and backtrack if that fails.

(define vl-mixed-sequence-oplist-p (x)
  :short "Temporary structure to support parsing left-associative sequence expressions."
  (and (consp x)
       (vl-seqexpr-p (first x))
       (or (not (consp (cdr x)))
           (and (consp (cddr x))
                (let ((op (second x))
                      (rest (cddr x)))
                  (and (vl-seqbinop-p op)
                       (vl-mixed-sequence-oplist-p rest))))))
  ///
  (defthm vl-mixed-sequence-oplist-p-when-atom
    (implies (atom x)
             (equal (vl-mixed-sequence-oplist-p x)
                    nil)))

  (defthm vl-mixed-sequence-oplist-p-of-singleton
    (equal (vl-mixed-sequence-oplist-p (list x))
           (vl-seqexpr-p x)))

  (defthm vl-mixed-sequence-oplist-p-of-list*
    (equal (vl-mixed-sequence-oplist-p (list* x y z))
           (and (vl-seqexpr-p x)
                (vl-seqbinop-p y)
                (vl-mixed-sequence-oplist-p z)))))

(define vl-left-associate-mixed-sequence-oplist ((x vl-mixed-sequence-oplist-p))
  :returns (seqexpr vl-seqexpr-p)
  :measure (len x)
  (if (atom (cdr x))
      (vl-seqexpr-fix (first x))
    (b* (((list* left op right rest) x))
      (vl-left-associate-mixed-sequence-oplist
       (cons (make-vl-seqbinary :left left
                                :op op
                                :right right)
             rest))))
  :prepwork ((local (in-theory (enable vl-mixed-sequence-oplist-p)))))


(define vl-delay-se-tail-p (x)
  :short "Temporary structure to support left-associative parsing of @('{ cycle_delay_range repeat_se }')."
  (if (atom x)
      (not x)
    (and (consp x)
         (consp (cdr x))
         (and (vl-cycledelayrange-p (first x))
              (vl-seqexpr-p (second x))
              (vl-delay-se-tail-p (cddr x)))))
  ///
  (defthm vl-delay-se-tail-p-when-atom
    (implies (atom x)
             (equal (vl-delay-se-tail-p x)
                    (not x))))

  (defthm vl-delay-se-tail-p-of-list*
    (equal (vl-delay-se-tail-p (list* delay expr rest))
           (and (vl-cycledelayrange-p delay)
                (vl-seqexpr-p expr)
                (vl-delay-se-tail-p rest)))))

(define vl-left-associate-delay-se-tail ((head vl-seqexpr-p)
                                         (tail vl-delay-se-tail-p))
  :returns (seqexpr vl-seqexpr-p)
  (b* (((when (atom tail))
        (vl-seqexpr-fix head))
       ((list* delay expr rest) tail)
       (new-head (make-vl-seqthen :left head
                                  :delay delay
                                  :right expr)))
    (vl-left-associate-delay-se-tail new-head rest))
  :prepwork ((local (in-theory (enable vl-delay-se-tail-p)))))




(defparsers parse-sequence-expr
  :verify-guards nil
  :flag-local nil
  :measure-debug t

  (defparser vl-parse-sequence-expr ()
    :short "Match @('sequence_expression  ::= [clocking_event] or_se')."
    :measure (two-nats-measure (vl-tokstream-measure) 100)
    (seq tokstream
         (when (vl-is-token? :vl-atsign)
           ;; I don't think there's any other case where we can have an @ sign
           ;; here, so this should definitely be a clocking event.
           (trigger := (vl-parse-clocking-event))
           (then    := (vl-parse-or-sequence-expr))
           (return (make-vl-seqclock :trigger trigger
                                     :then then)))
         ;; Else no clocking event, so just parse the or_se.
         (then := (vl-parse-or-sequence-expr))
         (return then)))


  ;; --- or_se ::= and_se { 'or' and_se } ((Left Associative))

  (defparser vl-parse-or-sequence-expr ()
    :short "Parse @('or_se ::= and_se { 'or' and_se }'), left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 95)
    (seq tokstream
         (mixed := (vl-parse-or-sequence-expr-aux))
         (return (vl-left-associate-mixed-sequence-oplist mixed))))

  (defparser vl-parse-or-sequence-expr-aux ()
    :short "Parse @('or_se ::= and_se { 'or' and_se }') into a @(see vl-mixed-sequence-oplist-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 90)
    (seq tokstream
         (first :s= (vl-parse-and-sequence-expr))
         (unless (vl-is-token? :vl-kwd-or)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-or-sequence-expr-aux))
         (return (list* first :vl-sequence-or tail))))


  ;; --- and_se ::= isect_se { 'and' isect_se } ((Left Associative))

  (defparser vl-parse-and-sequence-expr ()
    :short "Parse @('and_se ::= isect_se { 'and' isect_se }'), left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 85)
    (seq tokstream
         (mixed := (vl-parse-and-sequence-expr-aux))
         (return (vl-left-associate-mixed-sequence-oplist mixed))))

  (defparser vl-parse-and-sequence-expr-aux ()
    :short "Parse @('and_se ::= isect_se { 'and' isect_se }') into a @(see vl-mixed-sequence-oplist-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 80)
    (seq tokstream
         (first :s= (vl-parse-intersect-sequence-expr))
         (unless (vl-is-token? :vl-kwd-and)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-and-sequence-expr-aux))
         (return (list* first :vl-sequence-and tail))))


  ;; --- isect_se ::= within_se { 'intersect' within_se }  ((Left Associative))

  (defparser vl-parse-intersect-sequence-expr ()
    :short "Parse @('isect_se ::= within_se { 'intersect' within_se }'), left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 75)
    (seq tokstream
         (mixed := (vl-parse-intersect-sequence-expr-aux))
         (return (vl-left-associate-mixed-sequence-oplist mixed))))

  (defparser vl-parse-intersect-sequence-expr-aux ()
    :short "Parse @('isect_se ::= within_se { 'intersect' within_se }') into a @(see vl-mixed-sequence-oplist-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 70)
    (seq tokstream
         (first :s= (vl-parse-within-sequence-expr))
         (unless (vl-is-token? :vl-kwd-intersect)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-intersect-sequence-expr-aux))
         (return (list* first :vl-sequence-intersect tail))))


  ;; --- within_se ::= thout_se { 'within' thout_se }   ((Left Associative))

  (defparser vl-parse-within-sequence-expr ()
    :short "Parse @('within_se ::= thout_se { 'within' thout_se }'), left associative."
    :measure (two-nats-measure (vl-tokstream-measure) 65)
    (seq tokstream
         (mixed := (vl-parse-within-sequence-expr-aux))
         (return (vl-left-associate-mixed-sequence-oplist mixed))))

  (defparser vl-parse-within-sequence-expr-aux ()
    :short "Parse @('within_se ::= thout_se { 'within' thout_se }') into a @(see vl-mixed-sequence-oplist-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 60)
    (seq tokstream
         (first :s= (vl-parse-throughout-sequence-expr))
         (unless (vl-is-token? :vl-kwd-within)
           (return (list first)))
         (:= (vl-match))
         (tail := (vl-parse-within-sequence-expr-aux))
         (return (list* first :vl-sequence-within tail))))


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
               (return (make-vl-seqthroughout :left exprdist :right right))))
         ;; Didn't find throughout or just started at some non-expression in
         ;; the first place, so let's give up and try to just match a delay_se.
         ;; If exprdist is a good expression_or_dist, this may be some extra
         ;; work, but that seems fine and it's better to keep this simpler than
         ;; trying to figure out how to salvage it.
         (tokstream (vl-tokstream-restore backup)))
      (seq tokstream
           (delay := (vl-parse-delay-sequence-expr))
           (return delay))))

  ;; delay_se ::= [cycle_range] repeat_se { cycle_delay_range repeat_se }  ((Left Associative))

  (defparser vl-parse-delay-sequence-expr ()
    :short "Matches @('delay_se ::= [cycle_range] repeat_se { cycle_delay_range repeat_se }')."
    :measure (two-nats-measure (vl-tokstream-measure) 45)
    (seq tokstream
         (when (vl-is-token? :vl-poundpound)
           ;; Something like ##2 bar ##3 baz with no leading expression.
           ;; Pretend like we actually saw 1 ##2 bar ##3 baz instead.
           (tail := (vl-parse-delay-sequence-expr-tail))
           (return (vl-left-associate-delay-se-tail *vl-trivially-true-sequence-expr* tail)))
         (head :s= (vl-parse-repeat-sequence-expr))
         (when (vl-is-token? :vl-poundpound)
           ;; Something like foo ##2 bar ##3 baz.
           (tail := (vl-parse-delay-sequence-expr-tail))
           (return (vl-left-associate-delay-se-tail head tail)))
         ;; Just a foo with no ##2 bar ##3 baz style stuff after it.
         (return head)))

  (defparser vl-parse-delay-sequence-expr-tail ()
    :short "Match @('{ cycle_delay_range repeat_se }') constructs, may be empty."
    :measure (two-nats-measure (vl-tokstream-measure) 40)
    (seq tokstream
         (when (vl-is-token? :vl-poundpound)
           (del := (vl-parse-cycledelayrange))
           (expr :s= (vl-parse-repeat-sequence-expr))
           (rest := (vl-parse-delay-sequence-expr-tail))
           (return (list* del expr rest)))
         (return nil)))


  ;;   repeat_se ::= expression_or_dist [boolean_abbrev]
  ;;               | sequence_instance [sequence_abbrev]
  ;;               | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
  ;;               | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'

  (defparser vl-parse-repeat-sequence-expr ()
    :short "Matches @('repeat_se')."
    :measure (two-nats-measure (vl-tokstream-measure) 30)
    (seq tokstream

         (when (vl-is-token? :vl-kwd-first_match)
           ;; 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
           (:= (vl-match))
           (:= (vl-match-token :vl-lparen))
           (seq :s= (vl-parse-sequence-expr))
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
                           (make-vl-seqassign :seq seq :items items))))
              (make-vl-seqfirstmatch :seq fixup))))

         ;; See the notes above on resolving ambiguities.
         (return-raw
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
                ;; We hit the bad ambiguity between the expression_or_dist case
                ;; and the sequence_instance case.  Try to parse this as a
                ;; sequence instance instead because it doesn't seem like it
                ;; can be a valid expression.
                (let ((tokstream (vl-tokstream-restore backup)))
                  (vl-parse-instance-sequence-expr)))

               ((when err)
                ;; Failed to match expr_or_dist, so we can't be in the
                ;; sequence_inst case because its identifier would have been a
                ;; valid expression.  The only other possibility is that we're
                ;; in the embedded assignment case.
                (b* ((tokstream (vl-tokstream-restore backup))
                     ((when (vl-is-token? :vl-lparen))
                      (vl-parse-assign-sequence-expr)))
                  ;; Doesn't seem sensible.  I think it's better to give the
                  ;; error message right here, rather than where an expression
                  ;; parse failed, because we don't know whether this is
                  ;; supposed to be an expression or not anyway.
                  (vl-parse-error "Expected a valid sequence expression.")))

               ;; If we get here, we matched a exprdist successfully and we
               ;; think it's what we really wanted.  Don't backtrack, try to
               ;; match the rest.
               (core (make-vl-seqcore :guts exprdist))
               ((unless (vl-is-token? :vl-lbrack))
                (mv nil core tokstream)))
            (seq tokstream
                 (reps := (vl-parse-boolean-abbrev))
                 (return (make-vl-seqrepeat :seq core :reps reps)))))))

  (defparser vl-parse-assign-sequence-expr ()
    :short "Matches @(' '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev] ')"
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    (seq tokstream
         (:= (vl-match-token :vl-lparen))
         (seq := (vl-parse-sequence-expr))
         (items := (vl-parse-sequence-match-item-list))
         (:= (vl-match-token :vl-rparen))
         (when (vl-is-token? :vl-lbrack)
           (reps := (vl-parse-sequence-abbrev)))
         (return
          (b* ((core (if (atom items)
                         ;; No assignments so just collapse (foo) down to foo.
                         seq
                       ;; Build the internal (foo, x++) assignment
                       (make-vl-seqassign :seq seq :items items)))
               (ret  (if (not reps)
                         ;; No repetition part, so just return the core
                         core
                       (make-vl-seqrepeat :seq core :reps reps))))
            ret))))

  (defparser vl-parse-instance-sequence-expr ()
    :short "Matches @('sequence_instance [sequence_abbrev]')."
    :measure (two-nats-measure (vl-tokstream-measure) 20)
    ;; sequence_instance ::= ps_or_hierarchical_sequence_identifier [ '(' [sequence_list_of_arguments] ')' ]
    (seq tokstream
         (name := (vl-parse-scoped-or-hierarchical-identifier))
         (when (vl-is-token? :vl-lparen)
           (:= (vl-match))
           (args := (vl-parse-sequence-list-of-arguments))
           (:= (vl-match-token :vl-rparen)))
         (when (vl-is-token? :vl-lbrack)
           (reps := (vl-parse-sequence-abbrev)))
         (return
          (b* ((core (make-vl-seqinst :ref name :args args))
               (ret  (if (not reps)
                         core
                       (make-vl-seqrepeat :seq core :reps reps))))
            ret))))


  (defparser vl-parse-sequence-actual-arg ((name stringp))
    :measure (two-nats-measure (vl-tokstream-measure) 150)
    :short "Match a single @('sequence_actual_arg')."
    :long "<p>This is used in the special case where we know that we want to
match exactly one @('sequence_actual_arg') followed by a right paren, e.g., we
are matching @('bar') in @('.foo(bar)') or similar.</p>

<p>The basic grammar rule here is:</p>

@({
    sequence_actual_arg ::= event_expression
                          | sequence_expr
})

<p>This is ambiguous in a couple of ways.  First, any ordinary expression is
simultaneously an @('event_expression') and also a @('sequence_expr'), e.g.,
via @('expression_or_dist').  So if we just see an identifier like @('foo') or
some other expression, it may be an event expression or a sequence expression,
and it isn't clear what we should prefer.  Furthermore, the keyword @('or')
makes it so that an event expression such as @('a or b') might instead be
interpreted as a sequence expression.</p>

<p>In the special case where we know that we're expecting a single
@('sequence_actual_arg') followed by a right-paren, e.g., @('.foo(bar)'), it
seems fairly reasonable to just use backtracking to try both possibilities and
see which (if any) leads us to the right place.  If both succeed, e.g., perhaps
@('bar') is an ordinary expression, we arbitrarily choose to prefer a
@('sequence_expr') over an @('event_expression').</p>"
    (b* ((backup (vl-tokstream-save))
         ((mv err seqexpr tokstream) (vl-parse-sequence-expr))
         ((when (and (not err)
                     (vl-is-token? :vl-rparen)))
          ;; Parsing sequence_expr seems to work, so call it good.
          (mv err
              (make-vl-seqactual-sequence :name name
                                          :seqexpr seqexpr)
              tokstream))
         (tokstream (vl-tokstream-restore backup))

         ((mv err evatoms tokstream) (vl-parse-event-expression))
         ((when (and (not err)
                     (vl-is-token? :vl-rparen)))
          ;; Parsing event_expression  seems to work, so call it good.
          (mv err
              (make-vl-seqactual-event :name name
                                       :evatoms evatoms)
              tokstream)))
      (vl-parse-error
       "Expected lone event_expression or sequence_expr followed by ')'.")))

  (defparser vl-parse-1+-named-sequence-list-of-arguments ()
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :short "Match the named list portion of @('sequence_list_of_arguments')."
    :long "<p>See @(see vl-parse-sequence-list-of-arguments).  Our goal here is
to parse the named arguments in the tail of a @('sequence_list_of_arguments').
That is, we want to match:</p>

@({
      '.' identifier ( [sequence_actual_arg] )
           { ',' '.' identifier ( [sequence_actual_arg] ) }
})"

    (seq tokstream
         (:= (vl-match-token :vl-dot))
         (name := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-lparen))
         (first :s= (vl-parse-sequence-actual-arg (vl-idtoken->name name)))
         (:= (vl-match-token :vl-rparen))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-named-sequence-list-of-arguments))
           (return (cons first rest)))
         (return (list first))))

  (defparser vl-parse-sequence-list-of-arguments ()
    :measure (two-nats-measure (vl-tokstream-measure) 120)
    :short "Heuristically match a @('sequence_list_of_arguments')."
    :long "<p>Our goal is to match @('sequence_list_of_arguments'), defined in
the SystemVerilog-2012 grammar as follows:</p>

@({
    sequence_list_of_arguments ::=

        [sequence_actual_arg] { ',' [sequence_actual_arg] }
                              { ',' '.' identifier '(' [sequence_actual_arg] ')' }

      | '.' identifier ( [sequence_actual_arg] )
           { ',' '.' identifier ( [sequence_actual_arg] ) }
})

<p>Here is a slightly revised, equivalent grammar:</p>

@({
     named_sequence_list_of_arguments ::=
                    '.' identifier ( [sequence_actual_arg] )
              { ',' '.' identifier ( [sequence_actual_arg] ) }

     sequence_list_of_arguments ::=
         [sequence_actual_arg] { ',' [sequence_actual_arg] } [named_sequence_list_of_arguments]
       | named_sequence_list_of_arguments
})

<p>Note that we can match @('named_sequence_list_of_arguments') with @(see
vl-parse-1+-named-sequence-list-of-arguments) and we know that such a sequence
always starts with a dot.  Note also that by inspecting the grammar, we can see
that @('sequence_list_of_arguments') always occurs within parens, so we know
that we should end on a right paren.</p>

<p>Distressingly this rule is quite ambiguous.  We describe some of the basic
@('sequence_actual_arg') ambiguities in @(see vl-parse-sequence-actual-arg).
But beyond that, here we have @('sequence_actual_arg')s being separated by
commas, which is even more ambiguous because an @('event_expression') can
itself be a comma-delimited list of expressions!</p>

<p>So how can we handle this.  One option would be to try to aggressively use
backtracking to find a match.  But even then we have to make rather arbitrary
distinctions for expressions like @('a or b')---is it an event expression or
is it a sequence expression?</p>

<p>So I think something I like better is to be a little more restrictive.
Suppose that instead of the full @('event_expression') grammar, we only support
edge expressions that have an explicit posedge or negedge, and otherwise we
require a sequence expression.  This will still allow us to match most of the
grammar and will probably lead to mostly correct interpretations.</p>

<p>Coming up with a proper solution to this would probably require a lot of
experimentation.  This language is so awful...</p>"

    (seq tokstream
         (when (vl-is-token? :vl-rparen)
           (return nil))
         (when (vl-is-token? :vl-dot)
           ;; Switch to parsing a named_sequence_of_arguments, hooray.
           (rest := (vl-parse-1+-named-sequence-list-of-arguments))
           (return rest))
         (when (vl-is-token? :vl-comma)
           ;; Blank argument I guess.
           (:= (vl-match))
           (rest := (vl-parse-sequence-list-of-arguments))
           (return (cons (make-vl-seqactual-blank) rest)))
         (return-raw
          ;; Try backtracking to match a "proper" event_expression or a
          ;; sequence expression.
          (b* ((backup (vl-tokstream-save))
               ((mv err evatoms tokstream) (vl-parse-event-expression-fragment))
               ((unless err)
                ;; This really looks like an edge expression or a compound
                ;; event expression involving more than one event, so we want
                ;; to go ahead and make an event actual for it, rather than a
                ;; sequence actual.
                (mv err
                    (list (make-vl-seqactual-event :name nil
                                                   :evatoms evatoms))
                    tokstream))

               ;; Otherwise, and probably far more common, just try to match a
               ;; sequence expression.
               (tokstream (vl-tokstream-restore backup)))
            (seq tokstream
                 (first :s= (vl-parse-sequence-expr))
                 (when (vl-is-token? :vl-comma)
                   (:= (vl-match))
                   (rest := (vl-parse-sequence-list-of-arguments)))
                 (return (cons (make-vl-seqactual-sequence :name nil
                                                           :seqexpr first)
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
 `(defthm-parse-sequence-expr-flag vl-parse-sequence-expr-when-error
    ;; Whenever there's an error, the main return value is NIL.
    ,(vl-val-when-error-claim vl-parse-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-or-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-or-sequence-expr-aux)
    ,(vl-val-when-error-claim vl-parse-and-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-and-sequence-expr-aux)
    ,(vl-val-when-error-claim vl-parse-intersect-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-intersect-sequence-expr-aux)
    ,(vl-val-when-error-claim vl-parse-within-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-within-sequence-expr-aux)
    ,(vl-val-when-error-claim vl-parse-throughout-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-delay-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-delay-sequence-expr-tail)
    ,(vl-val-when-error-claim vl-parse-repeat-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-assign-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-instance-sequence-expr)
    ,(vl-val-when-error-claim vl-parse-sequence-actual-arg :args (name))
    ,(vl-val-when-error-claim vl-parse-1+-named-sequence-list-of-arguments)
    ,(vl-val-when-error-claim vl-parse-sequence-list-of-arguments)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-sequence-expr-fn (w state)))))))

(make-event
 `(defthm-parse-sequence-expr-flag vl-parse-sequence-expr-warning
    ,(vl-warning-claim vl-parse-sequence-expr)
    ,(vl-warning-claim vl-parse-or-sequence-expr)
    ,(vl-warning-claim vl-parse-or-sequence-expr-aux)
    ,(vl-warning-claim vl-parse-and-sequence-expr)
    ,(vl-warning-claim vl-parse-and-sequence-expr-aux)
    ,(vl-warning-claim vl-parse-intersect-sequence-expr)
    ,(vl-warning-claim vl-parse-intersect-sequence-expr-aux)
    ,(vl-warning-claim vl-parse-within-sequence-expr)
    ,(vl-warning-claim vl-parse-within-sequence-expr-aux)
    ,(vl-warning-claim vl-parse-throughout-sequence-expr)
    ,(vl-warning-claim vl-parse-delay-sequence-expr)
    ,(vl-warning-claim vl-parse-delay-sequence-expr-tail)
    ,(vl-warning-claim vl-parse-repeat-sequence-expr)
    ,(vl-warning-claim vl-parse-assign-sequence-expr)
    ,(vl-warning-claim vl-parse-instance-sequence-expr)
    ,(vl-warning-claim vl-parse-sequence-actual-arg :args (name))
    ,(vl-warning-claim vl-parse-1+-named-sequence-list-of-arguments)
    ,(vl-warning-claim vl-parse-sequence-list-of-arguments)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-sequence-expr-fn (w state)))))))

(make-event
 `(defthm-parse-sequence-expr-flag vl-parse-sequence-expr-progress
    ,(vl-progress-claim vl-parse-sequence-expr)
    ,(vl-progress-claim vl-parse-or-sequence-expr)
    ,(vl-progress-claim vl-parse-or-sequence-expr-aux)
    ,(vl-progress-claim vl-parse-and-sequence-expr)
    ,(vl-progress-claim vl-parse-and-sequence-expr-aux)
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
    ,(vl-progress-claim vl-parse-repeat-sequence-expr)
    ,(vl-progress-claim vl-parse-assign-sequence-expr)
    ,(vl-progress-claim vl-parse-instance-sequence-expr)
    ,(vl-progress-claim vl-parse-sequence-actual-arg :args (name))
    ,(vl-progress-claim vl-parse-1+-named-sequence-list-of-arguments)
    ,(vl-progress-claim vl-parse-sequence-list-of-arguments :strongp nil)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-sequence-expr-fn (w state)))))))


(defun vl-seqexpr-claim-fn (name args type)
  `'(,name (implies (force (not (mv-nth 0 (,name . ,args))))
                    (,(case type
                        (:seqexpr   'vl-seqexpr-p)
                        (:mixed     'vl-mixed-sequence-oplist-p)
                        (:delaytail 'vl-delay-se-tail-p)
                        (:actual    'vl-seqactual-p)
                        (:actuals   'vl-seqactuallist-p)
                        (otherwise
                         (er hard? 'vl-seqexpr-claim-fn "Bad type ~x0~%" type)))
                     (mv-nth 1 (,name . ,args))))))

(defmacro vl-seqexpr-claim (name type &key args)
  (vl-seqexpr-claim-fn name args type))

(make-event
 `(defthm-parse-sequence-expr-flag vl-parse-sequence-expr-value
    ,(vl-seqexpr-claim vl-parse-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-or-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-or-sequence-expr-aux :mixed)
    ,(vl-seqexpr-claim vl-parse-and-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-and-sequence-expr-aux :mixed)
    ,(vl-seqexpr-claim vl-parse-intersect-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-intersect-sequence-expr-aux :mixed)
    ,(vl-seqexpr-claim vl-parse-within-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-within-sequence-expr-aux :mixed)
    ,(vl-seqexpr-claim vl-parse-throughout-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-delay-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-delay-sequence-expr-tail :delaytail)
    ,(vl-seqexpr-claim vl-parse-repeat-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-assign-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-instance-sequence-expr :seqexpr)
    ,(vl-seqexpr-claim vl-parse-sequence-actual-arg :actual :args (name))
    ,(vl-seqexpr-claim vl-parse-1+-named-sequence-list-of-arguments :actuals)
    ,(vl-seqexpr-claim vl-parse-sequence-list-of-arguments :actuals)
    :hints((and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 ',(flag::get-clique-members 'vl-parse-sequence-expr-fn (w state)))))))

(verify-guards vl-parse-sequence-expr-fn)





;; ; module_common_item ::= assertion_item | ...
;; ;
;; ; module_item ::= {attribute_instance} module_common_item | ...






;; assertion_item ::= concurrent_assertion_item
;;                  | deferred_immediate_assertion_item

;; deferred_immediate_assertion_item ::= [ block_identifier ':' ] deferred_immediate_assertion_statement

;; procedural_assertion_statement ::= concurrent_assertion_statement
;;                                  | immediate_assertion_statement
;;                                  | checker_instantiation            ;; don't support these yet


;; immediate_assertion_statement ::= simple_immediate_assertion_statement
;;                                 | deferred_immediate_assertion_statement

;; ; Simple Immediate Assertions

;; simple_immediate_assertion_statement ::= simple_immediate_assert_statement
;;                                        | simple_immediate_assume_statement
;;                                        | simple_immediate_cover_statement

;; simple_immediate_assert_statement ::= 'assert' '(' expression ')' action_block
;; simple_immediate_assume_statement ::= 'assume' '(' expression ')' action_block
;; simple_immediate_cover_statement  ::= 'cover' '(' expression ')' statement_or_null


;; ; Deferred Immediate Assertions

;; deferred_immediate_assertion_statement ::= deferred_immediate_assert_statement
;;                                          | deferred_immediate_assume_statement
;;                                          | deferred_immediate_cover_statement

;; deferred_immediate_assert_statement ::= 'assert' '#0' '(' expression ')' action_block
;;                                       | 'assert' 'final' '(' expression ')' action_block

;; deferred_immediate_assume_statement ::= 'assume' '#0' '(' expression ')' action_block
;;                                       | 'assume' 'final' '(' expression ')' action_block

;; deferred_immediate_cover_statement ::= 'cover' '#0' '(' expression ')' statement_or_null
;;                                      | 'cover' 'final' '(' expression ')' statement_or_null




;; ; Concurrent Assertions

;; concurrent_assertion_item ::= [ block_identifier ':' ] concurrent_assertion_statement
;;                             | checker_instantiation                                        ;; don't support these yet

;; concurrent_assertion_statement ::= assert_property_statement
;;                                  | assume_property_statement
;;                                  | cover_property_statement
;;                                  | cover_sequence_statement
;;                                  | restrict_property_statement



;; assert_property_statement ::= 'assert' 'property' '(' property_spec ')' action_block

;; assume_property_statement ::= 'assume' 'property' '(' property_spec ')' action_block

;; cover_property_statement ::= 'cover' 'property' '(' property_spec ')' statement_or_null

;; cover_sequence_statement ::= 'cover' 'sequence' '('
;;                                                     [clocking_event]
;;                                                     [ 'disable' 'iff' '(' expression_or_dist ')' ]
;;                                                     sequence_expr
;;                                                 ')'
;;                               statement_or_null

;; restrict_property_statement::= 'restrict' 'property' '(' property_spec ')' ';'



;; property_spec ::= [clocking_event] [ 'disable' 'iff' '(' expression_or_dist ')' ] property_expr

;; property_expr ::= sequence_expr
;;                 | 'strong' '(' sequence_expr ')'
;;                 | 'weak' '(' sequence_expr ')'
;;                 | '(' property_expr ')'
;;                 | 'not' property_expr
;;                 | property_expr 'or' property_expr
;;                 | property_expr 'and' property_expr
;;                 | sequence_expr '|->' property_expr
;;                 | sequence_expr '|=>' property_expr
;;                 | 'if' '(' expression_or_dist ')' property_expr [ 'else' property_expr ]
;;                 | 'case' '(' expression_or_dist ')' property_case_item { property_case_item } 'endcase'
;;                 | sequence_expr '#-#' property_expr
;;                 | sequence_expr '#=#' property_expr
;;                 | 'nexttime' property_expr
;;                 | 'nexttime' '[' constant _expression ']' property_expr
;;                 | 's_nexttime' property_expr
;;                 | 's_nexttime' '[' constant_expression ']' property_expr
;;                 | 'always' property_expr
;;                 | 'always' '[' cycle_delay_const_range_expression ']' property_expr
;;                 | 's_always' '[' constant_range ']' property_expr                              ;; typo in spec on this line
;;                 | 's_eventually' property_expr
;;                 | 'eventually' '[' constant_range ']' property_expr
;;                 | 's_eventually' '[' cycle_delay_const_range_expression ']' property_expr
;;                 | property_expr 'until' property_expr
;;                 | property_expr 's_until' property_expr
;;                 | property_expr 'until_with' property_expr
;;                 | property_expr 's_until_with' property_expr
;;                 | property_expr 'implies' property_expr
;;                 | property_expr 'iff' property_expr
;;                 | 'accept_on' '(' expression_or_dist ')' property_expr
;;                 | 'reject_on' '(' expression_or_dist ')' property_expr
;;                 | 'sync_accept_on' '(' expression_or_dist ')' property_expr
;;                 | 'sync_reject_on' '(' expression_or_dist ')' property_expr
;;                 | property_instance
;;                 | clocking_event property_expr

;; property_case_item ::= expression_or_dist { ',' expression_or_dist } ':' property_expr [ ';' ]
;;                      | 'default' [ ':' ] property_expr [ ';' ]

;; sequence_declaration ::= 'sequence' sequence_identifier [ '(' [sequence_port_list] ')' ] ';'
;;                             { assertion_variable_declaration }
;;                             sequence_expr [ ';' ]
;;                          'endsequence' [ ':' sequence_identifier ]
