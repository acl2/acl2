; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "statements")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defxdoc parse-sequence
  :parents (parser)
  :short "Functions for parsing SystemVerilog assertion sequence expressions.")

(local (xdoc::set-default-parents parse-sequence))

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
  (make-vl-atom :guts (make-vl-keyguts :type :vl-$)))

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




#||

(i-am-here)


;; ; Section 16.9.1 gives the Sequence Operators and Precedence

;; <table>
;; <tr>  <th>          Operators       </th><th>  Associativity  </th></tr>
;; <tr>  <td>  @('[* ]  [= ]  [-> ]')  </td><td>  ---            </td></tr>
;; <tr>  <td>  @('##')                 </td><td>  Left           </td></tr>
;; <tr>  <td>  @('throughout')         </td><td>  Right          </td></tr>
;; <tr>  <td>  @('within')             </td><td>  Left           </td></tr>
;; <tr>  <td>  @('intersect')          </td><td>  Left           </td></tr>
;; <tr>  <td>  @('and')                </td><td>  Left           </td></tr>
;; <tr>  <td>  @('or')                 </td><td>  Left           </td></tr>
;; </table>


;; sequence_expr ::=               cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;;                 | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;;                 | expression_or_dist [boolean_abbrev]
;;                 | sequence_instance [sequence_abbrev]
;;                 | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;;                 | sequence_expr 'and' sequence_expr
;;                 | sequence_expr 'intersect' sequence_expr
;;                 | sequence_expr 'or' sequence_expr
;;                 | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
;;                 | expression_or_dist 'throughout' sequence_expr
;;                 | sequence_expr 'within' sequence_expr
;;                 | clocking_event sequence_expr





;; ## is next highest precedence

(defenum vl-seqbinop-p
  (:vl-sequence-and
   :vl-sequence-intersect
   :vl-sequence-or
   :vl-sequence-within))

(deftypes sequences
  :parents (syntax)
  :short "Representation of SystemVerilog sequence expressions."

  (deftagsum vl-sequence

    (:vl-seqbase
     ;; sequence_expr ::= expression_or_dist [boolean_abbrev]
     :layout :tree
     :base-name vl-seqbase
     ((item       vl-exprdist-p)
      (repetition vl-repetition-p)))

    (:vl-seqbinop
     ;; sequence_expr ::= ...
     ;;                 | sequence_expr 'and'       sequence_expr
     ;;                 | sequence_expr 'intersect' sequence_expr
     ;;                 | sequence_expr 'or'        sequence_expr
     ;;                 | sequence_expr 'within'    sequence_expr
     :layout :tree
     :base-name vl-seqbinop
     ((left  vl-sequence-p)
      (right vl-sequence-p)
      (op    vl-seqbinop-p)))))


I think the only atomic sequences are:

;;                 |


;; sequence_expr ::=               cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
;;                 | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }

;;                 | sequence_instance [sequence_abbrev]
;;                 | '(' sequence_expr { ',' sequence_match_item } ')' [sequence_abbrev]
;;                 | 'first_match' '(' sequence_expr {',' sequence_match_item} ')'
;;                 | expression_or_dist 'throughout' sequence_expr

;;                 | clocking_event sequence_expr



;; So this stuff is all mutually recursive

sequence_instance ::= ps_or_hierarchical_sequence_identifier [ '(' [sequence_list_of_arguments] ')' ]

sequence_list_of_arguments ::= [sequence_actual_arg] { ',' [sequence_actual_arg] }
                                                     { ',' '.' identifier '(' [sequence_actual_arg] ')' }
                             | '.' identifier ( [sequence_actual_arg] )
                                { ',' '.' identifier ( [sequence_actual_arg] ) }

sequence_actual_arg ::= event_expression
                      | sequence_expr





sequence_match_item ::= operator_assignment
                      | inc_or_dec_expression
                      | subroutine_call



subroutine_call ::= tf_call
                  | system_tf_call
                  | method_call
                  | [ 'std::' ] randomize_call

tf_call ::= ps_or_hierarchical_tf_identifier { attribute_instance } [ '(' list_of_arguments ')' ]

   ;; Note 37: It shall be illegal to omit the parentheses in a tf_call
   ;; unless the subroutine is a task, void function, or class method.
   ;; If the subroutine is a nonvoid class function method, it shall be
   ;; illegal to omit the parentheses if the call is directly recursive.

system_tf_call ::= system_tf_identifier [ '(' list_of_arguments ')' ]

method_call ::= method_call_root '.' method_call_body

method_call_body ::= method_identifier { attribute_instance } [ ( list_of_arguments ) ]
                   | built_in_method_call






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






;; ; Clocking Events

;; clocking_event ::= '@' identifier
;;                  | '@' '(' event_expression ')'



;; ; Event Expressions -- same stuff used in statements

;; event_control ::=
;; @ hierarchical_event_identifier
;; | @ ( event_expression )
;; | @*
;; | @ (*)
;; | @ ps_or_hierarchical_sequence_identifier

;; event_expression31 ::=
;; [ edge_identifier ] expression [ iff expression ]
;; | sequence_instance [ iff expression ]
;; | event_expression or event_expression
;; | event_expression , event_expression
;; | ( event_expression )

;; Parentheses are required when an event expression that contains comma-separated event expressions is passed as an
;; actual argument using positional binding.



;; ; Sequence match items

;; sequence_match_item ::= operator_assignment
;;                       | inc_or_dec_expression
;;                       | subroutine_call

;; ;; this is also something allowed in a blocking assignment now
;; operator_assignment ::= variable_lvalue assignment_operator expression

;; assignment_operator ::=
;;   '=' | '+=' | '-=' | '*=' | '/=' | '%=' | '&=' | '|=' | '^=' | '<<=' | '>>=' | '<<<=' | '>>>='

;; inc_or_dec_expression ::= inc_or_dec_operator { attribute_instance } variable_lvalue
;;                         | variable_lvalue { attribute_instance } inc_or_dec_operator

;; inc_or_dec_operator ::= '++' | '--'

;; subroutine_call ::= tf_call
;;                   | system_tf_call
;;                   | method_call
;;                   | [ 'std::' ] randomize_call

;; randomize_call ::= 'randomize' { attribute_instance }
;;                      [ '(' [ variable_identifier_list | 'null' ] ')' ]
;;                      [ 'with' [ '(' [identifier_list] ')' ] constraint_block ]

;; ;; 38) In a randomize_call that is not a method call of an object of class type (i.e., a scope randomize), the optional
;; ;; parenthesized identifier_list after the keyword with shall be illegal, and the use of null shall be illegal.

;; ...



||#
