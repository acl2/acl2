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
(include-book "parse-eventctrl")
(include-book "parse-blockitems")
(include-book "parse-lvalues")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))

(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ;consp-when-vl-atomguts-p
                           ;tag-when-vl-ifstmt-p
                           ;tag-when-vl-seqblockstmt-p
                           )))

; blocking_assignment ::=
;    lvalue '=' [delay_or_event_control] expression
;
; nonblocking_assignment ::=
;     lvalue '<=' [delay_or_event_control] expression

(defparser vl-parse-blocking-or-nonblocking-assignment (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-assignstmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
       (loc := (vl-current-loc))
       (lvalue := (vl-parse-lvalue))
       (type := (vl-match-some-token '(:vl-equalsign :vl-lte)))
       (when (vl-is-some-token? '(:vl-pound :vl-atsign :vl-kwd-repeat))
         (delay := (vl-parse-delay-or-event-control)))
       (expr := (vl-parse-expression))
       (return (vl-assignstmt (if (eq (vl-token->type type) :vl-equalsign)
                                  :vl-blocking
                                :vl-nonblocking)
                              lvalue expr delay atts loc))))

; procedural_continuous_assignments ::=
;    'assign' assignment
;  | 'deassign' lvalue
;  | 'force' assignment
;  | 'release' lvalue
;
; The verilog grammar makes it look worse than this, but with our treatment of
; assignment and lvalue, that's all there is to it.
;
; Curiously named production, given that only one can be returned.

(defparser vl-parse-procedural-continuous-assignments (atts tokens warnings)
  ;; Returns a vl-assignstmt-p or a vl-deassignstmt-p
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-some-token? '(:vl-kwd-assign :vl-kwd-force))
          (type := (vl-match-some-token '(:vl-kwd-assign :vl-kwd-force)))
          ((lvalue . expr) := (vl-parse-assignment))
          (return (vl-assignstmt (if (eq (vl-token->type type) :vl-kwd-assign)
                                     :vl-assign
                                   :vl-force)
                                 lvalue expr nil atts
                                 (vl-token->loc type))))
        (type := (vl-match-some-token '(:vl-kwd-deassign :vl-kwd-release)))
        (lvalue := (vl-parse-lvalue))
        (return (vl-deassignstmt (if (eq (vl-token->type type) :vl-kwd-deassign)
                                     :vl-deassign
                                   :vl-release)
                                 lvalue atts))))


; task_enable ::=
;   hierarchial_task_identifier [ '(' expression { ',' expression } ')' ] ';'

(defparser vl-parse-task-enable (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-enablestmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (hid := (vl-parse-hierarchial-identifier nil tokens))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match-token :vl-lparen))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rparen)))
        (:= (vl-match-token :vl-semi))
        (return (vl-enablestmt hid args atts))))


; system_task_enable ::=
;    system_identifier [ '(' [expression] { ',' [expression] } ')' ] ';'

(defparser vl-parse-system-task-enable (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-enablestmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-sysidtoken))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match-token :vl-lparen))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rparen)))
        (:= (vl-match-token :vl-semi))
        (return
         (vl-enablestmt (make-vl-atom
                         :guts (make-vl-sysfunname
                                :name (vl-sysidtoken->name id)))
                        args atts))))


; disable_statement ::=
;    'disable' hierarchial_identifier ';'

(defparser vl-parse-disable-statement (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-disablestmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-disable))
        (id := (vl-parse-hierarchial-identifier nil tokens))
        (:= (vl-match-token :vl-semi))
        (return (vl-disablestmt id atts))))


; event_trigger ::=
;   '->' hierachial_identifier { '[' expression ']' } ';'

(defparser vl-parse-event-trigger (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-eventtriggerstmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-arrow))
        (hid := (vl-parse-hierarchial-identifier nil tokens))
        (bexprs := (vl-parse-0+-bracketed-expressions))
        (:= (vl-match-token :vl-semi))
        (return (vl-eventtriggerstmt (vl-build-bitselect-nest hid bexprs) atts))))


(local (in-theory (disable character-listp
                           string-append
                           string-append-lst
                           append)))


; PARSING CASE STATEMENTS.
;
; See parsetree.lisp for a rudimentary discussion about our handling of compound
; statements.  In this new approach, case statements are somewhat awkward to handle.
; The syntax of the case statement is essentially:
;
;    case_kwd (expr) case_item { case_item } endcase
;
; Where case_kwd is either 'case', 'casez', or 'casex', and where case_item is:
;
; case_item ::=
;    | expr { , expr } : stmt/null
;    | default [ : ] stmt/null
;
; Since we allow the null statement as an atomic statement, we can simplify
; this to:
;
;  case_item ::=
;     expr { , expr } : stmt
;   | default [ : ] stmt
;
; The only reason this is at all awkward is that in the parse tree, we just
; have one big list of expressions and one big list of statements associated
; with each statement.  (This is a really wonderful simplification that we did
; not always have.)  So, what we need to do is collect up all of the
; expressions and statements throughout this structure and linearize them
; in some fashion.
;
; A basic note is that a case item such as
;
;    expr1, expr2, expr3 : stmt1
;
; Is semantically equivalent to three case items,
;
;    expr1 : stmt1
;    expr2 : stmt2
;    expr3 : stmt3
;
; By taking this approach, we can come up with a pairing of expressions and
; statements that covers the main cases.  This only leaves any "default
; statement", and the main "test" expression (i.e., the expression following
; the "case" keyword) to be accounted for.
;
; According to Section 9.5 (page 127) the default statement is optional but
; at most one default statement is permitted.  So, our representation of
; each case statement will be:
;
;   Expressions: test_expr, caseitem_expr1, ..., caseitem_exprN
;   Statements:  [default_stmt], caseitem_stmt1, ..., caseitem_stmtN
;
; In this scheme, we can detect the presence or absence of a default statement
; by comparing the lengths of the expressions and statements.  I admit that
; this is completely gross, but I think that the simplification it provides to
; the rest of our statement handling is so well worth it that I am willing to
; defend this ugly mess.
;
; If you have understood the above, then the parsing of case statements is not
; difficult to follow.  Our parser just constructs an intermediate structure
; that more directly captures the semantics of the case statement, and we
; develop some functions to transform from this intermediate representation
; into our desired statement structure.

(defaggregate vl-parsed-caseitem
  ;; Intermediate form for an individual case item.
  ;;   - Expr is NIL if this is a default case.
  ;;   - Expr is an expression otherwise.
  (expr stmt)
  :tag :vl-parsed-caseitem
  :require ((vl-maybe-expr-p-of-vl-parsed-caseitem->expr (vl-maybe-expr-p expr))
            (vl-stmt-p-of-vl-parsed-caseitem->stmt       (vl-stmt-p stmt)))
  :parents (parser))

(deflist vl-parsed-caseitemlist-p (x)
  ;; Each case_item turns into a list of vl-parsed-caseitems.  This lets
  ;; us handle "expr1, expr2, expr3 : stmt;" by just building a list of the
  ;; for "expr1 : stmt; expr2 : stmt; expr3 : stmt;"
  (vl-parsed-caseitem-p x)
  :guard t
  :elementp-of-nil nil)

(defprojection vl-parsed-caseitemlist->exprs (x)
  (vl-parsed-caseitem->expr x)
  :guard (vl-parsed-caseitemlist-p x))

(defprojection vl-parsed-caseitemlist->stmts (x)
  (vl-parsed-caseitem->stmt x)
  :guard (vl-parsed-caseitemlist-p x)
  :result-type vl-stmtlist-p)



(defund vl-make-parsed-caseitems (stmt x)
  ;; Given a stmt and a list of expressions, this builds the caseitemlist
  ;; corresponding to "expr1, expr2, ..., exprN : stmt".
  (declare (xargs :guard (and (vl-stmt-p stmt)
                              (vl-exprlist-p x))))
  (if (consp x)
      (cons (make-vl-parsed-caseitem :stmt stmt :expr (car x))
            (vl-make-parsed-caseitems stmt (cdr x)))
    nil))

(defthm vl-parsed-caseitemlist-p-of-vl-make-parsed-caseitems
  (implies (and (force (vl-stmt-p stmt))
                (force (vl-exprlist-p x)))
           (vl-parsed-caseitemlist-p (vl-make-parsed-caseitems stmt x)))
  :hints(("Goal" :in-theory (enable vl-make-parsed-caseitems))))



(defund vl-filter-parsed-caseitemlist (x)
  "Returns (MV DEFAULTS NON-DEFAULTS)"
  ;; Given a list of case items, we walk over the list and gather up any
  ;; items with NIL expressions (i.e., any "default" cases) into one list,
  ;; and any items with non-default expressions into the other list.
  (declare (xargs :guard (vl-parsed-caseitemlist-p x)))
  (if (atom x)
      (mv nil nil)
    (mv-let (defaults non-defaults)
            (vl-filter-parsed-caseitemlist (cdr x))
            (if (vl-parsed-caseitem->expr (car x))
                (mv defaults (cons (car x) non-defaults))
              (mv (cons (car x) defaults) non-defaults)))))

(defthm true-listp-of-vl-filter-parsed-caseitemlist-0
  (true-listp (mv-nth 0 (vl-filter-parsed-caseitemlist items)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-filter-parsed-caseitemlist))))

(defthm true-listp-of-vl-filter-parsed-caseitemlist-1
  (true-listp (mv-nth 1 (vl-filter-parsed-caseitemlist items)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-filter-parsed-caseitemlist))))

(defthm vl-caseitemlist-p-of-vl-filter-parsed-caseitemlist-0
  (implies (force (vl-parsed-caseitemlist-p x))
           (vl-parsed-caseitemlist-p (mv-nth 0 (vl-filter-parsed-caseitemlist x))))
  :hints(("Goal" :in-theory (enable vl-filter-parsed-caseitemlist))))

(defthm vl-caseitemlist-p-of-vl-filter-parsed-caseitemlist-1
  (implies (force (vl-parsed-caseitemlist-p x))
           (vl-parsed-caseitemlist-p (mv-nth 1 (vl-filter-parsed-caseitemlist x))))
  :hints(("Goal" :in-theory (enable vl-filter-parsed-caseitemlist))))

(defthm vl-exprlist-p-of-vl-parsed-caseitemlist->exprs-of-vl-filter-parsed-caseitemlist-1
  (implies (force (vl-parsed-caseitemlist-p x))
           (vl-exprlist-p (vl-parsed-caseitemlist->exprs
                           (mv-nth 1 (vl-filter-parsed-caseitemlist x)))))
  :hints(("Goal" :in-theory (enable vl-filter-parsed-caseitemlist))))



; Additional statement constructors
;
; We now provide constructor functions for other kinds of statements, so we can
; take care of all the guard proofs, etc., without having to complicate the
; mutual recursion.

(defund vl-make-case-statement (type expr items atts)
  ;; This either returns a STMT or NIL for failure.  The only reason it can
  ;; fail is that more than one "default" statement was provided.
  (declare (xargs :guard (and (member type '(:vl-kwd-case :vl-kwd-casez :vl-kwd-casex))
                              (vl-parsed-caseitemlist-p items)
                              (vl-expr-p expr)
                              (vl-atts-p atts))
                  :guard-debug t))
  (b* (((mv defaults non-defaults)
        (vl-filter-parsed-caseitemlist items))
       ((when (> (len defaults) 1))
        ;; More than one default statement, fail!
        nil)
       (match-exprs (vl-parsed-caseitemlist->exprs non-defaults))
       (match-stmts (vl-parsed-caseitemlist->stmts non-defaults))
       (default     (if defaults
                        (vl-parsed-caseitem->stmt (car defaults))
                      (make-vl-nullstmt))))
      (make-vl-casestmt :casetype (case type
                                    (:vl-kwd-case  nil)
                                    (:vl-kwd-casex :vl-casex)
                                    (:vl-kwd-casez :vl-casez))
                        :test expr
                        :default default
                        :exprs match-exprs
                        :bodies match-stmts
                        :atts atts)))

(defthm vl-stmt-p-of-vl-make-case-statement
  (implies (and (force (member type '(:vl-kwd-case :vl-kwd-casez :vl-kwd-casex)))
                (force (vl-parsed-caseitemlist-p items))
                (force (vl-expr-p expr))
                (force (vl-atts-p atts)))
           (equal (vl-stmt-p (vl-make-case-statement type expr items atts))
                  (if (vl-make-case-statement type expr items atts)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-make-case-statement))))





(vl-mutual-recursion

; case_statement ::=
;    'case' '(' expression ')' case_item { case_item } 'endcase'
;  | 'casez' '(' expression ')' case_item { case_item } 'endcase'
;  | 'casex' '(' expression ')' case_item { case_item } 'endcase'
;
; case_item ::=
;    expression { ',' expression } ':' statement_or_null
;  | 'default' [ ':' ] statement_or_null

 (defparser vl-parse-case-item (tokens warnings)
   ;; Returns a vl-parsed-caseitemlist-p
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)
                   :verify-guards nil))
   (seqw tokens warnings
         (when (vl-is-token? :vl-kwd-default)
           (:= (vl-match-token :vl-kwd-default))
           (when (vl-is-token? :vl-colon)
             (:= (vl-match-token :vl-colon)))
           (stmt := (vl-parse-statement-or-null))
           (return (list (make-vl-parsed-caseitem :expr nil
                                                  :stmt stmt))))
         (exprs :s= (vl-parse-1+-expressions-separated-by-commas))
         (:= (vl-match-token :vl-colon))
         (stmt := (vl-parse-statement-or-null))
         (return (vl-make-parsed-caseitems stmt exprs))))

 (defparser vl-parse-1+-case-items (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   ;; Returns a vl-parsed-caseitemlist-p
   ;; We keep reading until 'endcase' is encountered
   (seqw tokens warnings
         (first :s= (vl-parse-case-item))
         (when (vl-is-token? :vl-kwd-endcase)
           (return first))
         (rest := (vl-parse-1+-case-items))
         (return (append first rest))))

 (defparser vl-parse-case-statement (atts tokens warnings)
   ;; Returns a vl-stmt-p
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (type := (vl-match-some-token '(:vl-kwd-case :vl-kwd-casez :vl-kwd-casex)))
         (:= (vl-match-token :vl-lparen))
         (test :s= (vl-parse-expression))
         (:= (vl-match-token :vl-rparen))
         (items := (vl-parse-1+-case-items))
         (:= (vl-match-token :vl-kwd-endcase))
         (return-raw
          (let ((stmt (vl-make-case-statement (vl-token->type type) test items atts)))
            (if (not stmt)
                (vl-parse-error "Multiple defaults cases in case statement.")
              (mv nil stmt tokens warnings))))))


; conditional_statement ::=
;    'if' '(' expression ')' statement_or_null
;      { 'else' 'if' '(' expression ')' statement_or_null }
;      [ 'else' statement_or_null ]
;
; This suffers from the dangling else problem.  Per 9.4, an "else" should be
; bound to the closest if which does not have an else, which is good because
; that's easy to write.

; BOZO test this extensively.  I think it's right but it seems somehow subtle.

 (defparser vl-parse-conditional-statement (atts tokens warnings)
   ;; Returns a vl-stmt-p
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (iftok := (vl-match-token :vl-kwd-if))
         (:= (vl-match-token :vl-lparen))
         (expr :s= (vl-parse-expression))
         (:= (vl-match-token :vl-rparen))
         (then :s= (vl-parse-statement-or-null))
         (when (vl-is-token? :vl-kwd-else)
           (:= (vl-match-token :vl-kwd-else))
           (else := (vl-parse-statement-or-null)))
         (return (make-vl-ifstmt :condition expr
                                 :truebranch then
                                 :falsebranch (or else (vl-nullstmt nil))
                                 :atts atts))))


; loop_statement ::=
;    'forever' statement
;  | 'repeat' '(' expression ')' statement
;  | 'while' '(' expression ')' statement
;  | 'for' '(' variable_assignment ';' expression ';' variable_assignment ')'
;      statement

 (defparser vl-parse-loop-statement (atts tokens warnings)
   ;; Returns a vl-foreverstmt-p, vl-repeatstmt-p, vl-whilestmt-p, or vl-forstmt-p
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings

         (when (vl-is-token? :vl-kwd-forever)
           (:= (vl-match-token :vl-kwd-forever))
           (stmt :s= (vl-parse-statement))
           (return (make-vl-foreverstmt :body stmt
                                        :atts atts)))

         (when (vl-is-some-token? '(:vl-kwd-repeat :vl-kwd-while))
           (type := (vl-match-some-token '(:vl-kwd-repeat :vl-kwd-while)))
           (:= (vl-match-token :vl-lparen))
           (expr :s= (vl-parse-expression))
           (:= (vl-match-token :vl-rparen))
           (stmt :s= (vl-parse-statement))
           (return (case (vl-token->type type)
                     (:vl-kwd-repeat (make-vl-repeatstmt :condition expr
                                                         :body stmt
                                                         :atts atts))
                     (:vl-kwd-while  (make-vl-whilestmt :condition expr
                                                        :body stmt
                                                        :atts atts)))))

         (:= (vl-match-token :vl-kwd-for))
         (:= (vl-match-token :vl-lparen))
         ((initlhs . initrhs) :s= (vl-parse-assignment))
         (:= (vl-match-token :vl-semi))
         (test :s= (vl-parse-expression))
         (:= (vl-match-token :vl-semi))
         ((nextlhs . nextrhs) :s= (vl-parse-assignment))
         (:= (vl-match-token :vl-rparen))
         (body := (vl-parse-statement))
         (return (make-vl-forstmt :initlhs initlhs
                                  :initrhs initrhs
                                  :test test
                                  :nextlhs nextlhs
                                  :nextrhs nextrhs
                                  :body body
                                  :atts atts))))


; par_block ::=
;   'fork' [ ':' identifier { block_item_declaration } ]
;      { statement }
;   'join'

 (defparser vl-parse-par-block (atts tokens warnings)
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (:= (vl-match-token :vl-kwd-fork))
         (when (vl-is-token? :vl-colon)
           (:= (vl-match-token :vl-colon))
           (id := (vl-match-token :vl-idtoken))
           (items :w= (vl-parse-0+-block-item-declarations)))
         (stmts := (vl-parse-statements-until-join))
         (:= (vl-match-token :vl-kwd-join))
         (return (make-vl-blockstmt :sequentialp nil
                                    :name (and id (vl-idtoken->name id))
                                    :decls items
                                    :stmts stmts
                                    :atts atts))))


; seq_block ::=
;    'begin' [ ':' identifier { block_item_declaration } ]
;       { statement }
;    'end'

 (defparser vl-parse-seq-block (atts tokens warnings)
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (:= (vl-match-token :vl-kwd-begin))
         (when (vl-is-token? :vl-colon)
           (:= (vl-match-token :vl-colon))
           (id := (vl-match-token :vl-idtoken))
           (items :w= (vl-parse-0+-block-item-declarations)))
         (stmts := (vl-parse-statements-until-end))
         (:= (vl-match-token :vl-kwd-end))
         (return (make-vl-blockstmt :sequentialp t
                                    :name (and id (vl-idtoken->name id))
                                    :decls items
                                    :stmts stmts
                                    :atts atts))))


; procedural_timing_control_statement ::=
;    procedural_timing_control statement_or_null
;
; procedural_timing_control ::=
;    delay_control
;  | event_control

 (defparser vl-parse-procedural-timing-control-statement (atts tokens warnings)
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (ctrl :s= (if (vl-is-token? :vl-atsign)
                       (vl-parse-event-control)
                     (vl-parse-delay-control)))
         (stmt := (vl-parse-statement-or-null))
         (return (make-vl-timingstmt :ctrl ctrl
                                     :body stmt
                                     :atts atts))))



; wait_statement ::=
;    'wait' '(' expression ')' statement_or_null

 (defparser vl-parse-wait-statement (atts tokens warnings)
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 0)))
   (seqw tokens warnings
         (:= (vl-match-token :vl-kwd-wait))
         (:= (vl-match-token :vl-lparen))
         (expr :s= (vl-parse-expression))
         (:= (vl-match-token :vl-rparen))
         (stmt := (vl-parse-statement-or-null))
         (return (make-vl-waitstmt :condition expr
                                   :body stmt
                                   :atts atts))))


; statement ::=                                                      ;;; starts with
;    {attribute_instance} blocking_assignment ';'                    ;;; variable_lvalue
;  | {attribute_instance} case_statement                             ;;; 'case', 'casez', 'casex'
;  | {attribute_instance} conditional_statement                      ;;; 'if'
;  | {attribute_instance} disable_statement                          ;;; 'disable'
;  | {attribute_instance} event_trigger                              ;;; '->'
;  | {attribute_instance} loop_statement                             ;;; 'forever', 'repeat', 'while', 'for'
;  | {attribute_instance} nonblocking_assignment ';'                 ;;; variable_lvalue
;  | {attribute_instance} par_block                                  ;;; 'fork'
;  | {attribute_instance} procedural_continuous_assignments ';'      ;;; 'assign', 'deassign', 'force', 'release'
;  | {attribute_instance} procedural_timing_control_statement        ;;; '#', '@'
;  | {attribute_instance} seq_block                                  ;;; 'begin'
;  | {attribute_instance} system_task_enable                         ;;; sysidtoken
;  | {attribute_instance} task_enable                                ;;; hierarchial_identifier
;  | {attribute_instance} wait_statement                             ;;; 'wait'
;
; statement_or_null ::=
;    statement
;  | {attribute_instance} ';'

 (defparser vl-parse-statement-aux (atts tokens warnings)
   (declare (xargs :guard (vl-atts-p atts)
                   :measure (two-nats-measure (acl2-count tokens) 1)))
   (if (not (consp tokens))
       (vl-parse-error "Unexpected EOF.")
     (case (vl-token->type (car tokens))
       ;; Blocking assignment handled below.
       ((:vl-kwd-case :vl-kwd-casez :vl-kwd-casex)
        (vl-parse-case-statement atts))
       (:vl-kwd-if
        (vl-parse-conditional-statement atts))
       (:vl-kwd-disable
        (vl-parse-disable-statement atts))
       (:vl-arrow
        (vl-parse-event-trigger atts))
       ((:vl-kwd-forever :vl-kwd-repeat :vl-kwd-while :vl-kwd-for)
        (vl-parse-loop-statement atts))
       ;; Nonblocking assignment handled below.
       (:vl-kwd-fork
        (vl-parse-par-block atts))
       ((:vl-kwd-assign :vl-kwd-deassign :vl-kwd-force :vl-kwd-release)
        (seqw tokens warnings
              (ret := (vl-parse-procedural-continuous-assignments atts))
              (:= (vl-match-token :vl-semi))
              (return ret)))
       ((:vl-pound :vl-atsign)
        (vl-parse-procedural-timing-control-statement atts))
       (:vl-kwd-begin
        (vl-parse-seq-block atts))
       (:vl-sysidtoken
        (vl-parse-system-task-enable atts))
       ;; Task enable handled below
       (:vl-kwd-wait
        (vl-parse-wait-statement atts))
       (t
        ;; At this point, we can have either a blocking assignment, nonblocking
        ;; assignment, or task enable.  We will backtrack.  It doesn't matter
        ;; which order we try these, because the assignment will only think it
        ;; is successful when it sees an equal sign after the lvalue, while the
        ;; enable looks for a semicolon after the identifier, so there are no
        ;; inputs for which they both believe they are successful.
        (mv-let (erp val explore new-warnings)
                (seqw tokens warnings
                     (ret := (vl-parse-blocking-or-nonblocking-assignment atts tokens))
                     (:= (vl-match-token :vl-semi))
                     (return ret))
                (if erp
                    (vl-parse-task-enable atts tokens warnings)
                  (mv erp val explore new-warnings)))))))

 (defparser vl-parse-statement (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 2)))
   ;; Returns a vl-stmt-p.
   (seqw tokens warnings
         (atts :w= (vl-parse-0+-attribute-instances))
         (ret := (vl-parse-statement-aux atts))
         (return ret)))

 (defparser vl-parse-statement-or-null (tokens warnings)
   ;; Returns a vl-stmt-p.  (This is possible because we allow nullstmt as a
   ;; valid vl-stmt-p.)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 2)))
   (seqw tokens warnings
         (atts :w= (vl-parse-0+-attribute-instances))
         (when (vl-is-token? :vl-semi)
           (:= (vl-match-token :vl-semi))
           (return (make-vl-nullstmt :atts atts)))
         (ret := (vl-parse-statement-aux atts))
         (return ret)))

 (defparser vl-parse-statements-until-join (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 3)))
   ;; Returns a list of vl-stmt-p's.
   ;; Tries to read until the keyword "join"
   (seqw tokens warnings
         (when (vl-is-token? :vl-kwd-join)
           (return nil))
         (first :s= (vl-parse-statement))
         (rest := (vl-parse-statements-until-join))
         (return (cons first rest))))

 (defparser vl-parse-statements-until-end (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 3)))
   ;; Returns a list of vl-stmt-p's.
   ;; Tries to read until the keyword "end"
   (seqw tokens warnings
         (when (vl-is-token? :vl-kwd-end)
           (return nil))
         (first :s= (vl-parse-statement))
         (rest := (vl-parse-statements-until-end))
         (return (cons first rest)))))

(with-output
 :off (prove event)
 :gag-mode :goals
 (flag::make-flag vl-flag-parse-statement
                  vl-parse-statement-fn))
