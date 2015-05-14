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
(include-book "eventctrl")
(include-book "blockitems")
(include-book "lvalues")
(include-book "../../mlib/stmt-tools")
(local (include-book "../../util/arithmetic"))

;; Dumb accumulated persistence hacking
(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           )))

(local (in-theory (disable character-listp
                           string-append
                           string-append-lst
                           append)))



(define vl-inc-or-dec-expr ((var vl-expr-p) (op (member op '(:vl-plusplus :vl-minusminus))))
  :returns (expr vl-expr-p)
  :guard-debug t
  (make-vl-binary
   :op (if (eq op :vl-plusplus)
           :vl-binary-plus
         :vl-binary-minus)
   :left var
   :right (make-vl-literal :val
                           (make-vl-constint
                            :origwidth 32
                            :value 1
                            :origtype :vl-unsigned
                            :wasunsized t))))

(defconst *vl-assignment-operators*
  '(:vl-equalsign
    :vl-pluseq
    :vl-minuseq
    :vl-timeseq
    :vl-diveq
    :vl-remeq
    :vl-andeq
    :vl-oreq
    :vl-xoreq
    :vl-shleq
    :vl-shreq
    :vl-ashleq
    :vl-ashreq))

(define vl-assign-op-expr ((var vl-expr-p)
                           (op (member op *vl-assignment-operators*))
                           (rhs vl-expr-p))
  ;; Given an expression like a = b, returns b.
  ;; Given a %= b, returns a % b.
  :returns (expr vl-expr-p)
  :guard-debug t
  (if (eq op :vl-equalsign)
      (vl-expr-fix rhs)
    (make-vl-binary
     :op (case op
           (:vl-pluseq  :vl-binary-plus)
           (:vl-minuseq :vl-binary-minus)
           (:vl-timeseq :vl-binary-times)
           (:vl-diveq   :vl-binary-div)
           (:vl-remeq   :vl-binary-rem)
           (:vl-andeq   :vl-binary-bitand)
           (:vl-oreq    :vl-binary-bitor)
           (:vl-xoreq   :vl-binary-xor)
           (:vl-shleq   :vl-binary-shl)
           (:vl-shreq   :vl-binary-shr)
           (:vl-ashleq  :vl-binary-ashl)
           (:vl-ashreq  :vl-binary-ashr))
     :left var
     :right rhs)))


(defparser vl-parse-operator-assignment/inc/dec ()
  ;; Parses e.g "a += 1" and returns (a . (a + 1)).  Also handles a++ and ++a.
  :result (and (consp val)
                (vl-expr-p (car val))
                (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? '(:vl-plusplus :vl-minusminus))
         ;; inc_or_dec_operator case
         (op := (vl-match))
         (var := (vl-parse-lvalue))
         (return (cons var
                       (vl-inc-or-dec-expr var (vl-token->type op)))))
       (var := (vl-parse-lvalue))
       (when (vl-is-some-token? '(:vl-plusplus :vl-minusminus))
         ;; inc_or_dec_operator case
         (op := (vl-match))
         (return (cons var
                       (vl-inc-or-dec-expr var (vl-token->type op)))))
       (eq := (vl-match-some-token *vl-assignment-operators*))
       (rhs := (vl-parse-expression))
       (return (cons var
                     (vl-assign-op-expr var
                                        (vl-token->type eq)
                                        rhs)))))



; blocking_assignment ::=
;    lvalue '=' [delay_or_event_control] expression
;
; nonblocking_assignment ::=
;     lvalue '<=' [delay_or_event_control] expression

(defparser vl-parse-blocking-or-nonblocking-assignment (atts)
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
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

(defparser vl-parse-procedural-continuous-assignments (atts)
  ;; Returns a vl-assignstmt-p or a vl-deassignstmt-p
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-assign :vl-kwd-force))
          (type := (vl-match))
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
;   hierarchical_task_identifier [ '(' expression { ',' expression } ')' ] ';'

(defparser vl-parse-task-enable (atts)
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (hid := (vl-parse-hierarchical-identifier nil))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rparen)))
        (:= (vl-match-token :vl-semi))
        (return (vl-enablestmt (make-vl-scopeexpr-end :hid hid)
                               args atts))))


; system_task_enable ::=
;    system_identifier [ '(' [expression] { ',' [expression] } ')' ] ';'

(defparser vl-parse-system-task-enable (atts)
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (id := (vl-match-token :vl-sysidtoken))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match))
          (args := (vl-parse-1+-expressions-separated-by-commas))
          (:= (vl-match-token :vl-rparen)))
        (:= (vl-match-token :vl-semi))
        (return
         (make-vl-enablestmt :id (make-vl-scopeexpr-end
                                  :hid (make-vl-hidexpr-end
                                        :name (vl-sysidtoken->name id)))
                             :args args
                             :atts atts))))


; disable_statement ::=
;    'disable' hierarchical_identifier ';'

(defparser vl-parse-disable-statement (atts)
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-disable))
        (id := (vl-parse-hierarchical-identifier nil))
        (:= (vl-match-token :vl-semi))
        (return (vl-disablestmt (make-vl-scopeexpr-end :hid id)
                                atts))))


; event_trigger ::=
;   '->' hierachial_identifier { '[' expression ']' } ';'

(defparser vl-parse-event-trigger (atts)
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-arrow))
        (hid := (vl-parse-hierarchical-identifier nil))
        (bexprs := (vl-parse-0+-bracketed-expressions))
        (:= (vl-match-token :vl-semi))
        (return (vl-eventtriggerstmt
                 (make-vl-index
                  :scope (make-vl-scopeexpr-end :hid hid)
                  :part (make-vl-partselect-none)
                  :indices bexprs)
                  atts))))



; PARSING CASE STATEMENTS.
;
; In Verilog-2005, the syntax of the case statement is essentially:
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
; According to Section 9.5 (page 127) the default statement is optional but at
; most one default statement is permitted.
;
; SystemVerilog-2012 extends case statements in a couple of ways.
;
;   - All case statements can now begin with (optional) 'unique', 'priority',
;     or 'priority0' keywords.
;
;   - There are new "case matches" and "case inside" statements, i.e.,:
;
;        case/casez/casex (...) matches ... endcase
;        case (...) inside ... endcase
;
; The "case matches" and "case inside" forms have different guts, with
; case_pattern_items or case_inside_items.  So we don't yet support them.

(defparser vl-parse-unique-priority ()
  :result (vl-casecheck-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong-on-value
  (seq tokstream
        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          ;; Verilog-2005 doesn't support using "priority", "unique", or
          ;; "unique0" checks on case statements.
          (return nil))
        (unless (vl-is-some-token? '(:vl-kwd-priority :vl-kwd-unique :vl-kwd-unique0))
          (return nil))
        (check := (vl-match))
        (return (case (vl-token->type check)
                  (:vl-kwd-priority :vl-priority)
                  (:vl-kwd-unique   :vl-unique)
                  (:vl-kwd-unique0  :vl-unique0)))))

(defparser vl-parse-case-type ()
  :result (vl-casetype-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (type := (vl-match-some-token '(:vl-kwd-case :vl-kwd-casez :vl-kwd-casex)))
        (return (case (vl-token->type type)
                  (:vl-kwd-case  nil) ;; if you change this, update resultp-of-nil
                  (:vl-kwd-casez :vl-casez)
                  (:vl-kwd-casex :vl-casex)))))

; Our parser temporarily abuses the representation of vl-caselist-p and just
; use a NIL expression list to represent default statements.

(define vl-filter-parsed-caseitemlist ((x vl-caselist-p))
  ;; Given a list of case items, we walk over the list and gather up any items
  ;; with NIL expressions (i.e., any "default" cases) into one list, and any
  ;; items with non-default expressions into the other list.
  :returns (mv (default-stmts vl-stmtlist-p)
               (normal-cases  vl-caselist-p))
  :measure (vl-caselist-count x)
  (b* ((x (vl-caselist-fix x))
       ((when (atom x))
        (mv nil nil))
       ((mv default-stmts normal-cases) (vl-filter-parsed-caseitemlist (cdr x)))
       ((cons exprs1 stmt1) (car x))
       ((when exprs1)
        ;; Not a default statement
        (mv default-stmts (cons (car x) normal-cases))))
    (mv (cons stmt1 default-stmts) normal-cases))
  ///
  (defmvtypes vl-filter-parsed-caseitemlist (true-listp true-listp)))

(define vl-make-case-statement
  ;; Final work to turn the parsed things into a real case statement.
  ((check vl-casecheck-p)
   (type  vl-casetype-p)
   (expr  vl-expr-p)
   (items vl-caselist-p)
   (atts  vl-atts-p))
  ;; This either returns a STMT or NIL for failure.  The only reason it can
  ;; fail is that more than one "default" statement was provided.
  :returns (stmt? (equal (vl-stmt-p stmt?) (if stmt? t nil)))
  (b* (((mv defaults normal-cases)
        (vl-filter-parsed-caseitemlist items))
       ((when (> (len defaults) 1))
        ;; More than one default statement, fail!
        nil))
    (make-vl-casestmt :check    check
                      :casetype type
                      :test     expr
                      :caselist normal-cases
                      :default  (if defaults
                                    (car defaults)
                                  (make-vl-nullstmt))
                      :atts     atts)))

(defparser vl-parse-1+-id=expr-pairs (type varp)
  :guard (and (vl-datatype-p type)
              (booleanp varp))
  :result (vl-vardecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (id := (vl-match-token :vl-idtoken))
       (:= (vl-match-token :vl-equalsign))
       (initval := (vl-parse-expression))
       (return-raw
        (b* ((vardecl1 (make-vl-vardecl :name (vl-idtoken->name id)
                                        :type type
                                        :varp varp
                                        :initval initval
                                        :loc (vl-token->loc id)))
             (backup (vl-tokstream-save))
             ((mv erp rest tokstream)
              (seq tokstream
                   (:= (vl-match-token :vl-comma))
                   (return-raw (vl-parse-1+-id=expr-pairs type varp))))
             ((unless erp)
              (mv nil (cons vardecl1 rest) tokstream))
             (tokstream (vl-tokstream-restore backup)))
          (mv nil (list vardecl1) tokstream)))))

(defparser vl-parse-for-variable-declaration ()
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-kwd-var)
         (varp := (vl-match)))
       (type := (vl-parse-datatype))
       (return-raw (vl-parse-1+-id=expr-pairs type (if varp t nil)))))

(defparser vl-parse-1+-for-variable-declarations ()
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (decls1 := (vl-parse-for-variable-declaration))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (decls2 := (vl-parse-1+-for-variable-declarations)))
       (return (append decls1 decls2))))


(defparser vl-parse-1+-for-init-assignments ()
  :result (vl-stmtlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       ((lvalue . expr) := (vl-parse-assignment))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-for-init-assignments)))
       (return (cons (make-vl-assignstmt
                      :type :vl-blocking
                      :lvalue lvalue
                      :expr expr
                      :loc loc)
                     rest))))

(defparser vl-parse-for-initialization ()
  :result (and (consp val)
               (vl-vardecllist-p (car val))
               (vl-stmtlist-p (cdr val)))
  :fails gracefully
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-semi)
         (return '(nil . nil)))
       (return-raw
        (b* ((backup (vl-tokstream-save))
             ((mv erp1 vardecls tokstream)
              (vl-parse-1+-for-variable-declarations))
             ((unless erp1)
              (mv nil (cons vardecls nil) tokstream))
             (tokstream (vl-tokstream-restore backup))
             ((mv erp2 assigns tokstream)
              (vl-parse-1+-for-init-assignments))
             ((unless erp2)
              (mv nil (cons nil assigns) tokstream))
             (tokstream (vl-tokstream-restore backup)))
          (vl-parse-error
           "Failed to parse for loop initialization as either declarations or assignments.")))))




(defparser vl-parse-1+-for-step-assigns ()
  :result (vl-stmtlist-p val)
  :fails gracefully
  :true-listp t
  :resultp-of-nil t
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       ((lvalue . expr) := (vl-parse-operator-assignment/inc/dec))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-for-step-assigns)))
       (return (cons (make-vl-assignstmt
                      :type :vl-blocking
                      :lvalue lvalue
                      :expr expr
                      :loc loc)
                     rest))))

(defparser vl-parse-for-step ()
  :result (vl-stmtlist-p val)
  :fails gracefully
  :true-listp t
  :resultp-of-nil t
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-rparen)
         (return nil))
       (return-raw (vl-parse-1+-for-step-assigns))))


(defparser vl-parse-return-statement (atts)
  :result (vl-stmt-p val)
  :fails gracefully
  :resultp-of-nil nil
  :count strong
  :guard (vl-atts-p atts)
  :measure (two-nats-measure (vl-tokstream-measure) 0)
  (seq tokstream
       (:= (vl-match-token :vl-kwd-return))
       (when (vl-is-token? :vl-semi)
         (return (make-vl-returnstmt :atts atts)))
       (val := (vl-parse-expression))
       (return (make-vl-returnstmt :val val :atts atts))))


(local (in-theory (disable

                   (:t acl2-count)
                   (:t vl-is-some-token?)
                   (:t vl-is-token?)
                   (:t vl-tokenlist-p)
                   acl2-count-positive-when-consp
                   acl2::acl2-count-when-member
                   acl2::cancel_plus-equal-correct
                   acl2::cancel_plus-lessp-correct
                   acl2::cancel_times-equal-correct
                   acl2::consp-by-len
                   acl2::consp-under-iff-when-true-listp
                   acl2::subsetp-member
                   acl2::true-listp-when-character-listp-rewrite
                   acl2::true-listp-when-string-listp-rewrite
                   acl2::true-listp-when-symbol-listp-rewrite
                   acl2::car-when-all-equalp
                   acl2::consp-when-member-equal-of-cons-listp
                   default-<-1
                   default-<-2
                   double-containment
                   ;; first-under-iff-when-vl-exprlist-p
                   integerp-when-natp
                   member-equal-when-member-equal-of-cdr-under-iff
                   natp-when-posp
                   not
                   rationalp-implies-acl2-numberp
                   rationalp-when-integerp
                   set::sets-are-true-lists
                   vl-stmt-p-when-member-equal-of-vl-stmtlist-p
                   vl-tokenlist-p-when-subsetp-equal
                   vl-tokenlist-p-when-member-equal-of-vl-tokenlistlist-p
                   ;; new ones
                   acl2::len-when-prefixp
                   acl2::lower-bound-of-len-when-sublistp
                   ;acl2::member-of-cons
                   acl2::prefixp-when-equal-lengths
                   acl2::sublistp-when-prefixp
                   acl2::subsetp-member
                   default-+-2
                   acl2::member-equal-when-all-equalp
                   member-equal-when-member-equal-of-cdr-under-iff
                   )))




(defparsers parse-statements

; case_statement ::=
;    'case' '(' expression ')' case_item { case_item } 'endcase'
;  | 'casez' '(' expression ')' case_item { case_item } 'endcase'
;  | 'casex' '(' expression ')' case_item { case_item } 'endcase'
;
; case_item ::=
;    expression { ',' expression } ':' statement_or_null
;  | 'default' [ ':' ] statement_or_null

  :flag-local nil
 (defparser vl-parse-case-item ()
   ;; Returns a vl-caselist-p
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   :verify-guards nil
   (seq tokstream
         (when (vl-is-token? :vl-kwd-default)
           (:= (vl-match))
           (when (vl-is-token? :vl-colon)
             (:= (vl-match)))
           (stmt := (vl-parse-statement-or-null))
           (return (list (cons nil stmt))))
         (exprs :s= (vl-parse-1+-expressions-separated-by-commas))
         (:= (vl-match-token :vl-colon))
         (stmt := (vl-parse-statement-or-null))
         (return (list (cons exprs stmt)))))

 (defparser vl-parse-1+-case-items ()
   :measure (two-nats-measure (vl-tokstream-measure) 1)
   ;; Returns a vl-caselist-p
   ;; We keep reading until 'endcase' is encountered
   (seq tokstream
         (first :s= (vl-parse-case-item))
         (when (vl-is-token? :vl-kwd-endcase)
           (return first))
         (rest := (vl-parse-1+-case-items))
         (return (append first rest))))

 (defparser vl-parse-case-statement (atts)
   ;; Returns a vl-stmt-p
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
         (check := (vl-parse-unique-priority))
         (type := (vl-parse-case-type))
         (:= (vl-match-token :vl-lparen))
         (test :s= (vl-parse-expression)) ;; bozo why do we need :s= here??
         (:= (vl-match-token :vl-rparen))
         (items := (vl-parse-1+-case-items))
         (:= (vl-match-token :vl-kwd-endcase))
         (return-raw
          (let ((stmt (vl-make-case-statement check type test items atts)))
            (if (not stmt)
                (vl-parse-error "Multiple defaults cases in case statement.")
              (mv nil stmt tokstream))))))


; conditional_statement ::=
;    'if' '(' expression ')' statement_or_null
;      { 'else' 'if' '(' expression ')' statement_or_null }
;      [ 'else' statement_or_null ]
;
; This suffers from the dangling else problem.  Per 9.4, an "else" should be
; bound to the closest if which does not have an else, which is good because
; that's easy to write.

; BOZO test this extensively.  I think it's right but it seems somehow subtle.

 (defparser vl-parse-conditional-statement (atts)
   ;; Returns a vl-stmt-p
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
        (:= (vl-match-token :vl-kwd-if))
        (:= (vl-match-token :vl-lparen))
        (expr :s= (vl-parse-expression))
        (:= (vl-match-token :vl-rparen))
        (then :s= (vl-parse-statement-or-null))
        (when (vl-is-token? :vl-kwd-else)
          (:= (vl-match))
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

 (defparser vl-parse-loop-statement (atts)
   ;; Returns a vl-foreverstmt-p, vl-repeatstmt-p, vl-whilestmt-p, or vl-forstmt-p
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream

         (when (vl-is-token? :vl-kwd-forever)
           (:= (vl-match-token :vl-kwd-forever))
           (stmt :s= (vl-parse-statement))
           (return (make-vl-foreverstmt :body stmt
                                        :atts atts)))

         (when (vl-is-some-token? '(:vl-kwd-repeat :vl-kwd-while))
           (type := (vl-match))
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
         ((initdecls . initassigns) := (vl-parse-for-initialization))
         (:= (vl-match-token :vl-semi))
         (test :s= (vl-parse-expression))
         (:= (vl-match-token :vl-semi))
         (stepforms := (vl-parse-for-step))
         (:= (vl-match-token :vl-rparen))
         (body := (vl-parse-statement))
         (return (make-vl-forstmt :initdecls initdecls
                                  :initassigns initassigns
                                  :test test
                                  :stepforms stepforms
                                  :body body
                                  :atts atts))))


; par_block ::=
;
; In Verilog-2005:
;
;   'fork' [ ':' identifier { block_item_declaration } ]
;      { statement }
;   'join'
;
; SystemVerilog-2012 extends this to:
;
;   'fork' [ ':' identifier ]
;      { block_item_declaration } ]
;      { statement_or_null }
;   'join'


 (defparser vl-parse-par-block (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
         (:= (vl-match-token :vl-kwd-fork))
         (when (vl-is-token? :vl-colon)
           (:= (vl-match))
           (id := (vl-match-token :vl-idtoken)))

         (when (or id (not (equal (vl-loadconfig->edition config) :verilog-2005)))
           (items := (vl-parse-0+-block-item-declarations)))

         (stmts := (vl-parse-statements-until-join))
         (:= (vl-match-token :vl-kwd-join))
         (when (and id (not (equal (vl-loadconfig->edition config) :verilog-2005)))
           (:= (vl-parse-endblock-name (vl-idtoken->name id) "fork/join")))

         (return
          (b* (((mv vardecls paramdecls imports) (vl-sort-blockitems items)))
            (make-vl-blockstmt :sequentialp nil
                               :name (and id (vl-idtoken->name id))
                               :vardecls vardecls
                               :paramdecls paramdecls
                               :imports imports
                               :loaditems items
                               :stmts stmts
                               :atts atts)))))


; seq_block ::=
;
; In Verilog-2005:
;
;    'begin' [ ':' identifier { block_item_declaration } ]
;       { statement }
;    'end'
;
; SystemVerilog-2012 extends this to:
;
;  begin [ : block_identifier ]
;      { block_item_declaration }
;      { statement_or_null }
;  end [ : block_identifier ]

 (defparser vl-parse-seq-block (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
         (:= (vl-match-token :vl-kwd-begin))
         (when (vl-is-token? :vl-colon)
           (:= (vl-match))
           (id := (vl-match-token :vl-idtoken)))
         (when (or id (not (equal (vl-loadconfig->edition config) :verilog-2005)))
           (items := (vl-parse-0+-block-item-declarations)))
         (stmts := (vl-parse-statements-until-end))
         (:= (vl-match-token :vl-kwd-end))
         (when (and id (not (equal (vl-loadconfig->edition config) :verilog-2005)))
           (:= (vl-parse-endblock-name (vl-idtoken->name id) "begin/end")))
         (return
          (b* (((mv vardecls paramdecls imports) (vl-sort-blockitems items)))
            (make-vl-blockstmt :sequentialp t
                               :name (and id (vl-idtoken->name id))
                               :vardecls vardecls
                               :paramdecls paramdecls
                               :imports imports
                               :loaditems items
                               :stmts stmts
                               :atts atts)))))


; procedural_timing_control_statement ::=
;    procedural_timing_control statement_or_null
;
; procedural_timing_control ::=
;    delay_control
;  | event_control

 (defparser vl-parse-procedural-timing-control-statement (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
         (ctrl :s= (if (vl-is-token? :vl-atsign)
                       (vl-parse-event-control)
                     (vl-parse-delay-control)))
         (stmt := (vl-parse-statement-or-null))
         (return (make-vl-timingstmt :ctrl ctrl
                                     :body stmt
                                     :atts atts))))



; wait_statement ::=
;    'wait' '(' expression ')' statement_or_null

 (defparser vl-parse-wait-statement (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
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
;  | {attribute_instance} task_enable                                ;;; hierarchical_identifier
;  | {attribute_instance} wait_statement                             ;;; 'wait'
;
; statement_or_null ::=
;    statement
;  | {attribute_instance} ';'

 (defparser vl-parse-statement-aux (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 1)
   (if (not (consp (vl-tokstream->tokens)))
       (vl-parse-error "Unexpected EOF.")
     (case (vl-token->type (car (vl-tokstream->tokens)))
       ;; Blocking assignment handled below.
       ((:vl-kwd-case :vl-kwd-casez :vl-kwd-casex
         :vl-kwd-unique :vl-kwd-unique0 :vl-kwd-priority)
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
        (seq tokstream
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
       (:vl-kwd-return
        (seq tokstream
             (ret := (vl-parse-return-statement atts))
             (:= (vl-match-token :vl-semi))
             (return ret)))
       (t
        ;; At this point, we can have either a blocking assignment, nonblocking
        ;; assignment, or task enable.  We will backtrack.  It doesn't matter
        ;; which order we try these, because the assignment will only think it
        ;; is successful when it sees an equal sign after the lvalue, while the
        ;; enable looks for a semicolon after the identifier, so there are no
        ;; inputs for which they both believe they are successful.
        (b* ((backup (vl-tokstream-save))
             ((mv erp val tokstream)
              (seq tokstream
                   (ret := (vl-parse-blocking-or-nonblocking-assignment atts))
                   (:= (vl-match-token :vl-semi))
                   (return ret)))
             ((unless erp)
              (mv erp val tokstream))
             (tokstream (vl-tokstream-restore backup))
             ((mv erp val tokstream)
              (seq tokstream
                   (loc := (vl-current-loc))
                   ((lvalue . expr) := (vl-parse-operator-assignment/inc/dec))
                   (:= (vl-match-token :vl-semi))
                   (return (make-vl-assignstmt
                            :type :vl-blocking
                            :lvalue lvalue
                            :expr expr
                            :loc loc))))
             ((unless erp)
              (mv erp val tokstream))
             (tokstream (vl-tokstream-restore backup)))
          (vl-parse-task-enable atts))))))

 (defparser vl-parse-statement ()
   :measure (two-nats-measure (vl-tokstream-measure) 2)
   ;; Returns a vl-stmt-p.
   (seq tokstream
         (atts :w= (vl-parse-0+-attribute-instances))
         (ret := (vl-parse-statement-aux atts))
         (return ret)))

 (defparser vl-parse-statement-or-null ()
   ;; Returns a vl-stmt-p.  (This is possible because we allow nullstmt as a
   ;; valid vl-stmt-p.)
   :measure (two-nats-measure (vl-tokstream-measure) 2)
   (seq tokstream
         (atts :w= (vl-parse-0+-attribute-instances))
         (when (vl-is-token? :vl-semi)
           (:= (vl-match-token :vl-semi))
           (return (make-vl-nullstmt :atts atts)))
         (ret := (vl-parse-statement-aux atts))
         (return ret)))

 (defparser vl-parse-statements-until-join ()
   :measure (two-nats-measure (vl-tokstream-measure) 3)
   ;; Returns a list of vl-stmt-p's.
   ;; Tries to read until the keyword "join"
   (seq tokstream
         (when (vl-is-token? :vl-kwd-join)
           (return nil))
         (first :s= (vl-parse-statement))
         (rest := (vl-parse-statements-until-join))
         (return (cons first rest))))

 (defparser vl-parse-statements-until-end ()
   :measure (two-nats-measure (vl-tokstream-measure) 3)
   ;; Returns a list of vl-stmt-p's.
   ;; Tries to read until the keyword "end"
   (seq tokstream
         (when (vl-is-token? :vl-kwd-end)
           (return nil))
         (first :s= (vl-parse-statement))
         (rest := (vl-parse-statements-until-end))
         (return (cons first rest)))))


(defsection error

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-parse-statements-flag vl-parse-statement-val-when-error
        ,(vl-val-when-error-claim vl-parse-case-item)
        ,(vl-val-when-error-claim vl-parse-1+-case-items)
        ,(vl-val-when-error-claim vl-parse-case-statement
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-conditional-statement
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-loop-statement
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-par-block
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-seq-block
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-procedural-timing-control-statement
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-wait-statement
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-statement-aux
                                  :args (atts))
        ,(vl-val-when-error-claim vl-parse-statement)
        ,(vl-val-when-error-claim vl-parse-statement-or-null)
        ,(vl-val-when-error-claim vl-parse-statements-until-end)
        ,(vl-val-when-error-claim vl-parse-statements-until-join)
        :hints('(:do-not '(simplify))
               (flag::expand-calls-computed-hint
                acl2::clause
                ',(flag::get-clique-members 'vl-parse-statement-fn
                                            (w state)))
               (and stable-under-simplificationp
                    '(:do-not nil)))))))

(defsection error

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-parse-statements-flag vl-parse-statement-warning
        ,(vl-warning-claim vl-parse-case-item)
        ,(vl-warning-claim vl-parse-1+-case-items)
        ,(vl-warning-claim vl-parse-case-statement
                                  :args (atts))
        ,(vl-warning-claim vl-parse-conditional-statement
                                  :args (atts))
        ,(vl-warning-claim vl-parse-loop-statement
                                  :args (atts))
        ,(vl-warning-claim vl-parse-par-block
                                  :args (atts))
        ,(vl-warning-claim vl-parse-seq-block
                                  :args (atts))
        ,(vl-warning-claim vl-parse-procedural-timing-control-statement
                                  :args (atts))
        ,(vl-warning-claim vl-parse-wait-statement
                                  :args (atts))
        ,(vl-warning-claim vl-parse-statement-aux
                                  :args (atts))
        ,(vl-warning-claim vl-parse-statement)
        ,(vl-warning-claim vl-parse-statement-or-null)
        ,(vl-warning-claim vl-parse-statements-until-end)
        ,(vl-warning-claim vl-parse-statements-until-join)
        :hints('(:do-not '(simplify))
               (flag::expand-calls-computed-hint
                acl2::clause
                ',(flag::get-clique-members 'vl-parse-statement-fn (w state)))
               (and stable-under-simplificationp
                    '(:do-not nil)))))))



(defsection progress

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-parse-statements-flag vl-parse-statement-progress
        ,(vl-progress-claim vl-parse-case-item)
        ,(vl-progress-claim vl-parse-1+-case-items)
        ,(vl-progress-claim vl-parse-case-statement :args (atts))
        ,(vl-progress-claim vl-parse-conditional-statement :args (atts))
        ,(vl-progress-claim vl-parse-loop-statement :args (atts))
        ,(vl-progress-claim vl-parse-par-block :args (atts))
        ,(vl-progress-claim vl-parse-seq-block :args (atts))
        ,(vl-progress-claim vl-parse-procedural-timing-control-statement :args (atts))
        ,(vl-progress-claim vl-parse-wait-statement :args (atts))
        ,(vl-progress-claim vl-parse-statement-aux :args (atts))
        ,(vl-progress-claim vl-parse-statement)
        ,(vl-progress-claim vl-parse-statement-or-null)

        (vl-parse-statements-until-end
         (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-statements-until-end)))
                  (vl-tokstream-measure))
              (implies (and (not (mv-nth 0 (vl-parse-statements-until-end)))
                            (mv-nth 1 (vl-parse-statements-until-end)))
                       (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-statements-until-end)))
                          (vl-tokstream-measure))))
         :rule-classes ((:rewrite) (:linear)))

        (vl-parse-statements-until-join
         (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-statements-until-join)))
                  (vl-tokstream-measure))
              (implies (and (not (mv-nth 0 (vl-parse-statements-until-join)))
                            (mv-nth 1 (vl-parse-statements-until-join)))
                       (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-statements-until-join)))
                          (vl-tokstream-measure))))
         :rule-classes ((:rewrite) (:linear)))

        :hints((flag::expand-calls-computed-hint
                acl2::clause
                ',(flag::get-clique-members 'vl-parse-statement-fn (w state))))))))


;; (defsection tokenlist

;;   (with-output
;;     :off prove :gag-mode :goals
;;     (make-event
;;      `(defthm-parse-statements-flag vl-parse-statement-tokenlist
;;         ,(vl-tokenlist-claim vl-parse-case-item)
;;         ,(vl-tokenlist-claim vl-parse-1+-case-items)
;;         ,(vl-tokenlist-claim vl-parse-case-statement :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-conditional-statement :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-loop-statement :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-par-block :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-seq-block :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-procedural-timing-control-statement :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-wait-statement :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-statement-aux :args (atts))
;;         ,(vl-tokenlist-claim vl-parse-statement)
;;         ,(vl-tokenlist-claim vl-parse-statement-or-null)
;;         ,(vl-tokenlist-claim vl-parse-statements-until-end)
;;         ,(vl-tokenlist-claim vl-parse-statements-until-join)
;;         :hints((and acl2::stable-under-simplificationp
;;                     (flag::expand-calls-computed-hint
;;                      acl2::clause
;;                      ',(flag::get-clique-members 'vl-parse-statement-fn (w state)))))))))


;; (defsection parsestate

;;   (with-output
;;     :off prove :gag-mode :goals
;;     (make-event
;;      `(defthm-parse-statements-flag vl-parse-statement-parsestate
;;         ,(vl-parsestate-claim vl-parse-case-item)
;;         ,(vl-parsestate-claim vl-parse-1+-case-items)
;;         ,(vl-parsestate-claim vl-parse-case-statement :args (atts))
;;         ,(vl-parsestate-claim vl-parse-conditional-statement :args (atts))
;;         ,(vl-parsestate-claim vl-parse-loop-statement :args (atts))
;;         ,(vl-parsestate-claim vl-parse-par-block :args (atts))
;;         ,(vl-parsestate-claim vl-parse-seq-block :args (atts))
;;         ,(vl-parsestate-claim vl-parse-procedural-timing-control-statement :args (atts))
;;         ,(vl-parsestate-claim vl-parse-wait-statement :args (atts))
;;         ,(vl-parsestate-claim vl-parse-statement-aux :args (atts))
;;         ,(vl-parsestate-claim vl-parse-statement)
;;         ,(vl-parsestate-claim vl-parse-statement-or-null)
;;         ,(vl-parsestate-claim vl-parse-statements-until-end)
;;         ,(vl-parsestate-claim vl-parse-statements-until-join)
;;         :hints((and acl2::stable-under-simplificationp
;;                     (flag::expand-calls-computed-hint
;;                      acl2::clause
;;                      ',(flag::get-clique-members 'vl-parse-statement-fn (w state)))))))))


(defsection result

  (defun vl-stmt-claim-fn (name args extra-hyps type true-listp)
    (let* ((claim     (ACL2::substitute `(mv-nth 1 (,name . ,args)) 'val type)))
      `'(,name (implies (and (force (not (mv-nth 0 (,name . ,args))))
                             ,@extra-hyps)
                        ,(if true-listp
                             `(and ,claim
                                   (true-listp (mv-nth 1 (,name . ,args))))
                           claim)))))

  (defmacro vl-stmt-claim (name type &key args extra-hyps true-listp)
    (vl-stmt-claim-fn name args extra-hyps type true-listp))

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-parse-statements-flag vl-parse-statement-type

        ,(vl-stmt-claim vl-parse-case-item
                        (vl-caselist-p val)
                        :true-listp t)
        ,(vl-stmt-claim vl-parse-1+-case-items
                        (vl-caselist-p val)
                        :true-listp t)
        ,(vl-stmt-claim vl-parse-case-statement
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-conditional-statement
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-loop-statement
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-par-block
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-seq-block
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-procedural-timing-control-statement
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-wait-statement
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-statement-aux
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-statement
                        (vl-stmt-p val))
        ,(vl-stmt-claim vl-parse-statement-or-null
                        (vl-stmt-p val))
        ,(vl-stmt-claim vl-parse-statements-until-end
                        (vl-stmtlist-p val)
                        :true-listp t)
        ,(vl-stmt-claim vl-parse-statements-until-join
                        (vl-stmtlist-p val)
                        :true-listp t)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-statement-fn (w state)))))))))


(local (defthm vl-parse-event-control-value-under-iff
         ;; BOZO not sure why I suddenly need this
         (implies (and (not (mv-nth 0 (vl-parse-event-control))))
                  (mv-nth 1 (vl-parse-event-control)))
         :hints(("Goal"
                 :in-theory (disable vl-parse-event-control-result)
                 :use ((:instance vl-parse-event-control-result))))))

(local (defthm vl-parse-delay-control-value-under-iff
         ;; BOZO not sure why I suddenly need this
         (implies (and (not (mv-nth 0 (vl-parse-delay-control))))
                  (mv-nth 1 (vl-parse-delay-control)))
         :hints(("Goal"
                 :in-theory (disable vl-parse-delay-control-result)
                 :use ((:instance vl-parse-delay-control-result))))))

(with-output
 :off prove
 :gag-mode :goals
 (verify-guards vl-parse-statement-fn))

(defparser-top vl-parse-statement)
