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
(include-book "assignments")
(include-book "properties")
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


(defxdoc parse-statements
  :parents (parser)
  :short "Functions for parsing Verilog and SystemVerilog procedural statements.")

(local (xdoc::set-default-parents parse-statements))


(define vl-inc-or-dec-expr ((var vl-expr-p)
                            (op  (member op '(:vl-plusplus :vl-minusminus))))
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
                            :origsign :vl-unsigned
                            :wasunsized t))))

(defval *vl-assignment-operators*
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
  :short "Normalized right-hand side of an assignment operator expression."
  :long "<p>Given an expression like @('a = b') we return @('b').  Given an
         expression like @('a %= b') we return @('a % b').</p>"
  :returns (expr vl-expr-p)
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
  :short "Parses, e.g., @('a += 1') and returns @('(a . (a + 1))').  Also handles @('a++') and @('++a')."
  ;; BOZO what gramamr rule does this correspond to?
  :result (and (consp val)
                (vl-expr-p (car val))
                (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? '(:vl-plusplus :vl-minusminus))
         ;; inc_or_dec_operator case
         (op := (vl-match))
         (var := (vl-parse-variable-lvalue))
         (return (cons var
                       (vl-inc-or-dec-expr var (vl-token->type op)))))
       (var := (vl-parse-variable-lvalue))
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




(defparser vl-parse-blocking-or-nonblocking-assignment (atts)
  :short "Parse a @('blocking_assignment') or @('nonblocking_assignment')."
  :long "<p>Verilog-2005 syntax:</p>

         @({
             blocking_assignment ::=
               variable_lvalue '=' [delay_or_event_control] expression

             nonblocking_assignment ::=
               variable_lvalue '<=' [delay_or_event_control] expression
         })

         <p>BOZO SystemVerilog-2012 extends @('blocking_assignment') in several
         ways which we do not yet implement.</p>"
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       (lvalue := (vl-parse-variable-lvalue))
       (type := (vl-match-some-token '(:vl-equalsign :vl-lte)))
       (when (vl-is-some-token? '(:vl-pound :vl-atsign :vl-kwd-repeat))
         (delay := (vl-parse-delay-or-event-control)))
       (rhs := (vl-parse-rhs))
       (return (make-vl-assignstmt :type (if (eq (vl-token->type type) :vl-equalsign)
                                             :vl-blocking
                                           :vl-nonblocking)
                                   :lvalue lvalue
                                   :rhs rhs
                                   :ctrl delay
                                   :atts atts
                                   :loc loc))))


(defparser vl-parse-procedural-continuous-assignments (atts)
  :short "Parse a @('procedural_continuous_assignment')."
  ;; Curiously named production, given that only one can be returned.  In
  ;; SystemVerilog-2012 it gets changed to singular; we should probably rename
  ;; it as well.
  :long "<p>For Verilog-2005:</p>

         @({
              procedural_continuous_assignments ::= 'assign' variable_assignment
                                                  | 'deassign' variable_lvalue
                                                  | 'force' variable_assignment
                                                  | 'force' net_assignment
                                                  | 'release' variable_lvalue
                                                  | 'release' net_lvalue
         })

         <p>SystemVerilog-2012 is identical.  Note that a @('net_assignment') is
         a subset of a @('variable_assignment'), and a @('net_lvalue') is a subset
         of a @('variable_lvalue'), so we just use the variable versions in each
         case.</p>"
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-assign :vl-kwd-force))
          (type := (vl-match))
          ((lvalue . expr) := (vl-parse-variable-assignment))
          (return (make-vl-assignstmt :type (if (eq (vl-token->type type) :vl-kwd-assign)
                                                :vl-assign
                                              :vl-force)
                                      :lvalue lvalue
                                      :rhs (make-vl-rhsexpr :guts expr)
                                      :ctrl nil
                                      :atts atts
                                      :loc (vl-token->loc type))))
        (type := (vl-match-some-token '(:vl-kwd-deassign :vl-kwd-release)))
        (lvalue := (vl-parse-variable-lvalue))
        (return (make-vl-deassignstmt :type (if (eq (vl-token->type type) :vl-kwd-deassign)
                                                :vl-deassign
                                              :vl-release)
                                      :lvalue lvalue
                                      :atts atts))))


(local (defthm vl-maybe-exprlist-p-when-vl-exprlist-p
         (implies (vl-exprlist-p x)
                  (vl-maybe-exprlist-p x))
         :hints(("Goal" :induct (len x)))))

(defparser vl-parse-task-enable (atts)
  :short "Parse a @('task_enable').  Verilog-2005 Only."
  :long "<p>Verilog-2005 Syntax:</p>
         @({
              task_enable ::=
                 hierarchical_task_identifier [ '(' expression { ',' expression } ')' ] ';'

              hierarchical_task_identifier ::= hierarchical_identifier
         })

         <p>In SystemVerilog-2012 this goes away and is replaced by the
         @('subroutine_call_statement') case.  Per Section 13.3, ``A call to a
         task is also referred to as a <i>task enable</i> (see Section 13.5 for
         more details on calling tasks); and Section 13.5 is about subroutine
         calls and argument passing, and describes the
         @('subroutine_call_statement'), which has a @('tf_call') production
         that is very similar to the Verilog-2005 @('task_enable').</p>"
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream

       (loc := (vl-current-loc))
       (hid := (vl-parse-hierarchical-identifier nil))
       (unless (vl-is-token? :vl-lparen)
         (:= (vl-match-token :vl-semi))
         (return (make-vl-callstmt :id (make-vl-scopeexpr-end :hid hid)
                                   :typearg nil
                                   :systemp nil
                                   :voidp nil
                                   :args nil
                                   :atts atts
                                   :loc loc)))

       (:= (vl-match)) ;; eat the (

       ;; Old code from when this was also implementing subroutine_call_statement
       ;; for SystemVerilog-2012.  We no longer use this function in SystemVerilog
       ;; mode.  We can probably just delete this comment since the Verilog-2005
       ;; rule definitely requires at least one expression.
       ;;
       ;; (when (and (vl-is-token? :vl-rparen)
       ;;            (not (eq (vl-loadconfig->edition config) :verilog-2005)))
       ;;   ;; Verilog-2005 doesn't support explicit parens with empty argument
       ;;   ;; lists, but SystemVerilog-2012 adds them and other fancy stuff.  We
       ;;   ;; won't yet support the other fancy stuff, but can at least handle
       ;;   ;; empty argument lists very easily.
       ;;   (:= (vl-match))
       ;;   (:= (vl-match-token :vl-semi))
       ;;   (return (make-vl-enablestmt :id (make-vl-scopeexpr-end :hid hid)
       ;;                               :args nil
       ;;                               :atts atts)))

       (args := (vl-parse-1+-expressions-separated-by-commas))
       (:= (vl-match-token :vl-rparen))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-callstmt :id (make-vl-scopeexpr-end :hid hid)
                                 :typearg nil
                                 :systemp nil
                                 :voidp nil
                                 :args args
                                 :atts atts
                                 :loc loc))))


(defparser vl-parse-system-task-enable (atts)
  :short "Parse a @('system_task_enable').  Verilog-2005 Only."
  :long "<p>Verilog-2005 Syntax:</p>

        @({
             system_task_enable ::=
               system_identifier [ '(' [expression] { ',' [expression] } ')' ] ';'
        })

        <p>In SystemVerilog-2012 this goes away and gets folded into a
        @('subroutine_call_statement').</p>"
  :guard (and (vl-atts-p atts)
              (vl-is-token? :vl-sysidtoken))
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       (id := (vl-match))
       (when (vl-is-token? :vl-lparen)
         (:= (vl-match))
         ;; Bugfix 2016-02-18: the first expression is also optional, so if
         ;; we see (), that's fine; don't parse any arguments.
         (unless (vl-is-token? :vl-rparen)
           (args := (vl-parse-sysfuncall-args)))
         (:= (vl-match-token :vl-rparen)))
       (:= (vl-match-token :vl-semi))
       (return
        (make-vl-callstmt :id (make-vl-scopeexpr-end
                               :hid (make-vl-hidexpr-end
                                     :name (vl-sysidtoken->name id)))
                          :voidp nil
                          :typearg nil
                          :systemp t
                          :args args
                          :atts atts
                          :loc loc))))




; SystemVerilog Subroutine Calls -----------------------------------------------------------
;
; QUOTE means literally a quote character here.  I.e.,: '
;
;   subroutine_call_statement ::= subroutine_call ';'
;                               | 'void' QUOTE '(' function_subroutine_call ')' ';'
;
;   function_subroutine_call ::= subroutine_call
;
;   subroutine_call ::= tf_call
;                     | system_tf_call
;                     | method_call
;                     | 'std::' randomize_call
;
; As usual a big mess.  Let's start with tf_call:
;
;   tf_call ::= ps_or_hierarchical_tf_identifier { attribute_instance } [ '(' list_of_arguments ')' ]
;
;   ps_or_hierarchical_tf_identifier ::= [package_scope] tf_identifier | hierarchical_tf_identifier
;   hierarchical_tf_identifier ::= hierarchical_identifier
;   tf_identifier ::= identifier
;
;
; So it looks like we can probably implement this as:
;
;     tf_call ::= scoped_hid { attribute_instance } [ '(' list_of_arguments ')' ]
;
;
; Next up, system_tf_call:
;
;   system_tf_call ::= system_tf_identifier [ '(' list_of_arguments ')' ]
;                    | system_tf_identifier [ '(' data_type [ ',' expression ] ')'
;
;   system_tf_identifier ::= $[a-zA-Z0-9_$]{[a-zA-Z0-9_$]}
;
; So that's pretty easy except for the usual data_type/expression ambiguity
; thing, but we've dealt with that in lots of places and can probably handle
; it easily enough by copying one of those.
;
;
; Next up, method_call:
;
;   method_call ::= method_call_root '.' method_call_body
;
;   method_call_root ::= primary | implicit_class_handle
;
;   method_call_body ::= method_identifier {attribute_instance} [ '(' list_of_arguments ')' ]
;                      | built_in_method_call
;
;   built_in_method_call ::= array_manipulation_call
;                          | randomize_call
;
;   array_manipulation_call ::= array_method_name {attribute_instance}
;                                 [ '(' list_of_arguments ')' ]
;                                 [ 'with' '(' expression ')' ]
;
;   array_method_name ::= method_identifier | 'unique' | 'and' | 'or' | 'xor'
;
;   randomize_call ::= 'randomize' {attribute_instance}
;                        [ '(' [variable_identifier_list | 'null' ] ')' ]
;                        [ 'with' [ '(' [ identifier_list ] ')' ] constraint_block ]
;
; So, wow, that's a pile of stuff that I don't think we want to think about
; yet.  Let's just not support any of that yet.  Similarly, the final 'std::'
; randomize_call case is more of the same, and we'll just not support it yet.
;
;
; So for now that leaves us with:
;
;   subroutine_call ::= tf_call
;                     | system_tf_call
;
;   tf_call ::= scoped_hid { attribute_instance } [ '(' list_of_arguments ')' ]
;
;   system_tf_call ::= system_tf_identifier [ '(' list_of_arguments ')' ]
;                    | system_tf_identifier [ '(' data_type [ ',' expression ] ')'
;
; We'll implement these separately.

(defparser vl-parse-tf-call ()
  :short "Parse a @('tf_call').  SystemVerilog-2012 Only."
  :long "<p>Original grammar rules:</p>

         @({
               tf_call ::= ps_or_hierarchical_tf_identifier
                              { attribute_instance }
                              [ '(' list_of_arguments ')' ]

               ps_or_hierarchical_tf_identifier ::= [package_scope] tf_identifier
                                                  | hierarchical_tf_identifier

               hierarchical_tf_identifier ::= hierarchical_identifier
               tf_identifier ::= identifier
         })

         <p>So this is just:</p>

         @({
              tf_call ::= [package_scope] identifier {attribute_instance} [ '(' list_of_arguments ')' ]
                        | hierarchical_identifier    {attribute_instance} [ '(' list_of_arguments ')' ]
         })"
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       ;; This may be slightly too permissive, but is approximately
       ;;    [package_scope] identifier | hierarchical_identifier
       (loc := (vl-current-loc))
       (id :s= (vl-parse-scoped-hid))
       (atts := (vl-parse-0+-attribute-instances))
       (unless (vl-is-token? :vl-lparen)
         (return (make-vl-callstmt :id id
                                   :typearg nil
                                   :systemp nil
                                   :voidp nil
                                   :args nil
                                   :atts atts
                                   :loc loc)))

       (:= (vl-match)) ;; eat the (
       (when (vl-is-token? :vl-rparen)
         ;; No arguments.  Fine.  Eat the )
         (:= (vl-match))
         (return (make-vl-callstmt :id id
                                   :typearg nil
                                   :systemp nil
                                   :voidp nil
                                   :args nil
                                   :atts atts
                                   :loc loc)))

       ;; BOZO we're supposed to match list_of_arguments, but it's more complex
       ;; than I want to try to support right now.  (It permits things like
       ;; blank expressions and named .foo(bar) style connections.)  So for now
       ;; just require a comma-delimited list.  We'll have to rejigger the
       ;; representation to support these in the long term.
       (args := (vl-parse-1+-expressions-separated-by-commas))
       (:= (vl-match-token :vl-rparen))
       (return (make-vl-callstmt :id id
                                 :typearg nil
                                 :systemp nil
                                 :voidp nil
                                 :args args
                                 :atts atts
                                 :loc loc)))
  ///
  (defthm vl-stmt-kind-of-vl-parse-tf-call
    (b* (((mv err stmt ?tokstream) (vl-parse-tf-call)))
      (implies (not err)
               (equal (vl-stmt-kind stmt) :vl-callstmt)))))

(defparser vl-parse-system-tf-call ()
  :short "Parse a @('system_tf_call').  SystemVerilog-2012 only."
  :long "<p>Original grammar rules:</p>

         @({
             system_tf_call ::= system_tf_identifier [ '(' list_of_arguments ')' ]
                              | system_tf_identifier [ '(' data_type [ ',' expression ] ')'

             system_tf_identifier ::= $[a-zA-Z0-9_$]{[a-zA-Z0-9_$]}
         })"
  :guard (vl-is-token? :vl-sysidtoken)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       ;; We assume (via our guard) that we've got a system identifier token
       ;; here already.
       (fn := (vl-match-token :vl-sysidtoken))
       ;; This is very much styled after vl-parse-system-function-call.  We
       ;; have the usual ambiguity between datatypes and expressions.  At parse
       ;; time we may not have enough information to disambiguate this, so we
       ;; prefer expressions and then fix it up in type-disambiguation.
       (when (vl-is-token? :vl-lparen)
         (:= (vl-match))
         ;; Bugfix 2016-02-18: add proper support for ().
         (unless (vl-is-token? :vl-rparen)
           (arg1 := (vl-parse-expression-without-failure))
           (when (not arg1)
             (typearg := (vl-parse-simple-type)))
           (when (vl-is-token? :vl-comma)
             (:= (vl-match))
             ;; The grammar suggests that we need to have real expressions here.
             ;; However, commercial tools seem to support blank arguments to
             ;; functions like $display.
             (args := (vl-parse-sysfuncall-args))))
         (:= (vl-match-token :vl-rparen)))
       (return
        (let* ((fname (vl-sysidtoken->name fn))
               (id    (make-vl-scopeexpr-end
                       :hid (make-vl-hidexpr-end :name fname))))
          (make-vl-callstmt :id id
                            :systemp t
                            :typearg typearg
                            :args (if arg1 (cons arg1 args) args)
                            :voidp nil
                            :atts  nil
                            :loc (vl-token->loc fn)))))
  ///
  (defthm vl-stmt-kind-of-vl-parse-system-tf-call
    (b* (((mv err stmt ?tokstream) (vl-parse-system-tf-call)))
      (implies (not err)
               (equal (vl-stmt-kind stmt) :vl-callstmt)))))


(defparser vl-parse-subroutine-call ()
  :short "Parse a @('subroutine_call').  SystemVerilog-2012 only."
  :long "<p>Grammar rule:</p>

         @({
              subroutine_call ::= tf_call
                                | system_tf_call
                                | method_call
                                | 'std::' randomize_call
         })

         <p>The @('method_call') and @('randomize_call') stuff is elaborate and
         we don't yet try to support it.</p>"
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (if (vl-is-token? :vl-sysidtoken)
      (vl-parse-system-tf-call)
    (vl-parse-tf-call))
  ///
  (defthm vl-stmt-kind-of-vl-parse-subroutine-call
    (b* (((mv err stmt ?tokstream) (vl-parse-subroutine-call)))
      (implies (not err)
               (equal (vl-stmt-kind stmt) :vl-callstmt)))))


(defparser vl-parse-subroutine-call-statement (atts)
  :short "Parse a @('subroutine_call_statement').  SystemVerilog-2012 only."
  :long "<p>Grammar rules.  Note that QUOTE means literally a quote character here.</p>

         @({
              subroutine_call_statement ::= subroutine_call ';'
                                          | 'void' QUOTE '(' function_subroutine_call ')' ';'

              function_subroutine_call ::= subroutine_call
         })"
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (if (vl-is-token? :vl-kwd-void)
      (seq tokstream
           (:= (vl-match))
           (:= (vl-match-token :vl-quote))
           (:= (vl-match-token :vl-lparen))
           (inner := (vl-parse-subroutine-call))
           (:= (vl-match-token :vl-rparen))
           (:= (vl-match-token :vl-semi))
           (return (b* (((vl-callstmt inner))
                        ;; Note about attributes.  A subroutine call like
                        ;; tf_call can have its own attributes inside of it.
                        ;; Meanwhile, a subroutine_call_statement is an
                        ;; ordinary statement_item, so it can have attributes
                        ;; preceding it.  I have no idea what should happen
                        ;; here, so I'll just append these attributes together.
                        (atts (append atts inner.atts)))
                     (change-vl-callstmt inner :voidp t :atts atts))))
    (seq tokstream
         (inner := (vl-parse-subroutine-call))
         (:= (vl-match-token :vl-semi))
         (return (b* (((vl-callstmt inner))
                      ;; Same thing for attributes as above.
                      (atts (append atts inner.atts)))
                   (change-vl-callstmt inner :atts atts))))))


(defparser vl-parse-disable-statement (atts)
  :short "Parse a @('disable_statement')."
  :long "<p>Verilog-2005 Syntax:</p>
         @({
             disable_statement ::= 'disable' hierarchical_identifier ';'
         })

         <p>SystemVerilog-2012 extends this to:</p>
         @({
             disable_statement ::= 'disable' hierarchical_task_identifier ';'
             disable_statement ::= 'disable' hierarchical_block_identifier ';'
             disable_statement ::= 'disable' 'fork' ';'
         })

         <p>But both of these are just @('hierarchical_identifier'), so really
         the only extension is @('fork').</p>"
  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-disable))
        (when (and (not (eq (vl-loadconfig->edition config) :verilog-2005))
                   (vl-is-token? :vl-kwd-fork))
          (return-raw (vl-parse-error "BOZO not yet implemented: disable fork ;")))
        (id := (vl-parse-hierarchical-identifier nil))
        (:= (vl-match-token :vl-semi))
        (return (vl-disablestmt (make-vl-scopeexpr-end :hid id)
                                atts))))


(defparser vl-parse-event-trigger (atts)
  :short "Parse an @('event_trigger')."
  :long "<p>Verilog-2005 Syntax:</p>
        @({
             event_trigger ::= '->' hierarchical_identifier { '[' expression ']' } ';'
        })

        <p>SystemVerilog-2012 Syntax:</p>
        @({
             event_trigger ::= '->' hierarchical_identifier ';'
                             | '->>' [delay_or_event_control] hierarchical_identifier ';'
        })

        <p>Interestingly it seems that SystemVerilog doesn't permit the
        bracketed expressions after the event trigger.  What did they mean?  I
        am not sure.  There is virtually no discussion of what these bracketed
        expressions mean in the Verilog-2005 standard...</p>"

  :guard (vl-atts-p atts)
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (if (eq (vl-loadconfig->edition config) :verilog-2005)
      (seq tokstream
           (:= (vl-match-token :vl-arrow))
           (hid := (vl-parse-hierarchical-identifier nil))
           (bexprs := (vl-parse-0+-bracketed-expressions))
           (:= (vl-match-token :vl-semi))
           (return (make-vl-eventtriggerstmt :id (make-vl-index :scope (make-vl-scopeexpr-end :hid hid)
                                                                :part (make-vl-partselect-none)
                                                                :indices bexprs)
                                             :atts atts)))
    ;; SystemVerilog-2012 Version:
    (seq tokstream
         (when (vl-is-token? :vl-arrowgt)
           (return-raw (vl-parse-error "BOZO not yet implemented: '->>' style event trigger")))
         (:= (vl-match-token :vl-arrow))
         (hid := (vl-parse-hierarchical-identifier nil))
         ;; Unlike Verilog-2005, don't parse bracketed expressions here.
         (:= (vl-match-token :vl-semi))
         (return (make-vl-eventtriggerstmt :id (make-vl-index :scope (make-vl-scopeexpr-end :hid hid)
                                                              :part (make-vl-partselect-none))
                                           :atts atts)))))



(defparser vl-parse-unique-priority ()
  :short "Parse a @('unique_priority') into a @(see vl-casecheck-p)."
  :long "<p>SystemVerilog-2012 only:</p>
         @({
              unique_priority ::= 'unique' | 'unique0' | 'priority'
         })"
  :result (vl-casecheck-p val)
  :resultp-of-nil nil
  :fails never
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

(defparser vl-parse-case-keyword ()
  :short "Parse a @('case_keyword') into a @(see vl-casetype-p)."
  :long "<p>The rule from SystemVerilog-2012 is:</p>
         @({
              case_keyword ::= 'case' | 'casez' | 'casex'
         })

         <p>This is also useful in Verilog-2005, but isn't a named rule in the
         Verilog-2005 grammar.</p>"
  :result (and (consp val)
               (vl-casetype-p (car val))
               (vl-location-p (cdr val)))
  ;; :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (type := (vl-match-some-token '(:vl-kwd-case :vl-kwd-casez :vl-kwd-casex)))
        (return (cons (case (vl-token->type type)
                        (:vl-kwd-case  nil)
                        (:vl-kwd-casez :vl-casez)
                        (:vl-kwd-casex :vl-casex))
                      (vl-token->loc type)))))

; Our parser temporarily abuses the representation of vl-caselist-p and just
; use a NIL expression list to represent default statements.

(define vl-filter-parsed-caseitemlist ((x vl-caselist-p))
  :short "Split a list of cases into default and non-default cases."
  :returns (mv (default-stmts vl-stmtlist-p
                              "All statements in @('x') whose expressions are @('NIL'),
                               i.e., all of the @('default') statements.")
               (normal-cases vl-caselist-p
                             "All of the cases that are <b>not</b> @('default')
                              statements."))
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
  :short "Final work to turn the parsed elements into a real case statement."
  ((check vl-casecheck-p)
   (type  vl-casetype-p)
   (expr  vl-expr-p)
   (items vl-caselist-p)
   (atts  vl-atts-p)
   (loc   vl-location-p)
   (casekey (or (vl-token-p casekey) (not casekey))))
  :long "<p>This either returns a statement or @('nil') for failure.  The only
         reason it can fail is that more than one @('default') statement was
         provided.</p>"
  :returns (stmt? (equal (vl-stmt-p stmt?) (if stmt? t nil)))
  (b* (((mv defaults normal-cases)
        (vl-filter-parsed-caseitemlist items))
       ((when (> (len defaults) 1))
        ;; More than one default statement, fail!
        nil)
       (casekey (cond ((not casekey) nil)
                      ((eq (vl-token->type casekey) :vl-kwd-inside) :inside)
                      ((eq (vl-token->type casekey) :vl-kwd-matches) :matches)
                      (t nil))))
    (make-vl-casestmt :check    check
                      :casetype type
                      :test     expr
                      :caselist normal-cases
                      :default  (if defaults
                                    (car defaults)
                                  (make-vl-nullstmt))
                      :atts     atts
                      :casekey casekey
                      :loc loc)))

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
       (initval := (vl-parse-rhs))
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
       ((lvalue . expr) := (vl-parse-variable-assignment))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-for-init-assignments)))
       (return (cons (make-vl-assignstmt
                      :type :vl-blocking
                      :lvalue lvalue
                      :rhs (make-vl-rhsexpr :guts expr)
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
                      :rhs (make-vl-rhsexpr :guts expr)
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
  :short "Match @('return [expression] ';')."
  :result (vl-stmt-p val)
  :fails gracefully
  :resultp-of-nil nil
  :count strong
  :guard (vl-atts-p atts)
  :measure (two-nats-measure (vl-tokstream-measure) 0)
  (seq tokstream
       (kwd := (vl-match-token :vl-kwd-return))
       (when (vl-is-token? :vl-semi)
         (:= (vl-match))
         (return (make-vl-returnstmt :atts atts
                                     :loc (vl-token->loc kwd))))
       (val := (vl-parse-expression))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-returnstmt :val val
                                   :atts atts
                                   :loc (vl-token->loc kwd)))))

(defprod vl-actionblock
  :short "Temporary structure for parsing assertion statements."
  :tag nil
  :layout :tree
  ((then vl-stmt-p)
   (else vl-stmt-p)))

(defparser vl-maybe-parse-assert-deferral ()
  :short "Parse @('#0') or @('final'), if present."
  :result (vl-assertdeferral-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (when (vl-is-token? :vl-kwd-final)
         (:= (vl-match))
         (return :vl-defer-final))
       (when (vl-is-token? :vl-pound)
         (:= (vl-match))
         (zero := (vl-match-token :vl-inttoken))
         (return-raw (if (and (eql 0 (vl-inttoken->value zero))
                              (vl-inttoken->wasunsized zero))
                         (seq tokstream
                              (return :vl-defer-0))
                       (vl-parse-error "Expected #0."))))
       (return nil)))


(define vl-maybe-inject-block-name-into-assertion ((name stringp)
                                                   (stmt vl-stmt-p))
  :short "Maybe install an outer block name like @('foo : assert ...') into the
          assertion statement."
  :long "<p>Either way we still create a @('begin/end') block.</p>"
  :returns (new-stmt vl-stmt-p)
  (vl-stmt-case stmt
    :vl-assertstmt
    (change-vl-assertstmt stmt
                          :assertion (change-vl-assertion stmt.assertion :name name))
    :vl-cassertstmt
    (change-vl-cassertstmt stmt
                           :cassertion (change-vl-cassertion stmt.cassertion :name name))
    :otherwise
    (vl-stmt-fix stmt)))


(defparser vl-parse-foreach-statement-array-part ()

; This is meant to match the ps_or_hierarchical_array_identifier that occurs
; in a foreach loop_statement, e.g.,
;
; loop_statement ::= ...
;                  | 'foreach' '(' ps_or_hierarchical_array_identifier '[' loop_variables ']' ')' statement
;
; The rules are:
;
; ps_or_hierarchical_array_identifier ::= [implicit_class_handle '.' | class_scope | package_scope]
;                                         hierarchical_array_identifier
;
; hierarchical_array_identifier ::= hierarchical_identifier

  :result (vl-scopeexpr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (scopes := (vl-parse-0+-scope-prefixes))
       (hid    := (vl-parse-hierarchical-identifier nil))
       (return (vl-tack-scopes-onto-hid scopes hid))))

(defparser vl-parse-foreach-loop-variables ()

; The loop_variables are just a comma-separated list of identifiers, except
; that oddly this is allowed to be the empty list and any elements are allowed
; to have spurious commas.
;
; loop_variables ::= [index_variable_identifier] { ',' [index_variable_identifier] }
;
; index_variable_identifier ::= identifier

  :result (vl-maybe-string-list-p val)
  :resultp-of-nil t
  :fails gracefully
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-idtoken)
         (first := (vl-match)))
       (unless (vl-is-token? :vl-comma)
         (return (list (and first (vl-idtoken->name first)))))
       (:= (vl-match))
       (rest := (vl-parse-foreach-loop-variables))
       (return (cons (and first
                          (vl-idtoken->name first))
                     rest))))

(define vl-foreach-vardecls-from-loopvars ((loc      vl-location-p)
                                           (loopvars vl-maybe-string-list-p))
  :returns (vardecls vl-vardecllist-p)
  (cond ((atom loopvars)
         nil)
        ((atom (car loopvars))
         (vl-foreach-vardecls-from-loopvars loc (cdr loopvars)))
        (t
         (cons (make-vl-vardecl :name (car loopvars)
                                :loc loc
                                :type *vl-plain-old-integer-type*)
               (vl-foreach-vardecls-from-loopvars loc (cdr loopvars))))))


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


(defparsers vl-parse-statement
  :flag-local nil
;;  :measure-debug t

  (defparser vl-parse-case-item ()
    :short "Parse a @('case_item') into a singleton @(see vl-caselist-p)."
    :long "<p>Verilog-2005 Syntax:</p>

          @({
              case_item ::= expression { ',' expression } ':' statement_or_null
                          | 'default' [ ':' ] statement_or_null
          })

          <p>SystemVerilog-2012 is the same.</p>"
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
    :short "Parse @('case_item { case_item }') into a @(see vl-caselist-p)."
    :measure (two-nats-measure (vl-tokstream-measure) 1)
    ;; We keep reading until 'endcase' is encountered.
    (seq tokstream
         (first :s= (vl-parse-case-item))
         (when (vl-is-token? :vl-kwd-endcase)
           (return first))
         (rest := (vl-parse-1+-case-items))
         (return (append first rest))))

  (defparser vl-parse-case-statement (atts)
    :short "Parse @('case_statement') into a @(see vl-stmt-p)."
    :long "<p>Verilog-2005 Syntax:</p>
          @({
              case_statement ::=
                   'case' '(' expression ')' case_item {case_item} 'endcase'
                 | 'casez' '(' expression ')' case_item {case_item} 'endcase'
                 | 'casex' '(' expression ')' case_item {case_item} 'endcase'
          })

          <p>SystemVerilog-2012 extends this kind of basic case statement with
          optional @('unique'), @('priority') and @('priority0') keywords:</p>

          @({
               case_statement ::= [unique_priority]
                                  case_keyword '(' expression ')' case_item {case_item} 'endcase'
                                | ...

               case_keyword ::= 'case' | 'casez' | 'casex'
               unique_priority ::= 'unique' | 'unique0' | 'priority'
          })

          <p>So the above is the same across Verilog-2005 and
          SystemVerilog-2012 except for the optional @('unique_priority').</p>

          <p>SystemVerilog also adds new @('case matches') and @('case inside')
          statements:</p>

          @({
               case_statement ::= ...
                                | [unique_priority] case_keyword '(' expression ')'
                                     'matches' case_pattern_item {case_pattern_item} 'endcase'
                                | [unique_priority] 'case' '(' expression ')'
                                     'inside' case_inside_item {case_inside_item} 'endcase'
          })

          <p>But BOZO we do not yet implement these.</p>"
    :guard (vl-atts-p atts)
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    (seq tokstream
         (check := (vl-parse-unique-priority))
         ((type . loc) := (vl-parse-case-keyword))
         (:= (vl-match-token :vl-lparen))
         (test :s= (vl-parse-expression)) ;; bozo why do we need :s= here??
         (:= (vl-match-token :vl-rparen))

         (casekey := (if (and (not (eq (vl-loadconfig->edition config) :verilog-2005))
                              (or (vl-is-token? :vl-kwd-inside)
                                  (vl-is-token? :vl-kwd-matches)))
                         (vl-match)
                       (mv nil nil tokstream)))

         (items := (vl-parse-1+-case-items))
         (:= (vl-match-token :vl-kwd-endcase))
         (return-raw
          ;; Per Verilog-2005, Section 9.5 (page 127) the default statement is
          ;; optional but at most one default statement is permitted.  This
          ;; same restriction is kept SystemVerilog, Section 12.5 (Page 270).
          (let ((stmt (vl-make-case-statement check type test items atts loc casekey)))
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
;  | 'do' statement_or_null 'while' '(' expression ')' ';'
;  | 'foreach' '(' ps_or_hierarchical_array_identifier '[' loop_variables ']' ')' statement

 (defparser vl-parse-loop-statement (atts)
   ;; Returns a vl-foreverstmt-p, vl-repeatstmt-p, vl-whilestmt-p, ...
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream

         (when (vl-is-token? :vl-kwd-forever)
           (:= (vl-match))
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

         (when (vl-is-token? :vl-kwd-do)
           (:= (vl-match))
           (stmt :s= (vl-parse-statement))
           (:= (vl-match-token :vl-kwd-while))
           (:= (vl-match-token :vl-lparen))
           (expr := (vl-parse-expression))
           (:= (vl-match-token :vl-rparen))
           (:= (vl-match-token :vl-semi))
           (return (make-vl-dostmt :body stmt
                                   :condition expr
                                   :atts atts)))

         (when (vl-is-token? :vl-kwd-foreach)
           (type := (vl-match))
           (:= (vl-match-token :vl-lparen))
           (array := (vl-parse-foreach-statement-array-part))
           (:= (vl-match-token :vl-lbrack))
           (loopvars := (vl-parse-foreach-loop-variables))
           (:= (vl-match-token :vl-rbrack))
           (:= (vl-match-token :vl-rparen))
           (stmt :s= (vl-parse-statement))
           (return (make-vl-foreachstmt :array    array
                                        :loopvars loopvars
                                        :vardecls (vl-foreach-vardecls-from-loopvars (vl-token->loc type)
                                                                                     loopvars)
                                        :body     stmt
                                        :atts     atts)))

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




 (defparser vl-parse-par-block (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   :short "Parse a @('par_block') into a @(see vl-blockstmt)."
   :long "<p>Verilog-2005:</p>
          @({
               par_block ::= 'fork' [ ':' identifier { block_item_declaration } ]
                                 { statement }
                              'join'
          })

          <p>SystemVerilog-2012 changes this to allow declarations even on
          unnamed forks, to allow additional kinds of join keywords, and to
          allow end-block names.</p>

          @({
               par_block ::= 'fork' [ ':' identifier ]
                                 { block_item_declaration }
                                 { statement_or_null }
                             join_keyword [ ':' identifier ]

               join_keyword ::= 'join' | 'join_any' | 'join_none'
          })"
   (seq tokstream
        (:= (vl-match-token :vl-kwd-fork))
        (when (vl-is-token? :vl-colon)
          (:= (vl-match))
          (id := (vl-match-token :vl-idtoken)))

        (when (or id
                  (not (equal (vl-loadconfig->edition config) :verilog-2005)))
          ;; SystemVerilog allows declarations even if there is no ID.
          (items := (vl-parse-0+-block-item-declarations)))

        (stmts := (vl-parse-statements-until-join))

        (join := (if (eq (vl-loadconfig->edition config) :verilog-2005)
                     (vl-match-token ':vl-kwd-join)
                   (vl-match-some-token '(:vl-kwd-join :vl-kwd-join_any :vl-kwd-join_none))))
        (when id
          ;; This automatically checks for SystemVerilog mode.
          (:= (vl-parse-endblock-name (vl-idtoken->name id) "fork/join")))
        (return
         (b* (((mv vardecls paramdecls imports typedefs) (vl-sort-blockitems items)))
           (make-vl-blockstmt :blocktype (case (vl-token->type join)
                                           (:vl-kwd-join      :vl-forkjoin)
                                           (:vl-kwd-join_any  :vl-forkjoinany)
                                           (:vl-kwd-join_none :vl-forkjoinnone)
                                           (otherwise (impossible)))
                              :name (and id (vl-idtoken->name id))
                              :vardecls vardecls
                              :paramdecls paramdecls
                              :imports imports
                              :typedefs typedefs
                              :loaditems items
                              :stmts stmts
                              :atts atts)))))

 (defparser vl-parse-seq-block (atts)
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   :short "Parse a @('seq_block') into a @(see vl-blockstmt)."
   :long "<p>Verilog-2005:</p>
          @({
               seq_block ::= 'begin' [ ':' identifier { block_item_declaration } ]
                                { statement }
                             'end'
          })

          <p>SystemVerilog-2012 extends this so that even unnamed blocks can
          have declarations, and adds end-block names.</p>

          @({
               seq_block ::= 'begin' [ ':' identifier ]
                                { block_item_declaration }
                                { statement_or_null }
                             'end' [ ':' identifier ]
          })"

   (seq tokstream
         (:= (vl-match-token :vl-kwd-begin))
         (when (vl-is-token? :vl-colon)
           (:= (vl-match))
           (id := (vl-match-token :vl-idtoken)))
         (when (or id
                   (not (equal (vl-loadconfig->edition config) :verilog-2005)))
           ;; SystemVerilog allows declarations even if there is no ID.
           (items := (vl-parse-0+-block-item-declarations)))
         (stmts := (vl-parse-statements-until-end))
         (:= (vl-match-token :vl-kwd-end))
         (when id
           ;; This automatically checks for SystemVerilog mode.
           (:= (vl-parse-endblock-name (vl-idtoken->name id) "begin/end")))
         (return
          (b* (((mv vardecls paramdecls imports typedefs) (vl-sort-blockitems items)))
            (make-vl-blockstmt :blocktype :vl-beginend
                               :name (and id (vl-idtoken->name id))
                               :vardecls vardecls
                               :paramdecls paramdecls
                               :imports imports
                               :typedefs typedefs
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



 (defparser vl-parse-action-block ()
   :short "Parse an @('action_block') into a @(see vl-actionblock-p)."
   :long "<p>This is just used as a temporary structure in assertion statement
          parsing.  The rule from the SystemVerilog-2012 grammar is:</p>

          @({
               action_block ::= statement_or_null
                              | [statement] else statement
          })"
   :measure (two-nats-measure (vl-tokstream-measure) 180)
   (seq tokstream
        (when (vl-is-token? :vl-kwd-else)
          (:= (vl-match))
          (else := (vl-parse-statement))
          (return (make-vl-actionblock :then (make-vl-nullstmt)
                                       :else else)))
        (then :s= (vl-parse-statement-or-null))
        (when (vl-is-token? :vl-kwd-else)
          (:= (vl-match))
          (else := (vl-parse-statement)))
        (return (make-vl-actionblock :then then
                                     :else (or else (make-vl-nullstmt))))))

 (defparser vl-parse-expect-property-statement ()
   :short "Parse a @('expect_property_statement'), returning a @(see vl-cassertion)."
   :long "<p>SystemVerilog-2012 grammar:</p>

          @({
              expect_property_statement ::= 'expect' '(' property_spec ')' action_block
          })"
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
        (kwd := (vl-match-token :vl-kwd-expect))
        (:= (vl-match-token :vl-lparen))
        (spec := (vl-parse-property-spec))
        (:= (vl-match-token :vl-rparen))
        (act := (vl-parse-action-block))
        (return (make-vl-cassertion :type :vl-expect
                                    :sequencep nil
                                    :condition spec
                                    :success (vl-actionblock->then act)
                                    :failure (vl-actionblock->else act)
                                    :loc (vl-token->loc kwd)))))

 (defparser vl-parse-concurrent-assertion-statement ()
   :short "Parse a @('concurrent_assertion_statement'), returning a @(see vl-cassertion)."
   :long "<p>Almost the SystemVerilog-2012 grammar:</p>

          @({
              concurrent_assertion_statement ::= assert_property_statement
                                               | assume_property_statement
                                               | cover_property_statement
                                               | cover_sequence_statement
                                               | restrict_property_statement

              assert_property_statement ::= 'assert' 'property' '(' property_spec ')' action_block
              assume_property_statement ::= 'assume' 'property' '(' property_spec ')' action_block
              cover_property_statement ::= 'cover' 'property' '(' property_spec ')' statement_or_null
              cover_sequence_statement ::= 'cover' 'sequence' '(' property_spec ')' statement_or_null
              restrict_property_statement::= 'restrict' 'property' '(' property_spec ')' ';'
         })

         <p>The real grammar doesn't use a @('property_spec') in the case of
         @('cover sequence'), but the only difference is that it requires a
         @('sequence_expr') instead of a @('property_expr'), which we don't
         distinguish between at parse time.  So, the above is what we
         implement.</p>"
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
        ;; assert_property_statement ::= 'assert' 'property' '(' property_spec ')' action_block
        ;; assume_property_statement ::= 'assume' 'property' '(' property_spec ')' action_block
        (when (vl-is-some-token? '(:vl-kwd-assert :vl-kwd-assume))
          (kwd := (vl-match))
          (:= (vl-match-token :vl-kwd-property))
          (:= (vl-match-token :vl-lparen))
          (spec := (vl-parse-property-spec))
          (:= (vl-match-token :vl-rparen))
          (act := (vl-parse-action-block))
          (return (make-vl-cassertion :type (case (vl-token->type kwd)
                                              (:vl-kwd-assert :vl-assert)
                                              (:vl-kwd-assume :vl-assume)
                                              (otherwise (impossible)))
                                       :sequencep nil
                                       :condition spec
                                       :success (vl-actionblock->then act)
                                       :failure (vl-actionblock->else act)
                                       :loc (vl-token->loc kwd))))
        ;; restrict_property_statement::= 'restrict' 'property' '(' property_spec ')' ';'
        (when (vl-is-token? :vl-kwd-restrict)
          (kwd := (vl-match))
          (:= (vl-match-token :vl-kwd-property))
          (:= (vl-match-token :vl-lparen))
          (spec := (vl-parse-property-spec))
          (:= (vl-match-token :vl-rparen))
          (:= (vl-match-token :vl-semi))
          (return (make-vl-cassertion :type :vl-restrict
                                      :sequencep nil
                                      :condition spec
                                      :success (make-vl-nullstmt)
                                      :failure (make-vl-nullstmt)
                                      :loc (vl-token->loc kwd))))
        ;; cover_property_statement ::= 'cover' 'property' '(' property_spec ')' statement_or_null
        ;; cover_sequence_statement ::= 'cover' 'sequence' '(' property_spec ')' statement_or_null
        (kwd  := (vl-match-token :vl-kwd-cover))
        (kind := (vl-match-some-token '(:vl-kwd-property :vl-kwd-sequence)))
        (:= (vl-match-token :vl-lparen))
        (spec := (vl-parse-property-spec))
        (:= (vl-match-token :vl-rparen))
        (then := (vl-parse-statement-or-null))
        (return (make-vl-cassertion :type :vl-cover
                                    :sequencep (eq (vl-token->type kind) :vl-kwd-sequence)
                                    :condition spec
                                    :success then
                                    :failure (make-vl-nullstmt)
                                    :loc (vl-token->loc kwd)))))

 (defparser vl-parse-immediate-assertion-statement ()
   :short "Parse an @('immediate_assertion_statement'), returning a @(see vl-assertion)."
   :long "<p>SystemVerilog-2012 grammar:</p>

          @({
              immediate_assertion_statement ::= simple_immediate_assertion_statement
                                              | deferred_immediate_assertion_statement

              simple_immediate_assertion_statement ::= simple_immediate_assert_statement
                                                     | simple_immediate_assume_statement
                                                     | simple_immediate_cover_statement

              deferred_immediate_assertion_statement ::= deferred_immediate_assert_statement
                                                       | deferred_immediate_assume_statement
                                                       | deferred_immediate_cover_statement

              simple_immediate_assert_statement ::= 'assert' '(' expression ')' action_block
              simple_immediate_assume_statement ::= 'assume' '(' expression ')' action_block
              simple_immediate_cover_statement  ::= 'cover' '(' expression ')' statement_or_null

              deferred_immediate_assert_statement ::= 'assert' '#0' '(' expression ')' action_block
                                                    | 'assert' 'final' '(' expression ')' action_block

              deferred_immediate_assume_statement ::= 'assume' '#0' '(' expression ')' action_block
                                                    | 'assume' 'final' '(' expression ')' action_block

              deferred_immediate_cover_statement ::= 'cover' '#0' '(' expression ')' statement_or_null
                                                   | 'cover' 'final' '(' expression ')' statement_or_null
          })"
   :measure (two-nats-measure (vl-tokstream-measure) 0)
   (seq tokstream
        (type := (vl-match-some-token '(:vl-kwd-assert :vl-kwd-assume :vl-kwd-cover)))
        (deferral := (vl-maybe-parse-assert-deferral))
        (:= (vl-match-token :vl-lparen))
        (expr := (vl-parse-expression))
        (:= (vl-match-token :vl-rparen))
        ;; For assert/assume statements we need to get an action_block.
        (when (or (eq (vl-token->type type) :vl-kwd-assert)
                  (eq (vl-token->type type) :vl-kwd-assume))
          (action := (vl-parse-action-block))
          (return (make-vl-assertion :type (case (vl-token->type type)
                                             (:vl-kwd-assert :vl-assert)
                                             (:vl-kwd-assume :vl-assume)
                                             (otherwise (impossible)))
                                     :deferral deferral
                                     :condition expr
                                     :success (vl-actionblock->then action)
                                     :failure (vl-actionblock->else action)
                                     :loc (vl-token->loc type))))
        ;; ;; For cover statements we only need a statement_or_null.
        (stmt := (vl-parse-statement-or-null))
        (return (make-vl-assertion :type :vl-cover
                                   :deferral deferral
                                   :condition expr
                                   :success stmt
                                   :failure (make-vl-nullstmt)
                                   :loc (vl-token->loc type)))))

 (defparser vl-parse-procedural-assertion-statement (atts)
   :short "Parse a @('procedural_assertion_statement'), returning a @(see vl-stmt-p)."
   :long "<p>SystemVerilog-2012 grammar rules.</p>

          @({
               procedural_assertion_statement ::= concurrent_assertion_statement
                                                | immediate_assertion_statement
                                                | checker_instantiation
          })

          <p>BOZO we don't yet handle @('checker_instantiation').</p>"
   :guard (and (vl-atts-p atts)
               (vl-is-some-token? '(:vl-kwd-assert :vl-kwd-assume :vl-kwd-cover :vl-kwd-restrict)))
   :measure (two-nats-measure (vl-tokstream-measure) 10)
   (cond ((vl-is-token? :vl-kwd-restrict)
          ;; Restrict assertions only have concurrent form.  It's nicer to
          ;; check for them explicitly so that the user gets an error about
          ;; expecting a property/sequence keyword.
          (seq tokstream
               (cassertion := (vl-parse-concurrent-assertion-statement))
               (return (make-vl-cassertstmt :cassertion cassertion
                                            :atts atts))))
         ;; Otherwise:
         ;;  -- Concurrent assertions all have 'property' or 'sequence' after them
         ;;  -- Immediate assertions have '#0', 'final', or '(' after them.
         ;; So just look for property/sequence to decide what it is.
         ((vl-lookahead-is-some-token? '(:vl-kwd-property :vl-kwd-sequence)
                                       (cdr (vl-tokstream->tokens)))
          (seq tokstream
               (cassertion := (vl-parse-concurrent-assertion-statement))
               (return (make-vl-cassertstmt :cassertion cassertion
                                            :atts atts))))
         (t
          (seq tokstream
               (assertion := (vl-parse-immediate-assertion-statement))
               (return (make-vl-assertstmt :assertion assertion
                                           :atts atts))))))


 (defparser vl-parse-statement-2005-aux (atts)
   :short "Verilog-2005 Only.  Main part of statement parsing."
   :long "<p>Here's the Verilog-2005 statement rule:</p>
          @({
             statement ::=                                                      ;;; starts with
                {attribute_instance} blocking_assignment ';'                    ;;; <complicated>
              | {attribute_instance} case_statement                             ;;; 'case', 'casez', 'casex'
              | {attribute_instance} conditional_statement                      ;;; 'if'
              | {attribute_instance} disable_statement                          ;;; 'disable'
              | {attribute_instance} event_trigger                              ;;; '->'
              | {attribute_instance} loop_statement                             ;;; 'forever', 'repeat', 'while', 'for'
              | {attribute_instance} nonblocking_assignment ';'                 ;;; <complicated>
              | {attribute_instance} par_block                                  ;;; 'fork'
              | {attribute_instance} procedural_continuous_assignments ';'      ;;; 'assign', 'deassign', 'force', 'release'
              | {attribute_instance} procedural_timing_control_statement        ;;; '#', '@'
              | {attribute_instance} seq_block                                  ;;; 'begin'
              | {attribute_instance} system_task_enable                         ;;; sysidtoken
              | {attribute_instance} task_enable                                ;;; <complicated>
              | {attribute_instance} wait_statement                             ;;; 'wait'
          })

          <p>Here we assume we have already parsed the attributes and we are
          just wanting to parse the main part of the statement.</p>"
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 50)
   (if (not (consp (vl-tokstream->tokens)))
       (vl-parse-error "Unexpected EOF.")
     (case (vl-token->type (car (vl-tokstream->tokens)))
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
                   (return (make-vl-assignstmt :type :vl-blocking
                                               :lvalue lvalue
                                               :rhs (make-vl-rhsexpr :guts expr)
                                               :loc loc))))
             ((unless erp)
              (mv erp val tokstream))
             (tokstream (vl-tokstream-restore backup)))
          (vl-parse-task-enable atts))))))

 (defparser vl-parse-statement-2012-aux (atts)
   :short "SystemVerilog-2012 Only.  Main part of statement parsing."
   :long "<p>Here's the SystemVerilog-2012 statement rule:</p>

          @({
              statement ::= [ block_identifier : ] { attribute_instance } statement_item

                                                                          ;;; starts with:
              statement_item ::= blocking_assignment ;                    ;;; <complicated>
                               | nonblocking_assignment ;                 ;;; <complicated>
                               | procedural_continuous_assignment ;       ;;; 'assign', 'deassign', 'force', 'release'
                               | case_statement                           ;;; 'case', 'casez', 'casex', 'unique', 'unique0', 'priority'
                               | conditional_statement                    ;;; 'if', 'unique', 'unique0', 'priority'
                               | inc_or_dec_expression ;                  ;;; <complicated>
                               | subroutine_call_statement                ;;; <complicated>
                               | disable_statement                        ;;; 'disable'
                               | event_trigger                            ;;; '->', '->>'
                               | loop_statement                           ;;; 'forever', 'repeat', 'while', 'for', 'do', 'foreach'
                               | jump_statement                           ;;; 'return', 'break', 'continue'
                               | par_block                                ;;; 'fork', 'join', 'join_any', 'join_none'
                               | procedural_timing_control_statement      ;;; '#', '@', '##'
                               | seq_block                                ;;; 'begin'
                               | wait_statement                           ;;; 'wait', 'wait_order'
                               | procedural_assertion_statement           ;;; 'assert', 'assume', 'cover', 'restrict'
                               | clocking_drive ;                         ;;; <complicated>
                               | randsequence_statement                   ;;; 'randsequence'
                               | randcase_statement                       ;;; 'randcase'
                               | expect_property_statement                ;;; 'expect'
          })

          <p>Here we assume we have already parsed the block identifier and
          attributes, and we just want to parse the @('statement_item').  We
          will need to install the attributes, but the block identifier is
          handled separately.</p>"

   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 50)
   (if (not (consp (vl-tokstream->tokens)))
       (vl-parse-error "Unexpected EOF.")
     (case (vl-token->type (car (vl-tokstream->tokens)))
       ;; -- blocking_assignment handled below.
       ;; -- nonblocking_assignment handled below.

       ;; -- procedural_continuous_assignment
       ((:vl-kwd-assign :vl-kwd-deassign :vl-kwd-force :vl-kwd-release)
        (seq tokstream
             (ret := (vl-parse-procedural-continuous-assignments atts))
             (:= (vl-match-token :vl-semi))
             (return ret)))

       ;; -- case_statement         } tricky because of unique/unique0/priority
       ;; -- conditional_statement  }
       ((:vl-kwd-unique :vl-kwd-unique0 :vl-kwd-priority)
        ;; Can be either a case statement or an IF statement.
        (if (vl-lookahead-is-token? :vl-kwd-if (cdr (vl-tokstream->tokens)))
            (vl-parse-error "BOZO not yet implemented: unique/unique0/priority if statements.")
          (vl-parse-case-statement atts)))
       ((:vl-kwd-case :vl-kwd-casez :vl-kwd-casex)
        (vl-parse-case-statement atts))
       (:vl-kwd-if
        (vl-parse-conditional-statement atts))

       ;; -- inc_or_dec_expression handled below.
       ;; -- subroutine_call_statement handled below.

       ;; -- disable_statement
       (:vl-kwd-disable
        (vl-parse-disable-statement atts))
       ;; -- event_trigger
       ((:vl-arrow :vl-arrowgt)
        (vl-parse-event-trigger atts))

       ;; -- loop_statement
       ((:vl-kwd-forever :vl-kwd-repeat :vl-kwd-while :vl-kwd-for :vl-kwd-foreach :vl-kwd-do)
        (vl-parse-loop-statement atts))

       ;; -- jump_statement ::= 'return' [expression] ';'
       ;;                     | 'break' ';'
       ;;                     | 'continue' ';'
       (:vl-kwd-return
        (vl-parse-return-statement atts))
       (:vl-kwd-break
        (seq tokstream
             (:= (vl-match))
             (:= (vl-match-token :vl-semi))
             (return (make-vl-breakstmt :atts atts))))
       (:vl-kwd-continue
        (seq tokstream
             (:= (vl-match))
             (:= (vl-match-token :vl-semi))
             (return (make-vl-continuestmt :atts atts))))

       ;; -- par_block
       (:vl-kwd-fork
        (vl-parse-par-block atts))
       ((:vl-kwd-join :vl-kwd-join_any :vl-kwd-join_none)
        (vl-parse-error "BOZO not yet implemented: join, join_any, join_none"))

       ;; -- procedural_timing_control_statement
       ((:vl-pound :vl-atsign)
        (vl-parse-procedural-timing-control-statement atts))
       ((:vl-poundpound)
        (vl-parse-error "BOZO not yet implemnted: ## delay statements."))

       ;; -- seq_block
       (:vl-kwd-begin
        (vl-parse-seq-block atts))

       ;; -- wait_statement
       (:vl-kwd-wait
        (vl-parse-wait-statement atts))
       (:vl-kwd-wait_order
        (vl-parse-error "BOZO not yet implemented: wait_order statements."))

       ;; -- procedural_assertion_statement
       ((:vl-kwd-assert :vl-kwd-assume :vl-kwd-cover :vl-kwd-restrict)
        (vl-parse-procedural-assertion-statement atts))

       ;; -- clocking_drive handled below.

       ;; -- randsequence_statement
       (:vl-kwd-randsequence
        (vl-parse-error "BOZO not yet implemented: randsequence statements."))
       ;; -- randcase_statement
       (:vl-kwd-randcase
        (vl-parse-error "BOZO not yet implemented: randcase statements."))
       ;; -- expect_property_statement
       (:vl-kwd-expect
        (seq tokstream
             (cassertion := (vl-parse-expect-property-statement))
             (return (make-vl-cassertstmt :cassertion cassertion
                                          :atts atts))))

       ;; OK: with all that out of the way, the things we haven't handled yet
       ;; are:
       ;;  -- blocking_assignment handled below.
       ;;  -- nonblocking_assignment handled below.
       ;;  -- inc_or_dec_expression handled below.
       ;;  -- subroutine_call_statement handled below.
       ;;  -- clocking_drive handled below.

       ;; BOZO we handle some of this but surely not all of it.  Need to think
       ;; whether we're covering all of the above.

       ;; Previous comment which is now quite possibly bogus:
       ;;
       ;;  "At this point, we can have either a blocking assignment,
       ;;   nonblocking assignment, or task enable.  We will backtrack.  It
       ;;   doesn't matter which order we try these, because the assignment
       ;;   will only think it is successful when it sees an equal sign after
       ;;   the lvalue, while the enable looks for a semicolon after the
       ;;   identifier, so there are no inputs for which they both believe they
       ;;   are successful."
       (t
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
                            :rhs (make-vl-rhsexpr :guts expr)
                            :loc loc))))
             ((unless erp)
              (mv erp val tokstream))
             (tokstream (vl-tokstream-restore backup)))
          (vl-parse-subroutine-call-statement atts))))))

 (defparser vl-parse-statement-aux (atts)
   :short "Wrapper for parsing the rest of a statement after any attributes."
   :guard (vl-atts-p atts)
   :measure (two-nats-measure (vl-tokstream-measure) 51)
   (if (eq (vl-loadconfig->edition config) :verilog-2005)
       (vl-parse-statement-2005-aux atts)
     (vl-parse-statement-2012-aux atts)))

 (defparser vl-parse-statement-wrapped (null-okp)
   :short "Parse a statement or null, possibly with a label."
   :measure (two-nats-measure (vl-tokstream-measure) 80)
   :long "<p>This mainly handles SystemVerilog-2012 style statement labels; see
          Section 9.3.5 (Page 178).  We treat these labels as if they just
          create named blocks around the statement that they label.  Note that
          it is illegal to label a named block, i.e., you cannot write:</p>

          @({
               foo : begin : bar
          })

          <p>We enforce this by making sure that if we are labeling a
          @('begin/end') or @('fork/join') block, then it is not already a
          labeled block.</p>"
   (seq tokstream
        (when (and (not (eq (vl-loadconfig->edition config) :verilog-2005))
                   (vl-is-token? :vl-idtoken)
                   (vl-lookahead-is-token? :vl-colon (cdr (vl-tokstream->tokens))))
          ;; For SystemVerilog-2012, we can have [ block_identifier ':' ]
          ;; statement labels.
          (blockid := (vl-match))
          (:= (vl-match)))
        (atts :w= (vl-parse-0+-attribute-instances))
        (core :s= (if (and null-okp
                           (vl-is-token? :vl-semi))
                      (seq tokstream
                           (:= (vl-match-token :vl-semi))
                           (return (make-vl-nullstmt :atts atts)))
                    (vl-parse-statement-aux atts)))
        (unless blockid
          (return core))
        ;; Need to "install" the block ID.
        (return-raw
         (b* (((vl-idtoken blockid)))
           (vl-stmt-case core
             (:vl-blockstmt
              ;; We can directly put the name into this block.
              (if core.name
                  ;; Illegal per SystemVerilog-2012 Sec 9.3.5, page 195.
                  (vl-parse-error
                   (cat "begin/end or fork/join block has both a leading name ("
                        blockid.name ") and a trailing name (" core.name ")."))
                ;; All is well, install the name.
                (mv nil
                    (change-vl-blockstmt core :name blockid.name)
                    tokstream)))
             (:otherwise
              ;; We are just going to wrap this statement in a new, named block.
              (mv nil
                  (make-vl-blockstmt :blocktype :vl-beginend
                                     :name blockid.name
                                     ;; In case it's an assertion, it's maybe nice
                                     ;; to have the block id in the assertion itself
                                     ;; (for error reporting, for instance)
                                     :stmts (list (vl-maybe-inject-block-name-into-assertion blockid.name core))
                                     ;; Seems most sensible to associate any
                                     ;; attributes with the sub-statement core,
                                     ;; which should already be the case.
                                     :atts nil)
                  tokstream)))))))


 (defparser vl-parse-statement ()
   :short "Top level function for parsing a (non-null) @('statement') into a
           @(see vl-stmt)."
   :measure (two-nats-measure (vl-tokstream-measure) 100)
   (seq tokstream
        (stmt :s= (vl-parse-statement-wrapped nil))
        (return stmt)))

 (defparser vl-parse-statement-or-null ()
   :short "Parse a @('statement_or_null') into a @(see vl-stmt), which is
           possible since we allow a @(see vl-nullstmt) as a @(see vl-stmt)."
   :long "<p>This is the same in both Verilog-2005 and SystemVerilog-2012:</p>
          @({
               statement_or_null ::=
                   statement
                 | {attribute_instance} ';'
          })"
   :measure (two-nats-measure (vl-tokstream-measure) 150)
   (seq tokstream
        (stmt :s= (vl-parse-statement-wrapped t))
        (return stmt)))

 (defparser vl-parse-statements-until-join ()
   :measure (two-nats-measure (vl-tokstream-measure) 160)
   ;; Returns a list of vl-stmt-p's.
   ;; Tries to read until join, join_any, or join_none.
   (seq tokstream
         (when (vl-is-some-token? '(:vl-kwd-join :vl-kwd-join_any :vl-kwd-join_none))
           (return nil))
         (first :s= (vl-parse-statement-or-null))
         (rest := (vl-parse-statements-until-join))
         (return (cons first rest))))

 (defparser vl-parse-statements-until-end ()
   :measure (two-nats-measure (vl-tokstream-measure) 160)
   ;; Returns a list of vl-stmt-p's.
   ;; Tries to read until the keyword "end"
   (seq tokstream
         (when (vl-is-token? :vl-kwd-end)
           (return nil))
         (first :s= (vl-parse-statement-or-null))
         (rest := (vl-parse-statements-until-end))
         (return (cons first rest)))))


(defsection error

  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-vl-parse-statement-flag vl-parse-statement-val-when-error
        ,(vl-val-when-error-claim vl-parse-case-item)
        ,(vl-val-when-error-claim vl-parse-1+-case-items)
        ,(vl-val-when-error-claim vl-parse-case-statement :args (atts))
        ,(vl-val-when-error-claim vl-parse-conditional-statement :args (atts))
        ,(vl-val-when-error-claim vl-parse-loop-statement :args (atts))
        ,(vl-val-when-error-claim vl-parse-par-block :args (atts))
        ,(vl-val-when-error-claim vl-parse-seq-block :args (atts))
        ,(vl-val-when-error-claim vl-parse-procedural-timing-control-statement :args (atts))
        ,(vl-val-when-error-claim vl-parse-wait-statement :args (atts))
        ,(vl-val-when-error-claim vl-parse-action-block)
        ,(vl-val-when-error-claim vl-parse-expect-property-statement)
        ,(vl-val-when-error-claim vl-parse-concurrent-assertion-statement)
        ,(vl-val-when-error-claim vl-parse-immediate-assertion-statement)
        ,(vl-val-when-error-claim vl-parse-procedural-assertion-statement :args (atts))
        ,(vl-val-when-error-claim vl-parse-statement-2005-aux :args (atts))
        ,(vl-val-when-error-claim vl-parse-statement-2012-aux :args (atts))
        ,(vl-val-when-error-claim vl-parse-statement-aux :args (atts))
        ,(vl-val-when-error-claim vl-parse-statement-wrapped :args (null-okp))
        ,(vl-val-when-error-claim vl-parse-statement)
        ,(vl-val-when-error-claim vl-parse-statement-or-null)
        ,(vl-val-when-error-claim vl-parse-statements-until-end)
        ,(vl-val-when-error-claim vl-parse-statements-until-join)
        :hints((expand-only-the-flag-function-hint clause state)
               (and stable-under-simplificationp
                    '(:expand ((:free (null-okp) (vl-parse-statement-wrapped null-okp))))))))))


(defsection warning

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-vl-parse-statement-flag vl-parse-statement-warning
        ,(vl-warning-claim vl-parse-case-item)
        ,(vl-warning-claim vl-parse-1+-case-items)
        ,(vl-warning-claim vl-parse-case-statement :args (atts))
        ,(vl-warning-claim vl-parse-conditional-statement :args (atts))
        ,(vl-warning-claim vl-parse-loop-statement :args (atts))
        ,(vl-warning-claim vl-parse-par-block :args (atts))
        ,(vl-warning-claim vl-parse-seq-block :args (atts))
        ,(vl-warning-claim vl-parse-procedural-timing-control-statement :args (atts))
        ,(vl-warning-claim vl-parse-wait-statement :args (atts))
        ,(vl-warning-claim vl-parse-action-block)
        ,(vl-warning-claim vl-parse-expect-property-statement)
        ,(vl-warning-claim vl-parse-concurrent-assertion-statement)
        ,(vl-warning-claim vl-parse-immediate-assertion-statement)
        ,(vl-warning-claim vl-parse-procedural-assertion-statement :args (atts))
        ,(vl-warning-claim vl-parse-statement-2005-aux :args (atts))
        ,(vl-warning-claim vl-parse-statement-2012-aux :args (atts))
        ,(vl-warning-claim vl-parse-statement-aux :args (atts))
        ,(vl-warning-claim vl-parse-statement-wrapped :args (null-okp))
        ,(vl-warning-claim vl-parse-statement)
        ,(vl-warning-claim vl-parse-statement-or-null)
        ,(vl-warning-claim vl-parse-statements-until-end)
        ,(vl-warning-claim vl-parse-statements-until-join)
        :hints((expand-only-the-flag-function-hint clause state)
               (and stable-under-simplificationp
                    '(:expand ((:free (null-okp) (vl-parse-statement-wrapped null-okp))))))))))


(defsection progress

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-vl-parse-statement-flag vl-parse-statement-progress
        ,(vl-progress-claim vl-parse-case-item)
        ,(vl-progress-claim vl-parse-1+-case-items)
        ,(vl-progress-claim vl-parse-case-statement :args (atts))
        ,(vl-progress-claim vl-parse-conditional-statement :args (atts))
        ,(vl-progress-claim vl-parse-loop-statement :args (atts))
        ,(vl-progress-claim vl-parse-par-block :args (atts))
        ,(vl-progress-claim vl-parse-seq-block :args (atts))
        ,(vl-progress-claim vl-parse-procedural-timing-control-statement :args (atts))
        ,(vl-progress-claim vl-parse-wait-statement :args (atts))
        ,(vl-progress-claim vl-parse-action-block)
        ,(vl-progress-claim vl-parse-expect-property-statement)
        ,(vl-progress-claim vl-parse-concurrent-assertion-statement)
        ,(vl-progress-claim vl-parse-immediate-assertion-statement)
        ,(vl-progress-claim vl-parse-procedural-assertion-statement :args (atts))
        ,(vl-progress-claim vl-parse-statement-2005-aux :args (atts))
        ,(vl-progress-claim vl-parse-statement-2012-aux :args (atts))
        ,(vl-progress-claim vl-parse-statement-aux :args (atts))
        ,(vl-progress-claim vl-parse-statement-wrapped :args (null-okp))
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

        :hints((expand-only-the-flag-function-hint clause state)
               (and stable-under-simplificationp
                    '(:expand ((:free (null-okp) (vl-parse-statement-wrapped null-okp))))))))))



(local (defthm l0
         (implies (and (equal (vl-token->type (first (vl-tokstream->tokens))) type)
                       (consp (vl-tokstream->tokens)))
                  (vl-is-token? type))
         :hints(("Goal" :in-theory (enable vl-is-token?)))))

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

  ;; BOZO we should see about getting rid of these extra-hyps.  We should always
  ;; have unconditional theorems now.  But this will involve changing how defparser
  ;; handles guards in return-type theorems, which could lead to unexpected problems.
  ;; still probably worth doing.

  (with-output
    :off prove :gag-mode :goals
    (make-event
     `(defthm-vl-parse-statement-flag vl-parse-statement-type

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
        ,(vl-stmt-claim vl-parse-action-block
                        (vl-actionblock-p val))
        ,(vl-stmt-claim vl-parse-expect-property-statement
                        (vl-cassertion-p val))
        ,(vl-stmt-claim vl-parse-concurrent-assertion-statement
                        (vl-cassertion-p val))
        ,(vl-stmt-claim vl-parse-immediate-assertion-statement
                        (vl-assertion-p val))
        ,(vl-stmt-claim vl-parse-procedural-assertion-statement
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-statement-2005-aux
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-statement-2012-aux
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-statement-aux
                        (vl-stmt-p val)
                        :args (atts)
                        :extra-hyps ((force (vl-atts-p atts))))
        ,(vl-stmt-claim vl-parse-statement-wrapped
                        (vl-stmt-p val)
                        :args (null-okp))
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
        :hints((expand-only-the-flag-function-hint clause state)
               (and stable-under-simplificationp
                    '(:expand ((:free (null-okp) (vl-parse-statement-wrapped null-okp))))))))))

(with-output
  :off prove
  :gag-mode :goals
  (verify-guards vl-parse-statement-fn))

(defparser-top vl-parse-statement)

