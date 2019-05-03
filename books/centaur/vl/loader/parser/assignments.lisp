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
(include-book "expressions")
(include-book "../../mlib/lvalues")
(local (include-book "../../util/arithmetic"))

(defsection parse-assignments
  :parents (parser)
  :short "Functions for parsing lvalue expressions and assignments."
  :long "<p>Lvalues are used in the various kinds of assignment statements.
They are a restricted subset of expressions, so we do not introduce a separate
type for them but rather just reuse our usual expression representation.</p>")

(local (xdoc::set-default-parents parse-assignments))

(defparsers parse-lvalues-2005
  :short "Parser for Verilog-2005 @('net_lvalue') or @('variable_lvalue')s."

  :long "<p>The Verilog-2005 grammar distinguishes between
@('variable_lvalue')s and @('net_lvalue')s, but if we expand away simple
aliases such as</p>

@({
     hierarchial_net_identifier ::= hierarchial_identifier,
})

<p>and also account for our treatment of a @('constant_expression') being just
an ordinary @('expression'), then we find that both of these are the same
thing:</p>

@({
    net_lvalue ::=
       hierarchial_identifier [ { '[' expression ']' '[' range_expression ']' } ]
     | '{' net_lvalue { ',' net_lvalue } '}'

    variable_lvalue ::=
       hierarchial_identifier [ { '[' expression ']' '[' range_expression ']' } ]
     | '{' variable_lvalue { ',' variable_lvalue } '}'
})"

  :flag-local nil

  (defparser vl-parse-lvalue-2005 ()
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :verify-guards nil
    (if (not (vl-is-token? :vl-lcurly))
        (vl-parse-indexed-id)
      (seq tokstream
           (:= (vl-match-token :vl-lcurly))
           (args := (vl-parse-1+-lvalues-separated-by-commas-2005))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-concat :parts args)))))

  (defparser vl-parse-1+-lvalues-separated-by-commas-2005 ()
    :measure (two-nats-measure (vl-tokstream-measure) 1)
    (seq tokstream
         (first :s= (vl-parse-lvalue-2005))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-lvalues-separated-by-commas-2005)))
         (return (cons first rest))))

  ///
  (defthm-parse-lvalues-2005-flag count-strong
    (vl-parse-lvalue-2005
     (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-lvalue-2005)))
              (vl-tokstream-measure))
          (implies (not (mv-nth 0 (vl-parse-lvalue-2005)))
                   (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-lvalue-2005)))
                      (vl-tokstream-measure))))
     :rule-classes ((:rewrite) (:linear)))
    (vl-parse-1+-lvalues-separated-by-commas-2005
     (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas-2005)))
              (vl-tokstream-measure))
          (implies (not (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas-2005)))
                   (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas-2005)))
                      (vl-tokstream-measure))))
     :rule-classes ((:rewrite) (:linear)))
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-2005-fn (w state))))))

  (defthm-parse-lvalues-2005-flag fails-gracefully
    (vl-parse-lvalue-2005
     (and (implies (mv-nth 0 (vl-parse-lvalue-2005))
                   (not (mv-nth 1 (vl-parse-lvalue-2005))))
          (iff (vl-warning-p (mv-nth 0 (vl-parse-lvalue-2005)))
               (mv-nth 0 (vl-parse-lvalue-2005)))))
    (vl-parse-1+-lvalues-separated-by-commas-2005
     (and (implies (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas-2005))
                   (not (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas-2005))))
          (iff (vl-warning-p (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas-2005)))
               (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas-2005)))))
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-2005-fn (w state))))))

  (defthm-parse-lvalues-2005-flag result
    (vl-parse-lvalue-2005
     (equal (vl-expr-p (mv-nth 1 (vl-parse-lvalue-2005)))
            (not (mv-nth 0 (vl-parse-lvalue-2005)))))
    (vl-parse-1+-lvalues-separated-by-commas-2005
     (vl-exprlist-p (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas-2005))))
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-2005-fn (w state))))))

  (defthm-parse-lvalues-2005-flag parse-lvalues-true-listp
    (vl-parse-lvalue-2005
     t
     :rule-classes nil)
    (vl-parse-1+-lvalues-separated-by-commas-2005
     (true-listp (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas-2005)))
     :rule-classes :type-prescription)
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-2005-fn (w state))))))

  (verify-guards+ vl-parse-lvalue-2005))

(defparser vl-parse-net-lvalue-2012-aux ()
  :short "Parse a @('net_lvalue') for SystemVerilog-2012, but don't do much
          well-formedness checking."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-quote)
         ;; It can only be the assignment pattern case.
         (:= (vl-match))
         (:= (vl-match-token :vl-lcurly))
         (pat := (vl-parse-assignment-pattern))
         (return (make-vl-pattern :pattype nil :pat pat)))
       (when (vl-is-token? :vl-lcurly)
         ;; It can only be the concatenation case.
         (expr := (vl-parse-concatenation))
         (return expr))
       (when (vl-is-token? :vl-lparen)
         ;; This isn't explicitly allowed but we'll deal with it anyway
         (:= (vl-match))
         (lvalue := (vl-parse-net-lvalue-2012-aux))
         (:= (vl-match-token :vl-rparen))
         (return lvalue))
       ;; Otherwise we're in the identifier case.
       (expr := (vl-parse-indexed-id-2012))
       (return expr)))

(defparser vl-parse-net-lvalue-2012 ()
  :short "Parse a @('net_lvalue') for SystemVerilog-2012."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       ;; We can't just use vl-parse-expr here, because then when we run into
       ;; things like non-blocking assignment statements, e.g.,
       ;;    foo <= bar;
       ;; we would think that the <= is ours, and it isn't.
       (expr := (vl-parse-net-lvalue-2012-aux))
       (when (vl-expr-net-lvalue-p expr)
         (return expr))
       (return-raw
        ;; This checks the guts of the assignment pattern or concatenation cases.
        (mv (make-vl-warning :type :vl-parse-error
                             :msg "Parse error at ~a0: not a valid net_lvalue expression: ~a1"
                             :args (list loc expr)
                             :fn __function__
                             :fatalp t)
            nil tokstream))))

(defparser vl-parse-net-lvalue ()
  :short "Parse a @('net_lvalue')."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (if (eq (vl-loadconfig->edition config) :verilog-2005)
      (vl-parse-lvalue-2005)
    (vl-parse-net-lvalue-2012)))

(defparser vl-parse-variable-lvalue-2012-aux ()
  :short "Parse a @('variable_lvalue') for SystemVerilog-2012, but don't do
          much well-formedness checking."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-quote)
         ;; It can only be the assignment pattern case.
         (:= (vl-match))
         (:= (vl-match-token :vl-lcurly))
         (pat := (vl-parse-assignment-pattern))
         (return (make-vl-pattern :pattype nil :pat pat)))
       (when (vl-is-token? :vl-lcurly)
         ;; It can be a concatenation or a streaming concatenation.
         (expr := (vl-parse-any-sort-of-concatenation))
         (return expr))
       ;; Otherwise we're in the identifier case.
       (expr := (vl-parse-indexed-id-2012))
       (return expr)))

(defparser vl-parse-variable-lvalue-2012 ()
  :short "Parse a @('variable_lvalue') for SystemVerilog-2012."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (loc := (vl-current-loc))
       ;; We can't just use vl-parse-expr here, because then when we run into
       ;; things like non-blocking assignment statements, e.g.,
       ;;    foo <= bar;
       ;; we would think that the <= is ours, and it isn't.
       (expr := (vl-parse-variable-lvalue-2012-aux))
       (when (vl-expr-variable-lvalue-p expr)
         (return expr))
       (return-raw
        ;; This checks the guts of the assignment pattern or concatenation cases.
        (mv (make-vl-warning :type :vl-parse-error
                             :msg "Parse error at ~a0: not a valid lvalue expression: ~a1"
                             :args (list loc expr)
                             :fn __function__
                             :fatalp t)
            nil tokstream))))

(defparser vl-parse-variable-lvalue ()
  :short "Parse a @('variable_lvalue')."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (if (eq (vl-loadconfig->edition config) :verilog-2005)
      (vl-parse-lvalue-2005)
    (vl-parse-variable-lvalue-2012)))

(defparser vl-parse-net-assignment ()
  :short "Parse a @('net_assignment')."
  :long "<p>Both Verilog-2005 and SystemVerilog-2012 agree on this rule:</p>
         @({
             net_assignment ::= net_lvalue '=' expression
         })"
  :result (and (consp val)
               (vl-expr-p (car val))
               (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
        (lvalue := (vl-parse-net-lvalue))
        (:= (vl-match-token :vl-equalsign))
        (expr := (vl-parse-expression))
        (return (cons lvalue expr))))

(defparser vl-parse-variable-assignment ()
  :short "Parse a @('variable_assignment')."
  :long "<p>Both Verilog-2005 and SystemVerilog-2012 agree on this rule:</p>
         @({
              variable_assignment ::= variable_lvalue '=' expression
         })"
  :result (and (consp val)
               (vl-expr-p (car val))
               (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
        (lvalue := (vl-parse-variable-lvalue))
        (:= (vl-match-token :vl-equalsign))
        (expr := (vl-parse-expression))
        (return (cons lvalue expr))))


;; For continuous assignments, see nets.lisp (because they also involve
;; strengths and delays, etc.)

