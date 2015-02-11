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
(include-book "expressions")
(local (include-book "../../util/arithmetic"))

;                                 LVALUES
;
; Lvalues are used in the various assignment statements.  The Verilog grammar
; distinguishes between variable_lvalues and net_lvalues, but if we expand away
; simple aliases such as hierarchial_net_identifier ::= hierarchial_identifier,
; and also account for our treatment of constant_expression, then we see that
; both of these are actually the same thing:
;
; net_lvalue ::=
;    hierarchial_identifier [ { '[' expression ']' '[' range_expression ']' } ]
;  | '{' net_lvalue { ',' net_lvalue } '}'
;
; variable_lvalue ::=
;    hierarchial_identifier [ { '[' expression ']' '[' range_expression ']' } ]
;  | '{' variable_lvalue { ',' variable_lvalue } '}'
;
; So we will only talk about lvalues, and not about net_lvalues or
; variable_lvalues.
;
; Furthermore, lvalues are a subset of the expressions, formed by closing the
; bit- and part-selected hierarchial identifiers under concatenation.  So
; rather than introduce a new data type to represent the lvalues, we just
; represent them as expressions.

(defparsers parse-lvalues
  :flag-local nil
  (defparser vl-parse-lvalue ()
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :verify-guards nil
    (if (not (vl-is-token? :vl-lcurly))
        (vl-parse-indexed-id)
      (seq tokstream
           (:= (vl-match-token :vl-lcurly))
           (args := (vl-parse-1+-lvalues-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-nonatom :op :vl-concat
                                    :args args)))))

  (defparser vl-parse-1+-lvalues-separated-by-commas ()
    :measure (two-nats-measure (vl-tokstream-measure) 1)
    (seq tokstream
         (first :s= (vl-parse-lvalue))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-lvalues-separated-by-commas)))
         (return (cons first rest)))))

(encapsulate
  ()
  (local (in-theory (enable vl-parse-lvalue
                            vl-parse-1+-lvalues-separated-by-commas)))

  ;; (defthm-parse-lvalues-flag token-list
  ;;   (vl-parse-lvalue
  ;;    (vl-tokenlist-p (mv-nth 2 (vl-parse-lvalue))))
  ;;   (vl-parse-1+-lvalues-separated-by-commas
  ;;    (vl-tokenlist-p (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas))))
  ;;   :hints(("Goal" :do-not '(generalize fertilize))
  ;;          (and acl2::stable-under-simplificationp
  ;;               (flag::expand-calls-computed-hint
  ;;                acl2::clause
  ;;                (flag::get-clique-members 'vl-parse-lvalue-fn (w state))))))

  (defthm-parse-lvalues-flag count-strong
    (vl-parse-lvalue
     (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-lvalue)))
              (vl-tokstream-measure))
          (implies (not (mv-nth 0 (vl-parse-lvalue)))
                   (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-lvalue)))
                      (vl-tokstream-measure))))
     :rule-classes ((:rewrite) (:linear)))
    (vl-parse-1+-lvalues-separated-by-commas
     (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas)))
              (vl-tokstream-measure))
          (implies (not (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas)))
                   (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas)))
                      (vl-tokstream-measure))))
     :rule-classes ((:rewrite) (:linear)))
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-fn (w state))))))

  (defthm-parse-lvalues-flag fails-gracefully
    (vl-parse-lvalue
     (and (implies (mv-nth 0 (vl-parse-lvalue))
                   (not (mv-nth 1 (vl-parse-lvalue))))
          (iff (vl-warning-p (mv-nth 0 (vl-parse-lvalue)))
               (mv-nth 0 (vl-parse-lvalue)))))
    (vl-parse-1+-lvalues-separated-by-commas
     (and (implies (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas))
                   (not (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas))))
          (iff (vl-warning-p (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas)))
               (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas)))))
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-fn (w state))))))

  (defthm-parse-lvalues-flag result
    (vl-parse-lvalue
     (equal (vl-expr-p (mv-nth 1 (vl-parse-lvalue)))
            (not (mv-nth 0 (vl-parse-lvalue)))))
    (vl-parse-1+-lvalues-separated-by-commas
     (vl-exprlist-p (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas))))
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-fn (w state))))))

  ;; (defthm-parse-lvalues-flag pstate
  ;;   (vl-parse-lvalue
  ;;    (vl-parsestate-p (mv-nth 3 (vl-parse-lvalue))))
  ;;   (vl-parse-1+-lvalues-separated-by-commas
  ;;    (vl-parsestate-p (mv-nth 3 (vl-parse-1+-lvalues-separated-by-commas))))
  ;;   :hints(("Goal" :do-not '(generalize fertilize))
  ;;          (and acl2::stable-under-simplificationp
  ;;               (flag::expand-calls-computed-hint
  ;;                acl2::clause
  ;;                (flag::get-clique-members 'vl-parse-lvalue-fn (w state))))))

  (defthm-parse-lvalues-flag parse-lvalues-true-listp
    (vl-parse-lvalue
     t
     :rule-classes nil)
    (vl-parse-1+-lvalues-separated-by-commas
     (true-listp (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas)))
     :rule-classes :type-prescription)
    :hints(("Goal" :do-not '(generalize fertilize))
           (and acl2::stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause
                 (flag::get-clique-members 'vl-parse-lvalue-fn (w state))))))

  (verify-guards+ vl-parse-lvalue))




;                                ASSIGNMENTS
;
; The grammar also distinguishes between variable_assignment and
; net_assignment, but with our treatment of lvalue there is no longer any
; difference, so we merely use "assignment".
;
; variable_assignment ::=
;    lvalue '=' expression
;
; net_assignment ::=
;    lvalue '=' expression

(defparser vl-parse-assignment ()
  ;; Returns a (lvalue . expr) pair
  :result (and (consp val)
               (vl-expr-p (car val))
               (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
        (lvalue := (vl-parse-lvalue))
        (:= (vl-match-token :vl-equalsign))
        (expr := (vl-parse-expression))
        (return (cons lvalue expr))))




