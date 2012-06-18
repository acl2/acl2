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
(include-book "parse-expressions")
(local (include-book "../util/arithmetic"))

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

(vl-mutual-recursion

 (defparser vl-parse-lvalue (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 0)
                   :verify-guards nil))
   (if (not (vl-is-token? :vl-lcurly))
       (vl-parse-indexed-id)
     (seqw tokens warnings
           (:= (vl-match-token :vl-lcurly))
           (args := (vl-parse-1+-lvalues-separated-by-commas))
           (:= (vl-match-token :vl-rcurly))
           (return (make-vl-nonatom :op :vl-concat
                                    :args args)))))

 (defparser vl-parse-1+-lvalues-separated-by-commas (tokens warnings)
   (declare (xargs :measure (two-nats-measure (acl2-count tokens) 1)))
   (seqw tokens warnings
         (first :s= (vl-parse-lvalue))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match-token :vl-comma))
           (rest := (vl-parse-1+-lvalues-separated-by-commas tokens)))
         (return (cons first rest)))))

(encapsulate
  ()
  (flag::make-flag vl-flag-parse-lvalue
                   vl-parse-lvalue-fn)

  (local (in-theory (enable vl-parse-lvalue
                            vl-parse-1+-lvalues-separated-by-commas)))

  (defthm-vl-flag-parse-lvalue token-list
    (vl-parse-lvalue-fn
     (implies (force (vl-tokenlist-p tokens))
              (vl-tokenlist-p (mv-nth 2 (vl-parse-lvalue)))))
    (vl-parse-1+-lvalues-separated-by-commas-fn
     (implies (force (vl-tokenlist-p tokens))
              (vl-tokenlist-p (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas)))))
    :hints(("Goal" :induct (vl-flag-parse-lvalue flag tokens warnings))))

  (defthm-vl-flag-parse-lvalue count-strong
    (vl-parse-lvalue-fn
     (and (<= (acl2-count (mv-nth 2 (vl-parse-lvalue)))
              (acl2-count tokens))
          (implies (not (mv-nth 0 (vl-parse-lvalue)))
                   (< (acl2-count (mv-nth 2 (vl-parse-lvalue)))
                      (acl2-count tokens))))
     :rule-classes ((:rewrite) (:linear)))
    (vl-parse-1+-lvalues-separated-by-commas-fn
     (and (<= (acl2-count (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas)))
              (acl2-count tokens))
          (implies (not (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas)))
                   (< (acl2-count (mv-nth 2 (vl-parse-1+-lvalues-separated-by-commas)))
                      (acl2-count tokens))))
     :rule-classes ((:rewrite) (:linear)))
    :hints(("Goal" :induct (vl-flag-parse-lvalue flag tokens warnings))))

  (defthm-vl-flag-parse-lvalue fails-gracefully
    (vl-parse-lvalue-fn
     (implies (mv-nth 0 (vl-parse-lvalue))
              (not (mv-nth 1 (vl-parse-lvalue)))))
    (vl-parse-1+-lvalues-separated-by-commas-fn
     (implies (mv-nth 0 (vl-parse-1+-lvalues-separated-by-commas))
              (not (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas)))))
    :hints(("Goal" :induct (vl-flag-parse-lvalue flag tokens warnings))))

  (defthm-vl-flag-parse-lvalue result
    (vl-parse-lvalue-fn
     (implies (force (vl-tokenlist-p tokens))
              (equal (vl-expr-p (mv-nth 1 (vl-parse-lvalue)))
                     (not (mv-nth 0 (vl-parse-lvalue))))))
    (vl-parse-1+-lvalues-separated-by-commas-fn
     (implies (force (vl-tokenlist-p tokens))
              (equal (vl-exprlist-p (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas)))
                     t)))
    :hints(("Goal" :induct (vl-flag-parse-lvalue flag tokens warnings))))

  (defthm-vl-flag-parse-lvalue warnings
    (vl-parse-lvalue-fn
     (implies (force (vl-warninglist-p warnings))
              (vl-warninglist-p (mv-nth 3 (vl-parse-lvalue)))))
    (vl-parse-1+-lvalues-separated-by-commas-fn
     (implies (force (vl-warninglist-p warnings))
              (vl-warninglist-p (mv-nth 3 (vl-parse-1+-lvalues-separated-by-commas)))))
    :hints(("Goal" :induct (vl-flag-parse-lvalue flag tokens warnings))))

  (defthm-vl-flag-parse-lvalue true-listp
    (vl-parse-lvalue-fn
     t
     :rule-classes nil)
    (vl-parse-1+-lvalues-separated-by-commas-fn
     (true-listp (mv-nth 1 (vl-parse-1+-lvalues-separated-by-commas)))
     :rule-classes :type-prescription)
    :hints(("Goal" :induct (vl-flag-parse-lvalue flag tokens warnings))))

  (verify-guards vl-parse-lvalue-fn))




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

(defparser vl-parse-assignment (tokens warnings)
  ;; Returns a (lvalue . expr) pair
  :result (and (consp val)
               (vl-expr-p (car val))
               (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (lvalue := (vl-parse-lvalue))
        (:= (vl-match-token :vl-equalsign))
        (expr := (vl-parse-expression))
        (return (cons lvalue expr))))




