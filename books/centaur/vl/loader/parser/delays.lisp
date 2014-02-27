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
(include-book "expressions")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))



;                            PARSING DELAYS
;
; See Section 7.14 for the rules for computing delays.  Three delay expressions
; are associated with each gate: a rise delay, fall delay, and a high-impedence
; (or charge decay, for triregs) delay.  When three delays are specified, there
; is no confusion and everything is explicit.
;
; When only two delays are given, the first is the rise delay, the second is
; the fall delay.  For regular gates, the high impedence delay is supposed to
; be the "lesser" of these.  But it is not clear just what that means or how to
; compute it, because these may be compound mintypmax expressions.  That is,
; which is lesser, 1:2:5 or 1:3:4?  Also, the expression can mention variables,
; so the parser itself isn't going to be able to figure out the high impetence
; delay in all cases.  The rules are different for computing the charge decay
; delay for triregs, and we do not try to implement them, either.
;
; When only one delay is given, all three delays are set to it.
;
; When no delay is given, all three are treated as zero.

; delay_value ::=
;    unsigned_number
;  | real_number
;  | identifier

(encapsulate
 ()
 (local (in-theory (enable vl-is-token?)))
 (defparser vl-parse-delay-value ()
   :result (vl-expr-p val)
   :resultp-of-nil nil
   :fails gracefully
   :count strong

; Well, this is gross.  We are only supposed to permit unsigned numbers, not
; arbitrary integers.  But that's a lexer concept, not a parser one.  So we
; dive into the token and check that its etext does not contain #\', since
; that's the character that starts every base.  Maybe we should just be more
; flexible than the spec says, instead.

   (cond ((vl-is-token? :vl-inttoken)
          (if (member #\' (vl-echarlist->chars (vl-inttoken->etext (car tokens))))
              (vl-parse-error "Illegal delay value.")
            (vl-parse-primary)))

         ((vl-is-token? :vl-realtoken)
          (vl-parse-primary))

         ((vl-is-token? :vl-idtoken)
          (mv nil
              (make-vl-atom
               :guts (make-vl-id :name  (vl-idtoken->name (car tokens))))
              (cdr tokens)
              warnings))

         (t
          (vl-parse-error "Illegal delay value.")))))



; delay2 ::=
;    '#' delay_value
;  | '#' '(' mintypmax_expression [ ',' mintypmax_expression ] ')'

(defparser vl-parse-delay2 ()
  :result (vl-gatedelay-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-pound))
        (unless (vl-is-token? :vl-lparen)
          (delay := (vl-parse-delay-value))
          (return (make-vl-gatedelay :rise delay
                                     :fall delay
                                     :high delay)))
        (:= (vl-match-token :vl-lparen))
        (first := (vl-parse-mintypmax-expression))
        (when (vl-is-token? :vl-rparen)
          (:= (vl-match))
          (return (make-vl-gatedelay :rise first
                                     :fall first
                                     :high first)))
        (:= (vl-match-token :vl-comma))
        (second := (vl-parse-mintypmax-expression))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-gatedelay :rise first
                                   :fall second
                                   :high nil))))


; delay3 ::=
;    '#' delay_value
;  | '#' '(' mintypmax_expression [ ',' mintypmax_expression [ ',' mintypmax_expression ] ] ')'

(defparser vl-parse-delay3 ()
  :result (vl-gatedelay-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-pound))
        (unless (vl-is-token? :vl-lparen)
          (delay := (vl-parse-delay-value))
          (return (make-vl-gatedelay :rise delay
                                     :fall delay
                                     :high delay)))
        (:= (vl-match))
        (first := (vl-parse-mintypmax-expression))
        (when (vl-is-token? :vl-rparen)
          (:= (vl-match))
          (return (make-vl-gatedelay :rise first
                                     :fall first
                                     :high first)))
        (:= (vl-match-token :vl-comma))
        (second := (vl-parse-mintypmax-expression))
        (when (vl-is-token? :vl-rparen)
          (:= (vl-match))
          (return (make-vl-gatedelay :rise first
                                     :fall second
                                     :high nil)))
        (:= (vl-match-token :vl-comma))
        (third := (vl-parse-mintypmax-expression))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-gatedelay :rise first
                                   :fall second
                                   :high third))))


