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
 (defparser vl-parse-delay-value (tokens warnings)
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

(defparser vl-parse-delay2 (tokens warnings)
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
          (:= (vl-match-token :vl-rparen))
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

(defparser vl-parse-delay3 (tokens warnings)
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
          (:= (vl-match-token :vl-rparen))
          (return (make-vl-gatedelay :rise first
                                     :fall first
                                     :high first)))
        (:= (vl-match-token :vl-comma))
        (second := (vl-parse-mintypmax-expression))
        (when (vl-is-token? :vl-rparen)
          (:= (vl-match-token :vl-rparen))
          (return (make-vl-gatedelay :rise first
                                     :fall second
                                     :high nil)))
        (:= (vl-match-token :vl-comma))
        (third := (vl-parse-mintypmax-expression))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-gatedelay :rise first
                                   :fall second
                                   :high third))))






(local
 (encapsulate
   ()

   (local (include-book "lexer/lexer"))

   (program)

   (defmacro test-delay3 (&key input rise fall high (successp 't))
     `(assert! (let ((tokens (make-test-tokens ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-delay3 tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (equal warnings 'blah-warnings)
                                    (not ,successp)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (vl-gatedelay-p val)
                                  (prog2$ (cw "Rise = ~x0.~%" (vl-pretty-expr (vl-gatedelay->rise val)))
                                          (equal (vl-pretty-expr (vl-gatedelay->rise val)) ',rise))
                                  (prog2$ (cw "Fall = ~x0.~%" (vl-pretty-expr (vl-gatedelay->fall val)))
                                          (equal (vl-pretty-expr (vl-gatedelay->fall val)) ',fall))
                                  (prog2$ (cw "High = ~x0.~%"
                                              (and (vl-gatedelay->high val)
                                                   (vl-pretty-expr (vl-gatedelay->high val))))
                                          (if (vl-gatedelay->high val)
                                              (equal (vl-pretty-expr (vl-gatedelay->high val)) ',high)
                                            (not ',high))))))))))

   (test-delay3 :input "#5"
                :rise 5
                :fall 5
                :high 5)

   (test-delay3 :input "#2 0"
                :rise 2
                :fall 2
                :high 2)

   (test-delay3 :input "#3.4"
                :rise (real "3.4")
                :fall (real "3.4")
                :high (real "3.4"))

   (test-delay3 :input "#foo"
                :rise (id "foo")
                :fall (id "foo")
                :high (id "foo"))

   (test-delay3 :input "#'sd15"
                :successp nil)

   (test-delay3 :input "#('sd15)"
                :rise 15
                :fall 15
                :high 15)

   (test-delay3 :input "#(5, foo)"
                :rise 5
                :fall (id "foo")
                :high nil)

   (test-delay3 :input "#(5, 20, 55)"
                :rise 5
                :fall 20
                :high 55)

   (test-delay3 :input "#(1:2:3, 4:5:6, 7:8:9)"
                :rise (:vl-mintypmax nil 1 2 3)
                :fall (:vl-mintypmax nil 4 5 6)
                :high (:vl-mintypmax nil 7 8 9))

   (test-delay3 :input "#(1:2:3, 4:5:6)"
                :rise (:vl-mintypmax nil 1 2 3)
                :fall (:vl-mintypmax nil 4 5 6)
                :high nil)

   ))