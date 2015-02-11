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

  (seq tokstream
       (when (vl-is-token? :vl-inttoken)
         (int := (vl-match))
         (when (member #\' (vl-echarlist->chars (vl-token->etext int)))
           (return-raw (vl-parse-error "Illegal delay value.")))
         (return (make-vl-atom :guts (vl-make-guts-from-inttoken int))))

       (when (vl-is-token? :vl-realtoken)
         (ans := (vl-parse-primary))
         (return ans))

       (when (vl-is-token? :vl-idtoken)
         (id := (vl-match))
         (return (make-vl-atom :guts (make-vl-id :name (vl-idtoken->name id)))))

       (return-raw
        (vl-parse-error "Illegal delay value."))))



; delay2 ::=
;    '#' delay_value
;  | '#' '(' mintypmax_expression [ ',' mintypmax_expression ] ')'

(defparser vl-parse-delay2 ()
  :result (vl-gatedelay-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
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
  (seq tokstream
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


