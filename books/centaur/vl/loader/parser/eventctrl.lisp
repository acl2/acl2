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
(include-book "delays")
(local (include-book "../../util/arithmetic"))


; delay_control ::=
;    '#' delay_value
;  | '#' '(' mintypmax_expression ')'

(defparser vl-parse-delay-control ()
  :result (vl-delaycontrol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-pound))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match-token :vl-lparen))
          (ret := (vl-parse-mintypmax-expression))
          (:= (vl-match-token :vl-rparen))
          (return (vl-delaycontrol ret)))
        (ret := (vl-parse-delay-value))
        (return (vl-delaycontrol ret))))


; event_expression ::=
;    expression
;  | 'posedge' expression
;  | 'negedge' expression
;  | event_expression 'or' event_expression
;  | event_expression ',' event_expression

(defparser vl-parse-event-expression ()
  ;; Matches "1 or more evatoms"
  :result (vl-evatomlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-some-token? '(:vl-kwd-posedge :vl-kwd-negedge))
          (edge := (vl-match-some-token '(:vl-kwd-posedge :vl-kwd-negedge))))
        (expr := (vl-parse-expression))
        (when (vl-is-some-token? '(:vl-kwd-or :vl-comma))
          (:= (vl-match-some-token '(:vl-kwd-or :vl-comma)))
          (rest := (vl-parse-event-expression)))
        (return
         (let ((edgetype (if (not edge)
                             :vl-noedge
                           (case (vl-token->type edge)
                             (:vl-kwd-posedge :vl-posedge)
                             (:vl-kwd-negedge :vl-negedge)
                             (t (er hard 'vl-parse-event-expression "Impossible"))))))
           (cons (vl-evatom edgetype expr)
                 rest)))))


; event_control ::=
;    '@' hierarchial_identifier
;  | '@' '(' event_expression ')'
;  | '@' '*'
;  | '@' '(' '*' ')'

(defparser vl-parse-event-control ()
  :result (vl-eventcontrol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-atsign))

        (when (vl-is-token? :vl-times)
          (:= (vl-match-token :vl-times))
          (return (vl-eventcontrol t nil)))

        (when (vl-is-token? :vl-beginattr)
          ;; GROSS -- Special case to handle "@ (* )".  That is, the (* gets
          ;; interpreted by the lexer as a beginattr.  We don't have a good way
          ;; around this except to handle it explicitly.
          (:= (vl-match-token :vl-beginattr))
          (:= (vl-match-token :vl-rparen))
          (return (vl-eventcontrol t nil)))

        (unless (vl-is-token? :vl-lparen)
          (hid := (vl-parse-hierarchial-identifier nil))
          (return (vl-eventcontrol nil (list (vl-evatom :vl-noedge hid)))))

        (:= (vl-match-token :vl-lparen))

        (when (vl-is-token? :vl-endattr)
          ;; GROSS -- Special case to handle "@ ( *)".  That is, the *) gets
          ;; interpreted as an endattr.  We again have to handle it explicitly.
          (:= (vl-match-token :vl-endattr))
          (return (vl-eventcontrol t nil)))

        (when (vl-is-token? :vl-times)
          (:= (vl-match-token :vl-times))
          (:= (vl-match-token :vl-rparen))
          (return (vl-eventcontrol t nil)))

        (atoms := (vl-parse-event-expression))
        (:= (vl-match-token :vl-rparen))
        (return (vl-eventcontrol nil atoms))))



; delay_or_event_control ::=
;    delay_control
;  | event_control
;  | 'repeat' '(' expression ')' event_control

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (defparser vl-parse-delay-or-event-control ()
   :result (vl-delayoreventcontrol-p val)
   :resultp-of-nil nil
   :fails gracefully
   :count strong
   (seqw tokens warnings
         (when (vl-is-token? :vl-pound)
           (ret := (vl-parse-delay-control))
           (return ret))
         (when (vl-is-token? :vl-atsign)
           (ret := (vl-parse-event-control))
           (return ret))
         (:= (vl-match-token :vl-kwd-repeat))
         (:= (vl-match-token :vl-lparen))
         (expr := (vl-parse-expression))
         (:= (vl-match-token :vl-rparen))
         (ctrl := (vl-parse-event-control))
         (return (vl-repeateventcontrol expr ctrl)))))
