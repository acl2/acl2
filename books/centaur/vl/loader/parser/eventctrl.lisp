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
(include-book "delays")
(local (include-book "../../util/arithmetic"))

(defsection parse-eventctrl
  :parents (parser)
  :short "Functions for parsing event controls.")

(local (xdoc::set-default-parents parse-eventctrl))

; delay_control ::=
;    '#' delay_value
;  | '#' '(' mintypmax_expression ')'

(defparser vl-parse-delay-control ()
  :result (vl-delaycontrol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-pound))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match))
          (ret := (vl-parse-mintypmax-expression))
          (:= (vl-match-token :vl-rparen))
          (return (vl-delaycontrol ret)))
        (ret := (vl-parse-delay-value))
        (return (vl-delaycontrol ret))))


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
  (seq tokstream
        (:= (vl-match-token :vl-atsign))

        (when (vl-is-token? :vl-times)
          (:= (vl-match))
          (return (vl-eventcontrol t nil)))

        (when (vl-is-token? :vl-beginattr)
          ;; GROSS -- Special case to handle "@ (* )".  That is, the (* gets
          ;; interpreted by the lexer as a beginattr.  We don't have a good way
          ;; around this except to handle it explicitly.
          (:= (vl-match))
          (:= (vl-match-token :vl-rparen))
          (return (vl-eventcontrol t nil)))

        (unless (vl-is-token? :vl-lparen)
          (hid := (vl-parse-hierarchical-identifier nil))
          (return (vl-eventcontrol nil (list (vl-evatom :vl-noedge
                                                        (make-vl-index
                                                         :scope
                                                         (make-vl-scopeexpr-end
                                                          :hid hid)
                                                         :part (make-vl-partselect-none)))))))

        (:= (vl-match-token :vl-lparen))

        (when (vl-is-token? :vl-endattr)
          ;; GROSS -- Special case to handle "@ ( *)".  That is, the *) gets
          ;; interpreted as an endattr.  We again have to handle it explicitly.
          (:= (vl-match))
          (return (vl-eventcontrol t nil)))

        (when (vl-is-token? :vl-times)
          (:= (vl-match))
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
   (seq tokstream
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
