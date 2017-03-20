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


; Verilog-2005:
;
; event_expression ::=
;    expression
;  | 'posedge' expression
;  | 'negedge' expression
;  | event_expression 'or' event_expression
;  | event_expression ',' event_expression

(defparser vl-parse-event-expression-2005 ()
  ;; Matches "1 or more evatoms"
  :result (vl-evatomlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-posedge :vl-kwd-negedge))
          (edge := (vl-match)))
        (expr := (vl-parse-expression))
        (when (vl-is-some-token? '(:vl-kwd-or :vl-comma))
          (:= (vl-match))
          (rest := (vl-parse-event-expression-2005)))
        (return
         (let ((edgetype (if (not edge)
                             :vl-noedge
                           (case (vl-token->type edge)
                             (:vl-kwd-posedge :vl-posedge)
                             (:vl-kwd-negedge :vl-negedge)
                             (t (impossible))))))
           (cons (make-vl-evatom :type edgetype
                                 :expr expr)
                 rest))))
  ///
  (defthm consp-of-vl-parse-event-expression-2005
    (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2005)))
      (equal (consp val)
             (not err)))))


; SystemVerilog-2012:
;
; event_expression ::=
;     [edge_identifier] expression [ 'iff' expression]
;   | sequence_instance [ 'iff' expression ]
;   | event_expression 'or' event_expression
;   | event_expression ',' event_expression
;   | '(' event_expression ')'
;
; We don't yet handle the IFF expressions or sequence_instance things here.
; Handling sequence_instance would require making this mutually recursive with
; sequences, which are a godawful mess.

(defparser vl-parse-optional-edge-identifier ()
  :result (vl-evatomtype-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails never
  :count weak
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-posedge
                                  :vl-kwd-negedge
                                  :vl-kwd-edge))
         (edge := (vl-match)))
       (return (if (not edge)
                   :vl-noedge
                 (case (vl-token->type edge)
                   (:vl-kwd-posedge :vl-posedge)
                   (:vl-kwd-negedge :vl-negedge)
                   (:vl-kwd-edge    :vl-edge)
                   (t (impossible)))))))

(with-output
  ;; Gads, induction schemes are huge and awful...
  :off (prove proof-tree)
  (defparser vl-parse-event-expression-2012 ()
    :result (vl-evatomlist-p val)
    :resultp-of-nil t
    :true-listp t
    :fails gracefully
    :count strong
    :prepwork ( ;; Implicitly local
               (set-ruler-extenders :all))
    :verify-guards nil
    (seq tokstream

         (when (vl-is-token? :vl-lparen)
           ;; SystemVerilog-2012 adds support for arbitrary paren nesting here.
           (:= (vl-match))
           (nested :w= (vl-parse-event-expression-2012))
           (:= (vl-match-token :vl-rparen))
           ;; BUGFIX 2017-04-20.  We used to (return subexpr) here.  That
           ;; is good enough for simple cases of extra parentheses, like
           ;;
           ;;    always @((posedge foo))
           ;;
           ;; but it doesn't correctly parse the rest of the event expression
           ;; when there are things like
           ;;
           ;;    always @(((posedge foo)) or ((posedge bar)))
           ;;
           ;; or similar.  To handle those, we don't return here but instead fall
           ;; through to the rest of the function, and flatten the subexpr into
           ;; the list as we go.
           )

         (unless nested
           (edge := (vl-parse-optional-edge-identifier))
           (expr := (vl-parse-expression)))

         (when (vl-is-token? :vl-kwd-iff)
           ;; We don't have anywhere in our parse tree structures yet to put the
           ;; IFF part yet.
           (return-raw
            (vl-parse-error "BOZO need to implement event_expressions with 'iff' clauses.")))
         (when (vl-is-some-token? '(:vl-kwd-or :vl-comma))
           (:= (vl-match))
           (rest := (vl-parse-event-expression-2012)))
         (return (if nested
                     (append nested rest)
                   (cons (make-vl-evatom :type edge
                                         :expr expr)
                         rest))))
    ///
    (defthm consp-of-vl-parse-event-expression-2012
      (b* (((mv ?err val ?tokstream) (vl-parse-event-expression-2012)))
        (equal (consp val)
               (not err))))
    (verify-guards vl-parse-event-expression-2012-fn)))

(defparser vl-parse-event-expression ()
  :result (vl-evatomlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         (ret := (vl-parse-event-expression-2005))
         (return ret))
       (ret := (vl-parse-event-expression-2012))
       (return ret))
  ///
  (defthm consp-of-vl-parse-event-expression
    (b* (((mv ?err val ?tokstream) (vl-parse-event-expression)))
      (equal (consp val)
             (not err)))))



; SystemVerilog-2012 addition:
;
; clocking_event ::= '@' identifier
;                  | '@' '(' event_expression ')'

(defparser vl-parse-clocking-event ()
  :result (vl-evatomlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-atsign))
       (when (vl-is-token? :vl-idtoken)
         (id := (vl-match))
         (return (list (make-vl-evatom :type :vl-noedge
                                       :expr (vl-idexpr (vl-idtoken->name id))))))
       (:= (vl-match-token :vl-lparen))
       (evatoms := (vl-parse-event-expression))
       (:= (vl-match-token :vl-rparen))
       (return evatoms))
  ///
  (defthm consp-of-vl-parse-clocking-event
    (b* (((mv ?err val ?tokstream) (vl-parse-clocking-event)))
      (equal (consp val)
             (not err)))))


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
