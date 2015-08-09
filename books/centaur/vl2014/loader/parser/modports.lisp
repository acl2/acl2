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
; Original author: (this book) Sol Swords <sswords@centtech.com>
;                  (framework) Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "utils")
(include-book "../../parsetree")
(include-book "expressions")
(include-book "datatypes")
(include-book "functions")
(local (include-book "../../util/arithmetic"))




(defparser vl-parse-simple-modport-port (dir atts)
  :guard (and (vl-direction-p dir)
              (vl-atts-p atts))
  :result (vl-modport-port-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (loc := (vl-current-loc))
        (unless (vl-is-token? :vl-dot)
          (name := (vl-match-token :vl-idtoken))
          (return (make-vl-modport-port :name (vl-idtoken->name name)
                                        :dir dir
                                        :expr (vl-idexpr (vl-idtoken->name name) nil nil)
                                        :atts atts
                                        :loc loc)))
        (:= (vl-match))
        (name := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (unless (vl-is-token? :vl-rparen)
          (expr := (vl-parse-expression)))

        (:= (vl-match-token :vl-rparen))
        (return (make-vl-modport-port :name (vl-idtoken->name name)
                                      :dir dir
                                      :expr expr
                                      :atts atts
                                      :loc loc))))


(local (defthm len-cdr
         (<= (len (cdr x)) (len x))
         :rule-classes :linear))

(defparser vl-parse-1+-simple-modport-ports (dir atts)
  :guard (and (vl-direction-p dir)
              (vl-atts-p atts))
  :result (vl-modport-portlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (port1 := (vl-parse-simple-modport-port dir atts))
        (unless (vl-is-token? :vl-comma)
          (return (list port1)))
        ;; use backtracking to know when to stop, i.e. we see a keyword instead of
        ;; an identifier or .identifier(expr)
        (return-raw
         (seq-backtrack tokstream
                         ((:= (vl-match))
                          (ports2 := (vl-parse-1+-simple-modport-ports dir atts))
                          (return (cons port1 ports2)))
                         ((return (list port1)))))))

;; function_prototype ::= function data_type_or_void function_identifier [ ( [ tf_port_list ] ) ]
(defparser vl-parse-function-prototype ()
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-function))
        (:= (vl-parse-datatype-or-void))
        (:= (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        ;; should really be vl-parse-tf-port-list
        (:= (vl-parse-taskport-list))
        (:= (vl-match-token :vl-rparen))
        (return nil)))

(defparser vl-parse-task-prototype ()
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-task))
        (:= (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match))
          ;; should really be vl-parse-tf-port-list
          (:= (vl-parse-taskport-list))
          (:= (vl-match-token :vl-rparen)))
        (return nil)))

(defparser vl-parse-method-prototype ()
  :resultp-of-nil t
  :fails :gracefully
  :count strong
  (seq-backtrack tokstream
                  ((return-raw (vl-parse-function-prototype)))
                  ((return-raw (vl-parse-task-prototype)))))

(defparser vl-parse-modport-tf-port ()
  :resultp-of-nil t
  :fails :gracefully
  :count strong
  (seq-backtrack tokstream
                  ((return-raw (vl-parse-method-prototype)))
                  ((:= (vl-match-token :vl-idtoken))
                   (return nil))))


(defparser vl-parse-modport-port ()
  :result (vl-modport-portlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (when (vl-is-some-token? *vl-directions-kwds*)
          (dir := (vl-match-some-token *vl-directions-kwds*))
          (ports := (vl-parse-1+-simple-modport-ports
                     (cdr (assoc-eq (vl-token->type dir)
                                    *vl-directions-kwd-alist*))
                     atts))
          (return ports))
        (when (vl-is-some-token? '(:vl-kwd-import :vl-kwd-export))
          (:= (vl-match))
          (:= (vl-parse-modport-tf-port))
          (:= (vl-parse-warning
               :vl-warn-modport-tf
               "Tasks and functions in modports are not yet implemented."))
          (return nil))
        (when (vl-is-token? :vl-kwd-clocking)
          (:= (vl-match))
          (:= (vl-match-token :vl-idtoken))
          (:= (vl-parse-warning
               :vl-warn-modport-clocking
               "Clocking in modports is not yet implemented."))
          (return nil))
        (return-raw
         (vl-parse-error "Invalid modport port."))))

(defparser vl-parse-1+-modport-ports ()
  :result (vl-modport-portlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (ports1 := (vl-parse-modport-port))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (ports2 := (vl-parse-1+-modport-ports))
          (return (append-without-guard ports1 ports2)))
        (return ports1)))



;; modport_item ::= modport_identifier ( modport_ports_declaration { , modport_ports_declaration } )

(defparser vl-parse-modport-item (atts)
  :guard (vl-atts-p atts)
  :result (vl-modport-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (loc := (vl-current-loc))
        (name := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (ports := (vl-parse-1+-modport-ports))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-modport :name (vl-idtoken->name name)
                                 :ports ports
                                 :atts  atts
                                 :loc loc))))


;; modport_declaration ::= modport modport_item { , modport_item } ;

(defparser vl-parse-1+-modport-items (atts)
  :guard (vl-atts-p atts)
  :result (vl-modportlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (port1 := (vl-parse-modport-item atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (ports2 := (vl-parse-1+-modport-items atts))
          (return (cons port1 ports2)))
        (:= (vl-match-token :vl-semi))
        (return (list port1))))

(defparser vl-parse-modport-decl (atts)
  :guard (vl-atts-p atts)
  :result (vl-modportlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-modport))
        (modports := (vl-parse-1+-modport-items atts))
        (return modports)))
