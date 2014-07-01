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
(include-book "ranges")
(local (include-book "../../util/arithmetic"))



; BOZO haven't looked at any of this for SystemVerilog

; Parameters.
;
; local_parameter_declaration ::=
;    'localparam' ['signed'] [range] list_of_param_assignments
;  | 'localparam' parameter_type list_of_param_assignments
;
; parameter_declaration ::=
;    'parameter' ['signed'] [range] list_of_param_assignments
;  | 'parameter' parameter_type list_of_param_assignments
;
; parameter_type ::=
;    'integer' | 'real' | 'realtime' | 'time'
;
; list_of_param_assignments ::= param_assignment { ',' param_assignment }
;
; param_assignment ::=
;    identifier = mintypmax_expression

(defaggregate vl-param-assignment-tuple
  (loc name expr)
  :tag :vl-param-assignment-tuple
  :legiblep nil
  :require ((vl-location-p-of-vl-param-assignment-tuple->loc (vl-location-p loc))
            (stringp-of-vl-param-assignment-tuple->name      (stringp name))
            (vl-expr-p-of-vl-param-assignment-tuple->expr    (vl-expr-p expr)))
  :parents (parser))

(deflist vl-param-assignment-tuple-list-p (x)
  (vl-param-assignment-tuple-p x)
  :elementp-of-nil nil)

(defund vl-build-paramdecls (tuples type localp range atts)
  (declare (xargs :guard (and (vl-param-assignment-tuple-list-p tuples)
                              (vl-paramdecltype-p type)
                              (booleanp localp)
                              (vl-maybe-range-p range)
                              (vl-atts-p atts))))
  (if (consp tuples)
      (cons (make-vl-paramdecl
             :loc (vl-param-assignment-tuple->loc (car tuples))
             :name (vl-param-assignment-tuple->name (car tuples))
             :expr (vl-param-assignment-tuple->expr (car tuples))
             :type type
             :localp localp
             :range range
             :atts atts)
            (vl-build-paramdecls (cdr tuples) type localp range atts))
    nil))

(defthm vl-paramdecllist-p-of-vl-build-paramdecls
  (implies (and (force (vl-param-assignment-tuple-list-p tuples))
                (force (vl-paramdecltype-p type))
                (force (booleanp localp))
                (force (vl-maybe-range-p range))
                (force (vl-atts-p atts)))
           (vl-paramdecllist-p (vl-build-paramdecls tuples type localp range atts)))
  :hints(("Goal" :in-theory (enable vl-build-paramdecls))))

(defparser vl-parse-param-assignment ()
  :result (vl-param-assignment-tuple-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-equalsign))
        (expr := (vl-parse-mintypmax-expression))
        (return (vl-param-assignment-tuple (vl-token->loc id)
                                           (vl-idtoken->name id)
                                           expr))))

(defparser vl-parse-list-of-param-assignments ()
  :result (vl-param-assignment-tuple-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-param-assignment))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-param-assignments)))
        (return (cons first rest))))

(defparser vl-parse-param-or-localparam-declaration (atts types)
  :guard (and (vl-atts-p atts)
              ;; Types says what kinds (local or nonlocal) of parameters we permit
              (true-listp types)
              (subsetp types '(:vl-kwd-parameter :vl-kwd-localparam)))
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (start := (vl-match-some-token types))
        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-real
                                                   :vl-kwd-realtime :vl-kwd-time))
          (type := (vl-match))
          (tuples := (vl-parse-list-of-param-assignments))
          (return
           (let ((type    (case (vl-token->type type)
                            (:vl-kwd-integer  :vl-integer)
                            (:vl-kwd-real     :vl-real)
                            (:vl-kwd-realtime :vl-realtime)
                            (:vl-kwd-time     :vl-time)))
                 (localp  (eq (vl-token->type start) :vl-kwd-localparam)))
             (vl-build-paramdecls tuples type localp nil atts))))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (tuples := (vl-parse-list-of-param-assignments))
        (return
         (let ((localp  (eq (vl-token->type start) :vl-kwd-localparam)))
           (vl-build-paramdecls tuples
                                (if signed :vl-signed :vl-plain)
                                localp range atts)))))
