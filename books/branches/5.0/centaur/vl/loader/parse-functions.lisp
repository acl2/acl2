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
(include-book "parse-blockitems")
(include-book "parse-ports")
(include-book "parse-statements")
(local (include-book "../util/arithmetic"))


; function_range_or_type ::= ['signed'] range
;                          | 'integer'
;                          | 'real'
;                          | 'realtime'
;                          | 'time'

(defparser vl-parse-optional-function-range-or-type (tokens warnings)
  :result (and (consp val)
               (vl-funtype-p (car val))
               (vl-maybe-range-p (cdr val)))
  :fails gracefully
  :count weak
  (seqw tokens warnings
        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time))
          (vartype-token := (vl-match-some-token '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time)))
          (return (cons (case (vl-token->type vartype-token)
                          (:vl-kwd-integer  :vl-integer)
                          (:vl-kwd-real     :vl-real)
                          (:vl-kwd-realtime :vl-realtime)
                          (:vl-kwd-time     :vl-time))
                        nil)))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match-token :vl-kwd-signed)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (return (cons (if signed :vl-signed :vl-unsigned) range))))



; tf_input_declaration ::= 'input' [ 'reg' ] [ 'signed' ] [ range ] list_of_port_identifiers
;                        | 'input' task_port_type list_of_port_identifiers
;
; task_port_type ::= 'integer' | 'real' | 'realtime' | 'time'
;
; list_of_port_identifier ::= identifier { ',' identifier }

(defsection vl-build-function-inputs

  (defund vl-build-function-inputs (atts type range names)
    (declare (xargs :guard (and (vl-atts-p atts)
                                (vl-funtype-p type)
                                (vl-maybe-range-p range)
                                (vl-idtoken-list-p names))))
    (if (atom names)
        nil
      (cons (make-vl-funinput :name  (vl-idtoken->name (car names))
                              :type  type
                              :range range
                              :atts  atts
                              :loc   (vl-token->loc (car names)))
            (vl-build-function-inputs atts type range (cdr names)))))

  (local (in-theory (enable vl-build-function-inputs)))

  (defthm vl-funinputlist-p-of-vl-build-function-inputs
    (implies (and (force (vl-atts-p atts))
                  (force (vl-funtype-p type))
                  (force (vl-maybe-range-p range))
                  (force (vl-idtoken-list-p names)))
             (vl-funinputlist-p (vl-build-function-inputs atts type range names)))))


(defparser vl-parse-function-input-declaration (atts tokens warnings)
  ;; Matches tf_input_declaration, for functions.
  :guard (vl-atts-p atts)
  :result (vl-funinputlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-input))
        (when (vl-is-token? :vl-kwd-reg)
          (reg := (vl-match-token :vl-kwd-reg)))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match-token :vl-kwd-signed)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time))
          (type := (vl-match-some-token '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time))))
        (names := (vl-parse-1+-identifiers-separated-by-commas))
        (return-raw
         (if (and type (or reg signed range))
             (vl-parse-error "Function input declarations cannot have ~
                              variable types with reg/signed keywords or ~
                              ranges.")
           (let ((ret (vl-build-function-inputs
                       atts
                       (case type
                         (:vl-kwd-integer  :vl-integer)
                         (:vl-kwd-real     :vl-real)
                         (:vl-kwd-realtime :vl-realtime)
                         (:vl-kwd-time     :vl-time)
                         (otherwise
                          ;; BOZO Question: does the reg keyword actually do
                          ;; anything?  I think the answer is "no."  I haven't
                          ;; been able to see a difference resulting from
                          ;; saying "input reg v" versus "input v" for
                          ;; functions.  But But I have no justification for
                          ;; this.  A quick internet search revealed nothing.
                          ;; I don't know who would know what the answer is.
                          (if signed
                              :vl-signed
                            :vl-unsigned)))
                       range names)))
             (mv nil ret tokens warnings))))))



; function_port_list ::= { attribute_instance } tf_input_declaration
;                              { ',' { attribute_instance } tf_input_declaration }

(defparser vl-parse-function-port-list (tokens warnings)
  :result (vl-funinputlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (ins1 := (vl-parse-function-input-declaration atts))
        (unless (vl-is-token? :vl-comma)
          (return ins1))
        (:= (vl-match-token :vl-comma))
        (ins2 := (vl-parse-function-port-list))
        (return (append ins1 ins2))))


; function_item_declaration ::= block_item_declaration
;                             | { attribute_instance } tf_input_declaration ';'

(defsection vl-funinput-or-blockitem-p

  (defund vl-funinput-or-blockitem-p (x)
    (declare (xargs :guard t))
    (or (vl-funinput-p x)
        (vl-blockitem-p x)))

  (deflist vl-funinput-or-blockitem-list-p (x)
    (vl-funinput-or-blockitem-p x)
    :guard t
    :elementp-of-nil nil)

  (local (in-theory (enable vl-funinput-or-blockitem-p)))

  (defthm vl-funinput-or-blockitem-list-p-when-vl-funinputlist-p
    (implies (vl-funinputlist-p x)
             (vl-funinput-or-blockitem-list-p x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-funinput-or-blockitem-list-p-when-vl-blockitemlist-p
    (implies (vl-blockitemlist-p x)
             (vl-funinput-or-blockitem-list-p x))
    :hints(("Goal" :induct (len x))))

  (local (defthm crock
           (implies (vl-funinput-or-blockitem-p x)
                    (equal (vl-funinput-p x)
                           (eq (tag x) :vl-funinput)))
           :hints(("Goal" :in-theory (enable vl-blockitem-p)))))

  (defund vl-filter-funinput-or-blockitem-list (x)
    (declare (xargs :guard (vl-funinput-or-blockitem-list-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-funinputs cdr-blockitems)
          (vl-filter-funinput-or-blockitem-list (cdr x))))
      (if (eq (tag (car x)) :vl-funinput)
          (mv (cons (car x) cdr-funinputs)
              cdr-blockitems)
        (mv cdr-funinputs (cons (car x) cdr-blockitems)))))

  (defthm vl-filter-funinput-or-blockitem-list-basics
    (implies (force (vl-funinput-or-blockitem-list-p x))
             (let ((ret (vl-filter-funinput-or-blockitem-list x)))
               (and (vl-funinputlist-p (mv-nth 0 ret))
                    (vl-blockitemlist-p (mv-nth 1 ret)))))
    :hints(("Goal" :in-theory (enable vl-filter-funinput-or-blockitem-list)))))



(defparser vl-parse-function-item-declaration-noatts (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-funinput-or-blockitem-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-input)
          (decls := (vl-parse-function-input-declaration atts tokens warnings))
          (:= (vl-match-token :vl-semi))
          (return decls))
        (decls := (vl-parse-block-item-declaration-noatts atts tokens warnings))
        (return decls)))

(defparser vl-parse-function-item-declaration (tokens warnings)
  :result (vl-funinput-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-function-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-function-item-declarations (tokens warnings)
  ;; Tries to eat as many function items as it can find.
  ;; We use backtracking to know when to stop, because these declarations can be
  ;; followed by arbitrary statements, hence it's not clear whether (* ... *) is
  ;; the start of a new block item declaration or a statement.
  :result (vl-funinput-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (mv-let (erp first explore new-warnings)
    (vl-parse-function-item-declaration)
    (cond (erp
           (mv nil nil tokens warnings))
          (t
           (mv-let (erp rest tokens warnings)
             (vl-parse-0+-function-item-declarations explore new-warnings)
             (declare (ignore erp))
             (mv nil (append first rest) tokens warnings))))))



; function_declaration ::=
;
;    'function' [ 'automatic' ] [ function_range_or_type ]              ; variant 1
;      identifier ';'
;      function_item_declaration { function_item_declaration }
;      statement
;    'endfunction'
;
;
;  | 'function' [ 'automatic' ] [ function_range_or_type ]              ; variant 2
;     identifier '(' function_port_list ')' ';'
;     { block_item_declaration }
;     statement
;    'endfunction'

(defparser vl-parse-function-declaration (atts tokens warnings)
  ;; Returns a (singleton) list of function decls instead of a just a function
  ;; declaration, to fit nicely into vl-parse-module-or-generate-item.
  :guard (vl-atts-p atts)
  :result (vl-fundecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings

        (function := (vl-match-token :vl-kwd-function))
        (when (vl-is-token? :vl-kwd-automatic)
          (automatic := (vl-match-token :vl-kwd-automatic)))
        ((rtype . rrange) := (vl-parse-optional-function-range-or-type))
        (name := (vl-match-token :vl-idtoken))

        (when (vl-is-token? :vl-semi)
          ;; Variant 1.
          (:= (vl-match-token :vl-semi))
          (decls := (vl-parse-0+-function-item-declarations))
          (stmt := (vl-parse-statement))
          (:= (vl-match-token :vl-kwd-endfunction))
          (return-raw
           (b* (((mv funinputs blockitems)
                 (vl-filter-funinput-or-blockitem-list decls))
                ((unless (consp funinputs))
                 (vl-parse-error "Function has no inputs."))
                (ret (make-vl-fundecl :name       (vl-idtoken->name name)
                                      :automaticp (if automatic t nil)
                                      :rtype      rtype
                                      :rrange     rrange
                                      :inputs     funinputs
                                      :decls      blockitems
                                      :body       stmt
                                      :atts       atts
                                      :loc        (vl-token->loc function))))
             (mv nil (list ret) tokens warnings))))

        ;; Variant 2.
        (:= (vl-match-token :vl-lparen))
        (funinputs := (vl-parse-function-port-list))
        (:= (vl-match-token :vl-rparen))
        (:= (vl-match-token :vl-semi))
        (blockitems := (vl-parse-0+-block-item-declarations))
        (stmt := (vl-parse-statement))
        (:= (vl-match-token :vl-kwd-endfunction))
        (return
         (list (make-vl-fundecl :name       (vl-idtoken->name name)
                                :automaticp (if automatic t nil)
                                :rtype      rtype
                                :rrange     rrange
                                :inputs     funinputs
                                :decls      blockitems
                                :body       stmt
                                :atts       atts
                                :loc        (vl-token->loc function))))))

