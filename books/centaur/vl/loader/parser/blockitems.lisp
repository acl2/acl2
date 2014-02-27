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




;                      PARSING BLOCK ITEM DECLARATIONS
;
; Regs and variables.
;
; Filtering out some duplication and indirection, we have:
;
; integer_declaration  ::= 'integer'  list_of_variable_identifiers ';'
; real_declaration     ::= 'real'     list_of_variable_identifiers ';'
; time_declaration     ::= 'time'     list_of_variable_identifiers ';'
; realtime_declaration ::= 'realtime' list_of_variable_identifiers ';'
;
; reg_declaration      ::=
;   'reg' [ 'signed' ] [ range ] list_of_variable_identifiers ';'
;
; list_of_variable_identifiers ::=
;    variable_type { ',' variable_type }
;
; variable_type ::=
;    identifier { range }
;  | identifier '=' expression

(defun vl-vardecl-tuple-p (x)
  (declare (xargs :guard t))
  (and (tuplep 3 x)
       (stringp (first x))
       (vl-rangelist-p (second x))
       (vl-maybe-expr-p (third x))))

(defun vl-vardecl-tuple-list-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (vl-vardecl-tuple-p (car x))
           (vl-vardecl-tuple-list-p (cdr x)))
    t))

(defund vl-build-vardecls (loc type atts tuples)
  (declare (xargs :guard (and (vl-location-p loc)
                              (vl-vardecltype-p type)
                              (vl-atts-p atts)
                              (vl-vardecl-tuple-list-p tuples))))
  (if (consp tuples)
      (cons (make-vl-vardecl :loc loc
                             :name (first (car tuples))
                             :type type
                             :arrdims (second (car tuples))
                             :initval (third (car tuples))
                             :atts atts)
            (vl-build-vardecls loc type atts (cdr tuples)))
    nil))

(defund vl-build-regdecls (loc signedp range atts tuples)
  (declare (xargs :guard (and (vl-location-p loc)
                              (booleanp signedp)
                              (vl-maybe-range-p range)
                              (vl-atts-p atts)
                              (vl-vardecl-tuple-list-p tuples))))
  (if (consp tuples)
      (cons (make-vl-regdecl :loc loc
                             :name (first (car tuples))
                             :signedp signedp
                             :range range
                             :arrdims (second (car tuples))
                             :initval (third (car tuples))
                             :atts atts)
            (vl-build-regdecls loc signedp range atts (cdr tuples)))
    nil))

(defthm vl-vardecllist-p-of-vl-build-vardecls
  (implies (and (force (vl-location-p loc))
                (force (vl-vardecltype-p type))
                (force (vl-atts-p atts))
                (force (vl-vardecl-tuple-list-p tuples)))
           (vl-vardecllist-p (vl-build-vardecls loc type atts tuples)))
  :hints(("Goal" :in-theory (enable vl-build-vardecls))))

(defthm vl-regdecllist-p-of-vl-build-regdecls
  (implies (and (force (vl-location-p loc))
                (force (booleanp signedp))
                (force (vl-maybe-range-p range))
                (force (vl-atts-p atts))
                (force (vl-vardecl-tuple-list-p tuples)))
           (vl-regdecllist-p (vl-build-regdecls loc signedp range atts tuples)))
  :hints(("Goal" :in-theory (enable vl-build-regdecls))))

(defparser vl-parse-variable-type ()
  :result (vl-vardecl-tuple-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-equalsign)
          (:= (vl-match))
          (expr := (vl-parse-expression))
          (return (list (vl-idtoken->name id) nil expr)))
        (arrdims := (vl-parse-0+-ranges))
        (return (list (vl-idtoken->name id) arrdims nil))))

(defparser vl-parse-list-of-variable-identifiers ()
  :result (vl-vardecl-tuple-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-variable-type))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-variable-identifiers)))
        (return (cons first rest))))

(defparser vl-parse-integer-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-integer))
        (tuples := (vl-parse-list-of-variable-identifiers))
        (semi := (vl-match-token :vl-semi))
        (return (vl-build-vardecls (vl-token->loc kwd) :vl-integer atts tuples))))

(defparser vl-parse-real-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-real))
        (tuples := (vl-parse-list-of-variable-identifiers))
        (semi := (vl-match-token :vl-semi))
        (return (vl-build-vardecls (vl-token->loc kwd) :vl-real atts tuples))))

(defparser vl-parse-time-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-time))
        (tuples := (vl-parse-list-of-variable-identifiers))
        (semi := (vl-match-token :vl-semi))
        (return (vl-build-vardecls (vl-token->loc kwd) :vl-time atts tuples))))

(defparser vl-parse-realtime-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-realtime))
        (tuples := (vl-parse-list-of-variable-identifiers))
        (semi := (vl-match-token :vl-semi))
        (return (vl-build-vardecls (vl-token->loc kwd) :vl-realtime atts tuples))))

(defparser vl-parse-reg-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-regdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-reg))
        (when (vl-is-token? :vl-kwd-signed)
          (:= (vl-match))
          (signedp := (mv nil t tokens warnings)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (tuples := (vl-parse-list-of-variable-identifiers))
        (semi := (vl-match-token :vl-semi))
        (return (vl-build-regdecls (vl-token->loc kwd) signedp range atts tuples))))




; Events.
;
; event_declaration ::=
;    'event' list_of_event_identifiers ';'
;
; list_of_event_identifiers ::=
;    identifier {range} { ',' identifier {range} }

(defparser vl-parse-list-of-event-identifiers (atts)
  :guard (vl-atts-p atts)
  :result (vl-eventdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (arrdims := (vl-parse-0+-ranges))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-event-identifiers atts)))
        (return (cons (make-vl-eventdecl :loc (vl-token->loc id)
                                         :name (vl-idtoken->name id)
                                         :arrdims arrdims
                                         :atts atts)
                      rest))))

(defparser vl-parse-event-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-eventdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-event))
        (ret := (vl-parse-list-of-event-identifiers atts))
        (semi := (vl-match-token :vl-semi))
        (return ret)))




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




; Now we get to block items, themselves.
;
; block_item_declaration ::=
;    {attribute_instance} 'reg' ['signed'] [range] list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'integer' list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'time' list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'real' list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'realtime' list_of_block_variable_identifiers ';'
;  | {attribute_instance} event_declaration
;  | {attribute_instance} local_parameter_declaration ';'
;  | {attribute_instance} parameter_declaration ';'
;
; list_of_block_variable_identifiers ::=
;    block_variable_type { ',' block_variable_type }
;
; block_variable_type ::= identifier { dimension }
;
;
; Of particular note is that the rules for reg, integer, time, real, and
; realtime above are different than reg_declaration, integer_declaration, etc.,
; using list_of_block_variable_identifiers versus list_of_variable_identifiers.
; Comparing these, we see that the only difference is that these declarations
; are not allowed to have initial values assigned to them.  That is, "reg foo =
; 1" is okay as a module item, but not as a block item.
;
; With this in mind, our approach is to reuse our parsers above and simply walk
; through to ensure that none of the variables have been given initial values.

(defund vl-find-regdecl-with-initval (x)
  (declare (xargs :guard (vl-regdecllist-p x)))
  (if (consp x)
      (if (vl-regdecl->initval (car x))
          (car x)
        (vl-find-regdecl-with-initval (cdr x)))
    nil))

(defund vl-find-vardecl-with-initval (x)
  (declare (xargs :guard (vl-vardecllist-p x)))
  (if (consp x)
      (if (vl-vardecl->initval (car x))
          (car x)
        (vl-find-vardecl-with-initval (cdr x)))
    nil))


(defparser vl-parse-block-item-declaration-noatts (atts)
  :guard (vl-atts-p atts)
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (type := (mv nil
                     (and (consp tokens) (vl-token->type (car tokens)))
                     tokens warnings))
        (elements := (case type
                       (:vl-kwd-reg      (vl-parse-reg-declaration atts))
                       (:vl-kwd-integer  (vl-parse-integer-declaration atts))
                       (:vl-kwd-time     (vl-parse-time-declaration atts))
                       (:vl-kwd-real     (vl-parse-real-declaration atts))
                       (:vl-kwd-realtime (vl-parse-realtime-declaration atts))
                       (:vl-kwd-event    (vl-parse-event-declaration atts))
                       ((:vl-kwd-localparam :vl-kwd-parameter)
                        ;; Bug found on 2011-08-26 here.  We forgot to eat the
                        ;; semicolon, before.  This fix is ugly, since the
                        ;; other cases above do their own semicolon-handling,
                        ;; but we don't want the param parser to eat the semi
                        ;; because, e.g., a module_parameter_port_list has
                        ;; parameter declarations separated by commas instead.
                        (seqw tokens warnings
                              (elems := (vl-parse-param-or-localparam-declaration
                                         atts
                                         '(:vl-kwd-localparam
                                           :vl-kwd-parameter)))
                              (:= (vl-match-token :vl-semi))
                              (return elems)))
                       (t
                        (vl-parse-error "Invalid block item."))))
        (return-raw
         (let ((search (case type
                         (:vl-kwd-reg
                          (vl-find-regdecl-with-initval elements))
                         ((:vl-kwd-integer :vl-kwd-time :vl-kwd-real
                                           :vl-kwd-realtime)
                          (vl-find-vardecl-with-initval elements))
                         (t
                          nil))))
           (if search
               (vl-parse-error "Block item declarations are not allowed to have ~
                               initial values.")
             (mv nil elements tokens warnings))))))


(defparser vl-parse-block-item-declaration ()
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-block-item-declarations ()
  ;; Tries to eat as many block items as it can find.
  ;; We use backtracking to know when to stop, because these declarations can be
  ;; followed by arbitrary statements, hence it's not clear whether (* ... *) is
  ;; the start of a new block item declaration or a statement.
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (b* (((mv erp first explore new-warnings) (vl-parse-block-item-declaration))
       ((when erp)
        (mv nil nil tokens warnings))
       ((mv ?erp rest tokens warnings)
        (vl-parse-0+-block-item-declarations :tokens explore
                                             :warnings new-warnings)))
    (mv nil (append first rest) tokens warnings)))

