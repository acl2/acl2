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
(include-book "parse-ranges")
(local (include-book "../util/arithmetic"))




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

(defparser vl-parse-variable-type (tokens warnings)
  :result (vl-vardecl-tuple-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-equalsign)
          (:= (vl-match-token :vl-equalsign))
          (expr := (vl-parse-expression))
          (return (list (vl-idtoken->name id) nil expr)))
        (arrdims := (vl-parse-0+-ranges))
        (return (list (vl-idtoken->name id) arrdims nil))))

(defparser vl-parse-list-of-variable-identifiers (tokens warnings)
  :result (vl-vardecl-tuple-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-variable-type))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-variable-identifiers)))
        (return (cons first rest))))

(defparser vl-parse-integer-declaration (atts tokens warnings)
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

(defparser vl-parse-real-declaration (atts tokens warnings)
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

(defparser vl-parse-time-declaration (atts tokens warnings)
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

(defparser vl-parse-realtime-declaration (atts tokens warnings)
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

(defparser vl-parse-reg-declaration (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-regdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (kwd := (vl-match-token :vl-kwd-reg))
        (when (vl-is-token? :vl-kwd-signed)
          (:= (vl-match-token :vl-kwd-signed))
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

(defparser vl-parse-list-of-event-identifiers (atts tokens warnings)
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
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-event-identifiers atts tokens)))
        (return (cons (make-vl-eventdecl :loc (vl-token->loc id)
                                         :name (vl-idtoken->name id)
                                         :arrdims arrdims
                                         :atts atts)
                      rest))))

(defparser vl-parse-event-declaration (atts tokens warnings)
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

(defparser vl-parse-param-assignment (tokens warnings)
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

(defparser vl-parse-list-of-param-assignments (tokens warnings)
  :result (vl-param-assignment-tuple-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-param-assignment))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-param-assignments)))
        (return (cons first rest))))

(defparser vl-parse-param-or-localparam-declaration (atts types tokens warnings)
  :guard (and (vl-atts-p atts)
              ;; Types says what kinds (local or nonlocal) of parameters we permit
              (true-listp types)
              (subsetp types '(:vl-kwd-parameter :vl-kwd-localparam)))
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (let ((parameter-types '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time)))
    (seqw tokens warnings
          (start := (vl-match-some-token types))
          (when (vl-is-some-token? parameter-types)
            (type := (vl-match-some-token parameter-types))
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
            (signed := (vl-match-token :vl-kwd-signed)))
          (when (vl-is-token? :vl-lbrack)
            (range := (vl-parse-range)))
          (tuples := (vl-parse-list-of-param-assignments))
          (return
           (let ((localp  (eq (vl-token->type start) :vl-kwd-localparam)))
             (vl-build-paramdecls tuples
                                  (if signed :vl-signed :vl-plain)
                                  localp range atts))))))




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


(defparser vl-parse-block-item-declaration-noatts (atts tokens warnings)
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
                              (elems := (vl-parse-param-or-localparam-declaration atts
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


(defparser vl-parse-block-item-declaration (tokens warnings)
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-block-item-declarations (tokens warnings)
  ;; Tries to eat as many block items as it can find.
  ;; We use backtracking to know when to stop, because these declarations can be
  ;; followed by arbitrary statements, hence it's not clear whether (* ... *) is
  ;; the start of a new block item declaration or a statement.
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (mv-let (erp first explore new-warnings)
          (vl-parse-block-item-declaration)
          (cond (erp
                 (mv nil nil tokens warnings))
                (t
                 (mv-let (erp rest tokens warnings)
                         (vl-parse-0+-block-item-declarations explore new-warnings)
                         (declare (ignore erp))
                         (mv nil (append first rest) tokens warnings))))))







(local
 (encapsulate ()

   (local (include-book "lexer/lexer"))

   (program)

   (defun test-vardecls-fn (vars type atts names arrdims initvals)
     (if (atom vars)
         (and (atom names)
              (atom arrdims)
              (atom initvals))
       (debuggable-and (consp names)
                       (consp arrdims)
                       (consp initvals)
                       (not (cw "Inspecting ~x0.~%" (car vars)))
                       (vl-vardecl-p (car vars))
                       (equal type          (vl-vardecl->type (car vars)))
                       (equal atts          (vl-vardecl->atts (car vars)))
                       (equal (car names)   (vl-vardecl->name (car vars)))
                       (equal (car arrdims) (vl-pretty-range-list (vl-vardecl->arrdims (car vars))))
                       (if (car initvals)
                           (debuggable-and (vl-vardecl->initval (car vars))
                                           (equal (car initvals)
                                                  (vl-pretty-expr (vl-vardecl->initval (car vars)))))
                         (not (vl-vardecl->initval (car vars))))
                       (test-vardecls-fn (cdr vars) type atts (cdr names) (cdr arrdims) (cdr initvals)))))

   (defmacro test-parse-integer-declaration (&key input atts names arrdims initvals (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-integer-declaration ',atts tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (not ,successp)
                                    (equal warnings 'blah-warnings)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-vardecls-fn val :vl-integer ',atts
                                                    ',names ',arrdims ',initvals))))))))

   (defmacro test-parse-real-declaration (&key input atts names arrdims initvals (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-real-declaration ',atts tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (not ,successp)
                                    (equal warnings 'blah-warnings)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-vardecls-fn val :vl-real ',atts
                                                    ',names ',arrdims ',initvals))))))))

   (defmacro test-parse-time-declaration (&key input atts names arrdims initvals (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-time-declaration ',atts tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (not ,successp)
                                    (equal warnings 'blah-warnings)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-vardecls-fn val :vl-time ',atts
                                                    ',names ',arrdims ',initvals))))))))

   (defmacro test-parse-realtime-declaration (&key input atts names arrdims initvals (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-realtime-declaration ',atts tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (not ,successp)
                                    (equal warnings 'blah-warnings)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-vardecls-fn val :vl-realtime ',atts
                                                    ',names ',arrdims ',initvals))))))))



   (test-parse-integer-declaration :input "integer a, ; "
                                   :successp nil)

   (test-parse-integer-declaration :input "integer ; "
                                   :successp nil)

   (test-parse-integer-declaration :input "integer a = "
                                   :successp nil)

   (test-parse-integer-declaration :input "integer a = ; "
                                   :successp nil)

   (test-parse-integer-declaration :input "integer a ; "
                                   :atts (("some") ("atts"))
                                   :names ("a")
                                   :arrdims (nil)
                                   :initvals (nil))

   (test-parse-integer-declaration :input "integer a, b, c; "
                                   :atts (("some") ("atts"))
                                   :names ("a" "b" "c")
                                   :arrdims (nil nil nil)
                                   :initvals (nil nil nil))

   (test-parse-integer-declaration :input "integer a[1:2], b, c; "
                                   :atts (("some") ("atts"))
                                   :names ("a" "b" "c")
                                   :arrdims (((range 1 2)) nil nil)
                                   :initvals (nil nil nil))

   (test-parse-integer-declaration :input "integer a[1:2][3:4], b, c; "
                                   :atts (("some") ("atts"))
                                   :names ("a" "b" "c")
                                   :arrdims (((range 1 2) (range 3 4)) nil nil)
                                   :initvals (nil nil nil))

   (test-parse-integer-declaration :input "integer a[1:2][3:4], b = 5, c = 17 + 8; "
                                   :atts (("some") ("atts"))
                                   :names ("a" "b" "c")
                                   :arrdims (((range 1 2) (range 3 4)) nil nil)
                                   :initvals (nil 5 (:vl-binary-plus nil 17 8)))

   ;; Not allowed to have a range plus initial value.
   (test-parse-integer-declaration :input "integer a[1:2] = 17 ; "
                                   :successp nil)






   (test-parse-real-declaration :input "real a, ; "
                                :successp nil)

   (test-parse-real-declaration :input "real ; "
                                :successp nil)

   (test-parse-real-declaration :input "real a = "
                                :successp nil)

   (test-parse-real-declaration :input "real a = ; "
                                :successp nil)

   (test-parse-real-declaration :input "real a ; "
                                :atts (("some") ("atts"))
                                :names ("a")
                                :arrdims (nil)
                                :initvals (nil))

   (test-parse-real-declaration :input "real a, b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (nil nil nil)
                                :initvals (nil nil nil))

   (test-parse-real-declaration :input "real a[1:2], b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (((range 1 2)) nil nil)
                                :initvals (nil nil nil))

   (test-parse-real-declaration :input "real a[1:2][3:4], b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (((range 1 2) (range 3 4)) nil nil)
                                :initvals (nil nil nil))

   (test-parse-real-declaration :input "real a[1:2][3:4], b = 5, c = 17 + 8; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (((range 1 2) (range 3 4)) nil nil)
                                :initvals (nil 5 (:vl-binary-plus nil 17 8)))

   ;; Not allowed to have a range plus initial value.
   (test-parse-real-declaration :input "real a[1:2] = 17 ; "
                                :successp nil)






   (test-parse-time-declaration :input "time a, ; "
                                :successp nil)

   (test-parse-time-declaration :input "time ; "
                                :successp nil)

   (test-parse-time-declaration :input "time a = "
                                :successp nil)

   (test-parse-time-declaration :input "time a = ; "
                                :successp nil)

   (test-parse-time-declaration :input "time a ; "
                                :atts (("some") ("atts"))
                                :names ("a")
                                :arrdims (nil)
                                :initvals (nil))

   (test-parse-time-declaration :input "time a, b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (nil nil nil)
                                :initvals (nil nil nil))

   (test-parse-time-declaration :input "time a[1:2], b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (((range 1 2)) nil nil)
                                :initvals (nil nil nil))

   (test-parse-time-declaration :input "time a[1:2][3:4], b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (((range 1 2) (range 3 4)) nil nil)
                                :initvals (nil nil nil))

   (test-parse-time-declaration :input "time a[1:2][3:4], b = 5, c = 17 + 8; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :arrdims (((range 1 2) (range 3 4)) nil nil)
                                :initvals (nil 5 (:vl-binary-plus nil 17 8)))

   ;; Not allowed to have a range plus initial value.
   (test-parse-time-declaration :input "time a[1:2] = 17 ; "
                                :successp nil)





   (test-parse-realtime-declaration :input "realtime a, ; "
                                    :successp nil)

   (test-parse-realtime-declaration :input "realtime ; "
                                    :successp nil)

   (test-parse-realtime-declaration :input "realtime a = "
                                    :successp nil)

   (test-parse-realtime-declaration :input "realtime a = ; "
                                    :successp nil)

   (test-parse-realtime-declaration :input "realtime a ; "
                                    :atts (("some") ("atts"))
                                    :names ("a")
                                    :arrdims (nil)
                                    :initvals (nil))

   (test-parse-realtime-declaration :input "realtime a, b, c; "
                                    :atts (("some") ("atts"))
                                    :names ("a" "b" "c")
                                    :arrdims (nil nil nil)
                                    :initvals (nil nil nil))

   (test-parse-realtime-declaration :input "realtime a[1:2], b, c; "
                                    :atts (("some") ("atts"))
                                    :names ("a" "b" "c")
                                    :arrdims (((range 1 2)) nil nil)
                                    :initvals (nil nil nil))

   (test-parse-realtime-declaration :input "realtime a[1:2][3:4], b, c; "
                                    :atts (("some") ("atts"))
                                    :names ("a" "b" "c")
                                    :arrdims (((range 1 2) (range 3 4)) nil nil)
                                    :initvals (nil nil nil))

   (test-parse-realtime-declaration :input "realtime a[1:2][3:4], b = 5, c = 17 + 8; "
                                    :atts (("some") ("atts"))
                                    :names ("a" "b" "c")
                                    :arrdims (((range 1 2) (range 3 4)) nil nil)
                                    :initvals (nil 5 (:vl-binary-plus nil 17 8)))

   ;; Not allowed to have a range plus initial value.
   (test-parse-realtime-declaration :input "realtime a[1:2] = 17 ; "
                                    :successp nil)








   (defun test-regdecls-fn (regs atts signedp range names arrdims initvals)
     (if (atom regs)
         (and (atom names)
              (atom arrdims)
              (atom initvals))
       (debuggable-and (consp names)
                       (consp arrdims)
                       (consp initvals)
                       (not (cw "Inspecting ~x0.~%" (car regs)))
                       (vl-regdecl-p (car regs))
                       (equal atts          (vl-regdecl->atts (car regs)))
                       (equal signedp       (vl-regdecl->signedp (car regs)))
                       (equal range         (vl-pretty-maybe-range (vl-regdecl->range (car regs))))
                       (equal (car names)   (vl-regdecl->name (car regs)))
                       (equal (car arrdims) (vl-pretty-range-list (vl-regdecl->arrdims (car regs))))
                       (if (car initvals)
                           (debuggable-and (vl-regdecl->initval (car regs))
                                           (equal (car initvals)
                                                  (vl-pretty-expr (vl-regdecl->initval (car regs)))))
                         (not (vl-regdecl->initval (car regs))))
                       (test-regdecls-fn (cdr regs) atts signedp range (cdr names) (cdr arrdims) (cdr initvals)))))

   (defmacro test-parse-reg-declaration (&key input atts signedp range names arrdims initvals (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-reg-declaration ',atts tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (not ,successp)
                                    (equal warnings 'blah-warnings)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-regdecls-fn val ',atts ',signedp ',range
                                                    ',names ',arrdims ',initvals))))))))





   (test-parse-reg-declaration :input "reg a, ; "
                               :successp nil)

   (test-parse-reg-declaration :input "reg ; "
                               :successp nil)

   (test-parse-reg-declaration :input "reg a = "
                               :successp nil)

   (test-parse-reg-declaration :input "reg a = ; "
                               :successp nil)

   (test-parse-reg-declaration :input "reg a ; "
                               :atts (("some") ("atts"))
                               :range (no-range)
                               :signedp nil
                               :names ("a")
                               :arrdims (nil)
                               :initvals (nil))

   (test-parse-reg-declaration :input "reg signed a ; "
                               :atts (("some") ("atts"))
                               :range (no-range)
                               :signedp t
                               :names ("a")
                               :arrdims (nil)
                               :initvals (nil))

   (test-parse-reg-declaration :input "reg [1:3] a ; "
                               :atts (("some") ("atts"))
                               :range (range 1 3)
                               :signedp nil
                               :names ("a")
                               :arrdims (nil)
                               :initvals (nil))

   (test-parse-reg-declaration :input "reg signed [1:3] a ; "
                               :atts (("some") ("atts"))
                               :range (range 1 3)
                               :signedp t
                               :names ("a")
                               :arrdims (nil)
                               :initvals (nil))

   (test-parse-reg-declaration :input "reg signed [1:3] a, b, c; "
                               :atts (("some") ("atts"))
                               :names ("a" "b" "c")
                               :signedp t
                               :range (range 1 3)
                               :arrdims (nil nil nil)
                               :initvals (nil nil nil))

   (test-parse-reg-declaration :input "reg a[1:2], b, c; "
                               :atts (("some") ("atts"))
                               :names ("a" "b" "c")
                               :range (no-range)
                               :signedp nil
                               :arrdims (((range 1 2)) nil nil)
                               :initvals (nil nil nil))

   (test-parse-reg-declaration :input "reg signed a[1:2][3:4], b, c; "
                               :atts (("some") ("atts"))
                               :names ("a" "b" "c")
                               :range (no-range)
                               :signedp t
                               :arrdims (((range 1 2) (range 3 4)) nil nil)
                               :initvals (nil nil nil))

   (test-parse-reg-declaration :input "reg [7:0] a[1:2][3:4], b = 5, c = 17 + 8; "
                               :atts (("some") ("atts"))
                               :names ("a" "b" "c")
                               :range (range 7 0)
                               :signedp nil
                               :arrdims (((range 1 2) (range 3 4)) nil nil)
                               :initvals (nil 5 (:vl-binary-plus nil 17 8)))

   ;; Not allowed to have a range plus initial value.
   (test-parse-reg-declaration :input "reg a[1:2] = 17 ; "
                               :successp nil)




   (defun test-eventdecls-fn (events atts names arrdims)
     (if (atom events)
         (and (atom names)
              (atom arrdims))
       (debuggable-and (consp names)
                       (consp arrdims)
                       (not (cw "Inspecting ~x0.~%" (car events)))
                       (vl-eventdecl-p (car events))
                       (equal atts          (vl-eventdecl->atts (car events)))
                       (equal (car names)   (vl-eventdecl->name (car events)))
                       (equal (car arrdims) (vl-pretty-range-list (vl-eventdecl->arrdims (car events))))
                       (test-eventdecls-fn (cdr events) atts (cdr names) (cdr arrdims)))))

   (defmacro test-parse-event-declaration (&key input atts names arrdims (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-event-declaration ',atts tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (equal warnings 'blah-warnings)
                                    (not ,successp)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-eventdecls-fn val ',atts ',names ',arrdims))))))))


   (test-parse-event-declaration :input "event a, ; "
                                 :successp nil)

   (test-parse-event-declaration :input "event ; "
                                 :successp nil)

   (test-parse-event-declaration :input "event a = "
                                 :successp nil)

   (test-parse-event-declaration :input "event a = 1;"
                                 :successp nil)

   (test-parse-event-declaration :input "event a ; "
                                 :atts (("some") ("atts"))
                                 :names ("a")
                                 :arrdims (nil))

   (test-parse-event-declaration :input "event a, b, c ; "
                                 :atts (("some") ("atts"))
                                 :names ("a" "b" "c")
                                 :arrdims (nil nil nil))

   (test-parse-event-declaration :input "event a[3:4][5:6], b[1:2], c ; "
                                 :atts (("some") ("atts"))
                                 :names ("a" "b" "c")
                                 :arrdims (((range 3 4) (range 5 6))
                                           ((range 1 2))
                                           nil))





   (defun test-paramdecls-fn (params type localp range atts names exprs)
     (if (atom params)
         (and (atom names)
              (atom exprs))
       (debuggable-and
        (consp names)
        (consp exprs)
        (not (cw "Inspecting ~x0.~%" (car params)))
        (vl-paramdecl-p (car params))
        (equal type          (vl-paramdecl->type   (car params)))
        (equal localp        (vl-paramdecl->localp (car params)))
        (equal atts          (vl-paramdecl->atts   (car params)))
        (equal range         (and (vl-paramdecl->range (car params))
                                  (vl-pretty-range (vl-paramdecl->range (car params)))))
        (equal (car names)   (vl-paramdecl->name   (car params)))
        (equal (car exprs)   (vl-pretty-expr (vl-paramdecl->expr (car params))))
        (test-paramdecls-fn (cdr params) type localp range atts (cdr names) (cdr exprs)))))

   (defmacro test-parse-param-declaration (&key input type localp range atts names exprs (successp 't))
     `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                 (mv-let (erp val tokens warnings)
                   (vl-parse-param-or-localparam-declaration ',atts
                                                             '(:vl-kwd-parameter
                                                               :vl-kwd-localparam)
                                                             tokens 'blah-warnings)
                   (declare (ignore tokens))
                   (if erp
                       (prog2$ (cw "ERP is ~x0.~%" erp)
                               (and (equal warnings 'blah-warnings)
                                    (not ,successp)))
                     (prog2$ (cw "VAL is ~x0.~%" val)
                             (and ,successp
                                  (equal warnings 'blah-warnings)
                                  (test-paramdecls-fn val ',type ',localp ',range
                                                      ',atts ',names ',exprs))))))))

   (test-parse-param-declaration :input "parameter a = 1"
                                 :names ("a")
                                 :exprs (1)
                                 :range nil
                                 :type :vl-plain
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter a = 1 : 2 : 3"
                                 :names ("a")
                                 :exprs ((:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-plain
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "localparam a = 1 : 2 : 3"
                                 :names ("a")
                                 :exprs ((:vl-mintypmax nil 1 2 3))
                                 :localp t
                                 :range nil
                                 :type :vl-plain
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-plain
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter signed a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-signed
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter signed [7:8] a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range (range 7 8)
                                 :type :vl-signed
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter [7:8] a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range (range 7 8)
                                 :type :vl-plain
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter integer a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-integer
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter real a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-real
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter time a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-time
                                 :atts (("some") ("atts")))

   (test-parse-param-declaration :input "parameter realtime a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :type :vl-realtime
                                 :atts (("some") ("atts")))

   ;; can only use ranges on signed and plain
   (test-parse-param-declaration :input "parameter time [7:0] a = 1, b = 1 : 2 : 3"
                                 :successp nil)

   (test-parse-param-declaration :input "localparam realtime a = 1, b = 1 : 2 : 3"
                                 :names ("a" "b")
                                 :exprs (1   (:vl-mintypmax nil 1 2 3))
                                 :range nil
                                 :localp t
                                 :type :vl-realtime
                                 :atts (("some") ("atts")))


   ))