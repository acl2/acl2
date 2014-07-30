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
(include-book "blockitems")
(include-book "ports")
(include-book "statements")
(local (include-book "../../util/arithmetic"))


; function_range_or_type ::= ['signed'] range | 'integer' | 'real' | 'realtime' | 'time'

(defparser vl-parse-optional-function-range-or-type ()
  :result (and (consp val)
               (vl-taskporttype-p (car val))
               (vl-maybe-range-p (cdr val)))
  :fails gracefully
  :count weak
  (seqw tokens warnings
        (when (vl-is-some-token? '(:vl-kwd-integer
                                   :vl-kwd-real
                                   :vl-kwd-realtime
                                   :vl-kwd-time))
          (vartype-token := (vl-match-some-token '(:vl-kwd-integer
                                                   :vl-kwd-real
                                                   :vl-kwd-realtime
                                                   :vl-kwd-time)))
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
; tf_output_declaration ::= 'output' [ 'reg' ] [ 'signed' ] [ range ] list_of_port_identifiers
;                        | 'input' task_port_type list_of_port_identifiers
;
; tf_inout_declaration ::= 'inout' [ 'reg' ] [ 'signed' ] [ range ] list_of_port_identifiers
;                        | 'input' task_port_type list_of_port_identifiers
;
; task_port_type ::= 'integer' | 'real' | 'realtime' | 'time'
;
; list_of_port_identifier ::= identifier { ',' identifier }

(defsection vl-build-taskports

  (defund vl-build-taskports (atts dir type range names)
    (declare (xargs :guard (and (vl-atts-p atts)
                                (vl-direction-p dir)
                                (vl-taskporttype-p type)
                                (vl-maybe-range-p range)
                                (vl-idtoken-list-p names))))
    (if (atom names)
        nil
      (cons (make-vl-taskport :name  (vl-idtoken->name (car names))
                              :dir   dir
                              :type  type
                              :range range
                              :atts  atts
                              :loc   (vl-token->loc (car names)))
            (vl-build-taskports atts dir type range (cdr names)))))

  (local (in-theory (enable vl-build-taskports)))

  (defthm vl-taskportlist-p-of-vl-build-taskports
    (implies (and (force (vl-atts-p atts))
                  (force (vl-direction-p dir))
                  (force (vl-taskporttype-p type))
                  (force (vl-maybe-range-p range))
                  (force (vl-idtoken-list-p names)))
             (vl-taskportlist-p (vl-build-taskports atts dir type range names)))))

(defparser vl-parse-taskport-declaration (atts)
  ;; Matches tf_input_declaration, tf_output_declaration, or tf_inout_declaration.
  :guard (vl-atts-p atts)
  :result (vl-taskportlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (dir := (vl-match-some-token '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout)))
        (when (vl-is-token? :vl-kwd-reg)
          (reg := (vl-match-token :vl-kwd-reg)))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match-token :vl-kwd-signed)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (when (vl-is-some-token? '(:vl-kwd-integer
                                   :vl-kwd-real
                                   :vl-kwd-realtime
                                   :vl-kwd-time))
          (type := (vl-match-some-token '(:vl-kwd-integer
                                          :vl-kwd-real
                                          :vl-kwd-realtime
                                          :vl-kwd-time))))
        (names := (vl-parse-1+-identifiers-separated-by-commas))
        (return-raw
         (b* (((when (and type (or reg signed range)))
               (vl-parse-error "Task/function port declarations cannot ~
                                combine reg/signed keyword with variable ~
                                types (integer, real, realtime, time)."))
              (dir (case (vl-token->type dir)
                     (:vl-kwd-input    :vl-input)
                     (:vl-kwd-output   :vl-output)
                     (:vl-kwd-inout    :vl-inout)))
              (type (if type
                        (case (vl-token->type type)
                          (:vl-kwd-integer  :vl-integer)
                          (:vl-kwd-real     :vl-real)
                          (:vl-kwd-realtime :vl-realtime)
                          (:vl-kwd-time     :vl-time))
                      (if signed
                          :vl-signed
                        :vl-unsigned)))
              (ret (vl-build-taskports atts dir type range names)))
           (mv nil ret tokens warnings)))))


; task_port_item ::= { attribute_instance } tf_input_declaration
;                  | { attribute_instance } tf_output_declaration
;                  | { attribute_instance } tf_inout_declaration
;
; task_port_list ::= task_port_item { , task_port_item }
;
; function_port_list ::= { attribute_instance } tf_input_declaration
;                          { ',' { attribute_instance } tf_input_declaration }
;
; Note: function_port_list is just the subset of task_port_list where the ports
; are all of type input.
;
; Our approach: just write a parser for task_port_list, then separately check
; (when we construct the function declaration) that all the ports are inputs.

(defparser vl-parse-taskport-list ()
  :result (vl-taskportlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (ins1 := (vl-parse-taskport-declaration atts))
        (unless (vl-is-token? :vl-comma)
          (return ins1))
        (:= (vl-match-token :vl-comma))
        (ins2 := (vl-parse-taskport-list))
        (return (append ins1 ins2))))


; task_item_declaration ::= block_item_declaration
;                         | { attribute_instance } tf_input_declaration ';'
;                         | { attribute_instance } tf_output_declaration ';'
;                         | { attribute_instance } tf_inout_declaration ';'
;
; function_item_declaration ::= block_item_declaration
;                             | { attribute_instance } tf_input_declaration ';'
;
; Note: again, function_item_declaration is the subset of task_item_declaration
; where the only ports are inputs.
;
; Our approach: just writer a parser for task_item_declaration, then separately
; check (when we construct the function declaration) that all ports are inputs.

(defsection vl-taskport-or-blockitem-p

  (local (in-theory (enable tag-reasoning)))

  (defund vl-taskport-or-blockitem-p (x)
    (declare (xargs :guard t))
    (or (vl-taskport-p x)
        (vl-blockitem-p x)))

  (deflist vl-taskport-or-blockitem-list-p (x)
    (vl-taskport-or-blockitem-p x)
    :guard t
    :elementp-of-nil nil
    :parents nil)

  (local (defthm crock
           (implies (vl-taskport-or-blockitem-p x)
                    (equal (vl-taskport-p x)
                           (eq (tag x) :vl-taskport)))
           :hints(("Goal" :in-theory (enable vl-taskport-or-blockitem-p
                                             vl-blockitem-p)))))

  (local (in-theory (enable vl-taskport-or-blockitem-p
                            vl-taskport-or-blockitem-list-p)))

  (defthm vl-taskport-or-blockitem-list-p-when-vl-taskportlist-p
    (implies (vl-taskportlist-p x)
             (vl-taskport-or-blockitem-list-p x)))

  (defthm vl-taskport-or-blockitem-list-p-when-vl-blockitemlist-p
    (implies (vl-blockitemlist-p x)
             (vl-taskport-or-blockitem-list-p x)))

  (defund vl-filter-taskport-or-blockitem-list (x)
    (declare (xargs :guard (vl-taskport-or-blockitem-list-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-taskports cdr-blockitems)
          (vl-filter-taskport-or-blockitem-list (cdr x)))
         ((when (eq (tag (car x)) :vl-taskport))
          (mv (cons (car x) cdr-taskports) cdr-blockitems)))
      (mv cdr-taskports (cons (car x) cdr-blockitems))))

  (defthm vl-filter-taskport-or-blockitem-list-basics
    (implies (force (vl-taskport-or-blockitem-list-p x))
             (let ((ret (vl-filter-taskport-or-blockitem-list x)))
               (and (vl-taskportlist-p (mv-nth 0 ret))
                    (vl-blockitemlist-p (mv-nth 1 ret)))))
    :hints(("Goal" :in-theory (enable vl-filter-taskport-or-blockitem-list)))))


(defparser vl-parse-task-item-declaration-noatts (atts)
  :guard (vl-atts-p atts)
  :result (vl-taskport-or-blockitem-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-some-token? '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout))
          (decls := (vl-parse-taskport-declaration atts))
          (:= (vl-match-token :vl-semi))
          (return decls))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-task-item-declaration ()
  :result (vl-taskport-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts  := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-task-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-task-item-declarations ()
  ;; Tries to eat as many task items as it can find.
  ;; We use backtracking to know when to stop, because these declarations can be
  ;; followed by arbitrary statements, hence it's not clear whether (* ... *) is
  ;; the start of a new item declaration or a statement.
  :result (vl-taskport-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (mv-let (erp first explore new-warnings)
    (vl-parse-task-item-declaration)
    (cond (erp
           (mv nil nil tokens warnings))
          (t
           (mv-let (erp rest tokens warnings)
             (vl-parse-0+-task-item-declarations :tokens explore
                                                 :warnings new-warnings)
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
;  | 'function' [ 'automatic' ] [ function_range_or_type ]              ; variant 2
;     identifier '(' function_port_list ')' ';'
;     { block_item_declaration }
;     statement
;    'endfunction'

(defsection vl-taskportlist-find-noninput

  (defund vl-taskportlist-find-noninput (x)
    (declare (xargs :guard (vl-taskportlist-p x)))
    (cond ((atom x)
           nil)
          ((eq (vl-taskport->dir (car x)) :vl-input)
           (vl-taskportlist-find-noninput (cdr x)))
          (t
           (car x))))

  (local (in-theory (enable vl-taskportlist-find-noninput)))

  (defthm vl-taskport-p-of-vl-taskportlist-find-noninput
    (implies (force (vl-taskportlist-p x))
             (equal (vl-taskport-p (vl-taskportlist-find-noninput x))
                    (if (vl-taskportlist-find-noninput x)
                        t
                      nil)))))


(defparser vl-parse-function-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-fundecl-p val)
  :true-listp nil
  :resultp-of-nil nil
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
          (decls := (vl-parse-0+-task-item-declarations))
          (stmt := (vl-parse-statement))
          (:= (vl-match-token :vl-kwd-endfunction))
          (return-raw
           (b* (((mv inputs blockitems)
                 (vl-filter-taskport-or-blockitem-list decls))
                (non-input (vl-taskportlist-find-noninput inputs))
                ((when non-input)
                 (vl-parse-error (str::cat "Functions may only have inputs, but port "
                                           (vl-taskport->name non-input)
                                           " has direction "
                                           (symbol-name (vl-taskport->dir non-input)))))
                ((unless (consp inputs))
                 (vl-parse-error "Function has no inputs."))
                (ret (make-vl-fundecl :name       (vl-idtoken->name name)
                                      :automaticp (if automatic t nil)
                                      :rtype      rtype
                                      :rrange     rrange
                                      :inputs     inputs
                                      :decls      blockitems
                                      :body       stmt
                                      :atts       atts
                                      :loc        (vl-token->loc function))))
             (mv nil ret tokens warnings))))

        ;; Variant 2.
        (:= (vl-match-token :vl-lparen))
        (inputs := (vl-parse-taskport-list))
        (:= (vl-match-token :vl-rparen))
        (:= (vl-match-token :vl-semi))
        (blockitems := (vl-parse-0+-block-item-declarations))
        (stmt := (vl-parse-statement))
        (:= (vl-match-token :vl-kwd-endfunction))
        (return-raw
         (b* ((non-input (vl-taskportlist-find-noninput inputs))
              ((when non-input)
               (vl-parse-error (str::cat "Functions may only have inputs, but port "
                                         (vl-taskport->name non-input)
                                         " has direction "
                                         (symbol-name (vl-taskport->dir non-input)))))
              ;; (consp inputs) is automatic from vl-parse-taskport-list.
              (ret (make-vl-fundecl :name       (vl-idtoken->name name)
                                    :automaticp (if automatic t nil)
                                    :rtype      rtype
                                    :rrange     rrange
                                    :inputs     inputs
                                    :decls      blockitems
                                    :body       stmt
                                    :atts       atts
                                    :loc        (vl-token->loc function))))
           (mv nil ret tokens warnings)))))




; task_declaration ::=
;
;    'task' [ 'automatic' ] identifier ';'         ;; variant 1
;       { task_item_declaration }
;       statement_or_null
;    'endtask'
;
;  | 'task' [ 'automatic' ] identifier '(' [task_port_list] ')' ';'
;       { block_item_declaration }
;       statement_or_null
;    'endtask'

(defparser vl-parse-task-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-taskdecl-p val)
  :true-listp nil
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings

        (task := (vl-match-token :vl-kwd-task))
        (when (vl-is-token? :vl-kwd-automatic)
          (automatic := (vl-match-token :vl-kwd-automatic)))
        (name := (vl-match-token :vl-idtoken))

        (when (vl-is-token? :vl-semi)
          ;; Variant 1.
          (:= (vl-match-token :vl-semi))
          (decls := (vl-parse-0+-task-item-declarations))
          (stmt  := (vl-parse-statement-or-null))
          (:= (vl-match-token :vl-kwd-endtask))
          (return
           (b* (((mv ports blockitems)
                 (vl-filter-taskport-or-blockitem-list decls)))
             (make-vl-taskdecl :name       (vl-idtoken->name name)
                               :automaticp (if automatic t nil)
                               :ports      ports
                               :decls      blockitems
                               :body       stmt
                               :atts       atts
                               :loc        (vl-token->loc task)))))

        ;; Variant 2.
        (:= (vl-match-token :vl-lparen))
        (ports := (vl-parse-taskport-list))
        (:= (vl-match-token :vl-rparen))
        (:= (vl-match-token :vl-semi))
        (blockitems := (vl-parse-0+-block-item-declarations))
        (stmt       := (vl-parse-statement-or-null))
        (:= (vl-match-token :vl-kwd-endtask))
        (return (make-vl-taskdecl :name       (vl-idtoken->name name)
                                  :automaticp (if automatic t nil)
                                  :ports      ports
                                  :decls      blockitems
                                  :body       stmt
                                  :atts       atts
                                  :loc        (vl-token->loc task)))))

