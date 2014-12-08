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
  :result (vl-datatype-p val)
  :fails gracefully
  :count weak
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-integer
                                   :vl-kwd-real
                                   :vl-kwd-realtime
                                   :vl-kwd-time))
          (vartype-token := (vl-match-some-token '(:vl-kwd-integer
                                                   :vl-kwd-real
                                                   :vl-kwd-realtime
                                                   :vl-kwd-time)))
          (return (case (vl-token->type vartype-token)
                    (:vl-kwd-integer  *vl-plain-old-integer-type*)
                    (:vl-kwd-real     *vl-plain-old-real-type*)
                    (:vl-kwd-realtime *vl-plain-old-realtime-type*)
                    (:vl-kwd-time     *vl-plain-old-time-type*))))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match-token :vl-kwd-signed)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (return
         (make-vl-coretype :name :vl-logic
                           :signedp (if signed t nil)
                           :pdims   (and range
                                         (list range))))))


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

(define vl-build-taskports ((atts  vl-atts-p)
                            (dir   vl-direction-p)
                            (type  vl-datatype-p)
                            (names vl-idtoken-list-p))
  :returns (decls vl-portdecllist-p)
  (if (atom names)
      nil
    (cons (make-vl-portdecl :name    (vl-idtoken->name (car names))
                            :dir     dir
                            ;; We'll never have a net type on function/task ports
                            :nettype nil
                            :type    type
                            :atts    atts
                            :loc     (vl-token->loc (car names)))
          (vl-build-taskports atts dir type (cdr names)))))

(defparser vl-parse-taskport-declaration (atts)
  ;; Matches tf_input_declaration, tf_output_declaration, or tf_inout_declaration.
  :guard (vl-atts-p atts)
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
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
          (type := (vl-match)))
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
                          (:vl-kwd-integer  *vl-plain-old-integer-type*)
                          (:vl-kwd-real     *vl-plain-old-real-type*)
                          (:vl-kwd-realtime *vl-plain-old-realtime-type*)
                          (:vl-kwd-time     *vl-plain-old-time-type*))
                      (make-vl-coretype :name :vl-logic
                                        :signedp (if signed t nil)
                                        :pdims (and range (list range)))))
              (ret (vl-build-taskports atts dir type names)))
           (mv nil ret tokstream)))))


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
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
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

(defsection vl-portdecl-or-blockitem-p

  (local (in-theory (enable tag-reasoning)))

  (defund vl-portdecl-or-blockitem-p (x)
    (declare (xargs :guard t))
    (or (vl-portdecl-p x)
        (vl-blockitem-p x)))

  (deflist vl-portdecl-or-blockitem-list-p (x)
    (vl-portdecl-or-blockitem-p x)
    :guard t
    :elementp-of-nil nil
    :parents nil)

  (local (defthm crock
           (implies (vl-portdecl-or-blockitem-p x)
                    (equal (vl-portdecl-p x)
                           (eq (tag x) :vl-portdecl)))
           :hints(("Goal" :in-theory (enable vl-portdecl-or-blockitem-p
                                             vl-blockitem-p)))))

  (local (in-theory (enable vl-portdecl-or-blockitem-p
                            vl-portdecl-or-blockitem-list-p)))

  (defthm vl-portdecl-or-blockitem-list-p-when-vl-portdecllist-p
    (implies (vl-portdecllist-p x)
             (vl-portdecl-or-blockitem-list-p x)))

  (defthm vl-portdecl-or-blockitem-list-p-when-vl-blockitemlist-p
    (implies (vl-blockitemlist-p x)
             (vl-portdecl-or-blockitem-list-p x)))

  (defund vl-filter-portdecl-or-blockitem-list (x)
    (declare (xargs :guard (vl-portdecl-or-blockitem-list-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-portdecls cdr-blockitems)
          (vl-filter-portdecl-or-blockitem-list (cdr x)))
         ((when (eq (tag (car x)) :vl-portdecl))
          (mv (cons (car x) cdr-portdecls) cdr-blockitems)))
      (mv cdr-portdecls (cons (car x) cdr-blockitems))))

  (defthm vl-filter-portdecl-or-blockitem-list-basics
    (implies (force (vl-portdecl-or-blockitem-list-p x))
             (let ((ret (vl-filter-portdecl-or-blockitem-list x)))
               (and (vl-portdecllist-p (mv-nth 0 ret))
                    (vl-blockitemlist-p (mv-nth 1 ret)))))
    :hints(("Goal" :in-theory (enable vl-filter-portdecl-or-blockitem-list)))))


(defparser vl-parse-task-item-declaration-noatts (atts)
  :guard (vl-atts-p atts)
  :result (vl-portdecl-or-blockitem-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout))
          (decls := (vl-parse-taskport-declaration atts))
          (:= (vl-match-token :vl-semi))
          (return decls))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-task-item-declaration ()
  :result (vl-portdecl-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts  := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-task-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-task-item-declarations ()
  ;; Tries to eat as many task items as it can find.
  ;; We use backtracking to know when to stop, because these declarations can be
  ;; followed by arbitrary statements, hence it's not clear whether (* ... *) is
  ;; the start of a new item declaration or a statement.
  :result (vl-portdecl-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (b* ((backup (vl-tokstream-save))
       ((mv erp first tokstream) (vl-parse-task-item-declaration))
       ((when erp)
        (b* ((tokstream (vl-tokstream-restore backup)))
          (mv nil nil tokstream)))
       ((mv ?erp rest tokstream) (vl-parse-0+-task-item-declarations)))
    (mv nil (append first rest) tokstream)))


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

(defsection vl-portdecllist-find-noninput

  (defund vl-portdecllist-find-noninput (x)
    (declare (xargs :guard (vl-portdecllist-p x)))
    (cond ((atom x)
           nil)
          ((eq (vl-portdecl->dir (car x)) :vl-input)
           (vl-portdecllist-find-noninput (cdr x)))
          (t
           (car x))))

  (local (in-theory (enable vl-portdecllist-find-noninput)))

  (defthm vl-portdecl-p-of-vl-portdecllist-find-noninput
    (implies (force (vl-portdecllist-p x))
             (equal (vl-portdecl-p (vl-portdecllist-find-noninput x))
                    (if (vl-portdecllist-find-noninput x)
                        t
                      nil)))))


(define vl-make-hidden-variable-for-portdecl ((x vl-portdecl-p))
  :returns (var vl-vardecl-p)
  (b* (((vl-portdecl x)))
    (make-vl-vardecl :name x.name
                     :type x.type
                     ;; The pretty-printer will look for this and avoid
                     ;; printing out these "extra" variable declarations.
                     :atts (cons (list (hons-copy "VL_HIDDEN_DECL_FOR_TASKPORT"))
                                 x.atts)
                     :loc  x.loc)))

(defprojection vl-make-hidden-variables-for-portdecls ((x vl-portdecllist-p))
  :returns (vars vl-vardecllist-p)
  (vl-make-hidden-variable-for-portdecl x))

(define vl-make-fundecl-for-parser (&key (name       stringp)
                                         (automaticp booleanp)
                                         (rettype    vl-datatype-p)
                                         (inputs     vl-portdecllist-p)
                                         (decls      vl-blockitemlist-p)
                                         (body       vl-stmt-p)
                                         (atts       vl-atts-p)
                                         (loc        vl-location-p))
  ;; Adds the VL_HIDDEN_DECL_FOR_TASKPORTs.
  :returns (fun vl-fundecl-p)
  (b* ((port-vars (vl-make-hidden-variables-for-portdecls inputs))
       (ret-var   (make-vl-vardecl :name name
                                   :type rettype
                                   :atts (list
                                          (list (hons-copy "VL_HIDDEN_DECL_FOR_TASKPORT")))
                                   :loc  loc)))
    (make-vl-fundecl :name       name
                     :automaticp automaticp
                     :rettype    rettype
                     :portdecls  inputs
                     :decls      (append port-vars (list ret-var) decls)
                     :body       body
                     :atts       atts
                     :loc        loc)))


(defparser vl-skip-through-endfunction ()
  :result (vl-token-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-kwd-endfunction)
         (end := (vl-match))
         (return end))
       (:s= (vl-match-any))
       (end := (vl-skip-through-endfunction))
       (return end)))

(defparser vl-parse-function-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-fundecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (disable not))))

  (seq tokstream

        (function := (vl-match-token :vl-kwd-function))
        (when (vl-is-token? :vl-kwd-automatic)
          (automatic := (vl-match-token :vl-kwd-automatic)))
        (rettype := (vl-parse-optional-function-range-or-type))
        (name := (vl-match-token :vl-idtoken))

        (return-raw
         ;; In case of any error, we'll try to recover gracefully by reading
         ;; through endfunction.
         (b* (((mv err val tokstream)
               (seq tokstream

                    (when (vl-is-token? :vl-semi)
                      ;; Variant 1.
                      (:= (vl-match-token :vl-semi))
                      (decls := (vl-parse-0+-task-item-declarations))
                      (stmt := (vl-parse-statement))
                      (:= (vl-match-token :vl-kwd-endfunction))
                      (return-raw
                       (b* (((mv inputs blockitems)
                             (vl-filter-portdecl-or-blockitem-list decls))
                            (non-input (vl-portdecllist-find-noninput inputs))
                            ((when non-input)
                             (vl-parse-error (str::cat "Functions may only have inputs, but port "
                                                       (vl-portdecl->name non-input)
                                                       " has direction "
                                                       (symbol-name (vl-portdecl->dir non-input)))))
                            ((unless (consp inputs))
                             (vl-parse-error "Function has no inputs."))
                            (ret (vl-make-fundecl-for-parser :name       (vl-idtoken->name name)
                                                             :automaticp (if automatic t nil)
                                                             :rettype    rettype
                                                             :inputs     inputs
                                                             :decls      blockitems
                                                             :body       stmt
                                                             :atts       atts
                                                             :loc        (vl-token->loc function))))
                         (mv nil (list ret) tokstream))))

                    ;; Variant 2.
                    (:= (vl-match-token :vl-lparen))
                    (inputs := (vl-parse-taskport-list))
                    (:= (vl-match-token :vl-rparen))
                    (:= (vl-match-token :vl-semi))
                    (blockitems := (vl-parse-0+-block-item-declarations))
                    (stmt := (vl-parse-statement))
                    (:= (vl-match-token :vl-kwd-endfunction))
                    (return-raw
                     (b* ((non-input (vl-portdecllist-find-noninput inputs))
                          ((when non-input)
                           (vl-parse-error (str::cat "Functions may only have inputs, but port "
                                                     (vl-portdecl->name non-input)
                                                     " has direction "
                                                     (symbol-name (vl-portdecl->dir non-input)))))
                          ;; (consp inputs) is automatic from vl-parse-taskport-list.
                          (ret (vl-make-fundecl-for-parser :name       (vl-idtoken->name name)
                                                           :automaticp (if automatic t nil)
                                                           :rettype    rettype
                                                           :inputs     inputs
                                                           :decls      blockitems
                                                           :body       stmt
                                                           :atts       atts
                                                           :loc        (vl-token->loc function))))
                       (mv nil (list ret) tokstream)))))

              ((unless err)
               ;; Successfully parsed a function, nothing more to do.
               (mv nil val tokstream)))

           ;; Else, we failed to parse the function.  Skip through
           ;; 'endfunction', don't produce a function, and add a fatal warning
           (seq tokstream
                (end := (vl-skip-through-endfunction))
                (return-raw
                 (b* ((warning (make-vl-warning
                                :type :vl-parse-error
                                :msg "~a0: ignoring everything through 'endfunction' at ~a1."
                                :args (list (vl-idtoken->name name) (vl-token->loc end))
                                :fatalp t
                                :fn __function__))
                      (tokstream (vl-tokstream-add-warning err))
                      (tokstream (vl-tokstream-add-warning warning)))
                   (mv nil nil tokstream))))))))


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

(define vl-make-taskdecl-for-parser (&key (name       stringp)
                                          (automaticp booleanp)
                                          (ports      vl-portdecllist-p)
                                          (decls      vl-blockitemlist-p)
                                          (body       vl-stmt-p)
                                          (atts       vl-atts-p)
                                          (loc        vl-location-p))
  ;; Adds the VL_HIDDEN_DECL_FOR_TASKPORTs.
  :returns (task vl-taskdecl-p)
  (b* ((port-vars (vl-make-hidden-variables-for-portdecls ports)))
    (make-vl-taskdecl :name name
                      :automaticp automaticp
                      :portdecls ports
                      :decls (append port-vars decls)
                      :body body
                      :atts atts
                      :loc loc)))

(defparser vl-skip-through-endtask ()
  :result (vl-token-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-kwd-endtask)
         (end := (vl-match))
         (return end))
       (:s= (vl-match-any))
       (end := (vl-skip-through-endtask))
       (return end)))

(defparser vl-parse-task-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-taskdecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (disable not))))
  (seq tokstream

        (task := (vl-match-token :vl-kwd-task))
        (when (vl-is-token? :vl-kwd-automatic)
          (automatic := (vl-match-token :vl-kwd-automatic)))
        (name := (vl-match-token :vl-idtoken))

        ;; Error handling like in functions
        (return-raw
         (b* (((mv err val tokstream)
               (seq tokstream

                    (when (vl-is-token? :vl-semi)
                      ;; Variant 1.
                      (:= (vl-match-token :vl-semi))
                      (decls := (vl-parse-0+-task-item-declarations))
                      (stmt  := (vl-parse-statement-or-null))
                      (:= (vl-match-token :vl-kwd-endtask))
                      (return
                       (b* (((mv ports blockitems)
                             (vl-filter-portdecl-or-blockitem-list decls))
                            (ans (vl-make-taskdecl-for-parser :name       (vl-idtoken->name name)
                                                              :automaticp (if automatic t nil)
                                                              :ports      ports
                                                              :decls      blockitems
                                                              :body       stmt
                                                              :atts       atts
                                                              :loc        (vl-token->loc task))))
                         (list ans))))

                    ;; Variant 2.
                    (:= (vl-match-token :vl-lparen))
                    (ports := (vl-parse-taskport-list))
                    (:= (vl-match-token :vl-rparen))
                    (:= (vl-match-token :vl-semi))
                    (blockitems := (vl-parse-0+-block-item-declarations))
                    (stmt       := (vl-parse-statement-or-null))
                    (:= (vl-match-token :vl-kwd-endtask))
                    (return
                     (list (vl-make-taskdecl-for-parser :name       (vl-idtoken->name name)
                                                        :automaticp (if automatic t nil)
                                                        :ports      ports
                                                        :decls      blockitems
                                                        :body       stmt
                                                        :atts       atts
                                                        :loc        (vl-token->loc task))))))

              ((unless err)
               (mv nil val tokstream)))

           ;; Else, we failed to parse the function.  Skip through 'endtask',
           ;; don't produce a task, and add a fatal warning
           (seq tokstream
                (end := (vl-skip-through-endtask))
                (return-raw
                 (b* ((warning (make-vl-warning
                                :type :vl-parse-error
                                :msg "~a0: ignoring everything through 'endtask' at ~a1."
                                :args (list (vl-idtoken->name name) (vl-token->loc end))
                                :fatalp t
                                :fn __function__))
                      (tokstream (vl-tokstream-add-warning err))
                      (tokstream (vl-tokstream-add-warning warning)))
                   (mv nil nil tokstream))))))))


