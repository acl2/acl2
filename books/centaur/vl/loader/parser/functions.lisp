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
(local (in-theory (e/d (tag-reasoning)
                       (acl2::sublistp-when-prefixp
                        acl2::lower-bound-of-len-when-sublistp
                        acl2::len-when-prefixp
                        double-containment
                        acl2::prefixp-when-equal-lengths
                        acl2::consp-when-member-equal-of-cons-listp
                        acl2::consp-when-member-equal-of-atom-listp
                        (tau-system)))))

(defxdoc parse-functions
  :parents (parser)
  :short "Functions for parsing Verilog-2005 and SystemVerilog function and
  task declarations.")

(local (xdoc::set-default-parents parse-functions))

(define vl-portdecllist-find-noninput ((x vl-portdecllist-p))
  :short "Find the first non-@('input') in a list of port declarations, if there is one."
  :returns (decl? (equal (vl-portdecl-p decl?) (if decl? t nil)))
  (cond ((atom x)
         nil)
        ((eq (vl-portdecl->dir (car x)) :vl-input)
         (vl-portdecllist-find-noninput (cdr x)))
        (t
         (vl-portdecl-fix (car x)))))

(define vl-filter-portdecl-or-blockitem-list
  :short "Split out port declarations from other block items."
  ((x vl-portdecl-or-blockitem-list-p))
  :returns (mv (portdecls vl-portdecllist-p)
               (blockitems vl-blockitemlist-p))
  :prepwork ((local (in-theory (enable vl-portdecl-or-blockitem-p
                                       tag-reasoning))))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv cdr-portdecls cdr-blockitems)
        (vl-filter-portdecl-or-blockitem-list (cdr x)))
       ((when (eq (tag (car x)) :vl-portdecl))
        (mv (cons (vl-portdecl-fix (car x)) cdr-portdecls)
            cdr-blockitems)))
    (mv cdr-portdecls
        (cons (vl-blockitem-fix (car x)) cdr-blockitems))))

(define vl-build-taskports
  :short "Build port declarations for a task/function declaration."
  ((atts  vl-atts-p)
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

(define vl-make-hidden-variable-for-portdecl ((x vl-portdecl-p))
  :returns (var vl-vardecl-p)
  :short "Create the hidden @(see vl-vardecl)s corresponding to the @(see
vl-portdecl)s of a function or task."
  :long "<p>See the description of the @('decls') in @(see vl-fundecl) and
@(see vl-taskdecl): for each port of the function/task, we create a
corresponding variable declaration, marked with a special attribute.  This
variable declaration plays well with @(see scopestack) and similar.</p>"
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

(define vl-make-fundecl-for-parser
  :short "Main function the parser uses for creating function declarations."
  (&key (name       stringp)
        (lifetime   vl-lifetime-p)
        (rettype    vl-datatype-p)
        (inputs     vl-portdecllist-p)
        (decls      vl-blockitemlist-p)
        (loaditems  vl-portdecl-or-blockitem-list-p)
        (body       vl-stmt-p)
        (atts       vl-atts-p)
        (loc        vl-location-p))
  :returns (fun vl-fundecl-p)
  :long "<p>This mainly just adds the @('VL_HIDDEN_DECL_FOR_TASKPORT')
variables.  See the description of <i>decls</i> in @(see vl-fundecl) for more
information.</p>"
  (b* ((port-vars (vl-make-hidden-variables-for-portdecls inputs))
       (ret-var   (make-vl-vardecl :name name
                                   :type rettype
                                   :atts (list
                                          (list (hons-copy "VL_HIDDEN_DECL_FOR_TASKPORT")))
                                   :loc  loc))
       (decls (append port-vars (list ret-var) decls))
       ((mv vardecls paramdecls imports typedefs) (vl-sort-blockitems decls)))
    (make-vl-fundecl :name       name
                     :lifetime   lifetime
                     :rettype    rettype
                     :portdecls  inputs
                     :loaditems  loaditems
                     :vardecls   vardecls
                     :paramdecls paramdecls
                     :imports    imports
                     :typedefs   typedefs
                     :body       body
                     :atts       atts
                     :loc        loc)))

(define vl-make-taskdecl-for-parser
  :short "Main function the parser uses for creating task declarations."
  (&key (name       stringp)
        (lifetime   vl-lifetime-p)
        (ports      vl-portdecllist-p)
        (decls      vl-blockitemlist-p)
        (loaditems  vl-portdecl-or-blockitem-list-p)
        (body       vl-stmt-p)
        (atts       vl-atts-p)
        (loc        vl-location-p))
  :returns (task vl-taskdecl-p)
  :long "<p>This mainly just adds the @('VL_HIDDEN_DECL_FOR_TASKPORT')
variables.  See the description of <i>decls</i> in @(see vl-taskdecl) for more
information.</p>"
  (b* ((port-vars (vl-make-hidden-variables-for-portdecls ports))
       (decls (append port-vars decls))
       ((mv vardecls paramdecls imports typedefs) (vl-sort-blockitems decls)))
    (make-vl-taskdecl :name       name
                      :lifetime   lifetime
                      :portdecls  ports
                      :loaditems  loaditems
                      :vardecls   vardecls
                      :paramdecls paramdecls
                      :imports    imports
                      :typedefs   typedefs
                      :body       body
                      :atts       atts
                      :loc        loc)))



; -----------------------------------------------------------------------------
;
;                                Verilog-2005
;
; -----------------------------------------------------------------------------

(defparser vl-parse-optional-function-range-or-type ()
  :short "Verilog-2005 only.  Match @('function_type_or_range')."
  :long "@({
             function_range_or_type ::= ['signed'] range
                                      | 'integer'
                                      | 'real'
                                      | 'realtime'
                                      | 'time'
          })"
  :result (vl-datatype-p val)
  :fails gracefully
  :count weak
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time))
          (vartype-token := (vl-match))
          (return (case (vl-token->type vartype-token)
                    (:vl-kwd-integer  *vl-plain-old-integer-type*)
                    (:vl-kwd-real     *vl-plain-old-real-type*)
                    (:vl-kwd-realtime *vl-plain-old-realtime-type*)
                    (:vl-kwd-time     *vl-plain-old-time-type*))))

        ;; The only thing left is ['signed'] range
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match-token :vl-kwd-signed)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (return
         (make-vl-coretype :name    :vl-logic
                           :signedp (if signed t nil)
                           :pdims   (and range
                                         (list (vl-range->dimension range)))))))

(defparser vl-parse-taskport-declaration (atts)
  :short "Verilog-2005 only.  Match @('tf_input_declaration'), @('tf_output_declaration'), or @('tf_inout_declaration')."
  :guard (vl-atts-p atts)
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :long "<p>Relevant grammar rules:</p>

@({
   tf_input_declaration ::= 'input' [ 'reg' ] [ 'signed' ] [ range ] list_of_port_identifiers
                          | 'input' task_port_type list_of_port_identifiers

   tf_output_declaration ::= 'output' [ 'reg' ] [ 'signed' ] [ range ] list_of_port_identifiers
                          | 'input' task_port_type list_of_port_identifiers

   tf_inout_declaration ::= 'inout' [ 'reg' ] [ 'signed' ] [ range ] list_of_port_identifiers
                          | 'input' task_port_type list_of_port_identifiers

   task_port_type ::= 'integer' | 'real' | 'realtime' | 'time'

   list_of_port_identifiers ::= identifier { ',' identifier }
})"

  (seq tokstream
        (dir := (vl-match-some-token '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout)))
        (when (vl-is-token? :vl-kwd-reg)
          (reg := (vl-match-token :vl-kwd-reg)))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match-token :vl-kwd-signed)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time))
          (type := (vl-match)))
        (names := (vl-parse-1+-identifiers-separated-by-commas))
        (return-raw
         (b* (((when (and type (or reg signed range)))
               (vl-parse-error "Task/function port declarations cannot ~
                                combine reg/signed keyword with variable ~
                                types (integer, real, realtime, time)."))
              (dir (case (vl-token->type dir)
                     (:vl-kwd-input  :vl-input)
                     (:vl-kwd-output :vl-output)
                     (:vl-kwd-inout  :vl-inout)))
              (type (if type
                        (case (vl-token->type type)
                          (:vl-kwd-integer  *vl-plain-old-integer-type*)
                          (:vl-kwd-real     *vl-plain-old-real-type*)
                          (:vl-kwd-realtime *vl-plain-old-realtime-type*)
                          (:vl-kwd-time     *vl-plain-old-time-type*))
                      (make-vl-coretype :name :vl-logic
                                        :signedp (if signed t nil)
                                        :pdims (and range (list (vl-range->dimension range))))))
              (ret (vl-build-taskports atts dir type names)))
           (mv nil ret tokstream)))))

(defparser vl-parse-taskport-list ()
  :short "Verilog-2005 only.  Match @('task_port_list')."
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :long "<p>The basic grammar rules are:</p>

@({
    task_port_item ::= { attribute_instance } tf_input_declaration
                     | { attribute_instance } tf_output_declaration
                     | { attribute_instance } tf_inout_declaration

    task_port_list ::= task_port_item { , task_port_item }
})

<p>We use this same function for parsing function port lists.  Note that a
function port list is just the subset of a task port list, where the ports are
all of type input.</p>

@({
     function_port_list ::= { attribute_instance } tf_input_declaration
                              { ',' { attribute_instance } tf_input_declaration }
})

<p>We therefore just write a parser for task_port_list, then separately
check (when we construct the function declaration) that all the ports are
inputs.</p>"

  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (ins1 := (vl-parse-taskport-declaration atts))
        (unless (vl-is-token? :vl-comma)
          (return ins1))
        (:= (vl-match-token :vl-comma))
        (ins2 := (vl-parse-taskport-list))
        (return (append ins1 ins2))))

(defparser vl-parse-task-item-declaration-noatts (atts)
  :short "Verilog-2005 only.  Match @('task_item_declaration') except for the
attributes.  Also can be used to match @('function_item_declaration')."
  :guard (vl-atts-p atts)
  :result (vl-portdecl-or-blockitem-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :long "<p>Note: again, function_item_declaration is the subset of
task_item_declaration where the only ports are inputs.  We therefore just
writer a parser for task_item_declaration, then separately check (when we
construct the function declaration) that all ports are inputs.</p>

@({
    task_item_declaration ::= block_item_declaration
                            | { attribute_instance } tf_input_declaration ';'
                            | { attribute_instance } tf_output_declaration ';'
                            | { attribute_instance } tf_inout_declaration ';'

    function_item_declaration ::= block_item_declaration
                                | { attribute_instance } tf_input_declaration ';'
})"
  (seq tokstream
        (when (vl-is-some-token? '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout))
          (decls := (vl-parse-taskport-declaration atts))
          (:= (vl-match-token :vl-semi))
          (return decls))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-task-item-declaration ()
  :short "Verilog-2005 only.  Match @('task_item_declaration'), including attributes."
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
  :short "Verilog-2005 only.  Match as many @('task_item_declaration')s as possible."
  :result (vl-portdecl-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  :long "<p>We use backtracking to know when to stop, because these
declarations can be followed by arbitrary statements, hence it's not clear
whether @('(* ... *)') is the start of a new item declaration or a
statement.</p>"
  (b* ((backup (vl-tokstream-save))
       ((mv erp first tokstream) (vl-parse-task-item-declaration))
       ((when erp)
        (b* ((tokstream (vl-tokstream-restore backup)))
          (mv nil nil tokstream)))
       ((mv ?erp rest tokstream) (vl-parse-0+-task-item-declarations)))
    (mv nil (append first rest) tokstream)))

(defparser vl-skip-through-endfunction ()
  :short "Barbaric fault tolerance routine.  Find @('endfunction') so we can
try to resume parsing after a problematic function."
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

(defparser vl-parse-function-declaration-2005 (atts)
  :short "Verilog-2005 only.  Matches @('function_declaration') except for the attributes."
  :guard (vl-atts-p atts)
  :result (vl-fundecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (disable not))))
  :guard-debug t

:long "<p>Relevant grammar rules:</p>

@({
   function_declaration ::=

        'function' [ 'automatic' ] [ function_range_or_type ]         ; variant 1
          identifier ';'
          function_item_declaration { function_item_declaration }
          statement
        'endfunction'

      | 'function' [ 'automatic' ] [ function_range_or_type ]         ; variant 2
         identifier '(' function_port_list ')' ';'
         { block_item_declaration }
         statement
        'endfunction'
})"

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
                                                             :lifetime   (if automatic :vl-automatic nil)
                                                             :rettype    rettype
                                                             :inputs     inputs
                                                             :decls      blockitems
                                                             :loaditems  decls
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
                          (loaditems (append inputs blockitems))
                          (ret (vl-make-fundecl-for-parser :name       (vl-idtoken->name name)
                                                           :lifetime   (if automatic :vl-automatic nil)
                                                           :rettype    rettype
                                                           :inputs     inputs
                                                           :decls      blockitems
                                                           :loaditems  loaditems
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

(defparser vl-skip-through-endtask ()
  :short "Barbaric fault tolerance routine.  Find @('endtask') so we can
try to resume parsing after a problematic function."
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

(defparser vl-parse-task-declaration-2005 (atts)
  :short "Verilog-2005 only.  Matches @('task_declaration') except for the attributes."
  :guard (vl-atts-p atts)
  :result (vl-taskdecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (disable not))))

  :long "<p>Relevant grammar rules:</p>

@({
     task_declaration ::=

        'task' [ 'automatic' ] identifier ';'         ;; variant 1
           { task_item_declaration }
           statement_or_null
        'endtask'

      | 'task' [ 'automatic' ] identifier '(' [task_port_list] ')' ';'
           { block_item_declaration }
           statement_or_null
        'endtask'
})"

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
                            (ans (vl-make-taskdecl-for-parser :name      (vl-idtoken->name name)
                                                              :lifetime  (if automatic :vl-automatic nil)
                                                              :ports     ports
                                                              :decls     blockitems
                                                              :loaditems decls
                                                              :body      stmt
                                                              :atts      atts
                                                              :loc       (vl-token->loc task))))
                         (list ans))))

                    ;; Variant 2.
                    (:= (vl-match-token :vl-lparen))
                    (unless (vl-is-token? :vl-rparen) ;; the task_port_list is optional
                      (ports := (vl-parse-taskport-list)))
                    (:= (vl-match-token :vl-rparen))
                    (:= (vl-match-token :vl-semi))
                    (blockitems := (vl-parse-0+-block-item-declarations))
                    (stmt       := (vl-parse-statement-or-null))
                    (:= (vl-match-token :vl-kwd-endtask))
                    (return
                     (list (vl-make-taskdecl-for-parser :name      (vl-idtoken->name name)
                                                        :lifetime  (if automatic :vl-automatic nil)
                                                        :ports     ports
                                                        :decls     blockitems
                                                        :loaditems (append ports blockitems)
                                                        :body      stmt
                                                        :atts      atts
                                                        :loc       (vl-token->loc task))))))

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




; -----------------------------------------------------------------------------
;
;                             SystemVerilog-2012
;
; -----------------------------------------------------------------------------

;; BOZO what are function prototypes and do we care?
;; function_prototype ::= 'function' data_type_or_void identifier [ '(' [tf_port_list] ')' ]

(defsection parse-functions-sv2012
  :short "Parsing of functions and task for SystemVerilog.")

(local (xdoc::set-default-parents parse-functions-sv2012))

(defprod vl-datatype-or-implicit
  ((type vl-datatype-p)
   (implicitp booleanp)))

(defparser vl-parse-function-data-type-and-name (void-allowed-p)
  :short "Matches @('function_data_type_or_implicit identifier')."
  :result (and (consp val)
               (vl-datatype-or-implicit-p (car val))
               (vl-idtoken-p (cdr val)))
  :fails gracefully
  :count strong
  :long "<p>This matches the part of a function body consisting of:</p>

@({
    function_data_type_or_implicit
      [ interface_identifier '.' | class_scope ] identifier
})

<p>Except that we're going to ignore the interface_identifier and class_scope
part.</p>

<p>The following grammar rules are relevant:</p>

@({
    function_data_type_or_implicit ::= data_type_or_void
                                     | implicit_data_type

    data_type_or_void ::= data_type | 'void'

    implicit_data_type ::= [ signing ] { packed_dimension }
})

<p>So really what we're parsing is:</p>

@({
      'void' identifier
    | data_type identifier
    | [ signing ] { packed_dimension } identifier.
})

<p>This requires backtracking because if an identifier is first, we don't know
if we're in the data type or implicit case.  The way we resolve this is to
first try the datatype case.  If that works, it's definitely the right one,
because in all cases our final identifier is going to be followed by some
punctuation, and so if we parse both a data type and an identifier, we know the
third option wouldn't have worked (we would've just gotten an identifier and
then a semicolon or left-paren).</p>"
  (b* (((when (and void-allowed-p (vl-is-token? :vl-kwd-void)))
        ;; No ambiguity here.
        (seq tokstream
             (:= (vl-match))
             (name := (vl-match-token :vl-idtoken))
             (return (cons (make-vl-datatype-or-implicit
                            :type (make-vl-coretype :name :vl-void)
                            :implicitp nil)
                           name))))
       (backup (vl-tokstream-save))
       ((mv err1 val tokstream)
        (seq tokstream
             ;; Option 1: parse a datatype.
             (type := (vl-parse-datatype))
             (name := (vl-match-token :vl-idtoken))
             (return (cons (make-vl-datatype-or-implicit
                            :type type :implicitp nil)
                           name))))
       ((unless err1) (mv nil val tokstream))
       (pos1 (vl-tokstream->position))
       (tokstream (vl-tokstream-restore backup))
       ((mv err2 val tokstream)
        (seq tokstream
             ;; Option 2: implicit datatype.
             (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
               (signing := (vl-match)))
             (pdims := (vl-parse-0+-packed-dimensions))
             (name := (vl-match-token :vl-idtoken))
             (return (cons (make-vl-datatype-or-implicit
                            :type
                            (make-vl-coretype
                             :name :vl-logic
                             :signedp (and signing (eq (vl-token->type signing) :vl-kwd-signed))
                             :pdims pdims)
                            :implicitp t)
                           name))))
       ((unless err2) (mv nil val tokstream))
       (pos2 (vl-tokstream->position))
       ((mv pos err) (vl-choose-parse-error pos1 err1 pos2 err2))
       (tokstream (vl-tokstream-update-position pos)))
    (mv err nil tokstream)))


(defparser vl-parse-function-statements-aux ()
  :parents (vl-parse-function-statements)
  :result (vl-stmtlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       ;; Hack so we can reuse this in tasks.
       (when (vl-is-some-token? '(:vl-kwd-endfunction :vl-kwd-endtask))
         (return nil))
       (stmt1 := (vl-parse-statement-or-null))
       (rest := (vl-parse-function-statements-aux))
       (return (cons stmt1 rest))))

(defparser vl-parse-function-statements ()
  :short "Matches @('{ function_statement_or_null }') and returns a single statement."
  :result (vl-stmt-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count weak
  :long "<p>In Verilog-2005 a function's body can be a single statement.
However, in SystemVerilog this is extended to a list of:</p>

@({
     function_statement_or_null ::= function_statement
                                  | { attribute_instance } ';'

     function_statement ::= statement
})

<p>For greater compatibility between Verilog-2005 and SystemVerilog-2012, if we
encounter a function whose body is a list of statements, we convert it into an
implicit begin/end block.</p>

<p>In the case of tasks, there is evidence that this begin/end treatment is
reasonable.  From Page 287:</p>

<blockquote>\"Multiple statements can be written between the task declaration
and endtask.  Statements are executed sequentially, the same as if they were
enclosed in a @('begin .... end') group. It shall also be legal to have no
statements at all.\"</blockquote>

<p>Similar language is used to describe functions on page 291.</p>"

  (seq tokstream
       (stmts := (vl-parse-function-statements-aux))
       (when (atom stmts)
         (return (make-vl-nullstmt)))
       (when (atom (cdr stmts))
         ;; A single statement.  No need to add a block.
         (return (car stmts)))
       (return (make-vl-blockstmt :blocktype :vl-beginend
                                  :stmts stmts))))

(local (defthm vl-idtoken-p-of-car-by-vl-is-token-crock
         (implies (vl-is-token? :vl-idtoken)
                  (vl-idtoken-p (car (vl-tokstream->tokens))))
         :hints(("Goal" :in-theory (enable vl-is-token?)))))

(local (in-theory (disable not)))





(defparser vl-parse-tf-port-item (prev)
  :short "Matches @('tf_port_item'), not for prototypes."
  :guard (or (not prev)
             (vl-portdecl-p prev))
  :result (vl-portdecl-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  :long "<p>If we ever implement prototypes, this isn't the right function,
because we assume that we have names for the items.</p>

<p>These items occur in @('tf_port_list') in a C-style function declaration
such as:</p>

@({
       function foo (input int a, logic [3:0] b, c); ... endfunction
})

<p>The @('tf_port_item')s here are @('input int a'), @('logic [3:0] b'), and
@('c').  We will represent these using @(see vl-portdecl)s.</p>


<h5>Type Determination</h5>

<p>The type of each @('tf_port_item') may be explicitly declared or inherited
from the previous argument.  To support this, we take as input the previously
parsed port, if there is a previous port, so that we can infer our type from
it, if necessary.</p>

<p>SystemVerilog-2012 gives rules for inferring data types</p>
<ul>
<li>For tasks arguments in Section 13.3, Page 287, and</li>
<li>For function arguments in Section 13.4, page 291.</li>
</ul>

<p>In both cases identical language is used:</p>

<blockquote>\"If the data type is not explicitly declared, then the default
data type is logic if it is the first argument or if the argument direction is
explicitly specified.  Otherwise the data type is inherited from the previous
argument.\"</blockquote>


<h5>Direction Determination</h5>

<p>Per 13.3 (Page 287), regarding tasks:</p>

<blockquote>\"There is a default direction of @('input') if no direction has
been specified.  Once a direction is given, subsequent formals default to the
same direction.\"</blockquote>

<h5>Grammar rules:</h5>

@({
     tf_port_item ::= {attribute_instance}
                      [tf_port_direction] ['var'] data_type_or_implicit
                      [ identifier {variable_dimension} [ = expression ] ]

        ((footnote: it shall be illegal to omit the explicit port_identifier
                    except within a function_prototype or task_prototype.))

     tf_port_direction ::= direction | 'const' 'ref'

})"
  (seq tokstream
       (atts := (vl-parse-0+-attribute-instances))
       (dir  := (vl-parse-optional-port-direction))
       (when (vl-is-token? :vl-kwd-const)
         (return-raw
          (vl-parse-error "BOZO need to implement 'const ref' port on tasks/functions.")))
       (when (vl-is-token? :vl-kwd-var)
         (var := (vl-match)))

       ;; Implicit or explicit datatype, use vl-function-parse-data-type-and-name.
       ((type . name) := (vl-parse-function-data-type-and-name nil)) ;; void not allowed

       (udims := (vl-parse-0+-variable-dimensions))

       (when (vl-is-token? :vl-equalsign)
         (:= (vl-match))
         (default := (vl-parse-expression)))

       (return (make-vl-portdecl
                :name (vl-idtoken->name name)
                :loc (vl-token->loc name)
                  ;; See direction determination: use explicit direction, or
                  ;; inherit previous direction, or use input if this is the
                  ;; first port.
                :dir (cond (dir dir)
                           (prev (vl-portdecl->dir prev))
                           (t :vl-input))
                :type (b* (((vl-datatype-or-implicit type)))

                        (vl-datatype-update-udims
                         udims
                         (if (or (not type.implicitp)
                                 var dir (not prev)
                                 (vl-datatype-case type.type
                                   :vl-coretype (or type.type.pdims
                                                    type.type.signedp)
                                   :otherwise nil))
                             ;; In these cases we're to assume we don't try to
                             ;; inherit a type from the previous port.
                             ;;
                             ;;   - VAR: I think if there's a only just a VAR
                             ;;     keyword, then that should still count as being a
                             ;;     type (logic), because that's how it works in
                             ;;     module ports.
                             ;;
                             ;;   - DIR: If there's a direction but no type, then
                             ;;     we're to assume it's a logic and not inherit the
                             ;;     previous port's type.  See "Type Determination"
                             ;;     above.
                             ;;
                             ;;   - (NOT PREV): If it's the first port and there's
                             ;;     no type, then we're to assume it's a logic.
                             ;;
                             ;;   - Not implicit: explicit datatype given,
                             ;;   definitely use that
                             ;;
                             ;;   - pdims or signedp: implicit type, but enough type
                             ;;   info to rule out using the previous.
                             type.type

                           (vl-portdecl->type prev))))

                :default default
                :atts atts
                :nettype nil))))

(defparser vl-parse-tf-port-list-aux (prev)
  :parents (vl-parse-tf-port-list)
  :guard (or (not prev)
             (vl-portdecl-p prev))
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :count strong
  :fails gracefully
  (seq tokstream
       (first := (vl-parse-tf-port-item prev))
       (unless (vl-is-token? :vl-comma)
         (return (list first)))
       (:= (vl-match))
       (rest := (vl-parse-tf-port-list-aux first))
       (return (cons first rest))))

(defparser vl-parse-tf-port-list ()
  :short "Matches @('tf_port_list'), not for prototypes."
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :count strong
  :fails gracefully
  (seq tokstream
       (ans := (vl-parse-tf-port-list-aux nil))
       (return ans)))

(defaggregate vl-tf-parsed-var-id
  :short "Temporary structure used when parsing @('list_of_tf_variable_identifiers')."
  :tag :vl-tf-parsed-var-id
  ((name    vl-idtoken-p)
   (udims   vl-dimensionlist-p)
   (default vl-maybe-expr-p)))

(deflist vl-tf-parsed-var-idlist-p (x)
  (vl-tf-parsed-var-id-p x))

(defparser vl-parse-tf-variable-identifier ()
  :short "Matches @('port_identifier { variable_dimension } [ '=' expression ]')."
  :result (vl-tf-parsed-var-id-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
       (name  := (vl-match-token :vl-idtoken))
       (udims := (vl-parse-0+-ranges))
       (when (vl-is-token? :vl-equalsign)
         (:= (vl-match))
         (default := (vl-parse-expression)))
       (return (make-vl-tf-parsed-var-id :name name
                                         :udims (vl-ranges->dimensions udims)
                                         :default default))))

(defparser vl-parse-list-of-tf-variable-identifiers ()
  :short "Matches @('list_of_tf_variable_identifiers')."
  :long "@({
             list_of_tf_variable_identifiers ::= port_identifier { variable_dimension } [ '=' expression ]
                                                 { ',' port_identifier { variable_dimension } [ '=' expression ] }
         })"
  :result (vl-tf-parsed-var-idlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-tf-variable-identifier))
       (unless (vl-is-token? :vl-comma)
         (return (list first)))
       (:= (vl-match))
       (rest := (vl-parse-list-of-tf-variable-identifiers))
       (return (cons first rest))))

(define vl-make-tf-ports-from-parsed-ids ((ids vl-tf-parsed-var-idlist-p)
                                          &key
                                          (dir  vl-direction-p)
                                          (type vl-datatype-p)
                                          (atts vl-atts-p))
  :returns (ports vl-portdecllist-p)
  (b* (((when (atom ids))
        nil)
       ((vl-tf-parsed-var-id id1) (car ids)))
    (cons (make-vl-portdecl :name    (vl-idtoken->name id1.name)
                            :loc     (vl-token->loc id1.name)
                            :nettype nil
                            :dir     dir
                            :type    (vl-datatype-update-udims id1.udims type)
                            :default id1.default
                            :atts    atts)
          (vl-make-tf-ports-from-parsed-ids (cdr ids)
                                            :dir dir
                                            :type type
                                            :atts atts))))

(defparser vl-parse-tf-port-declaration (atts)
  :short "Matches @('tf_port_declaration')."
  :long "@({
             tf_port_declaration ::= { attribute_instance } tf_port_direction
                                     [ var ] data_type_or_implicit list_of_tf_variable_identifiers ';'
         })"
  :result (vl-portdecllist-p val)
  :guard (vl-atts-p atts)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       ;; tf_port_direction ::= port_direction | 'const' 'ref'
       (when (vl-is-token? :vl-kwd-const)
         (return-raw
          (vl-parse-error "BOZO implement 'const ref' task/function ports.")))
       (dir := (vl-match-some-token *vl-directions-kwds*))

       ;; I don't think the var actually matters here for anything?
       (when (vl-is-token? :vl-kwd-var)
         (:= (vl-match)))

       ;;    data_type_or_implicit ::= data_type | implicit_data_type
       ;;    implicit_data_type    ::= [ signing ] { packed_dimension }
       (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
         (signing := (vl-match)))
       (when (vl-is-token? :vl-lbrack)
         (ranges := (vl-parse-0+-ranges)))
       (when (or signing ranges)
         ;; Definitely in the implicit case.
         (ids := (vl-parse-list-of-tf-variable-identifiers))
         (:= (vl-match-token :vl-semi))
         (return (vl-make-tf-ports-from-parsed-ids
                  ids
                  :atts atts
                  :dir (cdr (assoc (vl-token->type dir) *vl-directions-kwd-alist*))
                  :type (make-vl-coretype :name    :vl-logic
                                          :signedp (and signing
                                                        (eq (vl-token->type signing) :vl-kwd-signed))
                                          :pdims   (vl-ranges->dimensions ranges)))))

       ;; Otherwise, usual ambiguity between data types and identifiers.
       ;; As with ports, we know this is followed by an identifier.

       (when (vl-is-token? :vl-idtoken)
         (type := (vl-parse-datatype-only-if-followed-by-id))
         (ids := (vl-parse-list-of-tf-variable-identifiers))
         (:= (vl-match-token :vl-semi))
         (return (vl-make-tf-ports-from-parsed-ids
                  ids
                  :atts atts
                  :dir (cdr (assoc (vl-token->type dir) *vl-directions-kwd-alist*))
                  :type (or type
                            (make-vl-coretype :name :vl-logic
                                              :signedp nil
                                              :pdims nil)))))

       ;; Else we'd better have a real datatype.
       (type := (vl-parse-datatype))
       (ids  := (vl-parse-list-of-tf-variable-identifiers))
       (:= (vl-match-token :vl-semi))
       (return (vl-make-tf-ports-from-parsed-ids
                ids
                :atts atts
                :dir (cdr (assoc (vl-token->type dir) *vl-directions-kwd-alist*))
                :type type))))


(defparser vl-parse-tf-item-declaration-noatts (atts)
  :short "Match @('tf_item_declaration') except for attributes."
  :guard (vl-atts-p atts)
  :result (vl-portdecl-or-blockitem-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :long "@({
                tf_item_declaration ::= block_item_declaration
                                      | tf_port_declaration
         })"
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout))
         (decls := (vl-parse-tf-port-declaration atts))
         (return decls))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-tf-item-declaration ()
  :short "Match @('tf_item_declaration'), including attributes."
  :result (vl-portdecl-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts  := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-tf-item-declaration-noatts atts))
        (return decls)))


(defparser vl-parse-0+-tf-item-declarations ()
  :short "Match @('{ tf_item_declaration }')."
  :result (vl-portdecl-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  :long "<p>We use backtracking to know when to stop, because these
declarations can be followed by arbitrary statements, hence it's not clear
whether @('(* ... *)') is the start of a new item declaration or a
statement.</p>"
  (b* ((backup (vl-tokstream-save))
       ((mv erp first tokstream) (vl-parse-tf-item-declaration))
       ((when erp)
        (b* ((tokstream (vl-tokstream-restore backup)))
          (mv nil nil tokstream)))
       ((mv ?erp rest tokstream) (vl-parse-0+-tf-item-declarations)))
    (mv nil (append first rest) tokstream)))


(defparser vl-parse-function-declaration-2012 (atts)
  :guard (vl-atts-p atts)
  :result (vl-fundecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :long "@({
             function_declaration ::= 'function' [ lifetime ] function_body_declaration

             function_body_declaration ::=

               function_data_type_or_implicit                                                           ; Variant 1
                 [ interface_identifier '.' | class_scope ] identifier ';'
                 { tf_item_declaration }
                 { function_statement_or_null }
               'endfunction' [ ':' identifier ]

              | function_data_type_or_implicit
                  [ interface_identifier '.' | class_scope ] identifier '(' [tf_port_list] ')' ';'      ; Variant 2
                  { block_item_declaration }
                  { function_statement_or_null }
                'endfunction' [ ':' identifier ]
         })

         <p>As is often the case with data_type_or_implicit forms, we need to
         backtrack to figure out whether an identifier is a datatype or the
         function name with an empty implicit datatype.  We do this in @(see
         vl-parse-function-data-type-and-name).</p>

         <p>BOZO we don't yet handle the interface identifier / class scope
         stuff, but instead just expect the function name to be a regular
         identifier.</p>"

  (seq tokstream
       (:= (vl-match-token :vl-kwd-function))
       (lifetime := (vl-maybe-parse-lifetime))

       ((rettype . name)  := (vl-parse-function-data-type-and-name t))

       ;; BOZO add better error handling stuff here.

       (when (vl-is-token? :vl-semi)
         ;; Variant 1.  We need to match:
         ;;    { tf_item_declaration } { function_statement_or_null } 'endfunction' [ ':' identifier ]
         (:= (vl-match)) ;; eat the semicolon
         (items := (vl-parse-0+-tf-item-declarations))
         (body := (vl-parse-function-statements))
         (:= (vl-match-token :vl-kwd-endfunction))
         (:= (vl-parse-endblock-name (vl-idtoken->name name) "function/endfunction"))
         (return (b* (((mv portdecls blockitems)
                       (vl-filter-portdecl-or-blockitem-list items)))
                   (list (vl-make-fundecl-for-parser :name      (vl-idtoken->name name)
                                                     :lifetime  lifetime
                                                     :rettype   (vl-datatype-or-implicit->type rettype)
                                                     :inputs    portdecls
                                                     :decls     blockitems
                                                     :loaditems items
                                                     :body      body
                                                     :atts      atts
                                                     :loc       (vl-token->loc name))))))

       ;; Variant 2.  We need to match:
       ;;    '(' [tf_port_list] ')' ';' { block_item_declaration } { function_statement_or_null } 'endfunction' [ ':' identifier ]
       (:= (vl-match-token :vl-lparen))
       (unless (vl-is-token? :vl-rparen) ;; the tf_port_list is optional
         (portdecls := (vl-parse-tf-port-list)))
       (:= (vl-match-token :vl-rparen))
       (:= (vl-match-token :vl-semi))
       (decls   := (vl-parse-0+-block-item-declarations))
       (body    := (vl-parse-function-statements))
       (:= (vl-match-token :vl-kwd-endfunction))
       (:= (vl-parse-endblock-name (vl-idtoken->name name) "function/endfunction"))
       (return (list (vl-make-fundecl-for-parser :name       (vl-idtoken->name name)
                                                 :lifetime   lifetime
                                                 :rettype    (vl-datatype-or-implicit->type rettype)
                                                 :inputs     portdecls
                                                 :decls      decls
                                                 :loaditems  (append portdecls decls)
                                                 :body       body
                                                 :atts       atts
                                                 :loc        (vl-token->loc name))))))

(defparser vl-parse-task-declaration-2012 (atts)
  :guard (vl-atts-p atts)
  :result (vl-taskdecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  :long "@({
              task_declaration ::= 'task' [lifetime] task_body_declaration

              task_body_declaration ::=

                  [ interface_identifier '.' | class_scope ] task_identifier ';'                         ;; Variant 1
                      {tf_item_declaration}
                      {statement_or_null}
                  'endtask' [ ':' task_identifier ]

                | [ interface_identifier '.' | class_scope ] task_identifier '(' [tf_port_list] ')' ';'  ;; Variant 2
                      {block_item_declaration}
                      {statement_or_null}
                  'endtask' [ ':' task_identifier ]
         })

         <p>BOZO we don't yet handle the interface_identifier/class-scope stuff
         but instead just expect the task name to be a regular identifier.</p>"

;Everything through the first semicolon is just like in functions.
; We have done {tf_item_declaration} above in vl-parse-0+-tf-item-declarations
; We definitely have statement_or_null already.
; We have {block_item_declaration} in (vl-parse-0+-block-item-declarations)
; So I think this is going to basically just be the same as for functions.

  (seq tokstream
       (:= (vl-match-token :vl-kwd-task))
       (lifetime := (vl-maybe-parse-lifetime))
       ;; BOZO eventually handle [ interface_identifier '.' | class_scope ] here.
       (name := (vl-match-token :vl-idtoken))

       (when (vl-is-token? :vl-semi)
         ;; Variant 1.  We need to match:
         ;;      { tf_item_declaration }
         ;;      { statement_or_null }
         ;;   'endtask' [ ':' identifier ]
         (:= (vl-match)) ;; eat the semicolon
         (items := (vl-parse-0+-tf-item-declarations))
         (body := (vl-parse-function-statements)) ;; yep, this does the right thing
         (:= (vl-match-token :vl-kwd-endtask))
         (:= (vl-parse-endblock-name (vl-idtoken->name name) "task/endtask"))
         (return (b* (((mv portdecls blockitems)
                       (vl-filter-portdecl-or-blockitem-list items)))
                   (list (vl-make-taskdecl-for-parser :name      (vl-idtoken->name name)
                                                      :lifetime  lifetime
                                                      :ports     portdecls
                                                      :decls     blockitems
                                                      :loaditems items
                                                      :body      body
                                                      :atts      atts
                                                      :loc       (vl-token->loc name))))))

       ;; Variant 2.  We need to match:
       ;;   '(' [tf_port_list] ')' ';'
       ;;       { block_item_declaration }
       ;;       { statement_or_null }
       ;;   'endtask' [ ':' identifier ]
       (:= (vl-match-token :vl-lparen))
       (unless (vl-is-token? :vl-rparen) ;; the tf_port_list is optional
         (portdecls := (vl-parse-tf-port-list)))
       (:= (vl-match-token :vl-rparen))
       (:= (vl-match-token :vl-semi))
       (decls   := (vl-parse-0+-block-item-declarations))
       (body    := (vl-parse-function-statements))
       (:= (vl-match-token :vl-kwd-endtask))
       (:= (vl-parse-endblock-name (vl-idtoken->name name) "task/endtask"))
       (return (list (vl-make-taskdecl-for-parser :name       (vl-idtoken->name name)
                                                  :lifetime   lifetime
                                                  :ports      portdecls
                                                  :decls      decls
                                                  :loaditems  (append portdecls decls)
                                                  :body       body
                                                  :atts       atts
                                                  :loc        (vl-token->loc name))))))



; -----------------------------------------------------------------------------
;
;                            Compatibility Wrappers
;
; -----------------------------------------------------------------------------

(defparser vl-parse-function-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-fundecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         (ans := (vl-parse-function-declaration-2005 atts))
         (return ans))
       ;; BOZO 2012 version
       (ans := (vl-parse-function-declaration-2012 atts))
       (return ans)))

(defparser vl-parse-task-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-taskdecllist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         (ans := (vl-parse-task-declaration-2005 atts))
         (return ans))
       (ans := (vl-parse-task-declaration-2012 atts))
       (return ans)))

