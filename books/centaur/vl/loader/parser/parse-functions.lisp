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
(include-book "parse-blockitems")
(include-book "parse-ports")
(include-book "parse-statements")
(local (include-book "../../util/arithmetic"))


; function_range_or_type ::= ['signed'] range | 'integer' | 'real' | 'realtime' | 'time'

(defparser vl-parse-optional-function-range-or-type (tokens warnings)
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

(defparser vl-parse-taskport-declaration (atts tokens warnings)
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

(defparser vl-parse-taskport-list (tokens warnings)
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


(defparser vl-parse-task-item-declaration-noatts (atts tokens warnings)
  :guard (vl-atts-p atts)
  :result (vl-taskport-or-blockitem-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-some-token? '(:vl-kwd-input :vl-kwd-output :vl-kwd-inout))
          (decls := (vl-parse-taskport-declaration atts tokens warnings))
          (:= (vl-match-token :vl-semi))
          (return decls))
        (decls := (vl-parse-block-item-declaration-noatts atts tokens warnings))
        (return decls)))

(defparser vl-parse-task-item-declaration (tokens warnings)
  :result (vl-taskport-or-blockitem-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts  := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-task-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-task-item-declarations (tokens warnings)
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
             (vl-parse-0+-task-item-declarations explore new-warnings)
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
             (mv nil (list ret) tokens warnings))))

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
           (mv nil (list ret) tokens warnings)))))




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

(defparser vl-parse-task-declaration (atts tokens warnings)
  ;; Returns a (singleton) list of task decls instead of a just a task
  ;; declaration, to fit nicely into vl-parse-module-or-generate-item.
  :guard (vl-atts-p atts)
  :result (vl-taskdecllist-p val)
  :true-listp t
  :resultp-of-nil t
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
             (list (make-vl-taskdecl :name       (vl-idtoken->name name)
                                     :automaticp (if automatic t nil)
                                     :ports      ports
                                     :decls      blockitems
                                     :body       stmt
                                     :atts       atts
                                     :loc        (vl-token->loc task))))))

        ;; Variant 2.
        (:= (vl-match-token :vl-lparen))
        (ports := (vl-parse-taskport-list))
        (:= (vl-match-token :vl-rparen))
        (:= (vl-match-token :vl-semi))
        (blockitems := (vl-parse-0+-block-item-declarations))
        (stmt       := (vl-parse-statement-or-null))
        (:= (vl-match-token :vl-kwd-endtask))
        (return (list (make-vl-taskdecl :name       (vl-idtoken->name name)
                                        :automaticp (if automatic t nil)
                                        :ports      ports
                                        :decls      blockitems
                                        :body       stmt
                                        :atts       atts
                                        :loc        (vl-token->loc task))))))


(local
 (encapsulate
   ()

   (local (include-book "../lexer/lexer")) ;; for making test inputs from strings

   (defund taskport-summary (x)
     (declare (xargs :guard (vl-taskport-p x)))
     (b* (((vl-taskport x) x))
       (list x.name x.dir x.type (vl-pretty-maybe-range x.range))))

   (defprojection taskportlist-summary (x)
     (taskport-summary x)
     :guard (vl-taskportlist-p x))

   (defmacro test-parse-taskports (&key input (successp 't) summary)
     `(with-output
        :off summary
        (assert! (b* (((mv erp val tokens warnings)
                       (vl-parse-taskport-list (make-test-tokens ,input)
                                               'blah-warnings))

                      ((unless ,successp)
                       (cw "Expected failure.~%")
                       (cw "Actual erp: ~x0.~%" erp)
                       erp)

                      ((when erp)
                       (cw "Expected success, but ERP is ~x0~%" erp))

                      (spec-summary ',summary)
                      (impl-summary (taskportlist-summary val)))
                   (and (progn$
                         (cw "Spec-Summary: ~x0~%" spec-summary)
                         (cw "Impl-Summary: ~x0~%" impl-summary)
                         (equal spec-summary impl-summary))
                        (progn$
                         (cw "Tokens: ~x0~%" tokens)
                         (not tokens))
                        (progn$
                         (cw "Warnings: ~x0~%" warnings)
                         (equal warnings 'blah-warnings)))))))


   (test-parse-taskports :input ""
                         :successp nil)

   (test-parse-taskports :input "foo"
                         :successp nil)

   (test-parse-taskports :input "input a"
                         :summary (("a" :vl-input :vl-unsigned (no-range))))

   (test-parse-taskports :input "input a, b"
                         :summary (("a" :vl-input :vl-unsigned (no-range))
                                   ("b" :vl-input :vl-unsigned (no-range))))

   (test-parse-taskports :input "input a, b, c, d"
                         :summary (("a" :vl-input :vl-unsigned (no-range))
                                   ("b" :vl-input :vl-unsigned (no-range))
                                   ("c" :vl-input :vl-unsigned (no-range))
                                   ("d" :vl-input :vl-unsigned (no-range))))

;; bozo we're currently ignoring reg.  does it mean anything?
   (test-parse-taskports :input "input reg a"
                         :summary (("a" :vl-input :vl-unsigned (no-range))))

   (test-parse-taskports :input "input reg a, b"
                         :summary (("a" :vl-input :vl-unsigned (no-range))
                                   ("b" :vl-input :vl-unsigned (no-range))))

   (test-parse-taskports :input "input signed a"
                         :summary (("a" :vl-input :vl-signed (no-range))))

   (test-parse-taskports :input "input signed a, b"
                         :summary (("a" :vl-input :vl-signed (no-range))
                                   ("b" :vl-input :vl-signed (no-range))))


   (test-parse-taskports :input "input [3:0] a"
                         :summary (("a" :vl-input :vl-unsigned (range 3 0))))

   (test-parse-taskports :input "input [3:0] a, b"
                         :summary (("a" :vl-input :vl-unsigned (range 3 0))
                                   ("b" :vl-input :vl-unsigned (range 3 0))))

   (test-parse-taskports :input "input [3:0] a, b, \c , d"
                         :summary (("a" :vl-input :vl-unsigned (range 3 0))
                                   ("b" :vl-input :vl-unsigned (range 3 0))
                                   ("c" :vl-input :vl-unsigned (range 3 0))
                                   ("d" :vl-input :vl-unsigned (range 3 0))
                                   ))

   (test-parse-taskports :input "input signed [3:0] a"
                         :summary (("a" :vl-input :vl-signed (range 3 0))))

   (test-parse-taskports :input "input signed [3:0] a, b"
                         :summary (("a" :vl-input :vl-signed (range 3 0))
                                   ("b" :vl-input :vl-signed (range 3 0))))

   (test-parse-taskports :input "input reg [3:0] a"
                         :summary (("a" :vl-input :vl-unsigned (range 3 0))))

   (test-parse-taskports :input "input reg signed [3:0] a"
                         :summary (("a" :vl-input :vl-signed (range 3 0))))

   (test-parse-taskports :input "input integer a"
                         :summary (("a" :vl-input :vl-integer (no-range))))

   (test-parse-taskports :input "input real a"
                         :summary (("a" :vl-input :vl-real (no-range))))

   (test-parse-taskports :input "input time a"
                         :summary (("a" :vl-input :vl-time (no-range))))

   (test-parse-taskports :input "input realtime a"
                         :summary (("a" :vl-input :vl-realtime (no-range))))


;; reg must come before signed
   (test-parse-taskports :input "input signed reg a"
                         :successp nil)

;; signed not okay with int/real/time/realtime
   (test-parse-taskports :input "input integer signed a" :successp nil)
   (test-parse-taskports :input "input signed integer a" :successp nil)
   (test-parse-taskports :input "input real signed a" :successp nil)
   (test-parse-taskports :input "input signed real a" :successp nil)
   (test-parse-taskports :input "input integer signed a" :successp nil)
   (test-parse-taskports :input "input signed integer a" :successp nil)
   (test-parse-taskports :input "input integer signed a" :successp nil)
   (test-parse-taskports :input "input signed integer a" :successp nil)
   (test-parse-taskports :input "input time signed a" :successp nil)
   (test-parse-taskports :input "input signed time a" :successp nil)
   (test-parse-taskports :input "input time signed a" :successp nil)
   (test-parse-taskports :input "input signed time a" :successp nil)
   (test-parse-taskports :input "input realtime signed a" :successp nil)
   (test-parse-taskports :input "input signed realtime a" :successp nil)
   (test-parse-taskports :input "input realtime signed a" :successp nil)
   (test-parse-taskports :input "input signed realtime a" :successp nil)

;; reg not okay with int/real/time/realtime
   (test-parse-taskports :input "input integer reg a" :successp nil)
   (test-parse-taskports :input "input reg integer a" :successp nil)
   (test-parse-taskports :input "input real reg a" :successp nil)
   (test-parse-taskports :input "input reg real a" :successp nil)
   (test-parse-taskports :input "input integer reg a" :successp nil)
   (test-parse-taskports :input "input reg integer a" :successp nil)
   (test-parse-taskports :input "input integer reg a" :successp nil)
   (test-parse-taskports :input "input reg integer a" :successp nil)
   (test-parse-taskports :input "input time reg a" :successp nil)
   (test-parse-taskports :input "input reg time a" :successp nil)
   (test-parse-taskports :input "input time reg a" :successp nil)
   (test-parse-taskports :input "input reg time a" :successp nil)
   (test-parse-taskports :input "input realtime reg a" :successp nil)
   (test-parse-taskports :input "input reg realtime a" :successp nil)
   (test-parse-taskports :input "input realtime reg a" :successp nil)
   (test-parse-taskports :input "input reg realtime a" :successp nil)

;; range not okay with int/real/time/realtime
   (test-parse-taskports :input "input integer [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] integer a" :successp nil)
   (test-parse-taskports :input "input real [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] real a" :successp nil)
   (test-parse-taskports :input "input integer [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] integer a" :successp nil)
   (test-parse-taskports :input "input integer [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] integer a" :successp nil)
   (test-parse-taskports :input "input time [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] time a" :successp nil)
   (test-parse-taskports :input "input time [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] time a" :successp nil)
   (test-parse-taskports :input "input realtime [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] realtime a" :successp nil)
   (test-parse-taskports :input "input realtime [3:0] a" :successp nil)
   (test-parse-taskports :input "input [3:0] realtime a" :successp nil)


   ))