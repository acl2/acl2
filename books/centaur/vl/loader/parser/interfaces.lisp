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
(include-book "utils")
(include-book "../../parsetree")

;; needed for generate regions -- maybe we can refactor to shrink the critical path.
(include-book "modules")

(local (include-book "../../util/arithmetic"))

;; BOZO we don't really implement interfaces yet.



#||

interface_declaration ::=
interface_nonansi_header [ timeunits_declaration ] { interface_item }
endinterface [ : interface_identifier ]
| interface_ansi_header [ timeunits_declaration ] { non_port_interface_item }
endinterface [ : interface_identifier ]
| { attribute_instance } interface interface_identifier ( .* ) ;
[ timeunits_declaration ] { interface_item }
endinterface [ : interface_identifier ]
| extern interface_nonansi_header
| extern interface_ansi_header

interface_nonansi_header ::=
{ attribute_instance } interface [ lifetime ] interface_identifier
{ package_import_declaration } [ parameter_port_list ] list_of_ports ;

interface_ansi_header ::=
{attribute_instance } interface [ lifetime ] interface_identifier
{ package_import_declaration }1 [ parameter_port_list ] [ list_of_port_declarations ] ;

interface_or_generate_item ::=
{ attribute_instance } module_common_item
| { attribute_instance } modport_declaration
| { attribute_instance } extern_tf_declaration

module_common_item ::=
module_or_generate_item_declaration
| interface_instantiation
| program_instantiation
| assertion_item
| bind_directive
| continuous_assign
| net_alias
| initial_construct
| final_construct
| always_construct
| loop_generate_construct
| conditional_generate_construct
| elaboration_system_task

module_or_generate_item_declaration ::=
package_or_generate_item_declaration
| genvar_declaration
| clocking_declaration
| default clocking clocking_identifier ;
| default disable iff expression_or_dist ;

package_or_generate_item_declaration ::=
net_declaration
| data_declaration
| task_declaration
| function_declaration
| checker_declaration
| dpi_import_export
| extern_constraint_declaration
| class_declaration
| class_constructor_declaration
| local_parameter_declaration ;
| parameter_declaration ;
| covergroup_declaration
| overload_declaration
| assertion_item_declaration
| ;

extern_tf_declaration ::=
extern method_prototype ;
| extern forkjoin task_prototype ;

interface_item ::=
port_declaration ;
| non_port_interface_item

non_port_interface_item ::=
generate_region
| interface_or_generate_item
| program_declaration
| interface_declaration
| timeunits_declaration

modport_declaration ::= modport modport_item { , modport_item } ;

modport_item ::= modport_identifier ( modport_ports_declaration { , modport_ports_declaration } )

modport_ports_declaration ::=
{ attribute_instance } modport_simple_ports_declaration
| { attribute_instance } modport_tf_ports_declaration
| { attribute_instance } modport_clocking_declaration

modport_clocking_declaration ::= clocking clocking_identifier

modport_simple_ports_declaration ::=
port_direction modport_simple_port { , modport_simple_port }

modport_simple_port ::=
port_identifier
| . port_identifier ( [ expression ] )

modport_tf_ports_declaration ::=
import_export modport_tf_port { , modport_tf_port }

import_export modport_tf_port { , modport_tf_port }
modport_tf_port ::=
method_prototype
| tf_identifier
import_export ::= import | export

||#


(defparser vl-parse-simple-modport-port (dir atts)
  :guard (and (vl-direction-p dir)
              (vl-atts-p atts))
  :result (vl-modport-port-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens pstate
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
  (seqw tokens pstate
        (port1 := (vl-parse-simple-modport-port dir atts))
        (unless (vl-is-token? :vl-comma)
          (return (list port1)))
        ;; use backtracking to know when to stop, i.e. we see a keyword instead of
        ;; an identifier or .identifier(expr)
        (return-raw
         (seqw-backtrack tokens pstate
                         ((:= (vl-match))
                          (ports2 := (vl-parse-1+-simple-modport-ports dir atts))
                          (return (cons port1 ports2)))
                         ((return (list port1)))))))

;; function_prototype ::= function data_type_or_void function_identifier [ ( [ tf_port_list ] ) ]
(defparser vl-parse-function-prototype ()
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens pstate
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
  (seqw tokens pstate
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
  (seqw-backtrack tokens pstate
                  ((return-raw (vl-parse-function-prototype)))
                  ((return-raw (vl-parse-task-prototype)))))

(defparser vl-parse-modport-tf-port ()
  :resultp-of-nil t
  :fails :gracefully
  :count strong
  (seqw-backtrack tokens pstate
                  ((return-raw (vl-parse-method-prototype)))
                  ((:= (vl-match-token :vl-idtoken))
                   (return nil))))
  

(defparser vl-parse-modport-port ()
  :result (vl-modport-portlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens pstate
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
  (seqw tokens pstate
        (ports1 := (vl-parse-modport-port))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (ports2 := (vl-parse-1+-modport-ports))
          (return (append-without-guard ports1 ports2)))
        (return ports1)))



;; modport_item ::= modport_identifier ( modport_ports_declaration { , modport_ports_declaration } )

(defparser vl-parse-modport-item ()
  :result (vl-modport-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens pstate
        (loc := (vl-current-loc))
        (name := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (ports := (vl-parse-1+-modport-ports))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-modport :name (vl-idtoken->name name)
                                 :ports ports
                                 :loc loc))))


;; modport_declaration ::= modport modport_item { , modport_item } ;

(defparser vl-parse-1+-modport-items ()
  :result (vl-modportlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens pstate
        (port1 := (vl-parse-modport-item))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (ports2 := (vl-parse-1+-modport-items))
          (return (cons port1 ports2)))
        (:= (vl-match-token :vl-semi))
        (return (list port1))))

(defparser vl-parse-modport-decl ()
  :result (vl-modportlist-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens pstate
        (:= (vl-match-token :vl-kwd-modport))
        (modports := (vl-parse-1+-modport-items))
        (return modports)))

#||
(include-book
 "../lexer/lexer")

(vl-parse-modport-decl
 :tokens (make-test-tokens
"
     modport master ( output Foo, Bar, Baz,
                      input  Valid,
                      input  DValid,
                      input  OnFire,
                      output KillMeNow ),

             slave  ( input Foo, Bar, Baz,
                      output  Valid,
                      output  DValid,
                      output  OnFire,
                      input KillMeNow );
")
 :warnings nil
 :config (make-vl-loadconfig))

||#



;; NOTE: modports and other interface internals are not yet parsed by this function
(defparser vl-parse-interface-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; interfaces only exist in SystemVerilog-2012.
  (seqw tokens pstate
        (unless (vl-is-token? :vl-kwd-endinterface)
          (:s= (vl-match-any))
          (info := (vl-parse-interface-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-interface-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-interface-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens pstate
        (:= (vl-match-token :vl-kwd-interface))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-interface-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched interface/endinterface pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-interface
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-interface
                           :msg "Interfaces are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))
