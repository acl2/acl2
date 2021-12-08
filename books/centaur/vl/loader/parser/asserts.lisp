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
(include-book "statements")
(include-book "ports")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defxdoc parse-asserts
  :parents (parser)
  :short "Functions for parsing SystemVerilog assertions.")

(local (xdoc::set-default-parents parse-asserts))


(define vl-plausible-start-of-assertion-item-p (&key (tokstream 'tokstream))
  (let ((assertion-keywords '(:vl-kwd-assume :vl-kwd-assert :vl-kwd-cover :vl-kwd-restrict)))
    (if (vl-is-token? :vl-idtoken)
        (and (vl-lookahead-is-token? :vl-colon (cdr (vl-tokstream->tokens)))
             (vl-lookahead-is-some-token? assertion-keywords (cddr (vl-tokstream->tokens))))
      (vl-is-some-token? assertion-keywords))))

(define vl-parse-assertion-item-looks-concurrent-p (&key (tokstream 'tokstream))
  (and (consp (vl-tokstream->tokens))
       (vl-lookahead-is-some-token? '(:vl-kwd-property :vl-kwd-sequence)
                                    (cdr (vl-tokstream->tokens)))))

(defparser vl-parse-assertion-item ()
  :short "Parse an @('assertion_item') into a @(see vl-modelement-p)."
  :long "<p>SystemVerilog-2012 grammar:</p>

         @({
              assertion_item ::= concurrent_assertion_item
                               | deferred_immediate_assertion_item

              deferred_immediate_assertion_item ::= [ block_identifier ':' ] deferred_immediate_assertion_statement

              concurrent_assertion_item ::= [ block_identifier ':' ] concurrent_assertion_statement
                                          | checker_instantiation
         })"
  :prepwork ((local (in-theory (enable vl-plausible-start-of-assertion-item-p))))
  :guard (vl-plausible-start-of-assertion-item-p)
  :guard-debug t
  :result (vl-modelementlist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       ;; We don't actually use vl-parse-concurrent-assertion-item since
       ;; there's so much lookahead going on here.  (But we keep it around
       ;; because concurrent_assertion_item can occur in other contexts than
       ;; assertion_item).
       (when (vl-is-token? :vl-idtoken)
         (blockid := (vl-match))
         (:= (vl-match)))
       ;; We can distinguish between concurrent and immediate assertions by
       ;; checking whether property/sequence occurs after the assert/assume/.
       ;; Blah, have to bottle this up into a function because it screws up
       ;; the progress proof otherwise.
       (when (vl-parse-assertion-item-looks-concurrent-p)
         (cassertion := (vl-parse-concurrent-assertion-statement))
         (return (list (if blockid
                           (change-vl-cassertion cassertion :name (vl-idtoken->name blockid))
                         cassertion))))
       (assertion := (vl-parse-immediate-assertion-statement))
       (unless (vl-assertion->deferral assertion)
         (return-raw
          (vl-parse-error "Top level assertion needs a deferral (i.e., '#0' or 'final').")))
       (return (list (if blockid
                         (change-vl-assertion assertion :name (vl-idtoken->name blockid))
                       assertion)))))



;; I think the following was wrong because a property_formal_type might be a
;; data_type_or_implicit, but we aren't properly accounting for the case where
;; this is implicit and there is nothing at all -- i.e., if there is no type at
;; all, then this will incorrectly eat the ID!

;; (defparser vl-parse-sequence-formal-type ()
;;   :short "Parse @('sequence_formal_type')."
;;   :long "@({ sequence_formal_type ::= 'untyped' | 'sequence' | data_type_or_implicit })"
;;   :result (vl-datatype-p val)
;;   :resultp-of-nil nil
;;   :fails gracefully
;;   :count weak
;;   (seq tokstream
;;        (when (vl-is-token? :vl-kwd-untyped)
;;          (return (make-vl-coretype :name :vl-untyped)))
;;        (when (vl-is-token? :vl-kwd-sequence)
;;          (return (make-vl-coretype :name :vl-sequence)))
;;        (ans := (vl-parse-datatype-or-implicit))
;;        (return ans)))

;; (defparser vl-parse-property-formal-type ()
;;   :short "Parse @('property_formal_type')."
;;   :long "@({ property_formal_type ::= sequence_formal_type | 'property' })"
;;   :result (vl-datatype-p val)
;;   :resultp-of-nil nil
;;   :fails gracefully
;;   :count weak
;;   (seq tokstream
;;        (when (vl-is-token? :vl-kwd-property)
;;          (return (make-vl-coretype :name :vl-property)))
;;        (ans := (vl-parse-sequence-formal-type))
;;        (return ans)))

;; Replacement that fixes the problem:

(defparser vl-parse-property-formal-type-and-id ()
  :short "Parse @('property_formal_type id')."
  :long "<p>Relevant grammar rules</p>
         @({
              sequence_formal_type ::= 'untyped' | 'sequence' | data_type_or_implicit

              property_formal_type ::= sequence_formal_type | 'property'
         })
         <p>We match @('property_formal_type') followed by an ID, which allows
         us to resolve the usual ambiguity due to a @('data_type_or_implicit')
         being followed by a regular identifier.</p>"
  :result (and (consp val)
               (vl-datatype-p (car val))
               (vl-idtoken-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-untyped
                                  :vl-kwd-sequence
                                  :vl-kwd-property))
         (type := (vl-match))
         (id   := (vl-match-token :vl-idtoken))
         (return (cons (make-vl-coretype :name (case (vl-token->type type)
                                                 (:vl-kwd-untyped  :vl-untyped)
                                                 (:vl-kwd-sequence :vl-sequence)
                                                 (:vl-kwd-property :vl-property)))
                       id)))
       ;; Styled loosely after vl-parse-net-declaration
       (return-raw
        (b* ((backup (vl-tokstream-save))
             ;; Even though vl-parse-datatype-or-implicit tries both ways, it
             ;; can still be wrong if, e.g., the datatype was supposed to be
             ;; implicit but it instead found something (identifier) that it
             ;; could parse as a datatype.  So we still may need to backtrack
             ;; here.
             ((mv erp ans tokstream)
              (seq tokstream
                   (type := (vl-parse-datatype-or-implicit))
                   (id   := (vl-match-token :vl-idtoken))
                   (return (cons type id))))
             ((unless erp)
              ;; That worked so great, nothing more to do
              (mv erp ans tokstream))
             ;; Else, didn't work.  Try to instead forge ahead and just match
             ;; an id without a datatype.
             (tokstream (vl-tokstream-restore backup)))
          (seq tokstream
               (id := (vl-match-token :vl-idtoken))
               (return (cons (make-vl-coretype :name :vl-logic) ;; BOZO should this be :vl-untyped ??
                             id)))))))

(defparser vl-parse-property-port-item ()
  :short "Parse @('property_port_item')."
  :long "@({
              property_port_item := { attribute_instance }
                                       [ 'local' [ property_lvar_port_direction ] ]
                                       property_formal_type
                                       formal_port_identifier {variable_dimension}
                                       [ '=' property_actual_arg ]

              property_lval_port_direction ::= 'input'
              formal_port_identifier ::= identifier
         })"
  :result (vl-propport-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (atts := (vl-parse-0+-attribute-instances))
       (when (vl-is-token? :vl-kwd-local)
         (local := (vl-match))
         (when (vl-is-token? :vl-kwd-input)
           ;; You can say input but it's also the default so there's no real
           ;; sense in this, just match it and ignore it.
           (:= (vl-match))))
       ;; (type := (vl-parse-property-formal-type))
       ;; (name := (vl-match-token :vl-idtoken))
       ((type . name) := (vl-parse-property-formal-type-and-id))
       (dims := (vl-parse-0+-variable-dimensions))
       (when (vl-is-token? :vl-equalsign)
         (:= (vl-match))
         (arg := (vl-parse-property-actual-arg
                  ;; It seems vaguely nice to install the name here, since it's easy.
                  (vl-idtoken->name name))))
       (return (make-vl-propport :name   (vl-idtoken->name name)
                                 :localp (if local t nil)
                                 :dir    :vl-input
                                 :type   (vl-datatype-update-udims dims type)
                                 :arg    (or arg
                                             (make-vl-propactual-blank :name (vl-idtoken->name name)))
                                 :atts   atts
                                 :loc    (vl-token->loc name)))))

(defparser vl-parse-sequence-port-item ()
  :short "Parse @('sequence_port_item')."
  :long "@({
             sequence_port_item ::= { attribute_instance }
                                       [ 'local' [ sequence_lvar_port_direction ] ]
                                       sequence_formal_type
                                       formal_port_identifier {variable_dimension}
                                       [ '=' sequence_actual_arg ]

             sequence_lvar_port_direction ::= 'input' | 'inout' | 'output'
             formal_port_identifier ::= identifier
         })"
  :result (vl-propport-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (atts := (vl-parse-0+-attribute-instances))
       (when (vl-is-token? :vl-kwd-local)
         (local := (vl-match))
         (dir := (vl-parse-optional-port-direction)))
       ((type . name) := (vl-parse-property-formal-type-and-id))
       (dims := (vl-parse-0+-variable-dimensions))
       (when (vl-is-token? :vl-equalsign)
         (:= (vl-match))
         (arg := (vl-parse-property-actual-arg
                  ;; It seems vaguely nice to install the name here, since it's easy.
                  (vl-idtoken->name name))))
       (return (make-vl-propport :name   (vl-idtoken->name name)
                                 :localp (if local t nil)
                                 ;; SystemVerilog-2012 Section 16.8.2, Page
                                 ;; 354: "If no direction is explicitly
                                 ;; specified, then the direction input shall
                                 ;; be inferred."
                                 :dir    (or dir :vl-input)
                                 :type   (vl-datatype-update-udims dims type)
                                 :arg    (or arg
                                             (make-vl-propactual-blank :name (vl-idtoken->name name)))
                                 :atts   atts
                                 :loc    (vl-token->loc name)))))

(defparser vl-parse-1+-property-port-items ()
  :short "Parse @('property_port_item { ',' property_port_item }')."
  :result (vl-propportlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-property-port-item))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-property-port-items)))
       (return (cons first rest))))

(defparser vl-parse-1+-sequence-port-items ()
  :short "Parse @('sequence_port_item { ',' sequence_port_item }')."
  :result (vl-propportlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-sequence-port-item))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-sequence-port-items)))
       (return (cons first rest))))

(define vl-make-assertion-vardecls ((type vl-datatype-p)
                                    (vars vl-vardeclassignlist-p)
                                    (loc  vl-location-p))
  :returns (vardecls vl-vardecllist-p)
  (b* (((when (atom vars))
        nil)
       ((vl-vardeclassign var1) (car vars)))
    (cons (make-vl-vardecl :name    var1.id
                           :type    (vl-datatype-update-udims var1.dims type)
                           :initval var1.rhs
                           :loc     loc)
          (vl-make-assertion-vardecls type (cdr vars) loc))))

(defparser vl-parse-0+-assertion-variable-declarations ()
  :short "Parse @(' { assertion_variable_declaration } ')."
  :long "<p>In @('sequence_declaration') and @('property_declaration') we need
         to match however many @('assertion_variable_declaration')s there are,
         followed by a sequence expression or property expression.  It's not
         very easy to tell if we're looking at a user-defined type or the start
         of a sequence/property expression, so we use backtracking.</p>

         @({
              assertion_variable_declaration ::= var_data_type list_of_variable_decl_assignments ';'

              var_data_type ::= data_type
                              | 'var' data_type_or_implicit
         })"
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  (b* ((loc (if (consp (vl-tokstream->tokens))
                (vl-token->loc (car (vl-tokstream->tokens)))
              *vl-fakeloc*))

       ((when (vl-is-token? :vl-kwd-var))
        ;; We are sure this should be a variable declaration.
        (seq tokstream
             (:= (vl-match))
             (type := (vl-parse-datatype-or-implicit))
             (vars := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
             (:= (vl-match-token :vl-semi))
             (rest := (vl-parse-0+-assertion-variable-declarations))
             (return (append (vl-make-assertion-vardecls type vars loc)
                             rest))))

       (backup (vl-tokstream-save))
       ((mv err type tokstream)
        (vl-parse-datatype))

       ;; We need to be careful for an ambiguous case like "foo", where we
       ;; aren't sure if foo is a datatype or a sequence/property expression.

       ((when (and (not err)
                   (vl-is-token? :vl-idtoken)))
        ;; We saw a datatype AND we see an identifier following it, so there's
        ;; no way this can be a sequence/property expression.
        (seq tokstream
             (vars := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
             (:= (vl-match-token :vl-semi))
             (return (vl-make-assertion-vardecls type vars loc))))

       ;; If we get here, either
       ;;   (1) We didn't see anything that looked like a valid datatype, or
       ;;   (2) We saw a potentially valid datatype but there's no ID after
       ;;       it, so we might be looking at something like "foo + bar", where
       ;;       we think foo might be a user-defined type.  But there's no way
       ;;       this can possibly be a valid assertion-variable-declaration
       ;;       because we need a name to follow the type for that.  So, let's
       ;;       assume we're finally to the property/sequence expr, and we need
       ;;       to go ahead and backtrack and try to parse it as that instead.
       (tokstream (vl-tokstream-restore backup)))
    (mv nil nil tokstream)))

(defparser vl-parse-sequence-declaration ()
  :short "Parse @('sequence_declaration')."
  :long "@({
              sequence_declaration ::= 'sequence' sequence_identifier [ '(' [sequence_port_list] ')' ] ';'
                                           { assertion_variable_declaration }
                                           sequence_expr [ ';' ]
                                       'endsequence' [ ':' sequence_identifier ]

              sequence_port_list ::= sequence_port_item { ',' sequence_port_item }
              sequence_identifier ::= identifier
         })"
  :result (vl-sequence-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; BOZO, we could probably do a better job of recovery here, e.g., search for
  ;; the endsequence as we do in endmodule, etc.
  (seq tokstream
       (:= (vl-match-token :vl-kwd-sequence))
       (name := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-lparen)
         (:= (vl-match))
         (when (not (vl-is-token? :vl-rparen))
           (ports := (vl-parse-1+-sequence-port-items)))
         (:= (vl-match-token :vl-rparen)))
       (:= (vl-match-token :vl-semi))
       (decls := (vl-parse-0+-assertion-variable-declarations))
       (expr := (vl-parse-property-expr))
       (when (vl-is-token? :vl-semi)
         (:= (vl-match)))
       (:= (vl-match-token :vl-kwd-endsequence))
       (:= (vl-parse-endblock-name (vl-idtoken->name name) "sequence/endsequence"))
       (return (make-vl-sequence :name (vl-idtoken->name name)
                                 :ports ports
                                 :decls decls
                                 :expr expr
                                 :loc (vl-token->loc name)))))


(defparser vl-parse-property-declaration ()
  :short "Parse @('property_declaration')."
  :long "@({
             property_declaration ::= 'property property_identifier' [ '(' [ property_port_list ] ')' ] ';'
                                         { assertion_variable_declaration }
                                         property_spec [ ';' ]
                                      'endproperty' [ ':' property_identifier ]

             property_port_list ::= property_port_item { ',' property_port_item }
             property_identifier ::= identifier
         })"
  :result (vl-property-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; BOZO, we could probably do a better job of recovery here, e.g., search for
  ;; the endproperty as we do in endmodule, etc.
  (seq tokstream
       (:= (vl-match-token :vl-kwd-property))
       (name := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-lparen)
         (:= (vl-match))
         (when (not (vl-is-token? :vl-rparen))
           (ports := (vl-parse-1+-property-port-items)))
         (:= (vl-match-token :vl-rparen)))
       (:= (vl-match-token :vl-semi))
       (decls := (vl-parse-0+-assertion-variable-declarations))
       (spec := (vl-parse-property-spec))
       (when (vl-is-token? :vl-semi)
         (:= (vl-match)))
       (:= (vl-match-token :vl-kwd-endproperty))
       (:= (vl-parse-endblock-name (vl-idtoken->name name) "property/endproperty"))
       (return (make-vl-property :name (vl-idtoken->name name)
                                 :ports ports
                                 :decls decls
                                 :spec spec
                                 :loc (vl-token->loc name)))))



