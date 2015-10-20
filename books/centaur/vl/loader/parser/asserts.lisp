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
(include-book "properties")
(include-book "ports")
(include-book "statements")

(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))

(defxdoc parse-asserts
  :parents (parser)
  :short "Functions for parsing SystemVerilog assertions.")

(local (xdoc::set-default-parents parse-asserts))



(defparser vl-parse-sequence-formal-type ()
  :short "Parse @('sequence_formal_type')."
  :long "@({ sequence_formal_type ::= 'untyped' | 'sequence' | data_type_or_implicit })"
  :result (vl-datatype-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-kwd-untyped)
         (return (make-vl-coretype :name :vl-untyped)))
       (when (vl-is-token? :vl-kwd-sequence)
         (return (make-vl-coretype :name :vl-sequence)))
       (ans := (vl-parse-datatype-or-implicit))
       (return ans)))

(defparser vl-parse-property-formal-type ()
  :short "Parse @('property_formal_type')."
  :long "@({ property_formal_type ::= sequence_formal_type | 'property' })"
  :result (vl-datatype-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-kwd-property)
         (return (make-vl-coretype :name :vl-property)))
       (ans := (vl-parse-sequence-formal-type))
       (return ans)))

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
       (type := (vl-parse-property-formal-type))
       (name := (vl-match-token :vl-idtoken))
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
       (type := (vl-parse-property-formal-type))
       (name := (vl-match-token :vl-idtoken))
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
                           :initval var1.expr
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
         (ports := (vl-parse-1+-sequence-port-items))
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
         (ports := (vl-parse-1+-property-port-items))
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




#||

(defparser vl-parse-concurrent-assertion-statement (name)
  ;; The name is the external name from the surrounding block, if present.
  ;; For instance, foo in "foo : assert property ..."
  :short "Parse any @('concurrent_assertion_statement')."
  :long "@({
              concurrent_assertion_statement ::= assert_property_statement
                                               | assume_property_statement
                                               | cover_property_statement
                                               | cover_sequence_statement
                                               | restrict_property_statement

              assert_property_statement ::= 'assert' 'property' '(' property_spec ')' action_block
              assume_property_statement ::= 'assume' 'property' '(' property_spec ')' action_block
              cover_property_statement ::= 'cover' 'property' '(' property_spec ')' statement_or_null
              cover_sequence_statement ::= 'cover' 'sequence' '('
                                                     [clocking_event]
                                                     [ 'disable' 'iff' '(' expression_or_dist ')' ]
                                                     sequence_expr
                                                 ')'
                                             statement_or_null
              restrict_property_statement::= 'restrict' 'property' '(' property_spec ')' ';'
         })"
  :result (vl-assert-p val)
  :resultp-of-nil nil
  :guard (maybe-stringp name)
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-assert :vl-kwd-assume))
         ;; assert_property_statement ::= 'assert' 'property' '(' property_spec ')' action_block
         ;; assume_property_statement ::= 'assume' 'property' '(' property_spec ')' action_block
         (kwd := (vl-match))
         (:= (vl-match-token :vl-kwd-property))
         (:= (vl-match-token :vl-lparen))
         (spec := (vl-parse-property-spec))
         (:= (vl-match-token :vl-rparen))
         (act := (vl-parse-action-block))
         (return (make-vl-assert-concurrent :name name
                                            :type (case (vl-token->type kwd)
                                                    (:vl-kwd-assert :vl-assert)
                                                    (:vl-kwd-assume :vl-assume)
                                                    (otherwise (impossible)))
                                            :condition spec
                                            :success (vl-actionblock->then act)
                                            :failure (vl-actionblock->else act)
                                            :loc (vl-token->loc kwd))))
       (when (vl-is-token? :vl-kwd-restrict)
         ;; restrict_property_statement::= 'restrict' 'property' '(' property_spec ')' ';'
         (kwd := (vl-match))
         (:= (vl-match-token :vl-kwd-property))
         (:= (vl-match-token :vl-lparen))
         (spec := (vl-parse-property-spec))
         (:= (vl-match-token :vl-rparen))
         (:= (vl-match-token :vl-semi))
         (return (make-vl-assert-concurrent :name name
                                            :type :vl-restrict
                                            :condition spec
                                            :success (make-vl-nullstmt)
                                            :failure (make-vl-nullstmt)
                                            :loc (vl-token->loc kwd))))
       ;; cover_property_statement ::= 'cover' 'property' '(' property_spec ')' statement_or_null
       ;; cover_sequence_statement ::= 'cover' 'sequence' '('
       ;;                                                   [clocking_event]
       ;;                                                   [ 'disable' 'iff' '(' expression_or_dist ')' ]
       ;;                                                   sequence_expr
       ;;                                                   ')'
       ;;                                 statement_or_null
       ;;
       ;; But note that in the ugly sequence case, the stuff in the parens is
       ;; just the same as a property_spec except that it has a sequence_expr
       ;; instead of a property_expr.  There's no difference as far as we're
       ;; concerned. So this reduces to:
       ;;
       ;; cover_property_statement ::= 'cover' 'property' '(' property_spec ')' statement_or_null
       ;; cover_sequence_statement ::= 'cover' 'sequence' '(' property_spec ')' statement_or_null
       (kwd  := (vl-match-token :vl-kwd-cover))
       (kind := (vl-match-some-token '(:vl-kwd-property :vl-kwd-sequence)))
       (:= (vl-match-token :vl-lparen))
       (spec := (vl-parse-property-spec))
       (:= (vl-match-token :vl-rparen))
       (then := (vl-parse-statement-or-null))
       (return (make-vl-assert-concurrent :name name
                                          :type (case (vl-token->type kind)
                                                  (:vl-kwd-property :vl-cover-property)
                                                  (:vl-kwd-sequence :vl-cover-sequence))
                                          :condition spec
                                          :success then
                                          :failure (make-vl-nullstmt)
                                          :loc (vl-token->loc kwd)))))

(defparser vl-parse-concurrent-assertion-item ()
  :short "Parse a @('concurrent_assertion_item')."
  :long "@({
             concurrent_assertion_item ::= [ block_identifier ':' ] concurrent_assertion_statement
                                         | checker_instantiation
         })

         <p>We don't yet support checker instantiation.</p>"
  ;; A checker instantiation looks something like a module instance, but it can
  ;; have property expressions as arguments.  In the long run we may want to
  ;; extend our notion of modinst-p to perhaps be a generalized instance of a
  ;; checker/module/udp/etc.  For now they're just beyond what we can handle.
  :result (vl-assert-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-idtoken)
         (name := (vl-match))
         (:= (vl-match-token :vl-colon)))
       (main := (vl-parse-concurrent-assertion-statement (and name (vl-idtoken->name name))))
       (return main)))

(defparser vl-maybe-parse-assert-deferral ()
  :short "Parse @('#0') or @('final'), if present."
  :result (vl-assertdeferral-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (when (vl-is-token? :vl-final)
         (:= (vl-match))
         (return :vl-defer-final))
       (when (vl-is-token? :vl-pound)
         (:= (vl-match))
         (zero := (vl-match-token :vl-inttoken))
         (return-raw (if (and (eql 0 (vl-inttoken->value zero))
                              (vl-inttoken->wasunsized zero))
                         (seq tokstream
                              (return :vl-defer-0))
                       (vl-parse-error "Expected #0."))))
       (return nil)))


(defparser vl-parse-immediate-assertion-statement (name)
  :short "Parse an @('immediate_assertion_statement')."
  :long "@({
              immediate_assertion_statement ::= simple_immediate_assertion_statement
                                              | deferred_immediate_assertion_statement

              simple_immediate_assertion_statement ::= simple_immediate_assert_statement
                                                     | simple_immediate_assume_statement
                                                     | simple_immediate_cover_statement

              simple_immediate_assert_statement ::= 'assert' '(' expression ')' action_block
              simple_immediate_assume_statement ::= 'assume' '(' expression ')' action_block
              simple_immediate_cover_statement  ::= 'cover' '(' expression ')' statement_or_null

              deferred_immediate_assertion_statement ::= deferred_immediate_assert_statement
                                                       | deferred_immediate_assume_statement
                                                       | deferred_immediate_cover_statement

              deferred_immediate_assert_statement ::= 'assert' '#0' '(' expression ')' action_block
                                                    | 'assert' 'final' '(' expression ')' action_block

              deferred_immediate_assume_statement ::= 'assume' '#0' '(' expression ')' action_block
                                                    | 'assume' 'final' '(' expression ')' action_block

              deferred_immediate_cover_statement ::= 'cover' '#0' '(' expression ')' statement_or_null
                                                   | 'cover' 'final' '(' expression ')' statement_or_null
         })"
  :guard (maybe-stringp name)
  :result (vl-assert-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (type := (vl-match-some-token '(:vl-kwd-assert :vl-kwd-assume :vl-kwd-cover)))
       (deferral := (vl-maybe-parse-assert-deferral))
       (:= (vl-match-token :vl-lparen))
       (expr := (vl-parse-expression))
       (:= (vl-match-token :vl-rparen))
       (when (or (eq (vl-token->type type) :vl-kwd-assert)
                 (eq (vl-token->type type) :vl-kwd-assume))
         (action := (vl-parse-action-block))
         (return (make-vl-assert-immediate :name name
                                           :type (case (vl-token->type type)
                                                   (:vl-kwd-assert :vl-assert)
                                                   (:vl-kwd-assume :vl-assume)
                                                   (otherwise (impossible)))
                                           :deferral deferral
                                           :condition expr
                                           :success (vl-actionblock->then action)
                                           :failure (vl-actionblock->else action)
                                           :loc (vl-token->loc type))))
       ;; else it's cover.
       (stmt := (vl-parse-statement-or-null))
       (return (make-vl-assert-immediate :name name
                                         :type :vl-cover
                                         :deferral deferral
                                         :condition expr
                                         :success stmt
                                         :failure (make-vl-nullstmt)
                                         :loc (vl-token->loc type))))
  ///
  (defthm vl-assert-kind-of-vl-parse-immediate-assertion-statement
    (b* (((mv err assert ?tokstream) (vl-parse-immediate-assertion-statement name)))
      (implies (not err)
               (equal (vl-assert-kind assert) :immediate)))))

(defparser vl-parse-simple-immediate-assertion-statement (name)
  :short "Parse a @('simple_immediate_assertion_statement')."
  :guard (maybe-stringp name)
  :result (vl-assert-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (ret := (vl-parse-immediate-assertion-statement name))
       (when (vl-assert-immediate->deferral ret)
         (return-raw
          (vl-parse-error "Expected a simple immediate assertion (i.e., ~
                           'final' or '#0' is not allowed.)")))
       (return ret)))

(defparser vl-parse-deferred-immediate-assertion-statement (name)
  :short "Parse a @('deferred_immediate_assertion_statement')."
  :guard (maybe-stringp name)
  :result (vl-assert-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (ret := (vl-parse-immediate-assertion-statement name))
       (unless (vl-assert-immediate->deferral ret)
         (return-raw
          (vl-parse-error "Expected a deferred assertion (i.e., you're ~
                           missing 'final' or '#0'.)")))
       (return ret)))


||#


#||
;; ; Deferred Immediate Assertions






;; assertion_item ::= concurrent_assertion_item
;;                  | deferred_immediate_assertion_item

;; deferred_immediate_assertion_item ::= [ block_identifier ':' ] deferred_immediate_assertion_statement

;; crap.  this occurs within statements.  so we're going to need to make this all mutually
;; recursive as part of the statement representation and parser.  whoooo.

;; procedural_assertion_statement ::= concurrent_assertion_statement
;;                                  | immediate_assertion_statement
;;                                  | checker_instantiation            ;; don't support these yet

(defparser vl-parse-procedural-assertion-statement ()
  :short 















immediate:

   assert (expression) action_block
   assume (expression) action_block
   cover (expression) statement_or_null
   assert #0/final (expression) action_block
   assume #0/final (expression) action_block
   cover #0/final (expression) action_block

concurrent:

   assert property (propspec) action_block
   assume property (propspec) action_block
   cover property (propspec) statement_or_null
   expect (propspec) action_block
   cover sequence (propspec-ish) statement_or_null
   restrict property (property_spec);



concurrent_assertion_statement can probably become a single defprod with a type
that is either assert, assume, cover, expect, or restrict.

immediate_assertion_statement can be simple or deferred

simple: assert assume cover 

deferred have #0 or final 

So I think we can build that in.

a deferred immediate assertion item can also have a block identifier, which i
guess can become part of the product.

what about a checker_instantiation?  it looks like it's basically like a module
instance, but can have property arguments strewn about.  let's ignore these for
now.


||#
