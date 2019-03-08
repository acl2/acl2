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
(include-book "datatypes")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

(defxdoc parse-paramdecls
  :parents (parser)
  :short "Functions for parsing parameter declarations."

  :long "<p>See the comments in @(see vl-paramdecl) and also especially in
@(see vl-paramtype) for details on how we represent parameter declarations.
Here are the grammar rules from Verilog-2005:</p>

@({
    local_parameter_declaration ::=
      'localparam' ['signed'] [range] list_of_param_assignments
    | 'localparam' parameter_type list_of_param_assignments

    parameter_declaration ::=
      'parameter' ['signed'] [range] list_of_param_assignments
    | 'parameter' parameter_type list_of_param_assignments

    parameter_type ::=
       'integer' | 'real' | 'realtime' | 'time'

    list_of_param_assignments ::= param_assignment { ',' param_assignment }

    param_assignment ::= identifier = mintypmax_expression
})

<p>SystemVerilog-2012 extends this in three ways.</p>

<p>First, it expands the valid types for value parameters, so that parameters
can now be of any arbitrary data type.  In particular:</p>

@({
    local_parameter_declaration ::=
        'localparam' data_type_or_implicit list_of_param_assignments
      | ...

    parameter_declaration ::=
       'parameter' data_type_or_implicit list_of_param_assignments
      | ...

    data_type_or_implicit ::= data_type
                            | implicit_data_type

    implicit_data_type ::= [ signing ] { packed_dimension }

    signing ::= 'signed' | 'unsigned'
})

<p>Second, it extends parameter assignments so that (1) the default value for
non-local parameters becomes optional, and (2) there can be an arbitrary list
of unpacked dimensions.  However, I don't believe the meaning of these unpacked
dimensions is ever explained, so VL <b>does not support it</b>.  There is no
place for these dimensions in our parsed representation, and our parser will
fail to parse declarations that include such dimensions:</p>

@({
    param_assignment ::= identifier { unpacked_dimension } [ '=' constant_param_expression ]

    constant_param_expression ::= constant_mintypmax_expression | data_type | '$'

    constant_mintypmax_expression ::=
       constant_expression
     | constant_expression : constant_expression : constant_expression
})

<p>It is unclear to me what it would mean to assign a data type to a value
parameter, so the parser currently does not support this.</p>

<p>The @('$') is a special, unbounded integer value.  See SystemVerilog Section
6.20.2.1.</p>

<p>Note that the omitting the default value for a parameter is not legal for
local parameters.  (SystemVerilog-2012, section A.10, note 18).  We enforce
this in the parser.</p>

<p>Finally, SystemVerilog-2012 adds completely new <b>type parameter</b>s in
addition to the <b>value parameters</b> above.  The syntax here is:</p>

@({
    local_parameter_declaration ::=
       ...
     | 'localparam' 'type' list_of_type_assignments

    parameter_declaration ::=
       ...
     | 'parameter' 'type' list_of_type_assignments

    list_of_type_assignments ::= type_assignment { ',' type_assignment }

    type_assignment ::= identifier [ '=' data_type ]
})

<p>Note that, as with value parameters, it is not legal to omit the default
data type for a local type parameter.  We enforce this in the parser.</p>")

(local (xdoc::set-default-parents parse-paramdecls))


; Value Parameters ------------------------------------------------------------

(define vl-update-paramtype-udims ((udims vl-dimensionlist-p)
                                   (x     vl-paramtype-p))
  :guard (and (consp udims)
              (member (vl-paramtype-kind x)
                      '(:vl-implicitvalueparam :vl-explicitvalueparam)))
  :returns (new-x vl-paramtype-p)
  (vl-paramtype-case x
    :vl-implicitvalueparam
    ;; Special hack.  We currently believe that there is no difference between
    ;;
    ;;    parameter [3:0] foo [1:0] = ...
    ;;    parameter logic [3:0] foo [1:0] = ...
    ;;
    ;; I.e., the presence of unpacked dimensions seems to imply that the
    ;; parameter has an explicit type.  So: if we started with an implicit
    ;; parameter and have now encountered some udims, we're going to go ahead
    ;; and turn it into an explicit parameter right at parse time.
    (b* ((signedp (cond ((not x.sign) nil)
                        ((vl-exprsign-equiv x.sign :vl-signed) t)
                        (t nil)))
         (pdims (and x.range
                     (list (vl-range->dimension x.range))))
         (datatype (make-vl-coretype :name :vl-logic
                                     :pdims pdims
                                     :signedp signedp
                                     :udims udims)))
      (make-vl-explicitvalueparam :type datatype
                                  :default x.default
                                  :final-value nil))
    :vl-explicitvalueparam
    (change-vl-explicitvalueparam x :type (vl-datatype-update-udims udims x.type))
    :otherwise
    (progn$ (impossible)
            (vl-paramtype-fix x))))


(defparser vl-parse-param-assignment (atts localp type)
  ;; Verilog-2005:       param_assignment ::= identifier = mintypmax_expression
  ;; SystemVerilog-2012: param_assignment ::= identifier { unpacked_dimension } [ '=' constant_param_expression ]
  :guard (and (vl-atts-p atts)
              (booleanp localp)
              ;; Type: a full or partial paramtype whose default value we haven't read yet.
              (vl-paramtype-p type)
              (member (vl-paramtype-kind type) '(:vl-implicitvalueparam :vl-explicitvalueparam)))
  :result (vl-paramdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (id := (vl-match-token :vl-idtoken))

        (when (not (eq (vl-loadconfig->edition config) :verilog-2005))
          ;; Per the SystemVerilog-2012 grammar, only unpacked_dimensions, not
          ;; variable_dimensions, are allowed here.
          (udims := (vl-parse-0+-unpacked-dimensions)))

        ;; For SystemVerilog-2012, the right hand side is optional but only for
        ;; non-local parameters.
        (when (and (not (vl-is-token? :vl-equalsign))
                   (not (eq (vl-loadconfig->edition config) :verilog-2005))
                   (not localp))
          ;; Special case: SystemVerilog-2012 with a non-local parameter, so
          ;; we're allowed to not have a default value here.
          (return
           (let ((type (if (atom udims)
                           type
                         (vl-update-paramtype-udims udims type))))
             (make-vl-paramdecl :loc (vl-token->loc id)
                                :name (vl-idtoken->name id)
                                :atts atts
                                :localp localp
                                :type type))))

        ;; Otherwise, a default value has been given or is required.
        (:= (vl-match-token :vl-equalsign))

        ;; For SystemVerilog-2012, the default value is supposed to be a
        ;;    constant_param_expression ::= constant_mintypmax_expression | data_type | '$'
        ;; But
        ;;   (1) I don't know what a data_type would mean here so I'm not going to support that, and
        ;;   (2) The lone $ is already supported as a kind of base expression
        ;; So this all just collapses down into a mintypmax expression.
        (default := (vl-parse-mintypmax-expression))
        (return
         (let* ((type (if (eq (vl-paramtype-kind type) :vl-implicitvalueparam)
                          (change-vl-implicitvalueparam type :default default)
                        (change-vl-explicitvalueparam type :default default)))
                (type (if (atom udims)
                          type
                        (vl-update-paramtype-udims udims type))))
           (make-vl-paramdecl :loc (vl-token->loc id)
                              :name (vl-idtoken->name id)
                              :atts atts
                              :localp localp
                              :type type)))))


(defparser vl-parse-list-of-param-assignments (atts localp type)
  ;; list_of_param_assignments ::= param_assignment { ',' param_assignment }
  :guard (and (vl-atts-p atts)
              (booleanp localp)
              (vl-paramtype-p type)
              (member (vl-paramtype-kind type) '(:vl-implicitvalueparam :vl-explicitvalueparam)))
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-param-assignment atts localp type))
        ;; We have to be careful here.  The comma may not belong to us.  For
        ;; instance, we may have something like: module foo #(parameter foo =
        ;; 1, parameter bar = 2), in which case the comma is separating
        ;; parameters, not identifiers.  So, only eat the comma if we see an
        ;; identifier afterward.
        (when (and (vl-is-token? :vl-comma)
                   (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens))))
          (:= (vl-match))
          (rest := (vl-parse-list-of-param-assignments atts localp type)))
        (return (cons first rest))))


; Type Parameters -------------------------------------------------------------

(defparser vl-parse-type-assignment (atts localp)
  ;; SystemVerilog-2012 Only.
  ;; type_assignment ::= identifier [ '=' data_type ]
  :guard (and (vl-atts-p atts)
              (booleanp localp))
  :result (vl-paramdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-equalsign))
        (type := (vl-parse-datatype))
        (return (make-vl-paramdecl
                 :loc  (vl-token->loc id)
                 :name (vl-idtoken->name id)
                 :atts atts
                 :localp localp
                 :type (make-vl-typeparam :default type)))))

(defparser vl-parse-list-of-type-assignments (atts localp)
  ;; SystemVerilog-2012 Only.
  ;; list_of_type_assignments ::= type_assignment { ',' type_assignment }
  :guard (and (vl-atts-p atts)
              (booleanp localp))
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-type-assignment atts localp))
        ;; Tricky.  A list_of_type_assignments can occur in a
        ;; parameter_port_declaration, and parameter_port_declarations are
        ;; comma-separated.  So, just seeing a comma here isn't good enough; we
        ;; need to also look for a subsequent identifier.
        (when (and (vl-is-token? :vl-comma)
                   (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens))))
          (:= (vl-match))
          (rest := (vl-parse-list-of-type-assignments atts localp)))
        (return (cons first rest))))


; Arbitrary Parameters --------------------------------------------------------

(defparser vl-parse-param-or-localparam-declaration-2005 (atts types)
  ;; Verilog-2005 Only.
  :guard (and (vl-atts-p atts)
              ;; Types says what kinds (local or nonlocal) of parameters we permit
              (true-listp types)
              (subsetp types '(:vl-kwd-parameter :vl-kwd-localparam)))
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        ;; Verilog-2005 rules:
        ;;
        ;; local_parameter_declaration ::=
        ;;    'localparam' ['signed'] [range] list_of_param_assignments
        ;;  | 'localparam' parameter_type list_of_param_assignments
        ;;
        ;; parameter_declaration ::=
        ;;    'parameter' ['signed'] [range] list_of_param_assignments
        ;;  | 'parameter' parameter_type list_of_param_assignments
        (start := (vl-match-some-token types))

        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-real :vl-kwd-realtime :vl-kwd-time))
          ;; No range on these types
          (type := (vl-match))
          ;; The type to use is tricky.  Consider the rules from Section 12.2
          ;; of the Verilog-2005 standard.  We are in the case where there is a
          ;; type but no range (because the grammar doesn't permit a range
          ;; here).  In this case, any override value shall be converted to the
          ;; type of the parameter.  So I think we're justified in calling
          ;; these fully specified and saying that we know the type.
          (decls := (vl-parse-list-of-param-assignments
                     atts
                     (eq (vl-token->type start) :vl-kwd-localparam) ;; localp
                     (make-vl-explicitvalueparam
                      :type (case (vl-token->type type)
                              (:vl-kwd-integer  *vl-plain-old-integer-type*)
                              (:vl-kwd-real     *vl-plain-old-real-type*)
                              (:vl-kwd-realtime *vl-plain-old-realtime-type*)
                              (:vl-kwd-time     *vl-plain-old-time-type*)
                              ))))
          (return decls))

        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))

        ;; The type to use is again tricky.  Consider the rules from Section
        ;; 12.2 of the Verilog-2005 standard.
        (decls := (vl-parse-list-of-param-assignments
                     atts
                     (eq (vl-token->type start) :vl-kwd-localparam) ;; localp

                     (mbe :logic
                          (cond
                           ((and (not signed)
                                 (not range))
                            ;; No type or range.  The rule is: use the type and
                            ;; range of the final override value.  This is the
                            ;; fully unspecified, partial case.
                            (make-vl-implicitvalueparam :range nil :sign nil))

                           ((not signed)
                            ;; Range but no type.  The rule is: use this range,
                            ;; and unsigned.
                            (make-vl-implicitvalueparam :range range :sign nil))

                           ((not range)
                            ;; Sign but no range.  Convert the final override
                            ;; value to signed, but keep its range.
                            (make-vl-implicitvalueparam :range nil :sign :vl-signed))

                           (t
                            ;; Sign and range.  This is fully specified.  It
                            ;; will be signed and will keep the range of its
                            ;; declaration.  I think there are a couple of
                            ;; options for how to represent this.  I think I'm
                            ;; just going to allow the partial type to be fully
                            ;; specified, so that it's easy to identify this
                            ;; case in, e.g., pretty printing.
                            (make-vl-implicitvalueparam :range range :sign :vl-signed)))

                          :exec
                          ;; I'll keep the above since it makes all the cases
                          ;; explicit, but it boils down to something very
                          ;; simple:
                          (make-vl-implicitvalueparam :range range
                                                      :sign (and signed :vl-signed)))))

        (return decls)))


(defparser vl-parse-param-or-localparam-declaration-2012 (atts types)
  ;; Verilog-2012 Only.
  :guard (and (vl-atts-p atts)
              ;; Types says what kinds (local or nonlocal) of parameters we permit
              (true-listp types)
              (subsetp types '(:vl-kwd-parameter :vl-kwd-localparam)))
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (start := (vl-match-some-token types)) ;; localparam or parameter

        (when (vl-is-token? :vl-kwd-type)
          ;; local_parameter_declaration ::= ... | 'localparam' 'type' list_of_type_assignments
          ;; parameter_declaration       ::= ... | 'parameter'  'type' list_of_type_assignments
          (:= (vl-match))
          (decls := (vl-parse-list-of-type-assignments atts
                                                       (eq (vl-token->type start) :vl-kwd-localparam)))
          (return decls))

        ;; Otherwise:
        ;; local_parameter_declaration ::= 'localparam' data_type_or_implicit list_of_param_assignments | ...
        ;; parameter_declaration       ::= 'parameter'  data_type_or_implicit list_of_param_assignments | ...
        ;;
        ;; data_type_or_implicit ::= data_type
        ;;                         | implicit_data_type
        ;;
        ;; implicit_data_type ::= [ signing ] { packed_dimension }
        ;;
        ;; signing ::= 'signed' | 'unsigned'
        ;;
        ;; We'll handle the implicit case first.
        (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
          (signing := (vl-match)))

        (when (vl-is-token? :vl-lbrack)
          (dims := (vl-parse-0+-packed-dimensions)))

        (when (or signing dims)
          (decls := (vl-parse-list-of-param-assignments
                     atts
                     (eq (vl-token->type start) :vl-kwd-localparam)
                     (if (or (atom dims)
                             (and (atom (cdr dims))
                                  (vl-dimension-case (car dims) :range)))
                         ;; If any dimensions are provided, there is only one
                         ;; of them and it is an ordinary sized dimension, so
                         ;; this is something like parameter [3:0] foo.  This
                         ;; is a partially implicit parameter; do basically
                         ;; like the Verilog-2005 version does.
                         (make-vl-implicitvalueparam :range (if (atom dims)
                                                                nil
                                                              (vl-dimension->range (car dims)))
                                                     :sign (and signing
                                                                (case (vl-token->type signing)
                                                                  (:vl-kwd-signed   :vl-signed)
                                                                  (:vl-kwd-unsigned :vl-unsigned))))
                       ;; Otherwise: there are multiple or complex dimensions
                       ;; here, but there is no base type like "logic".  That
                       ;; is, we're dealing with something like "parameter
                       ;; signed [3:0][4:0] foo" or perhaps "parameter
                       ;; [3:0][4:0] bar".  I don't know how to reconcile this
                       ;; with the different Verilog rules for implicit versus
                       ;; explicit parameters.  I think the most sensible thing
                       ;; to do here is treat this like an *explicitly* typed
                       ;; parameter, by acting as though it was written as
                       ;; "parameter logic [3:0][4:0] bar" or similar.
                       (make-vl-explicitvalueparam
                        :type (make-vl-coretype :name :vl-logic
                                                :pdims dims
                                                :udims nil
                                                :signedp (and signing
                                                              (case (vl-token->type signing)
                                                                (:vl-kwd-signed   t)
                                                                (:vl-kwd-unsigned nil))))))))
          (return decls))

        ;; Now this is tricky.  We know we don't have a signing or range, but
        ;; implicit_data_type might also be empty!  So valid tails at this
        ;; point include at least:
        ;;
        ;;   ``foo, bar``
        ;;   ``foo = 5``
        ;;   ``foo_t bar = 6``
        ;;
        ;; Basic idea: the sequences ``identifier ,`` and ``identifier =`` can only be the
        ;; start of a list_of_param_assignments.
        ;;
        ;; Things that can validly follow a parameter_declaration or local_parameter_declaration:
        ;;   semicolon (interface_class_item, config_declaration, class_item, package_or_generate_item_declaration,
        ;;              block item declaration)
        ;;   comma or close paren (parameter_port_declaration)
        ;;
        ;; Blah, this parameter_port_declaration stuff looks potentially ambiguous.
        ;;
        ;; For now I'm going to just try to implement this using backtracking.
        ;; This might work if we make sure to try to parse the data type first.
        (return-raw
         (b* ((localp    (eq (vl-token->type start) :vl-kwd-localparam))
              (emptytype (make-vl-implicitvalueparam :range nil :sign nil))

              ;; Case 1: maybe there's some data_type there.
              (backup (vl-tokstream-save))
              ((mv some-err some-decls tokstream)
               (seq tokstream
                     (type := (vl-parse-datatype))
                     (decls := (vl-parse-list-of-param-assignments
                                atts localp
                                (make-vl-explicitvalueparam :type type)))
                     (return decls)))
              ((unless some-err)
               ;; It worked, so that's great and we're done.
               (mv some-err some-decls tokstream))
              (some-tokens (vl-tokstream->tokens))
              (tokstream (vl-tokstream-restore backup))

              ;; Case 2: suppose there is no data_type.  Then we should be able
              ;; to just parse the param assignments.
              ((mv empty-err empty-decls tokstream)
               (vl-parse-list-of-param-assignments atts localp emptytype))
              ((unless empty-err)
               ;; It worked.  So there can't be a data type because the second
               ;; token has to be an = sign.  We win and we're done.
               (mv empty-err empty-decls tokstream))
              (empty-tokens (vl-tokstream->tokens))
              (tokstream (vl-tokstream-restore backup)))

           ;; Final cleanup case.  What if neither one works?  We have two
           ;; errors now.  Do the usual thing and choose whichever path got
           ;; farther.
           (if (< (len empty-tokens) (len some-tokens))
               ;; Case 2 got farther.  (it has fewer tokens left)
               (mv empty-err empty-decls tokstream)
             ;; Case 1 got farther.
             (mv some-err some-decls tokstream))))))

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
  (if (equal (vl-loadconfig->edition config) :verilog-2005)
      (vl-parse-param-or-localparam-declaration-2005 atts types)
    (vl-parse-param-or-localparam-declaration-2012 atts types)))



; #(...) style module parameters:
;
;
; Verilog-2005 syntax:
;
;    module_parameter_port_list ::= '#' '(' parameter_declaration { ',' parameter_declaration } ')'

(defparser vl-parse-module-parameter-port-list-aux-2005 ()
  ;; parameter_declaration { ',' parameter_declaration }
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        ;; No attributes, no localparams allowed.
        (first := (vl-parse-param-or-localparam-declaration nil '(:vl-kwd-parameter)))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-module-parameter-port-list-aux-2005)))
        (return (append first rest))))

(defparser vl-parse-module-parameter-port-list-2005 ()
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-pound))
        (:= (vl-match-token :vl-lparen))
        (params := (vl-parse-module-parameter-port-list-aux-2005))
        (:= (vl-match-token :vl-rparen))
        (return params)))

; SystemVerilog-2012 extends this considerably:
;
;       parameter_port_list ::= '#' '(' list_of_param_assignments { ',' parameter_port_declaration } ')'
;                             | '#' '(' parameter_port_declaration { ',' parameter_port_declaration } ')'
;                             | '#' '(' ')'
;
;       parameter_port_declaration ::= parameter_declaration
;                                    | local_parameter_declaration
;                                    | data_type list_of_param_assignments
;                                    | 'type' list_of_type_assignments
;
; This is a bit tricky.
;
; The list_of_param_assignments can match plain, untyped parameters like #( FOO
; = 1, BAR = 2 ).  If this is followed by a data_type parameter port declaration,
; then we could have something like this:
;
;     #( FOO = 1,
;        BAR [3:0] = 4,
;        foo_t BAZ = 2,
;        ...)
;
; Our strategy is to use back-tracking to match as many plain parameter
; assignments as we can, and then switch to just parsing a parameter port
; declaration list.

(defconst *vl-parse-0+-param-assignments-implicit-type*
  ;; Type for plain param_assignments (to avoid re-consing)
  ;;  - I'm not at all clear what the type of these parameter assignments should be, but
  ;;    it seems most reasonable to treat them as plain-Jane, implicit value parameters,
  ;;    as we would do if someone had written "parameter" first.
  (make-vl-implicitvalueparam :range nil :sign nil))

(defparser vl-parse-0+-param-assignments (leading-comma-required)
  ;; Only intended for use in vl-parse-module-parameter-port-list-2012
  ;;
  ;; We match an optional list_of_param_assignments.
  ;;   If it is followed by a comma, we read up to the comma (but does not eat the comma)
  ;;   If it is followed by a right paren, we read up to the paren (but do not eat the paren)
  ;;
  ;; Otherwise, we assume we have made a mistake and there are no
  ;; param_assignments here that we want.  Note that it is legal to have type-
  ;; and RHS-free param_assignments like #(foo).  So by naively looking for as
  ;; many param assignments as we can find, if we encounter a parameter
  ;; declaration like #(foo_t SIZE_B = 1), we might mistakenly think that foo_t
  ;; is a type- and RHS-free param assignment.  To avoid this ambiguity, make
  ;; sure that we see a comma or right-paren in order to succeed.
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (declare (xargs :ruler-extenders :all))
  (b* ((backup (vl-tokstream-save))
       ((mv err assigns tokstream)
        (seq tokstream
             (when leading-comma-required
               (:= (vl-match-token :vl-comma)))
             (first := (vl-parse-param-assignment nil ;; atts
                                                  nil ;; localp
                                                  *vl-parse-0+-param-assignments-implicit-type*))
             (unless (vl-is-some-token? '(:vl-comma :vl-rparen))
               (return-raw (mv t nil tokstream)))
             (rest := (vl-parse-0+-param-assignments t))
             (return (cons first rest))))
       ((unless err)
        (mv err assigns tokstream))
       ;; The error can only come from trying to parse 'first', so this is the
       ;; case where we have no more parameter assignments to return.  Restore
       ;; parse state and return nothing.
       (tokstream (vl-tokstream-restore backup)))
    (mv nil nil tokstream)))

(defparser vl-parse-parameter-port-declaration-2012 ()
  ;; SystemVerilog-2012 only.
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-parameter :vl-kwd-localparameter))
         (decls := (vl-parse-param-or-localparam-declaration-2012
                    nil ;; no attributes
                    '(:vl-kwd-parameter :vl-kwd-localparam) ;; allowed to be local or non-local
                    ))
         (return decls))

       (when (vl-is-token? :vl-kwd-type)
         (:= (vl-match))
         (decls := (vl-parse-list-of-type-assignments nil ;; no attributes
                                                      nil ;; not local
                                                      ))
         (return decls))

       ;; Otherwise, it had better be a data_type.
       (type := (vl-parse-datatype))
       (decls := (vl-parse-list-of-param-assignments nil ;; no attributes
                                                     nil ;; not local
                                                     (make-vl-explicitvalueparam :type type)))
       (return decls)))

(defparser vl-parse-1+-parameter-port-declarations-2012 ()
  ;; SystemVerilog-2012 only.
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-parameter-port-declaration-2012))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-parameter-port-declarations-2012)))
       (return (append first rest))))

(defparser vl-parse-module-parameter-port-list-2012 ()
;       parameter_port_list ::= '#' '(' list_of_param_assignments { ',' parameter_port_declaration } ')'
;                             | '#' '(' parameter_port_declaration { ',' parameter_port_declaration } ')'
;                             | '#' '(' ')'
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :prepwork ((local (defthm l0
                      (implies (vl-is-token? :vl-idtoken)
                               (vl-idtoken-p (car (vl-tokstream->tokens))))
                      :hints(("Goal" :in-theory (enable vl-is-token?))))))
  (seq tokstream
        (:= (vl-match-token :vl-pound))
        (:= (vl-match-token :vl-lparen))

        ;; Try to match as many plain param_assignment as we can
        (decls1 := (vl-parse-0+-param-assignments
                    nil ; No comma required before the first param assignment
                    ))

        ;; At this point we should have eaten everything except for the { ,
        ;; parameter_port_declaration } section.  Eat the comma so that we can
        ;; handle these parameter_port_declarations uniformly with the other
        ;; cases.
        (when (vl-is-token? :vl-comma)
          (:= (vl-match)))

        ;; Now either we had a list_of_param_assignments first or we didn't.
        ;; Either way, we ate the commas and now we should be looking at a list
        ;; of 0+ parameter_port_declarations.

        (when (vl-is-token? :vl-rparen)
          ;; Fine, no parameter port declarations, but #() is allowed in
          ;; SystemVerilog and it is also fine if we had any decls1 to not have
          ;; any subsequent, more explicit parameter declarations.
          (:= (vl-match))
          (return decls1))

        ;; Otherwise, there should be some parameter_port_declarations.
        (decls2 := (vl-parse-1+-parameter-port-declarations-2012))
        (:= (vl-match-token :vl-rparen))
        (return (append decls1 decls2))))

(defparser vl-parse-module-parameter-port-list ()
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         (ans := (vl-parse-module-parameter-port-list-2005))
         (return ans))
       (ans := (vl-parse-module-parameter-port-list-2012))
       (return ans)))

(defparser vl-maybe-parse-parameter-port-list ()
  ;; parses the parameter port list if the next token is #
  :result (vl-paramdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-pound)
         (res := (vl-parse-module-parameter-port-list))
         (return res))
       (return nil)))
