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
(include-book "expressions")
(include-book "assignments")
(include-book "delays")
(include-book "strengths")
(include-book "datatypes")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/port-tools")
(local (include-book "../../util/arithmetic"))


(defsection parse-insts
  :parents (parser)
  :short "Functions for parsing module instances.")

(local (xdoc::set-default-parents parse-insts))

(local (in-theory (disable ;consp-when-vl-expr-p
                           acl2::consp-under-iff-when-true-listp
                           ;consp-when-vl-atom-p
                           ;consp-when-vl-atomguts-p
                           default-car
                           default-cdr)))


(defsection special-note-about-blank-ports
  :short "Clarification regarding how empty module port lists are handled."
  :long "<p>The Verilog grammar contains a nasty ambiguity in handling
arguments for module instances due to the possibility of \"blank ports\".
Blank ports may be used to model an instantiation where a port is not
connected to anything.  For instance, after writing</p>

@({
    module m (a, b, c) ; ... ; endmodule
})

<p>In another module we may instantiate M, and not connect anything to port b,
by writing something like this:</p>

@({
    m my_instance (a, , c);
})

<p>In the grammar, this causes the following ambiguity.  Let Epsilon be the
empty production, and note that:</p>

<ul>
<li>Epsilon may be a valid ordered_port_connection.  I think of this as a
    \"blank port.\"  Hence, list_of_port_connections may be Epsilon, and such a
    think might be thought of as a singleton list containing a blank port.</li>

<li>On the other hand, module_instance is said to take an OPTIONAL
    list_of_port_connections.  If we omit the list_of_port_connections
    entirely, we might think of it it as an empty list containing no ports.</li>
</ul>

<p>So in the context of a module instance, what does Epsilon mean?  Is it an
empty list containing no ports, or is it a singleton list containing one
blank port.  The grammar is ambiguous.</p>

<p>To explore how Cadence handles this case, consider the file blank.v, which
explores this question and some related matters.  The short of it (in
particular see inst1a) is that Cadence seems to treat this as an empty list,
with no ports.  And a funny consequence of this is that one cannot instantiate
a one-port module with a blank, unless named argument lists are used.</p>

<p>Cadence's handling seems like the most sensible choice, and we are going to
mimick it.  Because this is somewhat delicate, we also include a number of unit
tests at the bottom of this file.</p>")

; list_of_port_connections ::=
;    ordered_port_connection { ',' ordered_port_connection }
;  | named_port_connection { ',' named_port_connection }
;
; ordered_port_connection ::=
;   {attribute_instance} [expression]
;
; named_port_connection ::=
;   {attribute_instance} '.' identifier '(' [expression] ')'



; SystemVerilog-2012 --------
;
; The only changed rule here is:
;
;    named_port_connection ::=
;       { attribute_instance } '.' identifier [ '(' [ expression ] ')' ]
;     | { attribute_instance } '.*'
;
; The differences are:
;
;  1. The named port list can now contain .*.  We are told in a footnote that
;     the .* must occur at most once in the list_of_port_connections.
;
;  2. The named port connection can now be just a mere .name, without even any
;     parens.  This is mostly equivalent to .name(name), but there are a few
;     differences: see SystemVerilog-2012 section 23.3.2.3 for details.

(defparser vl-parse-list-of-ordered-port-connections ()
  :result (vl-plainarglist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak

  ;; Think of this as "Get me 1+ ordered_port_connections, separated by
  ;; commas."  On success, this always returns at least one port, even if that
  ;; means returning a blank port!  Note that this leads to an unusually weak
  ;; count theorem.

  (seq tokstream

        (atts := (vl-parse-0+-attribute-instances))

        ;; If we see a comma to begin with, then we have a blank port at the
        ;; front of the list.
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-ordered-port-connections))
          (return (cons (make-vl-plainarg :expr nil :atts atts) rest)))

        ;; If we see an rparen, we have just one blank port.
        (when (vl-is-token? :vl-rparen)
          (return (list (make-vl-plainarg :expr nil :atts atts))))

        ;; Otherwise, there should be an expression here.
        (expr := (vl-parse-expression))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-ordered-port-connections)))
        (return (cons (make-vl-plainarg :expr expr :atts atts) rest))))

(defparser vl-parse-named-port-connection ()
  ;; Verilog-2005 or SystemVerilog-2012.  But note: SystemVerilog-2012: does not
  ;; handle .* style ports.
  :result (vl-namedarg-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (:= (vl-match-token :vl-dot))
        (id := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-lparen)
          (:= (vl-match))
          (unless (vl-is-token? :vl-rparen)
            (expr := (vl-parse-expression)))
          (:= (vl-match-token :vl-rparen))
          (return (make-vl-namedarg :name (vl-idtoken->name id)
                                    :expr expr
                                    :nameonly-p nil
                                    :atts atts)))
        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          (return-raw (vl-parse-error "Expected argument to named port connect.")))
        ;; SystemVerilog-2012: no port argument is okay, this is a .name style port.
        (return (make-vl-namedarg :name (vl-idtoken->name id)
                                  :expr (vl-idexpr (vl-idtoken->name id))
                                  :nameonly-p t
                                  :atts atts))))

(defparser vl-parse-list-of-named-port-connections-2005 ()
  :result (vl-namedarglist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-named-port-connection))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-named-port-connections-2005)))
        (return (cons first rest))))

(defparser vl-parse-list-of-named-port-connections-2012 ()
  ;; Returns (args . saw-dot-star)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  :verify-guards nil
  (seq tokstream
        (when (vl-is-token? :vl-dotstar)
          (dotstar := (vl-match)))

        (unless dotstar
          (first := (vl-parse-named-port-connection)))

        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          ((rest . saw-dot-star-in-tail) := (vl-parse-list-of-named-port-connections-2012)))

        (when (and dotstar saw-dot-star-in-tail)
          (return-raw (vl-parse-error "Multiple occurrences of .* in port list.")))

        (when dotstar
          (return (cons rest t)))

        (return (cons (cons first rest)
                      saw-dot-star-in-tail)))
  ///
  (defthm vl-namedarglist-p-of-vl-parse-list-of-named-port-connections-2012
    (vl-namedarglist-p (car (mv-nth 1 (vl-parse-list-of-named-port-connections-2012)))))
  (local (defthm booleanp-of-vl-parse-list-of-named-port-connections-2012
           (booleanp (cdr (mv-nth 1 (vl-parse-list-of-named-port-connections-2012))))))
  (verify-guards vl-parse-list-of-named-port-connections-2012-fn))

(defparser vl-parse-list-of-named-port-connections ()
  :result (vl-arguments-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          (args := (vl-parse-list-of-named-port-connections-2005))
          (return (make-vl-arguments-named :args args
                                           :starp nil)))
        ((args . saw-dot-star) := (vl-parse-list-of-named-port-connections-2012))
        (return (make-vl-arguments-named :args args
                                         :starp (if saw-dot-star t nil)))))

(defparser vl-parse-list-of-port-connections ()
  :result (vl-arguments-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count weak

  ;; Note that this function always returns a non-empty arguments object
  ;; on success.  The modinst production must explicitly handle the empty
  ;; case and NOT call this function if it sees "()".

  (b* ((backup (vl-tokstream-save))
       ((mv erp val tokstream)
        (seq tokstream
              (args := (vl-parse-list-of-ordered-port-connections))
              (return (make-vl-arguments-plain :args args))))
       ((unless erp)
        (mv erp val tokstream))
       (tokstream (vl-tokstream-restore backup)))
    (vl-parse-list-of-named-port-connections)))


; Verilog-2005:
;
;   parameter_value_assignment ::= '#' '(' list_of_parameter_assignments ')'
;
;   list_of_parameter_assignments ::=
;      expression { ',' expression }
;    | named_parameter_assignment { ',' named_parameter_assignment }
;
;   named_parameter_assignment ::=
;     '.' identifier '(' [ mintypmax_expression ] ')'
;
;
; SystemVerilog-2012:
;
;   parameter_value_assignment ::= '#' '(' [ list_of_parameter_assignments ] ')'
;
;   list_of_parameter_assignments ::=
;       ordered_parameter_assignment { ',' ordered_parameter_assignment }
;     | named_parameter_assignment { ',' named_parameter_assignment }
;
;   ordered_parameter_assignment ::= param_expression
;
;   named_parameter_assignment   ::=
;      '.' identifier ( [ param_expression ] )
;
;   param_expression ::= mintypmax_expression | data_type | $
;
; In short, SystemVerilog-2012 is extending the Verilog-2005 grammar by:
;
;   - Permitting completely blank lists, i.e., ``#()``
;   - Permitting datatypes instead of just expressions as values
;   - Allowing mintypmax expressions in plain lists

(local
 (defthm crock-idtoken-of-car
   (implies (vl-is-token? :vl-idtoken)
            (vl-idtoken-p (car (vl-tokstream->tokens))))
   :hints(("Goal" :in-theory (enable vl-is-token?)))))




; Verilog-2005:
;
; module_instantiation ::= identifier [ parameter_value_assignment ]
;                            module_instance { ',' module_instance } ';'
;
; module_instance ::= identifier [range] '(' [list_of_port_connections] ')'

(defparser vl-parse-module-instance-2005 (modname paramargs atts)
  :guard (and (stringp modname)
              (vl-paramargs-p paramargs)
              (vl-atts-p atts))
  :result (vl-modinst-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (instname := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-lbrack)
         (range := (vl-parse-range)))
       (:= (vl-match-token :vl-lparen))
       ;; Note special avoidance of actually parsing () lists.
       (unless (vl-is-token? :vl-rparen)
         (portargs := (vl-parse-list-of-port-connections)))
       (:= (vl-match-token :vl-rparen))
       (return (make-vl-modinst :loc (vl-token->loc instname)
                                :instname (vl-idtoken->name instname)
                                :modname modname
                                :range range
                                :paramargs paramargs
                                :portargs (or portargs (make-vl-arguments-plain :args nil))
                                :atts atts))))

; SystemVerilog-2012:
;
; module_instantiation ::=  identifier [ parameter_value_assignment ]
;                              hierarchical_instance { ',' hierarchical_instance } ';'
;
; hierarchical_instance ::= name_of_instance '(' [ list_of_port_connections ] ')'
;
; name_of_instance ::= identifier { unpacked_dimension }
;
; unpacked_dimension ::= '[' constant_range ']'
;                      | '[' constant_expression ']'
;
; So basically we can now have single-expression instance arrays like [5], and
; also multi-dimensional instance arrays.

(defparser vl-parse-module-instance-2012 (modname paramargs atts)
  :guard (and (stringp modname)
              (vl-paramargs-p paramargs)
              (vl-atts-p atts))
  :result (vl-modinst-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (instname := (vl-match-token :vl-idtoken))
       (udims := (vl-parse-0+-unpacked-dimensions))
       (when (> (len udims) 1)
         (return-raw
          (vl-parse-error "Not yet implemented: multi-dimensional instance arrays.")))
       (:= (vl-match-token :vl-lparen))
       ;; Note special avoidance of actually parsing () lists.
       (unless (vl-is-token? :vl-rparen)
         (portargs := (vl-parse-list-of-port-connections)))
       (:= (vl-match-token :vl-rparen))
       (return (make-vl-modinst :loc (vl-token->loc instname)
                                :instname (vl-idtoken->name instname)
                                :modname modname
                                :range (and (consp udims)
                                            (car udims))
                                :paramargs paramargs
                                :portargs (or portargs (make-vl-arguments-plain :args nil))
                                :atts atts))))

(defparser vl-parse-module-instance (modname paramargs atts)
  :guard (and (stringp modname)
              (vl-paramargs-p paramargs)
              (vl-atts-p atts))
  :result (vl-modinst-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (if (eq (vl-loadconfig->edition config) :verilog-2005)
      (vl-parse-module-instance-2005 modname paramargs atts)
    (vl-parse-module-instance-2012 modname paramargs atts)))



(defparser vl-parse-1+-module-instances (modname paramargs atts)
  :guard (and (stringp modname)
              (vl-paramargs-p paramargs)
              (vl-atts-p atts))
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-module-instance modname paramargs atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-module-instances modname paramargs atts)))
        (return (cons first rest))))

(defparser vl-parse-module-instantiation (atts)
  :guard (vl-atts-p atts)
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (modid := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-pound)
          (paramargs := (vl-parse-parameter-value-assignment)))
        (insts := (vl-parse-1+-module-instances (vl-idtoken->name modid)
                                                (or paramargs
                                                    (make-vl-paramargs-plain :args nil))
                                                atts))
        (:= (vl-match-token :vl-semi))
        (return insts)))



;; BOZO, okay now how do we tell these from UDP instantiations?


; udp_instantiation ::= identifier [drive_strength] [delay2] udp_instance { ',' udp_instance } ';'
;
; udp_instance ::=
;    [name_of_udp_instance] '(' net_lvalue ',' expression { ',' expression } ')'
;
; name_of_udp_instance ::= identifier [range]

(defparser vl-parse-udp-instance (loc modname str delay atts)
  :guard (and (vl-location-p loc)
              (stringp modname)
              (vl-maybe-gatestrength-p str)
              (vl-maybe-gatedelay-p delay)
              (vl-atts-p atts))
  :result (vl-modinst-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-token? :vl-idtoken)
          (inst-id := (vl-match-token :vl-idtoken))
          (when (vl-is-token? :vl-lbrack)
            (range := (vl-parse-range))))
        (:= (vl-match-token :vl-lparen))
        (lvalue := (vl-parse-net-lvalue))
        (:= (vl-match-token :vl-comma))
        (exprs := (vl-parse-1+-expressions-separated-by-commas))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-modinst :loc loc
                                 :instname (and inst-id
                                                (vl-idtoken->name inst-id))
                                 :modname modname
                                 :range range
                                 :paramargs (make-vl-paramargs-plain :args nil)
                                 :portargs  (make-vl-arguments-plain
                                             :args (vl-exprlist-to-plainarglist (cons lvalue exprs)))
                                 :str str
                                 :delay delay
                                 :atts atts))))

(defparser vl-parse-1+-udp-instances (loc modname str delay atts)
  :guard (and (vl-location-p loc)
              (stringp modname)
              (vl-maybe-gatestrength-p str)
              (vl-maybe-gatedelay-p delay)
              (vl-atts-p atts))
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-udp-instance loc modname str delay atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-udp-instances loc modname str delay atts)))
        (return (cons first rest))))

(defconst *vl-all-drivestr-kwds*
  (append (strip-cars *vl-ds0-alist*)
          (strip-cars *vl-ds1-alist*)))

(with-output
 :off prove :gag-mode :goals
 (defparser vl-parse-udp-instantiation (atts)
   :guard (vl-atts-p atts)
   :result (vl-modinstlist-p val)
   :resultp-of-nil t
   :true-listp t
   :fails gracefully
   :count strong
   (seq tokstream
        (modname := (vl-match-token :vl-idtoken))
        (when (and (vl-is-token? :vl-lparen)
                   (vl-lookahead-is-some-token?
                    *vl-all-drivestr-kwds* (cdr (vl-tokstream->tokens))))
          (str := (vl-parse-drive-strength)))
        (when (vl-is-token? :vl-pound)
          (delay := (vl-parse-delay2)))
        (insts := (vl-parse-1+-udp-instances (vl-token->loc modname)
                                             (vl-idtoken->name modname)
                                             str delay atts))
        (:= (vl-match-token :vl-semi))
        (return insts))))



(defun vl-udp/modinst-pick-error-to-report (m-err u-err)
  (declare (xargs :guard t))
  ;; Errors from vl-parse-error-fn have the form (MSG FUNCTION LOC).  This is
  ;; a godawful hack to try to figure out which error is "better".
  (b* ((mloc (if (and (tuplep 3 m-err)
                      (stringp (first m-err))
                      (vl-location-p (third m-err)))
                 (third m-err)
               *vl-fakeloc*))
       (uloc (if (and (tuplep 3 u-err)
                      (stringp (first u-err))
                      (vl-location-p (third u-err)))
                 (third u-err)
               *vl-fakeloc*))
       ((vl-location mloc) mloc)
       ((vl-location uloc) uloc)
       (u-greater (or (> uloc.line mloc.line)
                      (and (= uloc.line mloc.line)
                           (> uloc.col mloc.col)))))
    ;; Prefer the m-err if there's any tie...
    (if u-greater
        u-err
      m-err)))


; It is not always possible to distinguish between udp/module instantiations at
; parse time, because, e.g., "foo bar(x, 3, 5);" might be valid for either one,
; depending upon whether foo is a module or a primitive.  And foo might not yet
; have even been defined, so we really can't tell until later.
;
; The function below is not really that great of a solution.  We just try first
; to treat it as a module instantiation, and if that fails we try to treat it
; as a udp instantiation.  In either case, we make a modinst-p anyway, so
; really all this accomplishes is certain syntactic checks like "if you have a
; strength, you definitely are a UDP so don't allow named arglists", etc.

(defparser vl-parse-udp-or-module-instantiation (atts)
  :guard (vl-atts-p atts)
  :result (vl-modinstlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (b* ((backup (vl-tokstream-save))
       ((mv m-err val tokstream) (vl-parse-module-instantiation atts))
       ((unless m-err)
        (mv m-err val tokstream))
       (tokstream (vl-tokstream-restore backup))
       ((mv u-err val tokstream) (vl-parse-udp-instantiation atts))
       ((unless u-err)
        (mv u-err val tokstream))
       (tokstream (vl-tokstream-restore backup)))
    (mv (vl-udp/modinst-pick-error-to-report m-err u-err)
        nil tokstream)))



; Bind directives

; SystemVerilog-2012 Grammar:
;
;   bind_directive ::=
;      'bind' bind_target_scope [ ':' bind_target_instance_list ] bind_instantiation ';'
;    | 'bind' bind_target_instance bind_instantiation ';'
;
;   bind_target_scope ::= module_identifier | interface_identifier
;
;   bind_target_instance ::= hierarchical_identifier constant_bit_select
;
;   bind_target_instance_list ::= bind_target_instance { ',' bind_target_instance }
;
;   bind_instantiation ::= program_instantiation
;                        | module_instantiation
;                        | interface_instantiation
;                        | checker_instantiation
;
; But we make some simplifications:
;
;   - A bind_target_scope is really just an identifier.
;
;   - The rule for bind_target_instance seems wrong: SystemVerilog-2012 Section 23.11
;     shows examples where they don't have constant_bit_select, etc.  So we just match
;     expressions instead.
;
;   - The rules for bind directives seem wrong -- they have a semicolon but if
;     you look at module_instantiation, program_instantiation,
;     interface_instantiation, and checker_instantiation, they all have their
;     own semicolon.  So we think bind_directive should NOT have a semicolon
;     and we do not eat one.
;
;   - We don't distinguish program/module/interface/checker instantiation and just
;     try to parse modinsts.
;
; With these in place we have:
;
;    bind_directive ::=
;       'bind' identifier [ ':' expression_list ] module_instantiation
;     | 'bind' expression module_instantiation
;
; These are ambiguous so I'll just try to handle them with backtracking.


(defparser vl-parse-bind-directive-scoped (atts)
  ;; Matches 'bind' identifier [ ':' expression_list ] module_instantiation
  :guard (vl-atts-p atts)
  :result (vl-bind-p val)
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-bind))
       (target := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-colon)
         (:= (vl-match))
         (addto := (vl-parse-1+-expressions-separated-by-commas)))
       (modinsts := (vl-parse-module-instantiation nil)) ;; atts??
       (return (make-vl-bind :scope (vl-idtoken->name target)
                             :addto addto
                             :modinsts modinsts
                             :loc (vl-token->loc target)
                             :atts atts))))

(defparser vl-parse-bind-directive-scopeless (atts)
  ;; Matches 'bind' expression module_instantiation
  :guard (vl-atts-p atts)
  :result (vl-bind-p val)
  :fails gracefully
  :count strong
  (seq tokstream
       (kwd := (vl-match-token :vl-kwd-bind))
       (addto := (vl-parse-expression))
       (modinsts := (vl-parse-module-instantiation nil)) ;; atts??
       (return (make-vl-bind :scope nil
                             :addto (list addto)
                             :modinsts modinsts
                             :loc (vl-token->loc kwd)
                             :atts atts))))

(defparser vl-parse-bind-directive (atts)
  :guard (vl-atts-p atts)
  :result (vl-bind-p val)
  :fails gracefully
  :count strong
  (b* ((backup (vl-tokstream-save))
       ((mv m-err val tokstream) (vl-parse-bind-directive-scoped atts))
       ((unless m-err)
        (mv m-err val tokstream))
       (tokstream (vl-tokstream-restore backup))
       ((mv u-err val tokstream) (vl-parse-bind-directive-scopeless atts))
       ((unless u-err)
        (mv u-err val tokstream))
       (tokstream (vl-tokstream-restore backup)))
    (mv (vl-udp/modinst-pick-error-to-report m-err u-err)
        nil tokstream)))

