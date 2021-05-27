; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "expressions")
(include-book "ports")
(include-book "../../mlib/find")
(include-book "../../mlib/reorder")
(include-book "../../mlib/port-tools")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))

(defxdoc parse-udps
  :parents (parser)
  :short "Functions for parsing User Defined Primitives (UDPs)."

  :long "<p>There are two different ways to write UDPs, basically you can have
either an integrated port/portdecl list like:</p>

@({
    primitive foo(output reg o, input a, input b);
      ...
    endprimitive
})

<p>Or you can have a more traditional separation between the ports and their
declarations, e.g.,:</p>

@({
    primitive foo(o, a, b);
      output o;
      reg o;
      input a;
      input b;
      ...
    endprimitive
})

<p>In either case, our parser will create a temporary @(see vl-udp-head-p)
structure that records the output port declaration, the associated input port
declarations (in the correct order), and an indication of whether the output
port is a reg or not (i.e., whether or not this is a sequential UDP).</p>

<p>When parsing the body we can use the head information to know whether we
should be parisng a sequential or combinational UDP and whether the initial
statement is well-formed.</p>")

(local (xdoc::set-default-parents parse-udps))


; -----------------------------------------------------------------------------
;
;                                 UDP Symbols
;
; -----------------------------------------------------------------------------
;
; The low-level functions are goofy because these aren't proper keywords; we
; have to look at, e.g., numbers and identifiers and get their contents to see
; whether we are looking at the right things.
;
; edge_symbol ::= 'r' | 'R' | 'f' | 'F' | 'p' | 'P' | 'n' | 'N' | '*'
;
; level_symbol ::= '0' | '1' | 'x' | 'X' | '?' | 'b' | 'B'
;
; output_symbol ::= '0' | '1' | 'x' | 'X'
;
; next_state ::= output_symbol | '-'
;
; current_state ::= level_symbol

(define vl-udp-level-symbol-token-p ((x vl-token-p))
  :parents (vl-parse-level-symbol)
  :guard-debug t
  (case (vl-token->type x)
    (:vl-inttoken
     (let ((etext (vl-inttoken->etext x)))
       (and (consp etext)
            (not (consp (cdr etext)))
            (consp (member (vl-echar->char (car etext)) '(#\0 #\1))))))
    (:vl-idtoken
     (let ((name (vl-idtoken->name x)))
       (consp (member-equal name '("x" "X" "b" "B")))))
    (:vl-qmark
     t)
    (otherwise
     nil)))

(define vl-udp-level-symbol-token->interp ((x vl-token-p))
  :parents (vl-parse-level-symbol)
  :returns (level vl-udpsymbol-p)
  :guard (vl-udp-level-symbol-token-p x)
  (case (vl-token->type x)
    (:vl-inttoken
     (case (vl-echar->char (car (vl-inttoken->etext x)))
       (#\0 :vl-udp-0)
       (#\1 :vl-udp-1)
       (otherwise (progn$ (impossible) :vl-udp-0))))
    (:vl-idtoken
     (let ((name (vl-idtoken->name x)))
       (cond ((member-equal name '("x" "X")) :vl-udp-x)
             ((member-equal name '("b" "B")) :vl-udp-b)
             (t (progn$ (impossible) :vl-udp-0)))))
    (:vl-qmark :vl-udp-?)
    (otherwise
     (progn$ (impossible) :vl-udp-0)))

  :prepwork
  ((local (in-theory (enable vl-udp-level-symbol-token-p)))))

(define vl-udp-edge-symbol-token-p ((x vl-token-p))
  :parents (vl-parse-edge-symbol)
  (case (vl-token->type x)
    (:vl-times t)
    (:vl-idtoken (consp (member-equal (vl-idtoken->name x) '("r" "R" "f" "F" "p" "P" "n" "N"))))
    (otherwise nil)))

(define vl-udp-edge-symbol-token->interp ((x vl-token-p))
  :parents (vl-parse-edge-symbol)
  :guard (vl-udp-edge-symbol-token-p x)
  :returns (sym vl-udpsymbol-p)
  (case (vl-token->type x)
    (:vl-times :vl-udp-*)
    (:vl-idtoken
     (b* ((name (vl-idtoken->name x)))
       (cond ((member-equal name '("r" "R")) :vl-udp-r)
             ((member-equal name '("f" "F")) :vl-udp-f)
             ((member-equal name '("p" "P")) :vl-udp-p)
             ((member-equal name '("n" "N")) :vl-udp-n)
             (t (progn$ (impossible) :vl-udp-*)))))
    (otherwise
     (progn$ (impossible)
             :vl-udp-*)))
  :prepwork
  ((local (in-theory (enable vl-udp-edge-symbol-token-p)))))

(defparser vl-parse-edge-symbol ()
  :short "@('edge_symbol ::= 'r' | 'R' | 'f' | 'F' | 'p' | 'P' | 'n' | 'N' | '*'')."
  :result (vl-udpsymbol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (enable vl-match))))
  (seq tokstream
       (unless (and (consp (vl-tokstream->tokens))
                    (vl-udp-edge-symbol-token-p (car (vl-tokstream->tokens))))
         (return-raw (vl-parse-error "Expected a UDP edge symbol.")))
       (edge := (vl-match))
       (return (vl-udp-edge-symbol-token->interp edge))))

(defparser vl-parse-level-symbol ()
  :short "@('level_symbol ::= '0' | '1' | 'x' | 'X' | '?' | 'b' | 'B'')"
  :result (vl-udpsymbol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (enable vl-match))))
  (seq tokstream
       (unless (and (consp (vl-tokstream->tokens))
                    (vl-udp-level-symbol-token-p (car (vl-tokstream->tokens))))
         (return-raw (vl-parse-error "Expected a UDP level symbol.")))
       (level := (vl-match))
       (return (vl-udp-level-symbol-token->interp level))))

(defparser vl-parse-output-symbol ()
  :short "@('output_symbol ::= '0' | '1' | 'x' | 'X'')"
  :result (vl-udpsymbol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (ans := (vl-parse-level-symbol))
       (when (member ans '(:vl-udp-0 :vl-udp-1 :vl-udp-x))
         (return ans))
       (return-raw
        (vl-parse-error "Expected UDP output symbol."))))

(defparser vl-parse-next-state ()
  :short "@('next_state ::= output_symbol | '-'')"
  :result (vl-udpsymbol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-minus)
         (:= (vl-match))
         (return :vl-udp--))
       (ans := (vl-parse-output-symbol))
       (return ans)))

(defparser vl-parse-current-state ()
  :short "@('current_state ::= level_symbol')"
  :result (vl-udpsymbol-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :prepwork ((local (in-theory (enable vl-match))))
  (seq tokstream
       (ans := (vl-parse-level-symbol))
       (return ans)))



; -----------------------------------------------------------------------------
;
;                          Combinational UDP Tables
;
; -----------------------------------------------------------------------------

(defparser vl-parse-level-input-list ()
  :short "@('level_input_list ::= level_symbol { level_symbol }')"
  :result (vl-udpentrylist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first :s= (vl-parse-level-symbol))
       (when (and (consp (vl-tokstream->tokens))
                  (vl-udp-level-symbol-token-p (car (vl-tokstream->tokens))))
         (rest := (vl-parse-level-input-list)))
       (return (cons first rest))))

(defparser vl-parse-combinational-entry ()
  :short "@('combinational_entry ::= level_input_list ':' output_symbol ';'')"
  :result (vl-udpline-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (inputs := (vl-parse-level-input-list))
       (:= (vl-match-token :vl-colon))
       (output := (vl-parse-output-symbol))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-udpline :inputs inputs
                                :output output
                                ;; Not sequential, so no current value.
                                :current nil))))

(defparser vl-parse-combinational-entries-until-endtable ()
  :short "Matches @('combinational_entry { combinational_entry }')."
  :long "<p>Assumes we should read until @('endtable').</p>"
  :result (vl-udptable-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-combinational-entry))
       (unless (vl-is-token? :vl-kwd-endtable)
         (rest := (vl-parse-combinational-entries-until-endtable)))
       (return (cons first rest))))

(defparser vl-parse-combinational-body ()
  :short "@('combinational_body ::= 'table' combinational_entry { combinational_entry } 'endtable'')"
  :result (vl-udptable-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-table))
       (ans := (vl-parse-combinational-entries-until-endtable))
       (:= (vl-match-token :vl-kwd-endtable))
       (return ans)))


; -----------------------------------------------------------------------------
;
;                          Sequential UDP Tables
;
; -----------------------------------------------------------------------------

(defparser vl-parse-edge-indicator ()
  :short "@('edge_indicator ::= '(' level_symbol level_symbol ')' | edge_symbol')"
  :result (vl-udpentry-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-kwd-lparen)
         (:= (vl-match))
         (prev := (vl-parse-level-symbol))
         (next := (vl-parse-level-symbol))
         (:= (vl-match-token :vl-kwd-rparen))
         (return (make-vl-udpedge :prev prev
                                  :next next)))
       (sym := (vl-parse-edge-symbol))
       (return sym)))

(defparser vl-parse-0+-level-symbols ()
  :short "Matches @('{ level_symbol }')"
  :result (vl-udpentrylist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  :prepwork ((local (in-theory (enable vl-match))))
  (seq tokstream
       (unless (and (consp (vl-tokstream->tokens))
                    (vl-udp-level-symbol-token-p (car (vl-tokstream->tokens))))
         (return nil))

       (first := (vl-match))
       (rest := (vl-parse-0+-level-symbols))
       (return (cons (vl-udp-level-symbol-token->interp first) rest))))

(defparser vl-parse-edge-input-list ()
  :short "@('edge_input_list ::= { level_symbol } edge_indicator { level_symbol }')"
  :result (vl-udpentrylist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (prev := (vl-parse-0+-level-symbols))
       (edge := (vl-parse-edge-indicator))
       (post := (vl-parse-0+-level-symbols))
       (return (append prev (list edge) post))))

(defparser vl-parse-seq-input-list ()
  :short "@('seq_input_list ::= level_input_list | edge_input_list')"
  :result (vl-udpentrylist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  ;; We could be smarter but this should be rare, so just use backtracking
  (b* ((backup (vl-tokstream-save))
       ((mv err inputs tokstream) (vl-parse-edge-input-list))
       ((unless err)
        (mv err inputs tokstream))
       (tokstream (vl-tokstream-restore backup)))
    (vl-parse-level-input-list)))

(defparser vl-parse-sequential-entry ()
  :short "@('sequential_entry ::= seq_input_list ':' current_state ':' next_state ';'')"
  :result (vl-udpline-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  :guard-debug t
  (seq tokstream
       (inputs := (vl-parse-seq-input-list))
       (:= (vl-match-token :vl-colon))
       (current := (vl-parse-current-state))
       (:= (vl-match-token :vl-colon))
       (output := (vl-parse-next-state))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-udpline :inputs inputs
                                :current current
                                :output output))))

(defparser vl-parse-sequential-entries-until-endtable ()
  :short "Matches @('sequential_entry { sequential_entry }')"
  :long "<p>Assumes we should read until @('endtable').</p>"
  :result (vl-udptable-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-sequential-entry))
       (unless (vl-is-token? :vl-kwd-endtable)
         (rest := (vl-parse-sequential-entries-until-endtable)))
       (return (cons first rest))))

(defparser vl-parse-sequential-table ()
  :short "Matches @(''table' sequential_entry { sequential_entry } 'endtable'')"
  :result (vl-udptable-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-table))
       (ans := (vl-parse-sequential-entries-until-endtable))
       (:= (vl-match-token :vl-kwd-endtable))
       (return ans)))

(defparser vl-parse-udp-init-val ()
  :short "@('init_val ::= 1'b0 | 1'b1 | 1'bx | 1'bX | 1'B0 | 1'B1 | 1'Bx | 1'BX | 1 | 0')"
  :long "<p>This is really gross.</p>"
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (int := (vl-match-token :vl-inttoken))
       (return-raw
        (b* (((vl-inttoken int))
             (ans (and (or int.wasunsized
                           (eql int.width 1))
                       (not int.signedp)
                       (cond ((eql int.value 0) |*sized-1'b0*|)
                             ((eql int.value 1) |*sized-1'b1*|)
                             ((and (not int.value)
                                   (equal int.bits '(:vl-xval)))
                              |*sized-1'bx*|)
                             (t nil)))))
          (if ans
              (mv nil ans tokstream)
            (vl-parse-error "Expected valid UDP initial value."))))))

(defparser vl-parse-udp-initial-statement (regname)
  :short "@('udp_initial_statement ::= 'initial' output_port_identifier '=' init_val ';'')"
  :long "<p>Requires that the ID matches the regname, which will be the name of the output port.</p>"
  :guard (and (stringp regname)
              (vl-is-token? :vl-kwd-initial))
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match))
       (id := (vl-match-token :vl-idtoken))
       (unless (equal (vl-idtoken->name id) regname)
         (return-raw
          (vl-parse-error "UDP initial statement must assign to its register.")))
       (:= (vl-match-token :vl-equalsign))
       (val := (vl-parse-udp-init-val))
       (:= (vl-match-token :vl-semi))
       (return val)))



; -----------------------------------------------------------------------------
;
;                                UDP Body
;
; -----------------------------------------------------------------------------

(defaggregate vl-udp-head
  :tag nil
  :layout :fulltree
  :short "Temporary structure for parsing UDPs."
  ((output vl-portdecl-p     "Output port for this UDP.")
   (inputs vl-portdecllist-p "Input ports for this UDP, in order.")
   (sequentialp booleanp     "Whether or not this is a sequential UDP.")))

(defaggregate vl-udp-body
  :short "Temporary structure for parsing UDPs."
  :tag nil
  :layout :fulltree
  ((init  vl-maybe-expr-p "Initial value for the sequential UDP register, if applicable.")
   (table vl-udptable-p   "The parsed state table.")))

(defparser vl-parse-udp-body (head)
  :short "@('udp_body ::= combinational_body | sequential_body')"
  :guard (vl-udp-head-p head)
  :result (vl-udp-body-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (unless (vl-udp-head->sequentialp head)
         (table := (vl-parse-combinational-body))
         (return (make-vl-udp-body :init nil :table table)))

       ;; sequential_body ::= [ udp_initial_statement ] 'table' sequential_entry { sequential_entry } 'endtable'
       (when (vl-is-token? :vl-kwd-initial)
         (init := (vl-parse-udp-initial-statement
                   (vl-portdecl->name (vl-udp-head->output head)))))
       (table := (vl-parse-sequential-table))
       (return (make-vl-udp-body :init init
                                 :table table))))



; -----------------------------------------------------------------------------
;
;                         Integrated UDP Ports/Decls
;
; -----------------------------------------------------------------------------

(define vl-make-udp-portdecls ((ids  vl-idtoken-list-p)
                               (dir  vl-direction-p)
                               (type vl-datatype-p)
                               (atts vl-atts-p))
  :returns (portdecls vl-portdecllist-p)
  (if (atom ids)
      nil
    (cons (make-vl-portdecl :loc  (vl-token->loc (car ids))
                            :name (vl-idtoken->name (car ids))
                            :dir  dir
                            :type type
                            :atts atts)
          (vl-make-udp-portdecls (cdr ids) dir type atts)))
  ///
  (more-returns
   (portdecls (equal (len portdecls) (len ids))
              :name len-of-vl-make-udp-portdecls)))

(defparser vl-parse-udp-input-declaration (atts)
  :short "@('udp_input_declaration ::= { attribute_instance } 'input' list_of_port_identifiers')"
  :guard (vl-atts-p atts)
  :result (vl-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-input))
       ;; list_of_port_identifiers ::= identifier { ',' identifier }
       (ids := (vl-parse-1+-identifiers-separated-by-commas))
       (return (vl-make-udp-portdecls ids :vl-input *vl-plain-old-wire-type* atts))))

(defparser vl-parse-1+-udp-input-declarations-separated-by-commas ()
  :short "@('udp_input_declaration { ',' udp_input_declaration }')"
  :long "<p>This is used only in @('udp_declaration') where it is followed by a
right paren, so we can use the existence of commas to tell whether to keep
going.</p>"
  :result (vl-portdecllist-p val)
  :result-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (atts := (vl-parse-0+-attribute-instances))
       (decls1 := (vl-parse-udp-input-declaration atts))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (decls2 := (vl-parse-1+-udp-input-declarations-separated-by-commas)))
       (return (append decls1 decls2))))

(defparser vl-parse-udp-output-declaration (atts)
  :short "Matches @('udp_output_declaration')."
  :long "@({
  udp_output_declaration ::= { attribute_instance } 'output' port_identifier
                           | { attribute_instance } 'output' 'reg' port_identifier [ '=' constant_expression ] ')
})

<p>But BOZO I don't know what the constant_expression is for, so I don't
implement the optional assignment part here.</p>"
  :guard (vl-atts-p atts)
  :result (vl-portdecl-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-output))
       (when (vl-is-token? :vl-kwd-reg)
         (reg := (vl-match)))
       (id := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-equalsign)
         (return-raw
          (vl-parse-error "Assignments to UDP output reg declarations are not currently supported.")))
       (return
        (make-vl-portdecl :loc (vl-token->loc id)
                          :name (vl-idtoken->name id)
                          :dir :vl-output
                          :type (if reg *vl-plain-old-reg-type* *vl-plain-old-wire-type*)
                          :atts atts)))
  ///
  (defthm type-of-vl-parse-udp-output-declaration
    (b* (((mv err val ?tokstream) (vl-parse-udp-output-declaration atts)))
      (implies (not err)
               (let ((type (vl-portdecl->type val)))
                 (or (equal type *vl-plain-old-wire-type*)
                     (equal type *vl-plain-old-reg-type*)))))
    :rule-classes ((:forward-chaining :trigger-terms ((mv-nth 1 (vl-parse-udp-output-declaration atts)))))))


(defparser vl-parse-integrated-udp-head ()
  :short "Matches port stuff for UDPs with integrated port/port declaration lists."
  :long "<p>This is for UDPs like</p>

@({
     primitive foo(output reg o, input a, input b);
       ...
     endprimitive
})

<p>The formal syntax we're working with here is:</p>

@({
    udp_declaration ::=
      {attribute_instance} 'primitive' udp_identifier '(' udp_declaration_port_list ')' ';'
         udp_body
      'endprimitive'
})

<p>But in this function we assume we have read the \"primitive foo (\" part and
that the next token \"output\".  So all we really want to match is:</p>

@({
     udp_declaration_port_list ')' ';'
})

<p>We return a @(see vl-udp-head-p) that captures the ports correctly.</p>"
  :guard (or (vl-is-token? :vl-kwd-output)
             (vl-is-token? :vl-beginattr))
  :result (vl-udp-head-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       ;; Match udp_declaration_port_list ::=
       ;;   udp_output_declaration ',' udp_input_declaration { ',' udp_input_declaration }
       (outatts := (vl-parse-0+-attribute-instances))
       (output  := (vl-parse-udp-output-declaration outatts))
       (:= (vl-match-token :vl-comma))
       (inputs  := (vl-parse-1+-udp-input-declarations-separated-by-commas))
       (:= (vl-match-token :vl-rparen))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-udp-head :output output
                                 :inputs inputs
                                 :sequentialp (equal (vl-portdecl->type output)
                                                     *vl-plain-old-reg-type*)))))



; -----------------------------------------------------------------------------
;
;                         Traditional UDP Ports/Decls
;
; -----------------------------------------------------------------------------

(deftranssum vl-port/vardecl
  (vl-portdecl vl-vardecl))

(deflist vl-port/vardecllist-p (x)
  (vl-port/vardecl-p x)
  ///
  (defthm vl-port/vardecllist-p-when-vl-portdecllist-p
    (implies (vl-portdecllist-p x)
             (vl-port/vardecllist-p x)))
  (defthm vl-port/vardecllist-p-when-vl-vardecllist-p
    (implies (vl-vardecllist-p x)
             (vl-port/vardecllist-p x))))

(define vl-port/vardecllist->portdecls ((x vl-port/vardecllist-p))
  :returns (portdecls vl-portdecllist-p)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (cond ((atom x)
         nil)
        ((mbe :logic (vl-portdecl-p (car x))
              :exec  (eq (tag (car x)) :vl-portdecl))
         (cons (car x)
               (vl-port/vardecllist->portdecls (cdr x))))
        (t
         (vl-port/vardecllist->portdecls (cdr x)))))

(define vl-port/vardecllist->vardecls ((x vl-port/vardecllist-p))
  :returns (vardecls vl-vardecllist-p)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (cond ((atom x)
         nil)
        ((mbe :logic (vl-vardecl-p (car x))
              :exec  (eq (tag (car x)) :vl-vardecl))
         (cons (car x)
               (vl-port/vardecllist->vardecls (cdr x))))
        (t
         (vl-port/vardecllist->vardecls (cdr x)))))


(defparser vl-parse-udp-reg-declaration (atts)
  :short "@('udp_reg_declaration ::= { attribute_instance } 'reg' variable_identifier')"
  :guard (vl-atts-p atts)
  :result (vl-vardecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-reg))
       (id := (vl-match-token :vl-idtoken))
       (return (make-vl-vardecl :type *vl-plain-old-reg-type*
                                :name (vl-idtoken->name id)
                                :loc (vl-token->loc id)
                                :atts atts))))

(defparser vl-parse-udp-port-declaration ()
  :short "Matches @('udp_port_declaration')."
  :long "@({
              udp_port_declaration ::= udp_output_declaration ';'
                                     | udp_input_declaration ';'
                                     | udp_reg_declaration ';'
         })"
  :result (vl-port/vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (atts := (vl-parse-0+-attribute-instances))
       (when (vl-is-token? :vl-kwd-output)
         (out := (vl-parse-udp-output-declaration atts))
         (:= (vl-match-token :vl-semi))
         (return (list out)))
       (when (vl-is-token? :vl-kwd-input)
         (ins := (vl-parse-udp-input-declaration atts))
         (:= (vl-match-token :vl-semi))
         (return ins))
       (when (vl-is-token? :vl-kwd-reg)
         (reg := (vl-parse-udp-reg-declaration atts))
         (:= (vl-match-token :vl-semi))
         (return (list reg)))
       (return-raw
        (vl-parse-error "Expected UDP port declaration."))))

(defparser vl-parse-0+-udp-port-declarations ()
  :short "Matches @('{ udp_port_declaration }')."
  :long "<p>Uses backtracking to know when to stop, because these can start
  with arbitrary levels of attributes.</p>"
  :result (vl-port/vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (b* ((backup (vl-tokstream-save))

       ((mv err first tokstream) (vl-parse-udp-port-declaration))
       ((when err)
        (b* ((tokstream (vl-tokstream-restore backup)))
          (mv nil nil tokstream)))

       ((mv & rest tokstream) (vl-parse-0+-udp-port-declarations)))
    (mv nil (append first rest) tokstream)))

(defparser vl-parse-1+-udp-port-declarations ()
  :short "Matches @('udp_port_declaration { udp_port_declaration }')."
  :result (vl-port/vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-udp-port-declaration))
       (rest := (vl-parse-0+-udp-port-declarations))
       (return (append first rest))))

(defprojection vl-idtokenlist->names ((x vl-idtoken-list-p))
  :returns (names string-listp :hyp :fguard)
  (vl-idtoken->name x))

(define vl-make-traditional-udp-head
  :short "Cross-check ports against port declarations for traditional UDPs."
  ((name    vl-idtoken-p           "Name of UDP, context for warnings.")
   (portids vl-idtoken-list-p      "ID tokens for the port list, e.g., (o, a, b)")
   (decls   vl-port/vardecllist-p  "Corresponding port declarations."))
  :returns (mv (warning (and (implies warning (not head))
                             (iff (vl-warning-p warning) warning)))
               (head    (implies (not warning)
                                 (vl-udp-head-p head))
                        :hyp :fguard))
  (b* ((loc       (vl-token->loc name))
       (udpname   (vl-idtoken->name name))

       (portdecls (vl-port/vardecllist->portdecls decls))
       (vardecls  (vl-port/vardecllist->vardecls decls))
       (idnames   (vl-idtokenlist->names portids))
       (pdnames   (vl-portdecllist->names portdecls))

       ((unless (<= 2 (len idnames)))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: primitive ~m1 must have at least one ~
                                   output and one input port."
                             :args (list loc udpname)
                             :fatalp t
                             :fn __function__)
            nil))

       ((unless (uniquep idnames))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: primitive ~m1 has duplicate ports: ~&2."
                             :args (list loc udpname (duplicated-members idnames))
                             :fatalp t
                             :fn __function__)
            nil))

       ((unless (uniquep pdnames))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: primitive ~m1 multiply declares ports: ~&2."
                             :args (list loc udpname (duplicated-members pdnames))
                             :fatalp t
                             :fn __function__)
            nil))

       ((unless (or (atom vardecls)
                    (atom (cdr vardecls))))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: primitive ~m1 has ~x2 reg declareations, but ~
                                   only one is allowed."
                             :args (list loc udpname (len vardecls))
                             :fatalp t
                             :fn __function__)
            nil))

       ((unless (equal (mergesort idnames) (mergesort pdnames)))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: ports for primitive ~m1 don't line up with ~
                                   its port declarations.~% ~
                                     - Ports without declarations: ~&2~% ~
                                     - Declarations without ports: ~&3~%"
                             :args (list loc udpname
                                         (difference (mergesort idnames) (mergesort pdnames))
                                         (difference (mergesort pdnames) (mergesort idnames)))
                             :fatalp t
                             :fn __function__)
            nil))

       (outname (car idnames))
       (outdecl (vl-find-portdecl outname portdecls))
       (indecls (vl-portdecls-with-dir :vl-input portdecls))

       ((unless (equal (vl-portdecl->dir outdecl) :vl-output))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: first port of primitive ~m1, ~w2, must be
                                   an output."
                             :args (list loc udpname outname)
                             :fatalp t
                             :fn __function__)
            nil))

       (expected-innames (mergesort (cdr idnames)))
       (declared-innames (mergesort (vl-portdecllist->names indecls)))
       ((unless (equal expected-innames declared-innames))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: ports of primitive ~m1 after the first (~w2)
                                   are not declared as inputs: ~&3."
                             :args (list loc udpname outname
                                         (difference expected-innames declared-innames))
                             :fatalp t
                             :fn __function__)
            nil))

       ((unless (or (atom vardecls)
                    (equal (vl-vardecl->name (car vardecls)) outname)))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: primitive ~m1 has a reg declaration for ~w2 ~
                                    which is not its output ~w3."
                             :args (list loc udpname (vl-vardecl->name (car vardecls))
                                         outname)
                             :fatalp t
                             :fn __function__)
            nil))

       ;; I don't see that the standard explicitly forbids combinations such as:
       ;;
       ;;   output reg q;
       ;;   reg q;
       ;;
       ;; But tools such as Verilog-XL and NCVerilog reject this, saying that q
       ;; has already been declared, which seems basically reasonable given the
       ;; similar prohibition in modules.
       (outdecl-regp (equal (vl-portdecl->type outdecl) *vl-plain-old-reg-type*))
       (vardecl-p    (consp vardecls))
       ((when (and outdecl-regp
                   vardecl-p))
        (mv (make-vl-warning :type :vl-bad-udp
                             :msg "~a0: primitive ~m1 explicitly declares ~w2 as ~
                                   an output reg, so it must not also have a ~
                                   separate reg declaration."
                             :args (list loc udpname outname)
                             :fatalp t
                             :fn __function__)
            nil))

       (outdecl (if vardecl-p
                    (change-vl-portdecl outdecl :type *vl-plain-old-reg-type*)
                  outdecl))

       (sequentialp (equal (vl-portdecl->type outdecl) *vl-plain-old-reg-type*))

       (indecls
        ;; We need to put the input decls in the order that they're mentioned
        ;; in the port list (which may differ from their declared order).  This
        ;; is, after all, the order that other modules instantiate the
        ;; primitive with, and it's also the order that the state table must be
        ;; in (see for instance Verilog-2005 Section 8.1.4).
        (vl-reorder-portdecls (cdr idnames) indecls)))

    (mv nil
        (make-vl-udp-head :output outdecl
                          :inputs indecls
                          :sequentialp sequentialp))))


(defparser vl-parse-traditional-udp-head (udpname)
  :short "Matches port stuff for UDPs with traditional, separated ports and port
declarations lists."
  :long "<p>This is for UDPs like:</p>
@({
     primitive foo(o, a, b);
       output o;
       reg o;
       input a;
       input b;
       ...
     endprimitive
})

<p>The formal syntax we're working with here is:</p>

@({
     udp_declaration ::=

       {attribute_instance} 'primitive' udp_identifier '(' udp_port_list ')' ';'
          udp_port_declaration { udp_port_declaration }
          udp_body
          'endprimitive'
})

<p>We assume we've already read the attributes, primitive keyword, udp identifier, and
leading open paren.  So what remains is to match:</p>

@({
      udp_port_list ')' ';' udp_port_declaration { udp_port_declaration }
})

<p>If the port list and port declaration lists are sensible, we'll return a
@(see vl-udp-head-p) that captures the semantic content of these ports and
their declarations.</p>"
  :guard (vl-idtoken-p udpname)
  :result (vl-udp-head-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       ;; Match udp_port_list ::= output_port_identifier ',' input_port_identifier { ',' input_port_identifier }
       (ports := (vl-parse-1+-identifiers-separated-by-commas))
       (:= (vl-match-token :vl-rparen))
       (:= (vl-match-token :vl-semi))
       (decls := (vl-parse-1+-udp-port-declarations))
       (return-raw
        (b* (((mv warning head) (vl-make-traditional-udp-head udpname ports decls)))
          (mv warning head tokstream)))))

(defparser vl-skip-through-endprimitive (udpname)
  :short "Special error recovery for parse errors encountered during primitives."
  :guard (stringp udpname)
  :result (vl-token-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (unless (vl-is-token? :vl-kwd-endprimitive)
          (:s= (vl-match-any))
          (endkwd := (vl-skip-through-endprimitive udpname))
          (return endkwd))
        (endkwd := (vl-match))
        (:= (vl-parse-endblock-name udpname "primitive/endprimitive"))
        (return endkwd)))

(define vl-make-udp-with-parse-error ((name   stringp)
                                      (minloc vl-location-p)
                                      (maxloc vl-location-p)
                                      (err    vl-warning-p)
                                      (tokens vl-tokenlist-p))
  :returns (udp vl-udp-p)
  (b* (;; We also generate a second error message.
       ;;  - This lets us always show the remaining part of the token stream
       ;;    in each case.
       ;;  - It ensures that any module with a parse error always, absolutely,
       ;;    certainly has a fatal warning, even if somehow the real warning
       ;;    isn't marked as fatal.
       (warn2 (make-vl-warning :type :vl-parse-error
                               :msg "[[ Remaining ]]: ~s0 ~s1.~%"
                               :args (list (vl-tokenlist->string-with-spaces
                                            (take (min 4 (len tokens))
                                                  (list-fix tokens)))
                                           (if (> (len tokens) 4) "..." ""))
                               :fatalp t
                               :fn __function__)))
    (make-vl-udp :name name
                 :output (make-vl-portdecl :name "FAKE_PORT_FOR_UDP_WITH_PARSE_ERROR"
                                           :dir :vl-output
                                           :type *vl-plain-old-wire-type*
                                           :loc minloc)
                 :minloc minloc
                 :maxloc maxloc
                 :warnings (list err warn2))))

(defparser vl-parse-udp-declaration (atts)
  :short "Parse a @('udp_declaration')."
  :guard (vl-atts-p atts)
  :result (vl-udp-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (startkwd := (vl-match-token :vl-kwd-primitive))
       (udpname := (vl-match-token :vl-idtoken))
       (return-raw
        (b* ((backup (vl-tokstream-save))

             ;; Temporarily clear out the warnings so that we can associate any
             ;; warnings encountered while parsing the UDP with the UDP itself.
             (orig-warnings (vl-parsestate->warnings (vl-tokstream->pstate)))
             (tokstream     (vl-tokstream-update-pstate
                             (change-vl-parsestate (vl-tokstream->pstate) :warnings nil)))

             ((mv err udp tokstream)
              (seq tokstream
                   (:= (vl-match-token :vl-lparen))
                   (head := (if (or (vl-is-token? :vl-kwd-output)
                                    (vl-is-token? :vl-beginattr))
                                ;; This is a "integrated udp" -- that is, we're following:
                                ;;    {attribute_instance} 'primitive' udp_identifier '(' udp_declaration_port_list ')' ';'
                                ;;       udp_body
                                ;;    'endprimitive'
                                (vl-parse-integrated-udp-head)
                              ;; This is a traditional UDP -- that is:
                              ;;    {attribute_instance} 'primitive' udp_identifier '(' udp_port_list ')' ';'
                              ;;       udp_port_declaration { udp_port_declaration }
                              ;;       udp_body
                              ;;       'endprimitive'
                              (vl-parse-traditional-udp-head udpname)))
                   (body := (vl-parse-udp-body head))
                   (endkwd := (vl-match-token :vl-kwd-endprimitive))
                   (:= (vl-parse-endblock-name (vl-idtoken->name udpname) "primitive/endprimitive"))
                   (return
                    (b* (((vl-udp-head head))
                         ((vl-udp-body body))
                         (warnings (vl-parsestate->warnings (vl-tokstream->pstate))))
                      (make-vl-udp :name (vl-idtoken->name udpname)
                                   :minloc (vl-token->loc startkwd)
                                   :maxloc (vl-token->loc endkwd)
                                   :output head.output
                                   :inputs head.inputs
                                   :sequentialp head.sequentialp
                                   :table body.table
                                   :initval body.init
                                   :warnings warnings
                                   :atts atts)))))

             ((unless err)
              ;; We read the whole thing and made a valid UDP, so that's great.
              ;; We just need to restore the original warnings and return our answer.
              (let ((tokstream (vl-tokstream-update-pstate
                                (change-vl-parsestate (vl-tokstream->pstate) :warnings orig-warnings))))
                (mv nil udp tokstream)))

             ;; There was some error parsing the UDP.  Stop everything, go back to
             ;; 'primitive foo' part.  Scan for a matching 'endprimitive'.  Throw
             ;; away everything in between and create a fake UDP full of errors.
             (errtokens
              ;; To get the tokens at the point of the error, we need to do this
              ;; before restoring the tokstream!
              (vl-tokstream->tokens))
             (tokstream (vl-tokstream-restore backup)))
          (seq tokstream
               (endkwd := (vl-skip-through-endprimitive (vl-idtoken->name udpname)))
               (return
                (vl-make-udp-with-parse-error (vl-idtoken->name udpname)
                                              (vl-token->loc startkwd)
                                              (vl-token->loc endkwd)
                                              err
                                              errtokens)))))))

