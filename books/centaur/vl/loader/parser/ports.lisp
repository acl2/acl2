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
(include-book "nets")
(include-book "expressions")
(include-book "../../mlib/port-tools") ;; vl-ports-from-portdecls
(local (include-book "../../util/arithmetic"))

(defxdoc parse-ports
  :parents (parser)
  :short "Functions for parsing Verilog and SystemVerilog ports.")

(local (defthm dimension-p-when-vl-range-p
         (implies (vl-range-p x)
                  (vl-dimension-p x))
         :hints(("Goal" :in-theory (enable vl-range-p vl-dimension-p)
                 :expand ((vl-dimension-p x))))))

(local (defthm dimensionlist-p-when-vl-rangelist-p
         (implies (vl-rangelist-p x)
                  (vl-dimensionlist-p x))
         :hints(("Goal" :in-theory (enable vl-rangelist-p vl-dimension-p)))))


;; This file is organized as follows:
;; Portlist parsing:
;;    - Ansi-style ports
;;        *SV2012
;;        *Verilog2005
;;    - Non-ansi-style ports (2005/2012)
;;    - Choosing between ansi/non-ansi
;; Portdecl parsing (non-ansi)
;;    *Verilog2005
;;    *SV2012


;; ===================== PORTLIST PARSING ===========================

(deftagsum vl-parsed-ports
  :short "Top-level, temporary representation for the parsed port list."
  (:ansi
   :base-name vl-ansi-ports
   ((decls vl-ansi-portdecllist-p)))
  (:nonansi
   :base-name vl-nonansi-ports
   ((ports vl-portlist-p))))


(define vl-signing-kwd-to-exprsign ((x vl-token-p))
  :guard (or (eq (vl-token->type x) :vl-kwd-signed)
             (eq (vl-token->type x) :vl-kwd-unsigned))
  :returns (signing vl-exprsign-p)
  (case (vl-token->type x)
    (:vl-kwd-signed :vl-signed)
    (t              :vl-unsigned)))

(defval *vl-directions-kwd-alist*
  '((:vl-kwd-input . :vl-input)
    (:vl-kwd-output . :vl-output)
    (:vl-kwd-inout . :vl-inout)))

(defval *vl-directions-kwds*
  (strip-cars *vl-directions-kwd-alist*))

(defparser vl-parse-port-direction ()
  :result (vl-direction-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? *vl-directions-kwds*)
         (tok := (vl-match))
         (return (cdr (assoc (vl-token->type tok)
                             *vl-directions-kwd-alist*))))
       (return-raw (vl-parse-error "Expected a port direction."))))


(defparser vl-parse-optional-port-direction ()
  :result (vl-maybe-direction-p val)
  :resultp-of-nil t
  :true-listp nil
  :fails never
  :count strong-on-value
  (seq tokstream
       (when (vl-is-some-token? *vl-directions-kwds*)
         (tok := (vl-match))
         (return (cdr (assoc (vl-token->type tok)
                             *vl-directions-kwd-alist*))))
       (return nil)))


(local (in-theory (disable (tau-system) not nth tokstreamp)))

(defparser vl-parse-optional-var-kwd ()
  :fails never
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-kwd-var)
         (var := (vl-match)))
       (return var)))


;; ---------------- SV2012 Ansi Portlist Parsing ------------------

(defparser vl-parse-ansi-portdecl-with-datatype (atts dir nettype var)
  :guard (and (vl-atts-p atts)
              (vl-maybe-direction-p dir)
              (vl-maybe-nettypename-p nettype))
  :result (vl-ansi-portdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; 1.  data_type port_identifier { unpacked_dimension }
  (seq tokstream
       (type := (vl-parse-datatype))
       (portname := (vl-match-token :vl-idtoken))
       (udims := (vl-parse-0+-variable-dimensions))
       (unless (vl-is-some-token? '(:vl-comma :vl-rparen))
         (return-raw
          (vl-parse-error "Unreasonable tokens after
           \"data_type port_identifier { variable_dimension }\"
           style port.")))
       (return (make-vl-ansi-portdecl :atts atts
                                      :dir dir
                                      :nettype nettype
                                      :varp (and var t)
                                      :type type
                                      :name (vl-idtoken->name portname)
                                      :udims udims
                                      :loc (vl-token->loc portname)))))


(defparser vl-parse-ansi-portdecl-with-implicit-type (atts dir nettype var)
  :guard (and (vl-atts-p atts)
              (vl-maybe-direction-p dir)
              (vl-maybe-nettypename-p nettype))
  :result (vl-ansi-portdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; 2.  [ signing ] { packed_dimension } port_identifier { unpacked_dimension }
  (seq tokstream
       (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
         (signing := (vl-match)))
       (when (vl-is-token? :vl-lbrack)
         (ranges := (vl-parse-0+-ranges)))
       (portname := (vl-match-token :vl-idtoken))
       (udims := (vl-parse-0+-variable-dimensions))
       (unless (vl-is-some-token? '(:vl-comma :vl-rparen))
         (return-raw
          (vl-parse-error "Unreasonable tokens after
      \"[ signing ] { packed_dimension } port_identifier { variable_dimension }\"
      style port.")))
       (return (make-vl-ansi-portdecl :atts atts
                                      :dir dir
                                      :nettype nettype
                                      :varp (and var t)
                                      :signedness (and signing
                                                       (vl-signing-kwd-to-exprsign signing))
                                      :pdims ranges
                                      :name (vl-idtoken->name portname)
                                      :udims udims
                                      :loc (vl-token->loc portname)))))

(defparser vl-parse-ansi-regular-portdecl (atts dir nettype var)
  :guard (and (vl-atts-p atts)
              (vl-maybe-direction-p dir)
              (vl-maybe-nettypename-p nettype))
  :result (vl-ansi-portdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (b* ((backup (vl-tokstream-save))
       ((mv err port tokstream)
        ;; 1.  data_type port_identifier { unpacked_dimension }
        (vl-parse-ansi-portdecl-with-datatype atts dir nettype var))
       ((unless err) (mv nil port tokstream))
       (pos (vl-tokstream->position)) ;; position that try 1 got to
       (tokstream (vl-tokstream-restore backup))
       ((mv err2 port tokstream)
        ;; 2.  [ signing ] { packed_dimension } port_identifier { unpacked_dimension }
        (vl-parse-ansi-portdecl-with-implicit-type atts dir nettype var))
       ((unless err2) (mv nil port tokstream))
       (pos2 (vl-tokstream->position))
       ((mv pos err) (vl-choose-parse-error pos err pos2 err2))
       (tokstream (vl-tokstream-restore backup))
       (tokstream (vl-tokstream-update-position pos)))
    (mv err nil tokstream)))


(defparser vl-parse-ansi-interface-portdecl (atts)
  :guard (vl-atts-p atts)
  :result (vl-ansi-portdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; 3.  interface_identifier [ . modport_identifier ] port_identifier { unpacked_dimension }
  (seq tokstream
       (ifname := (vl-match-token :vl-idtoken))
       (when (vl-is-token? :vl-dot)
         (:= (vl-match))
         (modport := (vl-match-token :vl-idtoken)))

       (portname := (vl-match-token :vl-idtoken))
       (udims := (vl-parse-0+-variable-dimensions))
       (unless (vl-is-some-token? '(:vl-comma :vl-rparen))
         (return-raw
          (vl-parse-error "Unreasonable tokens after
      \"interface_identifier [ . modport_identifier ] port_identifier { unpacked_dimension }\"
      style port.")))
       (return (make-vl-ansi-portdecl :atts atts
                                      :typename (vl-idtoken->name ifname)
                                      :modport (and modport (vl-idtoken->name modport))
                                      :name (vl-idtoken->name portname)
                                      :udims udims
                                      :loc (vl-token->loc ifname)))))

;; (trace! #!vl (vl-parse-ansi-port-declaration-fn
;;               :entry (list 'vl-parse-ansi-port-declaration
;;                            (vl-debug-tokstream tokstream))
;;               :exit (cons 'vl-parse-ansi-port-declaration
;;                           (b* (((list err val tokstream) values))
;;                             (list (and err (with-local-ps
;;                                              (vl-print-warning err)))
;;                                   (and val (with-local-ps
;;                                              (vl-pp-ansi-portdecl val)))
;;                                   (vl-debug-tokstream tokstream))))))

;; (trace! #!vl (vl-parse-ansi-regular-portdecl-fn
;;               :entry (list 'vl-parse-ansi-regular-portdecl
;;                            (vl-debug-tokstream tokstream))
;;               :exit (cons 'vl-parse-ansi-regular-portdecl
;;                           (b* (((list err val tokstream) values))
;;                             (list (and err (with-local-ps
;;                                              (vl-print-warning err)))
;;                                   (and val (with-local-ps
;;                                              (vl-pp-ansi-portdecl val)))
;;                                   (vl-debug-tokstream tokstream))))))

;; (trace! #!vl (vl-parse-ansi-interface-portdecl-fn
;;               :entry (list 'vl-parse-ansi-interface-portdecl
;;                            (vl-debug-tokstream tokstream))
;;               :exit (cons 'vl-parse-ansi-interface-portdecl
;;                           (b* (((list err val tokstream) values))
;;                             (list (and err (with-local-ps
;;                                              (vl-print-warning err)))
;;                                   (and val (with-local-ps
;;                                              (vl-pp-ansi-portdecl val)))
;;                                   (vl-debug-tokstream tokstream))))))

(defparser vl-parse-ansi-port-declaration (atts)
  :parents (parse-ports)
  :short "Matches @('ansi_port_declaration').  Peeks at the token after to make
          sure it's a comma or right paren, but doesn't consume it."
  :guard (vl-atts-p atts)
  :result (vl-ansi-portdecl-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  ;; Here's what we currently support:
  ;;   [ port_direction ] [ net_type ] data_type port_identifier { unpacked_dimension }
  ;; | [ port_direction ] [ net_type ] [ signing ] { packed_dimension } port_identifier { unpacked_dimension }
  ;; | interface_identifier [ . modport_identifier ] port_identifier { unpacked_dimension }
  ;; | "interface" [ . modport_identifier ] port_identifier { unpacked_dimension }
  ;; | [ port_direction ] data_type  port_identifier { variable_dimension }
  ;; | [ port_direction ] var data_type port_identifier { variable_dimension }
  ;; | [ port_direction ] var [ signing ] { packed_dimension } port_identifier { variable_dimension }
  ;;
  ;; (The generic interface scheme isn't supported and will produce an error.)

  (seq tokstream
       (dir := (vl-parse-optional-port-direction))
       (nettype := (vl-parse-optional-nettype))
       (var := (vl-parse-optional-var-kwd))
       (return-raw
        ;; Here's where it gets hairy.  Ignoring the distinction between unpacked_dimension and variable_dimension:
        ;; 1.  data_type port_identifier { unpacked_dimension }                             (from either the net or variable case)
        ;; 2.  [ signing ] { packed_dimension } port_identifier { unpacked_dimension }      (from either the net or variable case)
        ;; 3.  interface_identifier [ . modport_identifier ] port_identifier { unpacked_dimension }
        ;; 4.  "interface" [ . modport_identifier ] port_identifier { unpacked_dimension }  (parse error).
        ;;
        ;; We'll need to use backtracking to tell the difference between
        ;;    foo_t [3:0] bar ...   (case 1)
        ;;    in [3:0] ...          (case 2).
        ;; We know we're good if the token after is a comma or right paren.
        ;;
        ;; We won't be able to tell the difference between case 3 (with no
        ;; modport) and case 1; we'll treat it as case 1 and fix it up later.

        (b* (((when (or dir nettype var))
              ;; Can't be an interface port.  Just parse it as a regular port.
              ;; This covers 1 and 2.
              (vl-parse-ansi-regular-portdecl atts dir nettype var))
             ((when (vl-is-token? :vl-kwd-interface))
              (vl-parse-error "BOZO implement explicit 'interface' ports."))

             (backup (vl-tokstream-save))
             ;; Otherwise, we'll try 3. first.  In ambiguous cases, it's easier
             ;; to change an interface port to a regular port than vice versa,
             ;; since a regular port also makes a portdecl and vardecl.

             ((mv err3 port tokstream)
              ;; 3.  interface_identifier [ . modport_identifier ] port_identifier { unpacked_dimension }
              (vl-parse-ansi-interface-portdecl atts))
             ((unless err3) (mv nil port tokstream))
             (pos3 (vl-tokstream->position))
             (tokstream (vl-tokstream-restore backup))

             ((mv err port tokstream)
              ;; 1-2
              (vl-parse-ansi-regular-portdecl atts dir nettype var))
             ((unless err) (mv nil port tokstream))
             (pos (vl-tokstream->position)) ;; position that try 1 got to
             (tokstream (vl-tokstream-restore backup))

             ((mv pos err) (vl-choose-parse-error pos err pos3 err3))
             (tokstream (vl-tokstream-update-position pos)))
          (mv err nil tokstream)))))

(defparser vl-parse-1+-ansi-port-declarations ()
  :parents (parse-ports)
  :short "Matches @(' {attribute_instance} ansi_port_declaration
                      { ',' {attribute_instance} ansi_port_declaration } ')"
  :result (vl-ansi-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (atts  := (vl-parse-0+-attribute-instances))
       (first := (vl-parse-ansi-port-declaration atts))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-1+-ansi-port-declarations)))
       (return (cons first rest))))




;; ---------------- Verilog2005 Ansi Portlist Parsing ------------------


(encapsulate nil
  (local (in-theory (enable vl-match vl-is-token? len vl-lookahead-is-token?)))
  (defparser vl-parse-0+-port-identifiers-as-ansi-decls-2005 ()
    :result (vl-ansi-portdecllist-p val)
    :resultp-of-nil t
    :true-listp t
    :fails never
    :count weak
    (seq tokstream
         (unless (vl-is-token? :vl-comma)
           (return nil))
         (unless (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens)))
           (return nil))
         (:= (vl-match))
         (name1 := (vl-match))
         (rest := (vl-parse-0+-port-identifiers-as-ansi-decls-2005))
         (return (cons (make-vl-ansi-portdecl :name (vl-idtoken->name name1)
                                              :loc (vl-token->loc name1))
                       rest)))))




(defparser vl-parse-ansi-port-declaration-2005 (atts)
  ;; inout_declaration ::= inout [ net_type ] [ signed ] [ range ] list_of_port_identifiers
  ;; input_declaration ::= input [ net_type ] [ signed ] [ range ] list_of_port_identifiers
  ;; output_declaration ::= output [ net_type ] [ signed ] [ range ] list_of_port_identifiers
  ;;                      | output reg [ signed ] [ range ] list_of_variable_port_identifiers
  ;;                      | output output_variable_type list_of_variable_port_identifiers

  :parents (parse-ports)
  :short "Matches a port declaration (which may involve several comma-separated variable names), and creates an ansi-portdecl object for each of them."
  :guard (vl-atts-p atts)
  :result (vl-ansi-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (unless (vl-is-some-token? *vl-directions-kwds*)
         (return-raw (vl-parse-error "Expected a port direction")))
       (dir := (vl-parse-port-direction))
       (nettype := (vl-parse-optional-nettype))
       (when (and (eq dir :vl-output)
                  (not nettype))
         (type := (vl-match-some-token '(:vl-kwd-reg :vl-kwd-integer :vl-kwd-time)))
         (when (eq (vl-token->type type) :vl-kwd-reg)
           (when (vl-is-token? :vl-kwd-signed)
             (signed := (vl-match)))
           (when (vl-is-token? :vl-lbrack)
             (range := (vl-parse-range))))
         (id := (vl-match-token :vl-idtoken))
         (rest := (vl-parse-0+-port-identifiers-as-ansi-decls-2005))
         (return (cons (make-vl-ansi-portdecl
                          :atts atts
                          :dir dir
                          :nettype nil
                          :type (make-vl-coretype :name (case (vl-token->type type)
                                                          (:vl-kwd-integer :vl-integer)
                                                          (t :vl-time))
                                                  :signedp (if signed
                                                               t
                                                             (eq (vl-token->type type)
                                                                 :vl-kwd-integer))
                                                  :pdims (and range (list range)))
                          :name (vl-idtoken->name id)
                          :loc (vl-token->loc id))
                         rest)))
       (unless nettype
         (return-raw
          (vl-parse-error "Expected a nettype after an 'input' or 'inout' declaration.")))
       (when (vl-is-token? :vl-kwd-signed)
         (signed := (vl-match)))
       (when (vl-is-token? :vl-lbrack)
         (range := (vl-parse-range)))
       (id := (vl-match-token :vl-idtoken))
       (rest := (vl-parse-0+-port-identifiers-as-ansi-decls-2005))
       (return (cons (make-vl-ansi-portdecl
                      :atts atts
                      :dir dir
                      :nettype nettype
                      :type (make-vl-coretype :name :vl-logic
                                              :signedp (and signed t)
                                              :pdims (and range (list range)))
                      :name (vl-idtoken->name id)
                      :loc (vl-token->loc id))
                     rest))))


(defparser vl-parse-1+-port-declarations-separated-by-commas-2005 ()
  :parents (parse-ports)
  :short "Verilog-2005 Only.  Matches @(' port_declaration { ',' port_declaration } ') in
ansi style port lists.  Creates ansi-portdecls."
  :result (vl-ansi-portdecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (portdecls1 := (vl-parse-ansi-port-declaration-2005 nil))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (portdecls2 := (vl-parse-1+-port-declarations-separated-by-commas-2005)))
       (return (append-without-guard portdecls1 portdecls2))))



;; ---------------- Non-Ansi Portlist Parsing (2005/2012) ------------------


(defsection verilog-2005-ports
  :parents (parse-ports)
  :short "Parsing for Verilog-2005 ports."
  :long "<p>In Verilog-2005, a @('port_expression') is just a syntactic means
to restrict the expressions allowed in ports to identifiers, bit-selects,
part-selects, and concatenations.  We just parse @('port_expression')s into
plain expressions.</p>

@({
    port_expression ::= port_reference
                      | '{' port_reference { ',' port_reference } '}'

    port_reference ::= identifier [ '[' constant_range_expression ']' ]

    constant_range_expression ::= constant_expression
                                | msb_constant_expression : lsb_constant_expression
})

<p>Port expressions are put into lists with the following rules.</p>

@({
     list_of_ports ::= '(' port { ',' port } ')'

     port ::= [port_expression]
            | '.' identifier '(' [port_expression] ')'
})

<p>Note that the above rules allow null ports, e.g., @('module foo ( a, , b
)').  As described in 12.3.2, the port expression is optional to allow for
ports that do not connect to anything internal to the module.</p>

<p>If we were to interpret the grammar very literally, the @('list_of_ports')
for @('module foo ()') would be a singleton list with a blank port.  But in
light of the way module instances work, e.g., see @(see
special-note-about-blank-ports), it seems like the nicest way to handle this is
to instead allow an empty list of ports, and treat @('()') as producing the
empty list of ports instead of a single blank port.</p>")

(local (xdoc::set-default-parents verilog-2005-ports))

(defparser vl-parse-port-reference ()
  :short "Matches @('port_reference')."
  :long "<p>Note: We assume that if a bracket follows the identifier, it
belongs to this port reference.  This is safe in port-expressions since only a
comma or end curly-brace will follow them.  Since @('port_reference') never
occurs anywhere else in the grammar, this should be fine everywhere.</p>"
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (id := (vl-match-token :vl-idtoken))
        (unless (vl-is-token? :vl-lbrack)
          (return (vl-idexpr (vl-idtoken->name id))))
        (:= (vl-match))
        (range := (vl-parse-range-expression))
        (unless (or (eq (vl-erange->type range) :vl-index)
                    (eq (vl-erange->type range) :vl-colon))
          (return-raw
           (vl-parse-error "The +: or -: operators are not allowed in port expressions.")))
        (:= (vl-match-token :vl-rbrack))
        (return (vl-build-range-select
                 (vl-index->scope (vl-idexpr (vl-idtoken->name id)))
                 nil range))))

(defparser vl-parse-1+-port-references-separated-by-commas ()
  :short "Matches @('port_reference { ',' port_reference }')"
  :result (vl-exprlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-port-reference))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-port-references-separated-by-commas)))
        (return (cons first rest))))

(defparser vl-parse-port-expression ()
  :short "Matches @('port_expression')."
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-token? :vl-lcurly)
          ;; A concatenation.
          (:= (vl-match))
          (args := (vl-parse-1+-port-references-separated-by-commas))
          (:= (vl-match-token :vl-rcurly))
          (return (make-vl-concat :parts args)))
        ;; A single port reference.
        (ref := (vl-parse-port-reference))
        (return ref)))

(defparser vl-parse-nonnull-port ()
  :short "Matches @('port'), except for the empty port."
  :result (vl-port-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (loc := (vl-current-loc))
        (unless (vl-is-token? :vl-dot)
          (pexpr := (vl-parse-port-expression))
          (return (cond ((vl-idexpr-p pexpr)
                         ;; Simple port like "x".  It gets its own name.
                         (make-vl-regularport :name (vl-idexpr->name pexpr)
                                              :expr pexpr
                                              :loc loc))
                        (t
                         ;; Expression port with no name.
                         (make-vl-regularport :name nil
                                              :expr pexpr
                                              :loc loc)))))
        ;; Otherwise, we have a name and possibly an expr.
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (unless (vl-is-token? :vl-rparen)
          (pexpr := (vl-parse-port-expression)))

        ;; Why can't I just use (vl-match) here? Ah, it's because (not
        ;; (vl-is-token? :vl-rparen)) isn't sufficient to know that we aren't
        ;; at the end of the stream.
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-regularport :name (vl-idtoken->name id)
                                     :expr pexpr
                                     :loc loc))))

(defparser vl-parse-1+-ports-separated-by-commas ()
  :short "Matches @('port { ',' port }'), possibly producing blank ports!"
  :result (vl-portlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  (seq tokstream
        (when (vl-is-token? :vl-rparen)
          ;; Blank port at the end.
          (loc := (vl-current-loc))
          (return (list (make-vl-regularport :name nil :expr nil :loc loc))))

        (when (vl-is-token? :vl-comma)
          (loc := (vl-current-loc))
          (:= (vl-match))
          (rest := (vl-parse-1+-ports-separated-by-commas))
          (return (cons (make-vl-regularport :name nil :expr nil :loc loc)
                        rest)))

        (first := (vl-parse-nonnull-port))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-ports-separated-by-commas)))
        (return (cons first rest))))



;; ------------- Choosing ANSI/Non-ANSI Portlist Parsing ---------------------


(define vl-port-starts-ansi-port-list-p
  :short "Determine whether we're in an ANSI or non-ANSI port list."
  ((port1 vl-ansi-portdecl-p))
  :returns (ansi-p)
  :long "<p>To tell which version we are in, we follow the rule suggested in
23.2.2.3 (pg 667):</p>

<blockquote> For the first port in the port list: if the direction, port kind,
and data type are all omitted, then the port shall be assumed to be a member of
a non-ANSI style list_of_ports...  </blockquote>"
  (b* (((vl-ansi-portdecl port1)))
    (or port1.dir
        port1.nettype
        port1.varp
        port1.typename
        port1.type
        port1.signedness
        port1.pdims)))



(defparser vl-parse-module-port-list-top-2005 ()
  :short "Verilog-2005 only.  Top-level function for parsing port lists in both
  ANSI and non-ANSI styles."

  :long "<p>See @(see verilog-2005-ports) and @(see verilog-2005-portdecls).
We match the following, contrived grammar rule:</p>

@({
   vl_module_port_list ::= list_of_ports
                         | [list_of_port_declarations]
})

<p>We can tell which variant we are following because a @('port_declaration') must
begin with one of:</p>

@({
     (*
     input
     output
     inout
})"
  :result (vl-parsed-ports-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count weak
  (seq tokstream
       (unless (vl-is-token? :vl-lparen)
         ;; No port list at all --> empty ports.
         (return (make-vl-nonansi-ports :ports nil)))
       (:= (vl-match))
       (when (vl-is-token? :vl-rparen)
         (:= (vl-match-token :vl-rparen))
         ;; Ports list is just () --> empty ports.
         (return (make-vl-nonansi-ports :ports nil)))

       (when (vl-is-some-token? '(:vl-kwd-output :vl-kwd-input :vl-kwd-inout :vl-beginattr))
         ;; This must be an ANSI-style declaration.
         (portdecls := (vl-parse-1+-port-declarations-separated-by-commas-2005))
         (:= (vl-match-token :vl-rparen))
         (return (make-vl-ansi-ports :decls portdecls)))

       ;; This must be a non-ANSI style declaration.
       (ports := (vl-parse-1+-ports-separated-by-commas))
       (:= (vl-match-token :vl-rparen))
       (return (make-vl-nonansi-ports :ports ports))))


(defparser vl-parse-module-port-list-top-2012 ()
  :short "SystemVerilog-2012 only.  Top-level function for parsing port lists
in both ANSI and non-ANSI styles."

  :long "<p>We match the following, contrived grammar rule:</p>

@({
   vl_module_port_list ::= list_of_ports
                         | [list_of_port_declarations]
})"

  :result (vl-parsed-ports-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count weak
  (seq tokstream
       (unless (vl-is-token? :vl-lparen)
         ;; No port list at all --> empty ports.
         (return (make-vl-nonansi-ports :ports nil)))
       (:= (vl-match))
       (when (vl-is-token? :vl-rparen)
         (:= (vl-match))
         ;; Ports list is just () --> empty ports.
         (return (make-vl-nonansi-ports :ports nil)))

       (return-raw
        (b* ((backup (vl-tokstream-save))
             ((mv err port1 tokstream)
              (seq tokstream
                   (atts  := (vl-parse-0+-attribute-instances))
                   (port1 := (vl-parse-ansi-port-declaration atts))
                   (return port1)))
             (ansi-p
              (and (not err)
                   (vl-port-starts-ansi-port-list-p port1)))
             (tokstream (vl-tokstream-restore backup))
             ((when ansi-p)
              (seq tokstream
                   (decls := (vl-parse-1+-ansi-port-declarations))
                   (:= (vl-match-token :vl-rparen))
                   (return (make-vl-ansi-ports :decls decls)))))
          ;; Non-ansi mode.
          (seq tokstream
               (ports := (vl-parse-1+-ports-separated-by-commas))
               (:= (vl-match-token :vl-rparen))
               (return (make-vl-nonansi-ports :ports ports)))))))


(defparser vl-parse-module-port-list-top ()
  :result (vl-parsed-ports-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count weak
  (seq tokstream
       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         (ans := (vl-parse-module-port-list-top-2005))
         (return ans))
       (ans := (vl-parse-module-port-list-top-2012))
       (return ans)))









(defsection creating-portdecls/vardecls
  :parents (parse-ports)
  :short "Utilities for the initial creation of port declarations and (if the
port declaration is complete) corresponding net declarations."

  :long "<p>The creation of port declarations and net declarations is very
subtle.  See also @(see portdecl-sign) and @(see make-implicit-wires).</p>

<p>From Verilog-2005, page 174:</p>

<ul>

<li>If a port declaration includes a net or variable type, then the port is
considered completely declared and it is an error for the port to be declared
again in a variable or net data type declaration...</li>

<li>If the port declaration does NOT include a net or variable type, then the
port can be declared again in a net or variable declaration.  If the net or
variable is declared as a vector, the range specification between the two
declarations shall be identical.</li>

</ul>

<p>So if the parser encounters a port declaration with a net or variable type,
the port is completely declared and we are going to generate both (1) a port
declaration and (2) the corresponding net declaration.</p>

<p>However, if we have no net type, then we'll instead only add the port
declaration, which we will mark with the attribute
@('VL_INCOMPLETE_DECLARATION').  The corresponding net will either be found
later in the module, or will be added automatically with the @(see
make-implicit-wires) transform.  Signedness is handled last, by @(see
portdecl-sign).</p>")

(local (xdoc::set-default-parents creating-portdecls/vardecls))

(defaggregate vl-parsed-port-identifier
  :short "Temporary structure created during port parsing."
  :tag nil
  :layout :fulltree
  ((name  vl-idtoken-p
          "Identifier for the port being declared.")
   (udims vl-dimensionlist-p
          "Unpacked dimensions for this port, if any.")))

(deflist vl-parsed-port-identifier-list-p (x)
  (vl-parsed-port-identifier-p x))

(define vl-parsed-port-identifier-list-from-idtokenlist
  :short "Convert idtokens into trivial @(see vl-parsed-port-identifier-p)s."
  ((x vl-idtoken-list-p "Plain old port names."))
  :returns (parsed vl-parsed-port-identifier-list-p :hyp :fguard
                   "The same names, but associated with empty unpacked
                    dimensions.")
  :long "<p>This is mostly for Verilog-2005, where port declarations can't have
any unpacked dimensions.</p>"
  (if (atom x)
      nil
    (cons (make-vl-parsed-port-identifier :name (car x)
                                          :udims nil)
          (vl-parsed-port-identifier-list-from-idtokenlist (cdr x)))))


(define vl-build-subsequent-portdecls
  :parents (vl-build-portdecls)
  :long "<p>We have sometimes encountered very long port lists like @('input
  a0, a1, ...;').  In these cases, we can win big for memory usage by reusing
  structure when we build the subsequent port declarations, by CHANGE-ing the
  declaration of @('a0') instead of MAKE-ing fresh ports.</p>"
  ((x         vl-parsed-port-identifier-list-p
              "The subsequent ports, @('a1, ...')")
   (base-decl vl-portdecl-p
              "Possibly the portdecl for @('a0'), but more generally it may be
               a portdecl that we are ``abusing'' to reuse structure.  In
               particular, if @('a0') has unpacked dimensions, then
               @('base-decl') is like @('a0') except that it does NOT have such
               dimensions."))
  :returns (portdecls vl-portdecllist-p)
  (b* (((when (atom x))
        nil)
       ((vl-parsed-port-identifier x1) (car x))
       (basetype (vl-portdecl->type base-decl))
       (- (or (not (vl-datatype->udims basetype))
              (raise "Base datatype already has unpacked dimensions?")))
       (type1 (if (consp x1.udims)
                  (vl-datatype-update-udims x1.udims basetype)
                basetype)))
    (cons (change-vl-portdecl base-decl
                              :name    (vl-idtoken->name x1.name)
                              :loc     (vl-token->loc x1.name)
                              :type    type1)
          (vl-build-subsequent-portdecls (cdr x) base-decl)))
  ///
  (more-returns
   (portdecls true-listp :rule-classes :type-prescription)
   (portdecls (equal (len portdecls) (len x)) :name len-of-vl-build-subsequent-portdecls)
   (portdecls (equal (consp portdecls) (consp x)) :name consp-of-vl-build-subsequent-portdecls)
   (portdecls (iff portdecls (consp x)) :name vl-build-subsequent-portdecls-under-iff)))

(define vl-build-portdecls
  :short "Main loop for creating real @(see vl-portdecl)s."
  ((x        vl-parsed-port-identifier-list-p)
   &key
   (dir      vl-direction-p)
   (nettype  vl-maybe-nettypename-p)
   (type     vl-datatype-p)
   (atts     vl-atts-p))
  :returns (portdecls vl-portdecllist-p)
  (b* (((when (atom x))
        nil)
       ((vl-parsed-port-identifier x1) (car x))
       (- (or (not (vl-datatype->udims type))
              (raise "Base datatype already has unpacked dimensions?")))
       (basedecl (make-vl-portdecl
                  :name    (vl-idtoken->name x1.name)
                  :loc     (vl-token->loc x1.name)
                  :type    type
                  :dir     dir
                  :nettype nettype
                  :atts    atts))
       ((when (consp x1.udims))
        ;; Nasty case.  We have something like "input logic [3:0] a0 [1:0], a1,
        ;; a2, ...;" The first declaration has its own udims that are NOT part
        ;; of the basetype that is to be inferred across these decls.  We'll
        ;; have to rebuild its declaration because basedecl is wrong.  Seems
        ;; easiest to abuse the aux function for this.
        (vl-build-subsequent-portdecls x basedecl)))
    ;; Else, there are no udims, so basetype is correct for x1, and hence
    ;; the whole basedecl is correct.
    (cons basedecl
          (vl-build-subsequent-portdecls (cdr x) basedecl)))
  ///
  (more-returns
   (portdecls true-listp :rule-classes :type-prescription)
   (portdecls (equal (len portdecls) (len x)) :name len-of-vl-build-portdecls)
   (portdecls (equal (consp portdecls) (consp x)) :name consp-of-vl-build-portdecls)
   (portdecls (iff portdecls (consp x)) :name vl-build-portdecls-under-iff)))


(define vl-build-subsequent-netdecls-for-ports
  :parents (vl-build-netdecls-for-ports)
  :short "See @(see vl-build-subsequent-portdecls).  This is identical but for
          the vardecls instead of the portdecls."
  ((x        vl-parsed-port-identifier-list-p)
   (basedecl vl-vardecl-p))
  :returns (netdecls vl-vardecllist-p)
  (b* (((when (atom x))
        nil)
       ((vl-parsed-port-identifier x1) (car x))
       (basetype (vl-vardecl->type basedecl))
       (- (or (not (vl-datatype->udims basetype))
              (raise "Base datatype already has unpacked dimensions?")))
       (type1 (if (consp x1.udims)
                  (vl-datatype-update-udims x1.udims basetype)
                basetype)))
    (cons (change-vl-vardecl basedecl
                             :name (vl-idtoken->name x1.name)
                             :loc  (vl-token->loc x1.name)
                             :type type1)
          (vl-build-subsequent-netdecls-for-ports (cdr x) basedecl)))
  ///
  (more-returns
   (netdecls true-listp :rule-classes :type-prescription)
   (netdecls (equal (len netdecls) (len x)) :name len-of-vl-build-subsequent-netdecls)
   (netdecls (equal (consp netdecls) (consp x)) :name consp-of-vl-build-subsequent-netdecls)
   (netdecls (iff netdecls (consp x)) :name vl-build-subsequent-netdecls-under-iff)))

(define vl-build-netdecls-for-ports
  :short "Main loop for creating the associated @(see vl-vardecl)s."
  ((x        vl-parsed-port-identifier-list-p)
   &key
   (nettype  vl-maybe-nettypename-p)
   (type     vl-datatype-p)
   (atts     vl-atts-p))
  :returns (netdecls vl-vardecllist-p)
  (b* (((when (atom x))
        nil)
       ((vl-parsed-port-identifier x1) (car x))
       (- (or (not (vl-datatype->udims type))
              (raise "Base datatype already has unpacked dimensions?")))
       (basedecl (make-vl-vardecl :name (vl-idtoken->name x1.name)
                                  :loc  (vl-token->loc x1.name)
                                  :nettype nettype
                                  :type type
                                  :atts atts
                                  ;; I think these are right because there isn't any way
                                  ;; to declare these as part of the port declaration?
                                  :varp nil
                                  :constp nil
                                  :lifetime nil
                                  :vectoredp nil
                                  :scalaredp nil
                                  :delay nil
                                  :cstrength nil))
       ((when (consp x1.udims))
        ;; Basedecl isn't right because its type doesn't have the udims.
        (vl-build-subsequent-netdecls-for-ports x basedecl)))
    ;; Else, the basedecl is correct, so use it.
    (cons basedecl
          (vl-build-subsequent-netdecls-for-ports (cdr x) basedecl)))
  ///
  (more-returns
   (netdecls true-listp :rule-classes :type-prescription)
   (netdecls (equal (len netdecls) (len x)) :name len-of-vl-build-netdecls)
   (netdecls (equal (consp netdecls) (consp x)) :name consp-of-vl-build-netdecls)
   (netdecls (iff netdecls (consp x)) :name vl-build-netdecls-under-iff)))

(define vl-make-ports-and-maybe-nets
  :short "Top level routine for creating proper port and variable declarations."
  ((x          vl-parsed-port-identifier-list-p)
   &key
   (dir        vl-direction-p)
   (nettype    vl-maybe-nettypename-p)
   (type       vl-datatype-p)
   (complete-p booleanp)
   (atts       vl-atts-p))
  :returns
  (val (and (consp val)
            (vl-portdecllist-p (car val))
            (vl-vardecllist-p  (cdr val))))
  (b* ((atts (if complete-p
                 atts
               (hons '("VL_INCOMPLETE_DECLARATION") atts)))
       (portdecls (vl-build-portdecls x
                                      :dir      dir
                                      :nettype  nettype
                                      :type     type
                                      :atts     atts))
       (netdecls (if (not complete-p)
                     ;; Don't introduce any net declarations since it's not a complete
                     ;; port declaration.
                     nil
                   (vl-build-netdecls-for-ports x
                                                :type     type
                                                :nettype  nettype
                                                ;; Make sure the variables are marked as
                                                ;; implicit to avoid pretty-printing them.
                                                :atts     (hons '("VL_PORT_IMPLICIT") atts)))))
    (cons portdecls netdecls))
  ///
  (defthm true-listp-of-vl-make-ports-and-maybe-nets-1
    (true-listp (car (vl-make-ports-and-maybe-nets x
                                                   :dir dir
                                                   :type type
                                                   :complete-p complete-p
                                                   :nettype nettype
                                                   :atts atts)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-make-ports-and-maybe-nets-2
    (true-listp (cdr (vl-make-ports-and-maybe-nets x
                                                   :dir dir
                                                   :type type
                                                   :complete-p complete-p
                                                   :nettype nettype
                                                   :atts atts)))
    :rule-classes :type-prescription)

  (defthm basics-of-vl-make-ports-and-maybe-nets
    (b* (((cons portdecls netdecls)
          (vl-make-ports-and-maybe-nets x
                                        :dir dir
                                        :type type
                                        :complete-p complete-p
                                        :nettype nettype
                                        :atts atts)))
      (and (equal (len portdecls) (len x))
           (equal (consp portdecls) (consp x))
           (iff portdecls (consp x))
           (equal (len netdecls) (if complete-p (len x) 0))
           (equal (consp netdecls) (and complete-p (consp x)))
           (iff netdecls (and complete-p (consp x)))))))







































;; ===================== Non-ANSI PORTDECL PARSING ===========================





(defsection verilog-2005-portdecls
  :parents (parse-ports)
  :short "Parsing for Verilog-2005 port declarations."
  :long "<p>Here is the grammar we're implementing.</p>

@({
 port_declaration ::= {attribute_instance} inout_declaration
                    | {attribute_instance} input_declaration
                    | {attribute_instance} output_declaration

 inout_declaration ::= 'inout' [net_type] ['signed'] [range] list_of_port_identifiers

 input_declaration ::= 'input' [net_type] ['signed'] [range] list_of_port_identifiers

 output_declaration ::= 'output' [net_type] ['signed'] [range] list_of_port_identifiers
                      | 'output' 'reg' ['signed'] [range] list_of_variable_port_identifiers
                      | 'output' output_variable_type list_of_variable_port_identifiers

 net_type ::= 'supply0' | 'supply1' | 'tri' | 'triand' | 'trior' | 'tri0' | 'tri1'
            | 'uwire' | 'wire' | 'wand' | 'wor'

 list_of_port_identifiers ::= identifier { ',' identifier }

 list_of_variable_port_identifiers ::=
    identifier ['=' expression] { ',' identifier [ '=' expression ] }

 output_variable_type ::= 'integer' | 'time'

 list_of_port_declarations ::= '(' port_declaration { ',' port_declaration } ')'
                             | '(' ')'
})")

(local (xdoc::set-default-parents verilog-2005-portdecls))

(defparser vl-parse-1+-identifiers-separated-by-commas ()
  :short "Matches @('identifier { ',' identifier }')"
  :long "<p>We have to take extra care here, because we can have situations like</p>

@({
     input [7:0] a, b, output c
})

<p>in @('list_of_port_declarations').  In this case, note that the comma
following @('b') is not really part of the identifier list.  Because of this,
we can't just assume that because we've seen a comma, \"the comma belongs to us
and must be followed by another identifier.\" Instead, we have to look for the
comma <b>and</b> the subsequent identifier.</p>"
  :result (vl-idtoken-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-match-token :vl-idtoken))
        (when (and (vl-is-token? :vl-comma)
                   (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens))))
          (:= (vl-match))
          (rest := (vl-parse-1+-identifiers-separated-by-commas)))
        (return (cons first rest))))

(defparser vl-parse-basic-port-declaration-tail (dir atts force-completep)
  :short "Matches @('[net_type] ['signed'] [range] list_of_port_identifiers')."
  :long "<p>See @(see creating-portdecls/vardecls) and @(see portdecl-sign).
The datatype we use here is not necessarily correct, e.g., because the
corresponding variable declaration might have some other type (e.g., @('wor')
or @('reg')).  However, due to the @('VL_INCOMPLETE_DECLARATION') attribute,
we'll correct for this before creating the module.</p>"
  :guard (and (vl-direction-p dir)
              (vl-atts-p atts)
              (booleanp force-completep))
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
        (nettype := (vl-parse-optional-nettype))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (ids := (vl-parse-1+-identifiers-separated-by-commas))
        (return (vl-make-ports-and-maybe-nets
                 (vl-parsed-port-identifier-list-from-idtokenlist ids)
                 :dir dir
                 :atts atts
                 :complete-p (or force-completep (if nettype t nil))
                 :nettype nettype
                 :type (make-vl-coretype :name :vl-logic
                                         :signedp (if signed t nil)
                                         :pdims (and range (list range))))))
  ///
  (defthm true-listp-of-vl-parse-basic-port-declaration-tail-1
    (true-listp (car (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts force-completep))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-basic-port-declaration-tail-2
    (true-listp (cdr (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts force-completep))))
    :rule-classes :type-prescription)

  (defthm vl-parse-basic-port-declaration-tail-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts force-completep))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts force-completep)))))))

(defparser vl-parse-output-reg-port-tail (atts)
  :short "We've just matched 'output reg'.  Now match @('['signed'] [range] list_of_variable_port_identifiers')."
  :guard (vl-atts-p atts)
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-kwd-signed)
         (signed := (vl-match)))
       (when (vl-is-token? :vl-lbrack)
         (range := (vl-parse-range)))
       (ids := (vl-parse-1+-identifiers-separated-by-commas))
       (return
        (vl-make-ports-and-maybe-nets
         (vl-parsed-port-identifier-list-from-idtokenlist ids)
         :dir :vl-output
         :atts atts
         :complete-p t ;; It's complete since we have a reg type
         :type (make-vl-coretype :name    :vl-reg
                                 :signedp (if signed t nil)
                                 :pdims   (and range
                                               (list range))))))
  ///
  (defthm true-listp-of-vl-parse-output-reg-port-tail-1
    (true-listp (car (mv-nth 1 (vl-parse-output-reg-port-tail atts))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-output-reg-port-tail-2
    (true-listp (cdr (mv-nth 1 (vl-parse-output-reg-port-tail atts))))
    :rule-classes :type-prescription)

  (defthm vl-parse-output-reg-port-tail-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-output-reg-port-tail atts))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-output-reg-port-tail atts)))))))


(defparser vl-parse-port-declaration-noatts-2005 (atts force-completep)
  :short "Verilog-2005 Only.  Match @('inout_declaration | input_declaration | output_declaration')."
  :guard (and (vl-atts-p atts)
              (booleanp force-completep))
  ;; Returns (portdecls . netdecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream

        (when (vl-is-token? :vl-kwd-input)
          (:= (vl-match))
          (ans := (vl-parse-basic-port-declaration-tail :vl-input atts force-completep))
          ;; input_declaration ::= 'input' [net_type] ['signed'] [range] list_of_port_identifiers
          (return ans))

        (when (vl-is-token? :vl-kwd-inout)
          (:= (vl-match))
          ;; inout_declaration ::= 'inout' [net_type] ['signed'] [range] list_of_port_identifiers
          (ans := (vl-parse-basic-port-declaration-tail :vl-inout atts force-completep))
          (return ans))

        ;; Outputs are more complex:
        ;;
        ;; output_declaration ::=
        ;;    'output' [net_type] ['signed'] [range] list_of_port_identifiers
        ;;  | 'output' 'reg' ['signed'] [range] list_of_variable_port_identifiers
        ;;  | 'output' output_variable_type list_of_variable_port_identifiers
        (:= (vl-match-token :vl-kwd-output))

        (when (vl-is-token? :vl-kwd-reg)
          (:= (vl-match))
          (ans := (vl-parse-output-reg-port-tail atts))
          (return ans))

        ;; output_variable_type ::= 'integer' | 'time'
        ;; 'output' output_variable_type list_of_variable_port_identifiers
        (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-time))
          (type := (vl-match))
          (ids := (vl-parse-1+-identifiers-separated-by-commas))
          (return
           (vl-make-ports-and-maybe-nets
            (vl-parsed-port-identifier-list-from-idtokenlist ids)
            :dir :vl-output
            :atts atts
            :complete-p t ;; It's complete since we have a variable type
            :type
            (if (eq (vl-token->type type) :vl-kwd-integer)
                *vl-plain-old-integer-type*
              *vl-plain-old-time-type*))))

        ;; 'output' [net_type] ['signed'] [range] list_of_port_identifiers
        (ans := (vl-parse-basic-port-declaration-tail :vl-output atts force-completep))
        (return ans))
  ///
  (defthm true-listp-of-vl-parse-port-declaration-noatts-2005-1
    (true-listp (car (mv-nth 1 (vl-parse-port-declaration-noatts-2005 atts force-completep))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-port-declaration-noatts-2005-2
    (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-noatts-2005 atts force-completep))))
    :rule-classes :type-prescription)

  (defthm vl-parse-port-declaration-noatts-2005-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-noatts-2005 atts force-completep))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-noatts-2005 atts force-completep)))))))



(defparser vl-parse-port-declaration-atts-2005 ()
  :short "Verilog-2005 Only.  Matches port_declaration in ansi-style port lists."
  :long "<p>We force these to be complete declarations because, per
Verilog-2005 Section 12.3.4, in this syntax \"Each declared port provides the
complete information about the port...\", which strongly suggests (when paired
with the description of \"completely declared\" ports on Page 174) that it
should not be declared again.</p>"
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (result := (vl-parse-port-declaration-noatts-2005 atts t))
        (return result))
  ///
  (defthm true-listp-of-vl-parse-port-declaration-atts-2005-1
    (true-listp (car (mv-nth 1 (vl-parse-port-declaration-atts-2005))))
    :rule-classes :type-prescription)
  (defthm true-listp-of-vl-parse-port-declaration-atts-2005-2
    (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-atts-2005))))
    :rule-classes :type-prescription)
  (defthm vl-parse-port-declaration-atts-2005-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-atts-2005))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-atts-2005)))))))






;; SystemVerilog --------------------------------------------------------------

(defsection parse-port-types
  :parents (parse-ports)
  :short "Handling of SystemVerilog-2012 port types."

  :long "<h3>Background</h3>

<p>Here are a few key grammar rules within SystemVerilog ports:</p>

@({
    net_port_type ::= [ net_type ] data_type_or_implicit
                    | identifier
                    | 'interconnect' implicit_data_type

    variable_port_type ::= var_data_type

    var_data_type ::= data_type
                    | 'var' data_type_or_implicit

    data_type_or_implicit ::= data_type | implicit_data_type

    implicit_data_type ::= [ signing ] { packed_dimension }
})

<p>These are used in two places.  The first is in non-ANSI style SystemVerilog
port declarations, where we have:</p>

@({
   inout_declaration  ::= 'inout' net_port_type      list_of_port_identifiers

   input_declaration  ::= 'input' net_port_type      list_of_port_identifiers
                        | 'input' variable_port_type list_of_variable_identifiers

   output_declaration ::= 'output' net_port_type      list_of_port_identifiers
                        | 'output' variable_port_type list_of_variable_port_identifiers

   ref_declaration    ::= 'ref'    variable_port_type list_of_variable_identifiers
})

<p>The other is in ANSI-style SystemVerilog port declarations, where we
have some trivial wrappers:</p>

@({
    net_port_header       ::= [port_direction] net_port_type

    variable_port_header  ::= [port_direction] variable_port_type

    interface_port_header ::= identifier [ '.' identifier ]
                            | 'interface' [ '.' identifier ]
})

<p>And then the main port declaration syntax:</p>

@({
    ansi_port_declaration ::=
        [ net_port_header | interface_port_header ] identifier {unpacked_dimension} [ '=' expression ]
      | [ variable_port_header ]                    identifier {variable_dimension} [ '=' expression ]
      | [ port_direction ] '.' identifier '(' [expression] ')'
})

<h3>Parsing Port Types</h3>

<p>Determining the type of a port is tricky.  Consider the above rules and
suppose we're past any port direction stuff.  Then,</p>

<ul>

<li>In the non-ANSI case, we need to be able to recognize whether we have a
@('net_port_type') or @('variable_port_type').</li>

<li>In the ANSI case, we need to recognize whether we have a
@('net_port_type'), @('variable_port_type'), or
@('interface_port_header').</li>

</ul>

<p>In either case, the port type is followed by an identifier (the port name),
which may have then be followed by unpacked/variable dimensions.  So to handle
the trickier ANSI case, we basically want to parse:</p>

@({
    my_port_type ::= net_port_type
                   | variable_port_type
                   | interface_port_type

    net_port_type ::= [net_type] data_type
                    | [net_type] [signing] {packed_dimension}
                    | identifier
                    | 'interconnect' [signing] {packed_dimension}

    variable_port_type ::= data_type
                         | 'var' data_type
                         | 'var' [signing] {packed_dimension}

    interface_port_header ::= identifier [ '.' identifier ]
                            | 'interface' [ '.' identifier ]
})

<p>Where @('my_port_type') is followed by an identifier and perhaps dimensions.
Much of this is easy to handle: it's easy to identify the @('net_type')
keywords, the @('signing') keywords, the @('var') and @('interface')
keywords.</p>

<p>The tricky case is what to do if we find an identifier.  A leading
identifier might be:</p>

<ol>

<li>Port name.  This can happen in the @('net_port_type') case, where there is
no net_type, signing, or dimensions.  In this case, the identifier might be
followed by its unpacked dimensions.</li>

<li>Data type name.  In the @('variable_port_type') or @('net_port_type')
cases, we can have just a plain data type, which could be the name of a
user-defined type like @('foo_t').  In this case, the type name could be
followed by packed dimensions that are part of the data type, but which come
before the port name.</li>

<li>Interface name.  In the @('interface_port_header') case, we can have just a
plain identifier that names an interface.  Such an identifier must be followed
by the port name or a period for modports.</li>

</ol>

<p>Both NCVerilog and VCS appear to require uses of data type names to come
earlier in the parse order.  However, they allow interface names to be used
even before the interface is defined.</p>

<h3>Ruling out Interfaces</h3>

<p>I believe it is the case that, whenever we see @('identifier . identifier'),
we can assume we are in the interface case.  This is difficult to be sure of,
but I've at least run some experiments on NCV/VCS to try to do things like:</p>

@({
     module tricky;
       typedef logic [2:0] foo_t;
     endmodule

     module m (tricky.foo_t a);
       ...
     endmodule
})

<p>See in particular the @('ifport*') files in the @('vl/failtest') directory.
Fortunately, both VCS and NCV appear to reject these sorts of attempts.  At any
rate, if this is correct, then when we are parsing a port and see @('identifier
. identifier'), we can be sure it is an interface.</p>

<p>The other tricky possibility is that we have a port such as @('foo_t foo').
In this case, @('foo_t') might be an interface or a data type.  We do basic
parsing in @(see vl-parse-port-declaration-head-2012) and then resolve whether
we got a datatype or interface after parsing, in @(see port-resolve).</p>")

(local (xdoc::set-default-parents parse-port-types))

(defprod vl-parsed-portdecl-head
  :short "Temporary structure to represent a parsed @('net_port_type') or a
@('var_port_type')."

  :long "<p>There are elaborate, capricious rules for determining the net
types, data types, and directions of ports.</p>

<p>To help separate out this complexity from the initial problem of just
parsing things like @('net_port_type') and @('variable_port_type'), we write a
very dumb parser that just builds intermediate structures to record what it has
seen.</p>"

  :tag :vl-parsed-portdecl-head
  :layout :tree
  ((nettype    vl-maybe-nettypename-p
               "True exactly when there was an explicit net type.")
   (var-p      booleanp
               "True exactly when we found a @('var') keyword.")
   (type       vl-maybe-datatype-p
               "Exists if we found an explicit datatype.")
   (signing    vl-maybe-exprsign-p
               "Exists if we had a signedness keyword without an explicit datatype.")
   (dims       vl-dimensionlist-p
               "Nonempty only if we had packed dimensions without an explicit datatype.")))

(local (defthm crock-idtoken-of-car
         (implies (vl-is-token? :vl-idtoken)
                  (vl-idtoken-p (car (vl-tokstream->tokens))))
         :hints(("Goal" :in-theory (enable vl-is-token?)))))


(defparser vl-parse-datatype-only-if-followed-by-id ()
  :result (vl-maybe-datatype-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (b* ((backup (vl-tokstream-save))
       ((mv err val tokstream)
        (vl-parse-datatype))
       ((when (and (not err)
                   (vl-is-token? :vl-idtoken)))
        (mv err val tokstream))
       (tokstream (vl-tokstream-restore backup)))
    (mv nil nil tokstream)))

(defparser vl-parse-port-declaration-head-2012 ()
  :short "Matches @('net_port_type') or @('variable_port_type').  Assumes that
an identifier (i.e., a port name) must follow."

  :long "<p>Here is the grammar we are implementing:</p>

@({
    net_port_type ::= [net_type] data_type
                    | [net_type] [signing] {packed_dimension}
                    | identifier                                           (*)
                    | 'interconnect' [signing] {packed_dimension}          (**)

    variable_port_type ::= data_type
                         | 'var' data_type
                         | 'var' [signing] {packed_dimension}
})

<p>(*) Since VL doesn't support user-defined net types, we don't implement the
second @('net_port_type') case.</p>

<p>(**) We do not yet implement @('interconnect') ports.</p>"

  :result (vl-parsed-portdecl-head-p val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count weak
  (seq tokstream

       (when (vl-is-token? :vl-kwd-interconnect)
         ;; Possibilities:
         ;; (1) net_port_type ::= 'interconnect' implicit_data_type
         (return-raw
          (vl-parse-error "BOZO implement interconnect ports!")))

       (when (vl-is-token? :vl-kwd-var)
         ;; Possibilities:
         ;; (1) variable_port_type ::= 'var' data_type                          "explicit case"
         ;; (2) variable_port_type ::= 'var' [signing] {packed_dimension}       "implicit case"
         (:= (vl-match))
         ;; We'll check for the implicit case first.
         (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
           (signing := (vl-match)))
         (when (vl-is-token? :vl-lbrack)
           (ranges := (vl-parse-0+-ranges)))
         (when (or signing ranges)
           ;; Definitely in the implicit case.
           (return (make-vl-parsed-portdecl-head
                    :nettype nil
                    :var-p t
                    :signing (and signing
                                  (vl-signing-kwd-to-exprsign signing))
                    :dims   ranges)))

         ;; Possibilities:
         ;; (1) variable_port_type ::= 'var' data_type                          "explicit case"
         ;; (2) variable_port_type ::= 'var'                                    "empty implicit case"
         ;;
         ;; In the empty case, we expect that an identifier (the port name)
         ;; follows.  However, a data_type can also start with an identifier
         ;; and can even just be an identifier!  So we have to be extra careful
         ;; in this case.
         (when (vl-is-token? :vl-idtoken)
           (type := (vl-parse-datatype-only-if-followed-by-id))
           (return
            (if type
                ;; Found (and matched) a datatype followed by an ID.  So we're
                ;; in the explicit case.
                (make-vl-parsed-portdecl-head :nettype nil
                                              :var-p t
                                              :type type)
              ;; No datatype, so we just have var ID, i.e., we're in the empty
              ;; implicit case.  We haven't eaten the ID.
              (make-vl-parsed-portdecl-head :nettype nil
                                            :var-p t))))

         ;; The only remaining possibility is that we have:
         ;; (1) variable_port_type ::= 'var' data_type                          "explicit case"
         (type := (vl-parse-datatype))
         (return (make-vl-parsed-portdecl-head :nettype nil
                                               :var-p t
                                               :type type)))

       ;; We have now ruled out leading 'interconnect' and 'var' keywords.
       ;; Possibilities:
       ;; (1) net_port_type      ::= [net_type] data_type                         "explicit case"
       ;; (2) net_port_type      ::= [net_type] [signing] {packed_dimension}      "implicit case"
       ;;
       ;; We could also have:
       ;; (3) variable_port_type ::= data_type
       ;;
       ;; But this would just be a special case of the explicit case, so
       ;; there's not any way to distinguish it, so let's ignore it.
       (nettype := (vl-parse-optional-nettype))
       ;; Lets check for the implicit case first.
       (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
         (signing := (vl-match)))
       (when (vl-is-token? :vl-lbrack)
         (ranges := (vl-parse-0+-ranges)))
       (when (or signing ranges)
         ;; Definitely in the implicit case.
         (return (make-vl-parsed-portdecl-head
                  :nettype nettype
                  :var-p nil
                  :signing (and signing
                                (vl-signing-kwd-to-exprsign signing))
                  :dims ranges)))

       ;; Possibilities:
       ;; (1) net_port_type  ::= [net_type] data_type                         "explicit case"
       ;; (2) net_port_type  ::= [net_type]                                   "empty implicit case"
       ;;
       ;; Similar to the 'var' case above.
       (when (vl-is-token? :vl-idtoken)
         (type := (vl-parse-datatype-only-if-followed-by-id))
         (return
          (if type
              ;; Explicit type case
              (make-vl-parsed-portdecl-head :nettype nettype
                                            :var-p nil
                                            :type type)
            ;; Empty implicit case
            (make-vl-parsed-portdecl-head :nettype nettype
                                          :var-p nil))))

       ;; The only remaining possibility is that we must have:
       ;; (1) net_port_type  ::= [net_type] data_type                         "explicit case"
       (type := (vl-parse-datatype))
       (return (make-vl-parsed-portdecl-head :nettype nettype
                                             :var-p nil
                                             :type type))))


(defsection sv-non-ansi-portdecls
  :parents (parse-ports)
  :short "Parsing of SystemVerilog-2012 non-ANSI port declarations."

  :long "<p>NOTE: the port declarations we now describe are permitted in
grammar rules such as @('module_item'), @('interface_item'), and
@('program_item').  In other words, they're things that are permitted in
non-ANSI contexts like</p>

@({
         module foo (o, a, b);
             output o;             <---- this kind of stuff
             ...
         endmodule
})

<p>These aren't the same as for fancy ANSI port declarations like</p>

@({
     module foo (output logic [2:0] o, ...)
})

<p>The grammar rules are:</p>

@({
    port_declaration ::= {attribute_instance} inout_declaration
                       | {attribute_instance} input_declaration
                       | {attribute_instance} output_declaration
                       | {attribute_instance} ref_declaration             // NEW, not yet supported
                       | {attribute_instance} interface_port_declaration  // NEW, not yet supported
})

<p>The declarations we will currently try to support are:</p>

@({
   inout_declaration ::= 'inout' net_port_type      list_of_port_identifiers

   input_declaration ::= 'input' net_port_type      list_of_port_identifiers
                       | 'input' variable_port_type list_of_variable_identifiers

   output_declaration ::= 'output' net_port_type      list_of_port_identifiers
                        | 'output' variable_port_type list_of_variable_port_identifiers
})

<p>See @(see parse-port-types) for the port-type handling.</p>

<p>As for the three different kinds of lists of identifiers, they are all quite
similar to one another, differing only in the kinds of dimensions that are
allowed and in whether or not default values are permitted.  Here are their
definitions:</p>

@({
   list_of_port_identifiers          ::= identifier {unpacked_dimension} { ',' identifier {unpacked_dimension} }
   list_of_variable_identifiers      ::= identifier {variable_dimension} { ',' identifier {variable_dimension} }
   list_of_variable_port_identifiers ::= identifier {variable_dimension} [ '=' expression ]
                                         { ',' identifier {variable_dimension} [ '=' expression ] }
})

<p><b>However</b>, we don't yet implement default values.  Section 23.2.2.4
talks about default port values, and says they can only be specified for input
ports.  But the grammar only permits them for output ports.  That seems like a
bug with the standard.  By omitting them, the above reduce to:</p>

@({
   list_of_port_identifiers          ::= identifier {unpacked_dimension} {',' identifier {unpacked_dimension} }
   list_of_variable_identifiers      ::= identifier {variable_dimension} {',' identifier {variable_dimension} }
   list_of_variable_port_identifiers ::= identifier {variable_dimension} {',' identifier {variable_dimension} }
})")

(local (xdoc::set-default-parents sv-non-ansi-portdecls))

(defparser vl-parse-list-of-port-identifiers ()
  :short "Approximation of @('list_of_port_identifiers'),
  @('list_of_variable_identifiers'), and
  @('list_of_variable_port_identifiers')."
  :result (vl-parsed-port-identifier-list-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (id := (vl-match-token :vl-idtoken))
       (udims := (vl-parse-0+-variable-dimensions))
       (when (and (vl-is-token? :vl-comma)
                  (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens))))
         (:= (vl-match))
         (rest := (vl-parse-list-of-port-identifiers)))
       (return (cons (make-vl-parsed-port-identifier :name id
                                                     :udims udims)
                     rest))))

(define vl-parsed-portdecl-head->complete-p ((head vl-parsed-portdecl-head-p))
  :short "Determines if a parsed @('net_port_type') or @('variable_port_type') is
\"completely declared\" and should therefore create a net."
  :long "<p>SystemVerilog Section 23.2.2.1: \"If a port declaration includes a
net or a variable type, then the port is considered completely declared.\"</p>"
  (b* (((vl-parsed-portdecl-head head)))
    (if (or head.nettype
            head.var-p
            head.type)
        ;; I'm pretty sure this is right.
        t
      nil)))

(defparser vl-parse-port-declaration-noatts-2012 (atts)
  :short "Matches the rest of any @('port_declaration'), after the attributes."
  :long "<p>BOZO many, many subtle questions here about the net types we're
supposed to use here.  See the comments.</p>"
  :guard (vl-atts-p atts)
  ;; Returns (portdecls . netdecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
         (when (vl-is-token? :vl-kwd-inout)
           ;; port_declaration  ::= {attribute_instance} inout_declaration
           ;; inout_declaration ::= 'inout' net_port_type list_of_port_identifiers
           (:= (vl-match))
           (head := (vl-parse-port-declaration-head-2012)) ;; net_port_type or variable_port_type
           (when (vl-parsed-portdecl-head->var-p head)
             (return-raw
              (vl-parse-error "Inout ports cannot have variable types, they must be nets.")))
           (pids := (vl-parse-list-of-port-identifiers)) ;; approximate list of identifiers/udims
           (return
            (b* (((vl-parsed-portdecl-head head)))
              (vl-make-ports-and-maybe-nets
               pids
               :dir       :vl-inout
               ;; BOZO.  I have no idea what the nettype is supposed to be
               ;; here.  This seems vaguely plausible?  (We know that the inout
               ;; has to be a net.)
               :nettype    (or head.nettype :vl-wire)
               :type       (or head.type
                               (make-vl-coretype :name :vl-logic
                                                 :signedp (eq head.signing :vl-signed)
                                                 :pdims head.dims))
               :complete-p (vl-parsed-portdecl-head->complete-p head)
               :atts       atts))))

         (when (vl-is-token? :vl-kwd-input)
           ;; port_declaration ::= {attribute_instance} input_declaration
           ;; input_declaration ::= 'input' net_port_type      list_of_port_identifiers
           ;;                     | 'input' variable_port_type list_of_variable_identifiers
           (:= (vl-match))
           (head := (vl-parse-port-declaration-head-2012)) ;; net_port_type or variable_port_type
           (pids := (vl-parse-list-of-port-identifiers))   ;; approximate list of identifiers/udims
           (return
            (b* (((vl-parsed-portdecl-head head)))
              (vl-make-ports-and-maybe-nets
               pids
               :dir       :vl-input
               ;; BOZO.  I have no idea what the nettype is supposed to be
               ;; here.  This seems vaguely plausible, based on the rules in
               ;; 23.2.2.3.  But those rules seem to be talking about the first
               ;; port in a port list, not about non-ansi style port
               ;; declarations.
               :nettype    (if head.var-p
                               nil
                             (or head.nettype :vl-wire))
               :type       (or head.type
                               (make-vl-coretype :name :vl-logic
                                                 :signedp (eq head.signing :vl-signed)
                                                 :pdims head.dims))
               :complete-p (vl-parsed-portdecl-head->complete-p head)
               :atts       atts))))

         (when (vl-is-token? :vl-kwd-output)
           ;; port_declaration ::= {attribute_instance} output_declaration
           ;; output_declaration ::= 'output' net_port_type      list_of_port_identifiers
           ;;                      | 'output' variable_port_type list_of_variable_port_identifiers
           (:= (vl-match))
           (head := (vl-parse-port-declaration-head-2012)) ;; net_port_type or variable_port_type
           (pids := (vl-parse-list-of-port-identifiers))   ;; approximate list of identifiers/udims
           (return
            (b* (((vl-parsed-portdecl-head head)))
              (vl-make-ports-and-maybe-nets
               pids
               :dir :vl-output
               ;; BOZO I have no idea what the net type is supposed to be here.
               ;; This seems vaguely plausible, based on the rules in 23.2.2.3.
               ;; But those rules seem to be talking about the first port in a
               ;; port list, not about non-ansi style port declarations.
               :nettype    (cond (head.var-p      nil) ;; explicit var -- then var.
                                 (head.nettype    head.nettype) ;; explicit net type, so use it
                                 (head.type       nil) ;; explicit data type, no net type -- then var.
                                 (t               :vl-wire)) ;; implicit data type, no nettype/var keyword, then default net type
               :type       (or head.type
                               (make-vl-coretype :name :vl-logic
                                                 :signedp (eq head.signing :vl-signed)
                                                 :pdims head.dims))
               :complete-p (vl-parsed-portdecl-head->complete-p head)
               :atts       atts))))

         (when (vl-is-token? :vl-kwd-ref)
           ;; port_declaration ::= {attribute_instance} ref_declaration
           (return-raw
            (vl-parse-error "BOZO ref ports are not yet implemented.")))

         ;; Otherwise:
         ;; port_declaration ::= {attribute_instance} interface_port_declaration

         ;; interface_port_declaration ::= identifier list_of_interface_identifiers
         ;;                              | identifier '.' identifier list_of_interface_identifiers
         (:= (vl-match-token :vl-idtoken))
         (return-raw
          (vl-parse-error "BOZO interface ports are not yet implemented.")))
   ///
   (defthm true-listp-of-vl-parse-port-declaration-noatts-2012-1
     (true-listp (car (mv-nth 1 (vl-parse-port-declaration-noatts-2012 atts))))
     :rule-classes :type-prescription)

   (defthm true-listp-of-vl-parse-port-declaration-noatts-2012-2
     (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-noatts-2012 atts))))
     :rule-classes :type-prescription)

   (defthm vl-parse-port-declaration-noatts-2012-basics
     (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-noatts-2012 atts))))
          (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-noatts-2012 atts)))))))

(defparser vl-parse-port-declaration-noatts (atts)
  :parents (verilog-2005-portdecls sv-non-ansi-portdecls)
  :short "Matches @('port_declaration') for Verilog-2005 or SystemVerilog-2012,
except for the initial attributes.  Used for port declarations within modules."
  :guard (vl-atts-p atts)
  ;; Returns (portdecls . netdecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seq tokstream
       (when (eq (vl-loadconfig->edition config) :verilog-2005)
         (ans := (vl-parse-port-declaration-noatts-2005 atts nil))
         (return ans))
       (ans := (vl-parse-port-declaration-noatts-2012 atts))
       (return ans))
  ///
  (defthm true-listp-of-vl-parse-port-declaration-noatts-1
    (true-listp (car (mv-nth 1 (vl-parse-port-declaration-noatts atts))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-port-declaration-noatts-2
    (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-noatts atts))))
    :rule-classes :type-prescription)

  (defthm vl-parse-port-declaration-noatts-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-noatts atts))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-noatts atts)))))))



;; (defsection sv-ansi-portdecls
;;   :parents (parse-ports)
;;   :short "Parsing of SystemVerilog-2012 ANSI-style port declarations."
;;   :long "<p>Here's the basic grammar:</p>

;; @({
;;     list_of_port_declarations ::=  '(' [ {attribute_instance} ansi_port_declaration
;;                                            { ',' {attribute_instance} ansi_port_declaration } ] ')'

;;     ansi_port_declaration ::=
;;         [ net_port_header | interface_port_header ] identifier {unpacked_dimension} [ '=' expression ]
;;       | [ variable_port_header ] identifier {variable_dimension} [ '=' expression ]
;;       | [ port_direction ] '.' identifier '(' [expression] ')'

;;     net_port_header ::= [port_direction] net_port_type

;;     interface_port_header ::= identifier [ '.' identifier ]
;;                             | 'interface' [ '.' identifier ]

;;     variable_port_header ::= [port_direction] variable_port_type

;;     port_direction ::= 'input' | 'output' | 'inout' | 'ref'
;; })

;; <p>There are also some footnotes.  Section 23.2.2.2 imposes various semantic
;; restrictions, e.g.,: a ref port shall be a variable type and an inout port
;; shall not be; it shall be illegal to initialize a port that is not a variable
;; output port or to specify a default value for a port that is not an input
;; port.</p>

;; <p>Section 23.2.2.3 also gives a LOT of subtle rules regarding how the
;; directions/kinds get inherited across the list of port declarations, etc.
;; See @(see sv-ansi-port-interpretation).</p>


;; <h3>Simplifications and Limitations</h3>

;; <p>We have decided to NOT yet implement the third kind of
;; @('ansi_port_declaration'), which has a separate \"external\" name from the
;; internal expression.  That is, we do not try to implement:</p>

;; @({
;;    ansi_port_declaration ::= [ port_direction ] '.' identifier '(' [expression] ')'
;; })

;; <p>If we do want to come back and implement this some day, we will need to
;; figure out a way to reconcile the lack of port declarations for the wires
;; in the expression.  That is, back in the Verilog-2005 days, we could expect
;; that a port such as:</p>

;; @({
;;      module mymod (.foo( {a, b} ), ...)
;; })

;; <p>Would be followed up with port declarations for A and B.  However, these new
;; SystemVerilog ANSI-style declarations don't seem to have any such corresponding
;; port declarations.  It would likely take a bit of work to get transforms like
;; argresolve, replicate, and toe, to cope with this.</p>

;; <p>Anyway, this simplification means we're only going to try to support:</p>

;; @({
;;     ansi_port_declaration ::=
;;         [ net_port_header | interface_port_header ] identifier {unpacked_dimension} [ '=' expression ]
;;       | [ variable_port_header ]                    identifier {variable_dimension} [ '=' expression ]
;; })

;; <p>Furthermore, we'll not support default expressions yet (we don't support
;; them on non-ANSI ports yet, either) and since we don't really have any support
;; for fancy dimensions, what we'll really try to implement is just:</p>

;; @({
;;     ansi_port_declaration ::=
;;         net_port_header         identifier {unpacked_dimension}
;;       | variable_port_header    identifier {variable_dimension}
;;       | interface_port_header   identifier {unpacked_dimension}

;;     net_port_header ::= [port_direction] net_port_type

;;     variable_port_header ::= [port_direction] variable_port_type

;;     interface_port_header ::= identifier  [ '.' identifier ]
;;                             | 'interface' [ '.' identifier ]
;; })

;; <p>The tricky part of this is dealing with port types.  See @(see
;; parse-port-types) for notes about how we distinguish between
;; @('net_port_type'), @('variable_port_type'), and
;; @('interface_port_header').</p>")

;; (local (xdoc::set-default-parents sv-ansi-portdecls))

;; (defprod vl-parsed-interface-head
;;   :tag :vl-parsed-interface-head
;;   :layout :tree
;;   ((ifname stringp :rule-classes :type-prescription)
;;    (modport maybe-stringp :rule-classes :type-prescription)))

;; (deftranssum vl-parsed-ansi-head
;;   (vl-parsed-interface-head
;;    vl-parsed-portdecl-head))

;; (defthm vl-parsed-ansi-head-p-forward
;;   (implies (vl-parsed-ansi-head-p x)
;;            (or (eq (tag x) :vl-parsed-interface-head)
;;                (eq (tag x) :vl-parsed-portdecl-head)))
;;   :rule-classes :forward-chaining)

;; (defaggregate vl-parsed-ansi-port
;;   :tag :vl-parsed-ansi-port
;;   :legiblep nil
;;   ((dir  vl-maybe-direction-p)
;;    (head vl-parsed-ansi-head-p)
;;    (id   vl-parsed-port-identifier-p)
;;    (atts vl-atts-p)))

;; (defthm vl-parsed-ansi-port-p-forward
;;   (implies (vl-parsed-ansi-port-p x)
;;            (or (eq (tag (vl-parsed-ansi-port->head x)) :vl-parsed-interface-head)
;;                (eq (tag (vl-parsed-ansi-port->head x)) :vl-parsed-portdecl-head)))
;;   :rule-classes :forward-chaining
;;   :hints(("Goal"
;;           :in-theory (disable vl-parsed-ansi-head-p-forward)
;;           :use ((:instance vl-parsed-ansi-head-p-forward (x (vl-parsed-ansi-port->head x)))))))

;; (deflist vl-parsed-ansi-portlist-p (x)
;;   (vl-parsed-ansi-port-p x)
;;   :elementp-of-nil nil)



;; ;; (defparser vl-parse-ansi-port-header ()
;; ;;   :parents (sv-ansi-portdecls parse-port-types)
;; ;;   :short "Matches @('interface_port_header'), @('net_port_type'), or @('variable_port_type')."
;; ;;   :long "<p>See especially the discussion of \"ruling out interfaces\" in @(see
;; ;;   parse-port-types).</p>"
;; ;;   :result (vl-parsed-ansi-head-p val)
;; ;;   :resultp-of-nil nil
;; ;;   :true-listp nil
;; ;;   :fails gracefully
;; ;;   :count weak
;; ;;   :prepwork ((local (set-default-hints
;; ;;                      '((and stable-under-simplificationp
;; ;;                             '(:in-theory (enable vl-idtoken-p
;; ;;                                                  vl-lookahead-is-token?
;; ;;                                                  vl-match)))))))
;; ;;   (seq tokstream
;; ;;        (when (vl-is-token? :vl-kwd-interface)
;; ;;          (return-raw
;; ;;           (vl-parse-error "BOZO implement explicit 'interface' ports.")))
;; ;;        (when (and (vl-is-token? :vl-idtoken)
;; ;;                   (vl-lookahead-is-token? :vl-dot (cdr (vl-tokstream->tokens)))
;; ;;                   (vl-lookahead-is-token? :vl-idtoken (cddr (vl-tokstream->tokens))))
;; ;;          ;; Found "foo.bar".
;; ;;          ;; This is definitely an interface port with a modport.  See PARSE-PORT-TYPES.
;; ;;          (iface := (vl-match))
;; ;;          (:= (vl-match))
;; ;;          (modport := (vl-match))
;; ;;          (return (make-vl-parsed-interface-head :ifname (vl-idtoken->name iface)
;; ;;                                                 :modport (vl-idtoken->name modport))))
;; ;;        (when (and (vl-is-token? :vl-idtoken)
;; ;;                   (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens)))
;; ;;                   (not (vl-parsestate-is-user-defined-type-p
;; ;;                         (vl-idtoken->name (car (vl-tokstream->tokens)))
;; ;;                         (vl-tokstream->pstate))))
;; ;;          ;; Found "foo bar" and "foo" is NOT the name of a user-defined type.
;; ;;          ;; This has to be an interface port.  See PARSE-PORT-TYPES.
;; ;;          ;;   - "foo" is the name of the interface.
;; ;;          ;;   - "bar" is the name of the port identifier (which doesn't belong to us)
;; ;;          (iface := (vl-match))
;; ;;          (return (make-vl-parsed-interface-head :ifname (vl-idtoken->name iface)
;; ;;                                                 :modport nil)))
;; ;;        ;; Otherwise this can't be an interface, so it can only be a variable or
;; ;;        ;; port header.
;; ;;        (ans := (vl-parse-port-declaration-head-2012))
;; ;;        (return ans)))

;; ;; (defparser vl-parse-ansi-port-declaration (atts)
;; ;;   :short "Matches @('ansi_port_declaration')."
;; ;;   :guard (vl-atts-p atts)
;; ;;   :result (vl-parsed-ansi-port-p val)
;; ;;   :resultp-of-nil nil
;; ;;   :true-listp nil
;; ;;   :fails gracefully
;; ;;   :count strong
;; ;;   (seq tokstream
;; ;;        (dir := (vl-parse-optional-port-direction))
;; ;;        (when dir
;; ;;          ;; It cannot be an interface port header.
;; ;;          (head  := (vl-parse-port-declaration-head-2012))
;; ;;          (id    := (vl-match-token :vl-idtoken))
;; ;;          (udims := (vl-parse-0+-variable-dimensions))
;; ;;          (return (make-vl-parsed-ansi-port :dir  dir
;; ;;                                            :atts atts
;; ;;                                            :head head
;; ;;                                            :id  (make-vl-parsed-port-identifier :name id
;; ;;                                                                                 :udims udims))))
;; ;;        ;; Else, no direction; can have interface, net, or variable port type.
;; ;;        (head  := (vl-parse-ansi-port-header))
;; ;;        (id    := (vl-match-token :vl-idtoken))
;; ;;        (udims := (vl-parse-0+-variable-dimensions))
;; ;;        (return (make-vl-parsed-ansi-port :dir  nil
;; ;;                                          :head head
;; ;;                                          :atts atts
;; ;;                                          :id   (make-vl-parsed-port-identifier :name id
;; ;;                                                                                :udims udims)))))







;; (defsection sv-ansi-port-interpretation
;;   :parents (parse-ports)
;;   :short "SystemVerilog-2012 rules for determining port kind/type/direction for
;; ANSI ports (Section 23.2.2.3)."

;;   :long "<p>SystemVerilog has some tricky rules for how ANSI port lists are
;; interpreted.  For instance, in a module like:</p>

;; @({
;;      module foo (output o,
;;                  input logic [3:0] a, b, c) ;
;;        ...
;;      endmodule
;; })

;; <p>The @('input logic [3:0]') part gets used for @('a'), @('b'), and @('c').
;; Our actual parsing routines (see @(see sv-ansi-portdecls)) don't try to follow
;; these rules.  Instead, they give us a list of \"raw\" @(see
;; vl-parsed-ansi-port-p) structures, which we then need to convert into actual
;; ports, port declarations, and variable declarations.</p>")

;; (local (xdoc::set-default-parents sv-ansi-port-interpretation))





