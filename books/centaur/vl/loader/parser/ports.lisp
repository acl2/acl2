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
(local (include-book "../../util/arithmetic"))



; A port_expression is just a syntactic means to restrict the expressions
; allowed in ports to identifiers, bit-selects, part-selects, and
; concatenations.  We just parse port_expressions into plain expressions:
;
; port_expression ::=
;    port_reference
;  | '{' port_reference { ',' port_reference } '}'
;
; port_reference ::=
;    identifier [ '[' constant_range_expression ']' ]
;
; constant_range_expression ::=
;    constant_expression
;  | msb_constant_expression : lsb_constant_expression

(defparser vl-parse-port-reference ()
  ;; Note: Assumes that if a bracket follows the identifier, it belongs to this
  ;; port reference.  This is safe in port-expressions since only a comma or
  ;; end curly-brace will follow them, and they never occur in other parts of
  ;; the grammar so it should be fine universally.
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (unless (vl-is-token? :vl-lbrack)
          (return (make-vl-atom
                   :guts (make-vl-id :name (vl-idtoken->name id)))))
        (:= (vl-match))
        (range := (vl-parse-range-expression))
        (unless (or (eq (vl-erange->type range) :vl-index)
                    (eq (vl-erange->type range) :vl-colon))
          (return-raw
           (vl-parse-error "The +: or -: operators are not allowed in port expressions.")))
        (:= (vl-match-token :vl-rbrack))
        (return (vl-build-range-select
                 (make-vl-atom
                  :guts (make-vl-id :name (vl-idtoken->name id)) )
                 range))))

(defparser vl-parse-1+-port-references-separated-by-commas ()
  ;; Matches port_reference { ',' port_reference }
  :result (vl-exprlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-port-reference))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-port-references-separated-by-commas)))
        (return (cons first rest))))

(defparser vl-parse-port-expression ()
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-lcurly)
          ;; A concatenation.
          (:= (vl-match))
          (args := (vl-parse-1+-port-references-separated-by-commas))
          (:= (vl-match-token :vl-rcurly))
          (return (make-vl-nonatom :op :vl-concat
                                   :args args)))
        ;; A single port reference.
        (ref := (vl-parse-port-reference))
        (return ref)))



; From the specification:
;
; list_of_ports ::= '(' port { ',' port } ')'
;
; port ::=
;    [port_expression]
;  | '.' identifier '(' [port_expression] ')'
;
; Note that the above rules allow null ports, e.g., "module foo ( a, , b )".
; As described in 12.3.2, the port expression is optional to allow for ports
; that do not connect to anything internal to the module.
;
; If we were to interpret this very literally, the list_of_ports for "()" would
; be a singleton list with a blank port.  But in light of the way module
; instances work (see the "Special note about blank ports" in
; parse-insts.lisp), it seems like the nicest way to handle this is to instead
; allow an empty list of ports, and treat () as producing the empty list of
; ports instead.

(defparser vl-parse-nonnull-port ()
  ;; Matches ports except for the empty port
  :result (vl-port-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (loc := (vl-current-loc))
        (unless (vl-is-token? :vl-dot)
          (pexpr := (vl-parse-port-expression))
          (return (cond ((and (vl-atom-p pexpr)
                              (vl-id-p (vl-atom->guts pexpr)))
                         ;; Simple port like "x".  It gets its own name.
                         (make-vl-port :name (vl-id->name (vl-atom->guts pexpr))
                                       :expr pexpr
                                       :loc loc))
                        (t
                         ;; Expression port with no name.
                         (make-vl-port :name nil
                                       :expr pexpr
                                       :loc loc)))))
        ;; Otherwise, we have a name and possibly an expr.
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (unless (vl-is-token? :vl-rparen)
          (pexpr := (vl-parse-port-expression)))

        ;; BOZO why can't I just use (vl-match) here?
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-port :name (vl-idtoken->name id)
                              :expr pexpr
                              :loc loc))))

(defparser vl-parse-1+-ports-separated-by-commas ()
  ;; Matches port { ',' port }, possibly producing blank ports!
  :result (vl-portlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  (seqw tokens warnings
        (when (vl-is-token? :vl-rparen)
          ;; Blank port at the end.
          (loc := (vl-current-loc))
          (return (list (make-vl-port :name nil :expr nil :loc loc))))

        (when (vl-is-token? :vl-comma)
          (loc := (vl-current-loc))
          (:= (vl-match))
          (rest := (vl-parse-1+-ports-separated-by-commas))
          (return (cons (make-vl-port :name nil :expr nil :loc loc)
                        rest)))

        (first := (vl-parse-nonnull-port))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-ports-separated-by-commas)))
        (return (cons first rest))))

(defparser vl-parse-list-of-ports ()
  :result (vl-portlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        ;; Special hack: if it's just (), just return NIL instead of a
        ;; list with a blank port.
        (:= (vl-match-token :vl-lparen))
        (unless (vl-is-token? :vl-rparen)
          (ports := (vl-parse-1+-ports-separated-by-commas)))
        ;; BOZO why can't I use (vl-match) here?
        (:= (vl-match-token :vl-rparen))
        (return ports)))


;                              PORT DECLARATIONS
;
; port_declaration ::=
;   {attribute_instance} inout_declaration
; | {attribute_instance} input_declaration
; | {attribute_instance} output_declaration
;
; inout_declaration ::=
;    'inout' [net_type] ['signed'] [range] list_of_port_identifiers
;
; input_declaration ::=
;    'input' [net_type] ['signed'] [range] list_of_port_identifiers
;
; output_declaration ::=
;    'output' [net_type] ['signed'] [range] list_of_port_identifiers
;  | 'output' 'reg' ['signed'] [range] list_of_variable_port_identifiers
;  | 'output' output_variable_type list_of_variable_port_identifiers
;
; net_type ::= 'supply0' | 'supply1' | 'tri' | 'triand' | 'trior' | 'tri0' | 'tri1'
;            | 'uwire' | 'wire' | 'wand' | 'wor'
;
; list_of_port_identifiers ::= identifier { ',' identifier }
;
; list_of_variable_port_identifiers ::=
;    identifier ['=' expression] { ',' identifier [ '=' expression ] }
;
; output_variable_type ::= 'integer' | 'time'
;
; list_of_port_declarations ::=
;    '(' port_declaration { ',' port_declaration } ')'
;  | '(' ')'

(defparser vl-parse-1+-identifiers-separated-by-commas ()
  ;; Matches identifier { ',' identifier }
  :result (vl-idtoken-list-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-match-token :vl-idtoken))

; We have to take extra care here, because we can have situations like "input
; [7:0] a, b, output c" in list_of_port_declarations, where the comma following
; b is not really part of the identifier list.  That is, we can't just assume
; that because we've seen a comma, "the comma belongs to us and must be
; followed by another identifier"   We have to look for the identifier, too.

        (when (and (vl-is-token? :vl-comma)
                   (vl-is-token? :vl-idtoken :tokens (cdr tokens)))
          (:= (vl-match))
          (rest := (vl-parse-1+-identifiers-separated-by-commas)))
        (return (cons first rest))))


(define vl-build-portdecls (&key (ids vl-idtoken-list-p)
                                 (dir vl-direction-p)
                                 (type vl-datatype-p)
                                 (atts vl-atts-p))
  :returns (portdecls vl-portdecllist-p)
  (if (atom ids)
      nil
    (cons (make-vl-portdecl :name (vl-idtoken->name (car ids))
                            :loc  (vl-token->loc (car ids))
                            :dir  dir
                            :type type
                            :atts atts)
          (vl-build-portdecls :ids  (cdr ids)
                              :dir  dir
                              :type type
                              :atts atts))))

(define vl-build-netdecls-for-ports (&key (ids vl-idtoken-list-p)
                                          (type vl-datatype-p)
                                          (atts vl-atts-p))
  :returns (netdecls vl-vardecllist-p)
  (if (atom ids)
      nil
    (cons (make-vl-vardecl :name (vl-idtoken->name (car ids))
                           :loc  (vl-token->loc (car ids))
                           :type type
                           :atts atts
                           ;; BOZO are these right?  I think so?  I think
                           ;; there isn't a way to declare these in a port,
                           ;; at least in Verilog-2005?
                           :vectoredp nil
                           :scalaredp nil
                           :dims nil
                           :delay nil
                           :cstrength nil)
          (vl-build-netdecls-for-ports :ids (cdr ids)
                                       :type type
                                       :atts atts))))


(defconst *vl-directions-kwd-alist*
  '((:vl-kwd-input . :vl-input)
    (:vl-kwd-output . :vl-output)
    (:vl-kwd-inout . :vl-inout)))

(defconst *vl-directions-kwds*
  (strip-cars *vl-directions-kwd-alist*))



(defparser vl-parse-basic-port-declaration-tail (dir atts)
  ;; Matches [net_type] ['signed'] [range] list_of_port_identifiers
  :guard (and (vl-direction-p dir)
              (vl-atts-p atts))
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (nettype := (vl-parse-optional-nettype))
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (ids := (vl-parse-1+-identifiers-separated-by-commas))
        (return
         ;; What happens next is very subtle.  See also portdecl-sign and
         ;; make-implicit-wires.
         ;;
         ;; From Verilog-2005, page 174:
         ;;
         ;;  - "If a port declaration includes a net or variable type, then the
         ;;     port is considered completely declared and it is an error for
         ;;     the port to be declared again in a variable or net data type
         ;;     declaration..."
         ;;
         ;;  - "If the port declaration does NOT include a net or variable
         ;;     type, then the port can be declared again in a net or variable
         ;;     declaration.  If the net or variable is declared as a vector,
         ;;     the range specification between the two declarations shall be
         ;;     identical."
         ;;
         ;; So if we have a net type, then this is completely declared and we
         ;; are going to generate both (1) a port declaration and (2) the
         ;; corresponding net declaration.
         ;;
         ;; If we have no net type, then we'll instead only add the port
         ;; declaration, which we will mark with the attribute
         ;; VL_INCOMPLETE_DECLARATION.  The corresponding net will either be
         ;; found later in the module, or will be added automatically with the
         ;; make-implicit-wires transform.  Signedness is handled last, by
         ;; portdecl-sign.
         (b* ((atts (if nettype
                        atts
                      (acons "VL_INCOMPLETE_DECLARATION" nil atts)))
              ;; See portdecl-sign.  The datatype here is not necessarily
              ;; correct, e.g., because the corresponding variable declaration
              ;; might have some other type (e.g., WOR or REG).  However, due
              ;; to the VL_INCOMPLETE_DECLARATION attribute, we'll correct for
              ;; this before creating the module.
              (datatype (make-vl-nettype :name (or nettype :vl-wire)
                                         :signedp (if signed t nil)
                                         :range range))
              (portdecls
               (vl-build-portdecls :dir dir
                                   :ids ids
                                   :type datatype
                                   :atts atts))
              (netdecls (if nettype
                            (vl-build-netdecls-for-ports :ids ids
                                                         :type datatype
                                                         :atts
                                                         ;; Make sure the variables are marked as implicit
                                                         ;; to avoid pretty-printing them.
                                                         (acons "VL_PORT_IMPLICIT" nil atts))
                          ;; No netdecls since we're incomplete
                          nil)))
           (cons portdecls netdecls))))
  ///
  (defthm true-listp-of-vl-parse-basic-port-declaration-tail-1
    (true-listp (car (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-basic-port-declaration-tail-2
    (true-listp (cdr (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts))))
    :rule-classes :type-prescription)

  (defthm vl-parse-basic-port-declaration-tail-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-basic-port-declaration-tail dir atts)))))))

(defparser vl-parse-output-reg-port-tail (atts)
  ;; We've just matched 'output reg'.
  ;; Now match ['signed'] [range] list_of_variable_port_identifiers
  :guard (vl-atts-p atts)
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-signed)
          (signed := (vl-match)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (ids := (vl-parse-1+-identifiers-separated-by-commas))
        (return
         ;; We have a reg type, so this is completely declared.
         (b* ((datatype (make-vl-coretype :name :vl-reg
                                          :signedp (if signed t nil)
                                          :dims (and range
                                                     (list range))))
              (portdecls (vl-build-portdecls :dir :vl-output
                                             :ids ids
                                             :type datatype
                                             :atts atts))
              (netdecls (vl-build-netdecls-for-ports :ids ids
                                                     :type datatype
                                                     :atts (acons "VL_PORT_IMPLICIT" nil atts))))
           (cons portdecls netdecls))))
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


(defparser vl-parse-port-declaration-noatts (atts)
  ;; Matches inout_declaration | input_declaration | output_declaration
  :guard (vl-atts-p atts)
   ;; Returns (portdecls . netdecls)
   :result (consp val)
   :resultp-of-nil nil
   :true-listp nil
   :fails gracefully
   :count strong
   (seqw tokens warnings

         (when (vl-is-token? :vl-kwd-input)
           (:= (vl-match))
           (ans := (vl-parse-basic-port-declaration-tail :vl-input atts))
           ;; input_declaration ::= 'input' [net_type] ['signed'] [range] list_of_port_identifiers
           (return ans))

         (when (vl-is-token? :vl-kwd-inout)
           (:= (vl-match))
           ;; inout_declaration ::= 'inout' [net_type] ['signed'] [range] list_of_port_identifiers
           (ans := (vl-parse-basic-port-declaration-tail :vl-inout atts))
           (return ans))

         ;; Outputs are more complex:
         ;;
         ;; output_declaration ::=
         ;;    'output' [net_type] ['signed'] [range] list_of_port_identifiers
         ;;  | 'output' 'reg' ['signed'] [range] list_of_variable_port_identifiers
         ;;  | 'output' output_variable_type list_of_variable_port_identifiers
         (:= (vl-match-token :vl-kwd-output))

         (when (vl-is-token? :vl-kwd-reg)
           (ans := (vl-parse-output-reg-port-tail atts))
           (return ans))

         ;; output_variable_type ::= 'integer' | 'time'
         ;; 'output' output_variable_type list_of_variable_port_identifiers
         (when (vl-is-some-token? '(:vl-kwd-integer :vl-kwd-time))
           (type := (vl-match))
           (ids := (vl-parse-1+-identifiers-separated-by-commas))
           (return
            (b* ((datatype (if (eq (vl-token->type type) :vl-kwd-integer)
                               *vl-plain-old-integer-type*
                             *vl-plain-old-time-type*))
                 (portdecls (vl-build-portdecls :dir :vl-output
                                                :ids ids
                                                :type datatype
                                                :atts atts))
                 (netdecls (vl-build-netdecls-for-ports :ids ids
                                                        :type datatype
                                                        :atts (acons "VL_PORT_IMPLICIT" nil atts))))
              (cons portdecls netdecls))))

         ;; 'output' [net_type] ['signed'] [range] list_of_port_identifiers
         (ans := (vl-parse-basic-port-declaration-tail :vl-output atts))
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



(defparser vl-parse-port-declaration-atts ()
  ;; BOZO this appears to be unused??  Ah, it's in support of the alternate form of module definition
  ;; that is currently unsupported.
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (result := (vl-parse-port-declaration-noatts atts))
        (return result))
  ///
  (defthm true-listp-of-vl-parse-port-declaration-atts-1
    (true-listp (car (mv-nth 1 (vl-parse-port-declaration-atts))))
    :rule-classes :type-prescription)
  (defthm true-listp-of-vl-parse-port-declaration-atts-2
    (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-atts))))
    :rule-classes :type-prescription)
  (defthm vl-parse-port-declaration-atts-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-atts))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-atts)))))))



(defparser vl-parse-1+-port-declarations-separated-by-commas ()
  ;; BOZO this appears to be unused??  Ah, it's in support of the alternate form of module definition
  ;; that is currently unsupported.
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :verify-guards nil
  :count strong
  (seqw tokens warnings
        ((portdecls1 . vardecls1) := (vl-parse-port-declaration-atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          ((portdecls2 . vardecls2) := (vl-parse-1+-port-declarations-separated-by-commas)))
        (return (cons (append portdecls1 portdecls2)
                      (append vardecls1 vardecls2))))
  ///
  (defthm true-listp-of-vl-parse-1+-port-declarations-separated-by-commas-1
    (true-listp (car (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-1+-port-declarations-separated-by-commas-2
    (true-listp (cdr (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas))))
    :rule-classes :type-prescription)

  (defthm vl-parse-1+-port-declarations-separated-by-commas-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas))))))

  (verify-guards vl-parse-1+-port-declarations-separated-by-commas-fn))



(defparser vl-parse-list-of-port-declarations ()
  ;; BOZO this appears to be unused??  Ah, it's in support of the alternate form of module definition
  ;; that is currently unsupported.
  ;; Returns (portdecls . vardecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-lparen))
        (decls := (vl-parse-1+-port-declarations-separated-by-commas))
        (:= (vl-match-token :vl-rparen))
        (return decls))
  ///
  (defthm true-listp-of-vl-parse-list-of-port-declarations-1
    (true-listp (car (mv-nth 1 (vl-parse-list-of-port-declarations))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-parse-list-of-port-declarations-2
    (true-listp (cdr (mv-nth 1 (vl-parse-list-of-port-declarations))))
    :rule-classes :type-prescription)

  (defthm vl-parse-list-of-port-declarations-basics
    (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-list-of-port-declarations))))
         (vl-vardecllist-p (cdr (mv-nth 1 (vl-parse-list-of-port-declarations)))))))
