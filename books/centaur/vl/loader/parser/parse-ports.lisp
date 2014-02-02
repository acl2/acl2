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
(include-book "parse-nets")
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

(defparser vl-parse-port-reference (tokens warnings)
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
        (:= (vl-match-token :vl-lbrack))
        (range := (vl-parse-range-expression))
        (unless (or (eq (vl-erange->type range) :vl-bitselect)
                    (eq (vl-erange->type range) :vl-colon))
          (return-raw
           (vl-parse-error "The +: or -: operators are not allowed in port expressions.")))
        (:= (vl-match-token :vl-rbrack))
        (return (vl-build-range-select
                 (make-vl-atom
                  :guts (make-vl-id :name (vl-idtoken->name id)) )
                 range))))

(defparser vl-parse-1+-port-references-separated-by-commas (tokens warnings)
  ;; Matches port_reference { ',' port_reference }
  :result (vl-exprlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-port-reference))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-port-references-separated-by-commas)))
        (return (cons first rest))))

(defparser vl-parse-port-expression (tokens warnings)
  :result (vl-expr-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-lcurly)
          ;; A concatenation.
          (:= (vl-match-token :vl-lcurly))
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

(defparser vl-parse-nonnull-port (tokens warnings)
  ;; Matches ports except for the empty port
  :result (vl-port-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (loc := (vl-current-loc tokens))
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
        (:= (vl-match-token :vl-dot))
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-lparen))
        (unless (vl-is-token? :vl-rparen)
          (pexpr := (vl-parse-port-expression)))
        (:= (vl-match-token :vl-rparen))
        (return (make-vl-port :name (vl-idtoken->name id)
                              :expr pexpr
                              :loc loc))))

(defparser vl-parse-1+-ports-separated-by-commas (tokens warnings)
  ;; Matches port { ',' port }, possibly producing blank ports!
  :result (vl-portlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  (seqw tokens warnings
        (when (vl-is-token? :vl-rparen)
          ;; Blank port at the end.
          (loc := (vl-current-loc tokens))
          (return (list (make-vl-port :name nil :expr nil :loc loc))))

        (when (vl-is-token? :vl-comma)
          (loc := (vl-current-loc tokens))
          (first := (mv nil (make-vl-port :name nil :expr nil :loc loc)
                        tokens warnings))
          (:= (vl-match-token :vl-comma))
          (rest  := (vl-parse-1+-ports-separated-by-commas))
          (return (cons first rest)))

        (first := (vl-parse-nonnull-port))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-ports-separated-by-commas)))
        (return (cons first rest))))

(defparser vl-parse-list-of-ports (tokens warnings)
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
; ------NOT SUPPORTED------
;  | 'output' 'reg' ['signed'] [range] list_of_variable_port_identifiers
;  | 'output' output_variable_type list_of_variable_port_identifiers
; ------/NOT SUPPORTED------
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

(defparser vl-parse-1+-identifiers-separated-by-commas (tokens warnings)
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
                   (vl-is-token? :vl-idtoken (cdr tokens)))
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-1+-identifiers-separated-by-commas)))
        (return (cons first rest))))



(defund vl-build-portdecls (loc ids dir signedp range atts)
  (declare (xargs :guard (and (vl-location-p loc)
                              (vl-idtoken-list-p ids)
                              (vl-direction-p dir)
                              (booleanp signedp)
                              (vl-maybe-range-p range)
                              (vl-atts-p atts))))
  (if (consp ids)
      (cons (make-vl-portdecl :loc loc
                              :name (vl-idtoken->name (car ids))
                              :dir dir
                              :signedp signedp
                              :range range
                              :atts atts)
            (vl-build-portdecls loc (cdr ids) dir signedp range atts))
    nil))

(defthm vl-portdecllist-p-of-vl-build-portdecls
  (implies (and (force (vl-location-p loc))
                (force (vl-idtoken-list-p ids))
                (force (vl-direction-p dir))
                (force (booleanp signedp))
                (force (vl-maybe-range-p range))
                (force (vl-atts-p atts)))
           (vl-portdecllist-p
            (vl-build-portdecls loc ids dir signedp range atts)))
  :hints(("Goal" :in-theory (enable vl-build-portdecls))))


(defun vl-build-netdecls-for-ports (loc ids type signedp range atts)
  (declare (xargs :guard (and (vl-location-p loc)
                              (vl-idtoken-list-p ids)
                              (vl-netdecltype-p type)
                              (booleanp signedp)
                              (vl-maybe-range-p range)
                              (vl-atts-p atts))))
  (if (consp ids)
      (cons (make-vl-netdecl :loc loc
                             :name (vl-idtoken->name (car ids))
                             :type type
                             :range range
                             :signedp signedp
                             :atts atts
                             ;; BOZO are these right?
                             :vectoredp nil
                             :scalaredp nil
                             :arrdims nil
                             :delay nil
                             :cstrength nil)
            (vl-build-netdecls-for-ports loc (cdr ids) type signedp range atts))
    nil))

(defthm vl-netdecllist-p-of-vl-build-netdecls-for-ports
  (implies (and (force (vl-location-p loc))
                (force (vl-idtoken-list-p ids))
                (force (vl-netdecltype-p type))
                (force (booleanp signedp))
                (force (vl-maybe-range-p range))
                (force (vl-atts-p atts)))
           (vl-netdecllist-p
            (vl-build-netdecls-for-ports loc ids type signedp range atts)))
  :hints(("Goal" :in-theory (enable vl-build-netdecls-for-ports))))


(defconst *vl-directions-kwd-alist*
  '((:vl-kwd-input . :vl-input)
    (:vl-kwd-output . :vl-output)
    (:vl-kwd-inout . :vl-inout)))


(defconst *vl-directions-kwds*
  (strip-cars *vl-directions-kwd-alist*))


; BOZO think about maybe just having this function return a module item list
; directly.  We end up not distinguishing in parse-modules anyway.

(with-output
 :off prove :gag-mode :goals

 (defparser vl-parse-port-declaration-noatts (atts tokens warnings)

; We may need to change what this returns if we add support for the "output"
; types, because those can have assignments.

   :guard (vl-atts-p atts)
   ;; Returns (portdecls . netdecls)
   :result (consp val)
   :resultp-of-nil nil
   :true-listp nil
   :fails gracefully
   :count strong

   (seqw tokens warnings
         (dir := (vl-match-some-token *vl-directions-kwds*))
         (when (and (eq (vl-token->type dir) :vl-kwd-output)
                    (vl-is-some-token? '(:vl-kwd-reg :vl-kwd-time :vl-kwd-integer)))
           (return-raw (vl-parse-error "Output reg, output integer, and output time ~
                                        are not supported.")))
         (type := (vl-parse-optional-nettype))
         (when (vl-is-token? :vl-kwd-signed)
           (signed := (vl-match-token :vl-kwd-signed)))
         (when (vl-is-token? :vl-lbrack)
           (range := (vl-parse-range)))
         (ids := (vl-parse-1+-identifiers-separated-by-commas))
         (return
          (let ((portdecls
                 (vl-build-portdecls (vl-token->loc dir)
                                     ids
                                     (cdr (assoc-eq (vl-token->type dir)
                                                    *vl-directions-kwd-alist*))
                                     (if signed t nil)
                                     range atts))
                (netdecls
                 (and type
                      (vl-build-netdecls-for-ports (vl-token->loc dir)
                                                   ids
                                                   type
                                                   (if signed t nil)
                                                   range atts))))
            (cons portdecls netdecls))))))

(defthm true-listp-of-vl-parse-port-declaration-noatts-1
  (true-listp (car (mv-nth 1 (vl-parse-port-declaration-noatts atts tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-port-declaration-noatts))))

(defthm true-listp-of-vl-parse-port-declaration-noatts-2
  (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-noatts atts tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-port-declaration-noatts))))

(defthm vl-parse-port-declaration-noatts-basics
  (implies (and (force (vl-tokenlist-p tokens))
                (force (vl-atts-p atts)))
           (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-noatts atts tokens warnings))))
                (vl-netdecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-noatts atts tokens warnings))))))
  :hints(("Goal" :in-theory (enable vl-parse-port-declaration-noatts))))



(defparser vl-parse-port-declaration-atts (tokens warnings)
  ;; BOZO this appears to be unused??  Ah, it's in support of the alternate form of module definition
  ;; that is currently unsupported.
  ;; Returns (portdecls . netdecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (result := (vl-parse-port-declaration-noatts atts))
        (return result)))

(defthm true-listp-of-vl-parse-port-declaration-atts-1
  (true-listp (car (mv-nth 1 (vl-parse-port-declaration-atts tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-port-declaration-atts))))

(defthm true-listp-of-vl-parse-port-declaration-atts-2
  (true-listp (cdr (mv-nth 1 (vl-parse-port-declaration-atts tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-port-declaration-atts))))

(defthm vl-parse-port-declaration-atts-basics
  (implies (force (vl-tokenlist-p tokens))
           (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-port-declaration-atts tokens warnings))))
                (vl-netdecllist-p (cdr (mv-nth 1 (vl-parse-port-declaration-atts tokens warnings))))))
  :hints(("Goal" :in-theory (enable vl-parse-port-declaration-atts))))



(defparser vl-parse-1+-port-declarations-separated-by-commas (tokens warnings)
  ;; BOZO this appears to be unused??  Ah, it's in support of the alternate form of module definition
  ;; that is currently unsupported.
  ;; Returns (portdecls . netdecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :verify-guards nil
  :count strong
  (seqw tokens warnings
        ((portdecls1 . netdecls1) := (vl-parse-port-declaration-atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          ((portdecls2 . netdecls2) := (vl-parse-1+-port-declarations-separated-by-commas)))
        (return (cons (append portdecls1 portdecls2)
                      (append netdecls1 netdecls2)))))

(defthm true-listp-of-vl-parse-1+-port-declarations-separated-by-commas-1
  (true-listp (car (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-1+-port-declarations-separated-by-commas))))

(defthm true-listp-of-vl-parse-1+-port-declarations-separated-by-commas-2
  (true-listp (cdr (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-1+-port-declarations-separated-by-commas))))

(defthm vl-parse-1+-port-declarations-separated-by-commas-basics
  (implies (force (vl-tokenlist-p tokens))
           (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas tokens warnings))))
                (vl-netdecllist-p (cdr (mv-nth 1 (vl-parse-1+-port-declarations-separated-by-commas tokens warnings))))))
  :hints(("Goal" :in-theory (enable vl-parse-1+-port-declarations-separated-by-commas))))

(verify-guards vl-parse-1+-port-declarations-separated-by-commas-fn)



(defparser vl-parse-list-of-port-declarations (tokens warnings)
  ;; BOZO this appears to be unused??  Ah, it's in support of the alternate form of module definition
  ;; that is currently unsupported.
  ;; Returns (portdecls . netdecls)
  :result (consp val)
  :resultp-of-nil nil
  :true-listp nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-lparen))
        (decls := (vl-parse-1+-port-declarations-separated-by-commas))
        (:= (vl-match-token :vl-rparen))
        (return decls)))

(defthm true-listp-of-vl-parse-list-of-port-declarations-1
  (true-listp (car (mv-nth 1 (vl-parse-list-of-port-declarations tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-list-of-port-declarations))))

(defthm true-listp-of-vl-parse-list-of-port-declarations-2
  (true-listp (cdr (mv-nth 1 (vl-parse-list-of-port-declarations tokens warnings))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-parse-list-of-port-declarations))))

(defthm vl-parse-list-of-port-declarations-basics
  (implies (force (vl-tokenlist-p tokens))
           (and (vl-portdecllist-p (car (mv-nth 1 (vl-parse-list-of-port-declarations tokens warnings))))
                (vl-netdecllist-p (cdr (mv-nth 1 (vl-parse-list-of-port-declarations tokens warnings))))))
  :hints(("Goal" :in-theory (enable vl-parse-list-of-port-declarations))))




;; BOZO more unit tests!

(local
 (encapsulate
   ()
   (local (include-book "../lexer/lexer")) ;; for making test inputs from strings

   (defmacro test-parse-port (&key input (successp 't) name expr)
     `(with-output
        :off summary
        (assert! (mv-let (erp val tokens warnings)
                   (vl-parse-nonnull-port (make-test-tokens ,input) 'blah-warnings)
                   (if ,successp
                       (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                    (not erp))
                            (prog2$ (cw "Val: ~x0.~%" val)
                                    (vl-port-p val))
                            (prog2$ (cw "Name: ~x0.~%" (vl-port->name val))
                                    (equal (vl-port->name val) ',name))
                            (prog2$ (cw "Expr: ~x0.~%"
                                        (vl-pretty-expr (vl-port->expr val)))
                                    (equal (vl-pretty-expr (vl-port->expr val))
                                           ',expr))
                            (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                    (not tokens))
                            (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                    (equal warnings 'blah-warnings)))
                     ;; Otherwise, we expect it to fail.
                     (prog2$ (cw "Erp: ~x0.~%" erp)
                             erp))))))

   (test-parse-port :input "a"
                    :name "a"
                    :expr (id "a"))

   (test-parse-port :input "a[3:0]"
                    :name nil
                    :expr (:vl-partselect-colon nil (id "a") 3 0))

   (test-parse-port :input "a[3]"
                    :name nil
                    :expr (:vl-bitselect nil (id "a") 3))

   (test-parse-port :input "{a, b, c}"
                    :name nil
                    :expr (:vl-concat nil
                                      (id "a")
                                      (id "b")
                                      (id "c")))

   (test-parse-port :input ".foo(bar)"
                    :name "foo"
                    :expr (id "bar"))

   (test-parse-port :input ".foo(a[3:0])"
                    :name "foo"
                    :expr (:vl-partselect-colon nil (id "a") 3 0))

   (test-parse-port :input ".foo(a[3])"
                    :name "foo"
                    :expr (:vl-bitselect nil (id "a") 3))

   (test-parse-port :input ".foo({a, b, c})"
                    :name "foo"
                    :expr (:vl-concat nil
                                      (id "a")
                                      (id "b")
                                      (id "c")))

   (test-parse-port :input ".(a[3:0])"
                    :successp nil)

   (test-parse-port :input ".(a[3])"
                    :successp nil)

   (test-parse-port :input ".foo(a[3 +: 0])"
                    :successp nil)

   (test-parse-port :input ".foo(a[3 -: 0])"
                    :successp nil)




   (defun vl-pretty-maybe-exprlist (x)
     (if (atom x)
         nil
       (cons (if (car x)
                 (vl-pretty-expr (car x))
               nil)
             (vl-pretty-maybe-exprlist (cdr x)))))





   (defmacro test-parse-portlist (&key input (successp 't) names exprs)
     `(with-output
        :off summary
        (assert! (mv-let (erp val tokens warnings)
                   (vl-parse-list-of-ports (make-test-tokens ,input) 'blah-warnings)
                   (if ,successp
                       (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                    (not erp))
                            (prog2$ (cw "Val: ~x0.~%" val)
                                    (vl-portlist-p val))
                            (prog2$ (cw "Names: ~x0.~%" (vl-portlist->names val))
                                    (equal (vl-portlist->names val) ',names))
                            (prog2$ (cw "Exprs: ~x0.~%"
                                        (vl-pretty-maybe-exprlist (vl-portlist->exprs val)))
                                    (equal (vl-pretty-maybe-exprlist (vl-portlist->exprs val))
                                           ',exprs))
                            (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                    (not tokens))
                            (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                    (equal warnings 'blah-warnings)))
                     ;; Otherwise, we expect it to fail.
                     (prog2$ (cw "Erp: ~x0.~%" erp)
                             erp))))))

   (test-parse-portlist :input "()"
                        :names nil
                        :exprs nil)

   (test-parse-portlist :input "(a)"
                        :names ("a")
                        :exprs ((id "a")))

   (test-parse-portlist :input "(a,b)"
                        :names ("a"      "b")
                        :exprs ((id "a") (id "b")))

   (test-parse-portlist :input "(a,,b)"
                        :names ("a"      nil "b")
                        :exprs ((id "a") nil (id "b")))

   (test-parse-portlist :input "(,)"
                        :names (nil nil)
                        :exprs (nil nil))

   (test-parse-portlist :input "(,,,,,)"
                        :names (nil nil nil nil nil nil)
                        :exprs (nil nil nil nil nil nil))

   (test-parse-portlist :input "(a,,,b)"
                        :names ("a" nil nil "b")
                        :exprs ((id "a") nil nil (id "b")))


   (test-parse-portlist :input "(,a)"
                        :names (nil "a")
                        :exprs (nil (id "a")))

   (test-parse-portlist :input "(a,)"
                        :names ("a" nil)
                        :exprs ((id "a") nil))


   (test-parse-portlist :input "(.a(), b[3:0])"
                        :names ("a" nil)
                        :exprs (nil (:vl-partselect-colon nil (id "b") 3 0)))

   ))


