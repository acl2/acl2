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
(include-book "paramdecls")
(include-book "imports")
(local (include-book "../../util/arithmetic"))

(defxdoc parse-blockitems
  :parents (parser)
  :short "Functions for parsing Verilog and SystemVerilog block items."

  :long "<p>The Verilog-2005 grammar for regs and variables is, after filtering
out some duplication and indirection:</p>

@({
    integer_declaration  ::= 'integer'  list_of_variable_identifiers ';'
    real_declaration     ::= 'real'     list_of_variable_identifiers ';'
    time_declaration     ::= 'time'     list_of_variable_identifiers ';'
    realtime_declaration ::= 'realtime' list_of_variable_identifiers ';'
    reg_declaration      ::= 'reg' [ 'signed' ] [ range ] list_of_variable_identifiers ';'

    list_of_variable_identifiers ::= variable_type { ',' variable_type }

    variable_type ::= identifier { range }
                    | identifier '=' expression
})

<p>For SystemVerilog-2012 this is quite a bit more complex.  Quick rundown:</p>

<ul>
<li>additional 'const', 'var', and lifetime specifiers</li>
<li>variables can be of many new built-in or user-defined types</li>
<li>initializers can have \"new\", etc., instead of just being expressions</li>
<li>ranges for each variable_type can now be lists of variable_dimensions</li>
<li>package import statements are also considered data declarations, for whatever reason.</li>
</ul>

<p>The new grammar looks like this:</p>

@({
    data_declaration ::=
        ['const'] ['var'] [lifetime] data_type_or_implicit list_of_variable_decl_assignments ';'
      | ...

    data_type_or_implicit ::= data_type
                            | implicit_data_type

    implicit_data_type ::= [ signing ] { packed_dimension }

    list_of_variable_decl_assignments ::= variable_decl_assignment { ',' variable_decl_assignment }

    variable_decl_assignment ::=
         identifier { variable_dimension } [ '=' expression ]
       | identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
       | identifier [ '=' class_new ]

    dynamic_array_new ::= new [ expression ] [ ( expression ) ]

    class_new ::= [ class_scope ] new [ ( list_of_arguments ) ]
                | new expression

    variable_dimension ::= unsized_dimension
                         | unpacked_dimension
                         | associative_dimension
                         | queue_dimension

    unsized_dimension     ::= '[' ']'
    packed_dimension      ::= '[' constant_range ']' | unsized_dimension
    associative_dimension ::= '[' data_type ']' | '[' '*' ']'
    queue_dimension       ::= '[' '$' [ ':' expression ] ']'

    list_of_arguments ::= [expression] { ',' [expression] } { ',' '.' identifier '(' [expression] ')' }
                        | '.' identifier '(' [expression] ')' { ',' '.' identifier '(' [expression] ')' }
})")

(local (xdoc::set-default-parents parse-blockitems))
(local (in-theory (disable (tau-system))))

; -------------------------------------------------------------------------
;
;       Verilog-2005 Style Variables
;
; -------------------------------------------------------------------------

(define vl-build-vardecls (&key (temps    vl-vardeclassignlist-p)
                                (constp   booleanp)
                                (varp     booleanp)
                                (lifetime vl-lifetime-p)
                                (type     vl-datatype-p)
                                (atts     vl-atts-p)
                                (loc      vl-location-p))
  :returns (vardecls vl-vardecllist-p)
  (b* (((when (atom temps))
        nil)
       ((vl-vardeclassign temp1) (car temps))
       (decl1 (make-vl-vardecl :name     temp1.id
                               :initval  temp1.expr
                               :constp   constp
                               :varp     varp
                               :lifetime lifetime
                               :type     (vl-datatype-update-udims temp1.dims type)
                               :atts     atts
                               :loc      loc)))
    (cons decl1
          (vl-build-vardecls :temps    (cdr temps)
                             :constp   constp
                             :varp     varp
                             :lifetime lifetime
                             :type     type
                             :atts     atts
                             :loc      loc))))

;; (local (defthm vl-packeddimensionlist-p-when-vl-rangelist-p
;;          (implies (vl-rangelist-p x)
;;                   (vl-packeddimensionlist-p x))
;;          :hints(("Goal" :induct (len x)))))

(defprojection vl-ranges->packeddimensions ((x vl-rangelist-p))
  :returns (dims vl-packeddimensionlist-p)
  (vl-range->packeddimension x))


(defparser vl-parse-variable-type ()
  ;; Verilog-2005 Only.
  ;;
  ;; variable_type ::= identifier { range }
  ;;                 | identifier '=' expression
  :result (vl-vardeclassign-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (id := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-equalsign)
          (:= (vl-match))
          (expr := (vl-parse-expression))
          (return (make-vl-vardeclassign :id (vl-idtoken->name id)
                                         :dims nil
                                         :expr expr)))
        (arrdims := (vl-parse-0+-ranges))
        (return (make-vl-vardeclassign :id (vl-idtoken->name id)
                                       :dims (vl-ranges->packeddimensions arrdims)
                                       :expr nil))))

(defparser vl-parse-list-of-variable-identifiers ()
  ;; Verilog-2005 Only.
  ;;
  ;; list_of_variable_identifiers ::= variable_type { ',' variable_type }
  :result (vl-vardeclassignlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (first := (vl-parse-variable-type))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-variable-identifiers)))
        (return (cons first rest))))


(defparser vl-parse-integer-declaration (atts)
  ;; Verilog-2005 Only.
  ;;
  ;;    integer_declaration  ::= 'integer'  list_of_variable_identifiers ';'
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-token :vl-kwd-integer))
        (temps := (vl-parse-list-of-variable-identifiers))
        (:= (vl-match-token :vl-semi))
        (return (vl-build-vardecls :temps    temps
                                   :constp   nil
                                   :varp     nil
                                   :lifetime nil
                                   :type     *vl-plain-old-integer-type*
                                   :atts     atts
                                   :loc      (vl-token->loc kwd)))))

(defparser vl-parse-real-declaration (atts)
  ;; Verilog-2005 Only.
  ;;
  ;;    real_declaration     ::= 'real'     list_of_variable_identifiers ';'
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-token :vl-kwd-real))
        (temps := (vl-parse-list-of-variable-identifiers))
        (:= (vl-match-token :vl-semi))
        (return (vl-build-vardecls :temps    temps
                                   :constp   nil
                                   :varp     nil
                                   :lifetime nil
                                   :type     *vl-plain-old-real-type*
                                   :atts     atts
                                   :loc      (vl-token->loc kwd)))))


(defparser vl-parse-time-declaration (atts)
  ;; Verilog-2005 Only.
  ;;
  ;;   time_declaration     ::= 'time'     list_of_variable_identifiers ';'
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd    := (vl-match-token :vl-kwd-time))
        (temps  := (vl-parse-list-of-variable-identifiers))
        (:= (vl-match-token :vl-semi))
        (return (vl-build-vardecls :temps    temps
                                   :constp   nil
                                   :varp     nil
                                   :lifetime nil
                                   :type     *vl-plain-old-time-type*
                                   :atts     atts
                                   :loc      (vl-token->loc kwd)))))

(defparser vl-parse-realtime-declaration (atts)
  ;; Verilog-2005 Only.
  ;;
  ;;    realtime_declaration ::= 'realtime' list_of_variable_identifiers ';'
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd   := (vl-match-token :vl-kwd-realtime))
        (temps := (vl-parse-list-of-variable-identifiers))
        (:= (vl-match-token :vl-semi))
        (return (vl-build-vardecls :temps    temps
                                   :constp   nil
                                   :varp     nil
                                   :lifetime nil
                                   :type     *vl-plain-old-realtime-type*
                                   :atts     atts
                                   :loc      (vl-token->loc kwd)))))

(defparser vl-parse-reg-declaration (atts)
  ;; Verilog-2005 Only.
  ;;
  ;;    reg_declaration      ::= 'reg' [ 'signed' ] [ range ] list_of_variable_identifiers ';'
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-token :vl-kwd-reg))
        (when (vl-is-token? :vl-kwd-signed)
          (:= (vl-match))
          (signedp := (mv nil t tokstream)))
        (when (vl-is-token? :vl-lbrack)
          (range := (vl-parse-range)))
        (temps := (vl-parse-list-of-variable-identifiers))
        (:= (vl-match-token :vl-semi))
        (return (vl-build-vardecls :temps temps
                                   :constp nil
                                   :varp nil
                                   :lifetime nil
                                   :type (hons-copy
                                          (make-vl-coretype :name :vl-reg
                                                            :signedp signedp
                                                            :pdims (if range
                                                                       (list (vl-range->packeddimension range))
                                                                     nil)))
                                   :atts atts
                                   :loc (vl-token->loc kwd)))))

(defparser vl-parse-list-of-event-identifiers (atts)
  ;; Verilog-2005 Only.
  ;;
  ;; list_of_event_identifiers ::=
  ;;    identifier {range} { ',' identifier {range} }
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (id := (vl-match-token :vl-idtoken))
        (arrdims := (vl-parse-0+-ranges))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-list-of-event-identifiers atts)))
        (return (cons (make-vl-vardecl :type (make-vl-coretype :name :vl-event
                                                               :udims (vl-ranges->packeddimensions arrdims))
                                       :name (vl-idtoken->name id)
                                       :loc (vl-token->loc id)
                                       :atts atts)
                      rest))))

(defparser vl-parse-event-declaration (atts)
  ;; Verilog-2005 Only.
  ;;
  ;; event_declaration ::=
  ;;    'event' list_of_event_identifiers ';'
  :guard (vl-atts-p atts)
  :result (vl-vardecllist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-event))
       (ret := (vl-parse-list-of-event-identifiers atts))
       (:= (vl-match-token :vl-semi))
       (return ret)))



; -------------------------------------------------------------------------
;
;       Verilog-2012 Style Variables
;
; -------------------------------------------------------------------------
;
;    data_declaration ::=
;        ['const'] ['var'] [lifetime] data_type_or_implicit list_of_variable_decl_assignments ';'
;      | ...
;
;    data_type_or_implicit ::= data_type
;                            | implicit_data_type
;
;    implicit_data_type ::= [ signing ] { packed_dimension }

; There are a lot of ways for a data_declaration to start, so we'll use
; backtracking and just try to parse one.

(defparser vl-maybe-parse-lifetime ()
  :result (vl-lifetime-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
        (when (vl-is-token? :vl-kwd-static)
          (:= (vl-match))
          (return :vl-static))
        (when (vl-is-token? :vl-kwd-automatic)
          (:= (vl-match))
          (return :vl-automatic))
        (return nil)))


(encapsulate nil ;; vl-parse-main-data-declaration
  (local (in-theory (disable not iff
                             acl2::lower-bound-of-len-when-sublistp
                             acl2::len-when-prefixp
                             acl2::len-when-atom)))

  (defparser vl-parse-main-data-declaration (atts)
    ;; SystemVerilog-2012 Only.
    ;;
    ;;    data_declaration ::=
    ;;       ['const'] ['var'] [lifetime] data_type_or_implicit list_of_variable_decl_assignments ';'
    ;;     | ...
    ;;
    :guard (vl-atts-p atts)
    :result (vl-vardecllist-p val)
    :guard-debug t
    :resultp-of-nil t
    :true-listp t
    :fails gracefully
    :count strong
    (seq tokstream
         (loc := (vl-current-loc))
         (when (vl-is-token? :vl-kwd-const)
           (const := (vl-match)))
         (when (vl-is-token? :vl-kwd-var)
           (var := (vl-match)))
         (lifetime := (vl-maybe-parse-lifetime))
         ;; In the implicit case (which is only legal when the 'var' keyword is provided), it
         ;; seems like we probably need to just use backtracking.  After all, we have:
         ;;    implicit_data_type ::= [ signing ] { packed_dimension }
         ;; so the whole thing can be null, and if it is null, then we're left with the task
         ;; of distinguishing between a data_type, which could just be an identifier, versus
         ;; a variable_decl_assignment, which could also just be an identifier.  So we're
         ;; really not going to know which one we're dealing with until we read the whole
         ;; data type and then see if there are any variables that come afterward.
         (return-raw
          (b* ((backup (vl-tokstream-save))
               ((mv explicit-err explicit-val tokstream)
                (seq tokstream
                     ;; Try to match the explicit data type case.
                     (datatype := (vl-parse-datatype))
                     (assigns := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
                     (:= (vl-match-token :vl-semi))
                     (return
                      (vl-build-vardecls :temps    assigns
                                         :constp   (if const t nil)
                                         :varp     (if var t nil)
                                         :lifetime lifetime
                                         :type     datatype
                                         :atts     atts
                                         :loc      loc))))
               ((unless explicit-err)
                ;; Successfully matched explicit data type case, return answer
                (mv explicit-err explicit-val tokstream))

               ((unless var)
                ;; Not allowed to have implicit data type because didn't say 'var'.
                ;; Just return the failure from the explicit case.
                (mv explicit-err explicit-val tokstream))

               (tokstream (vl-tokstream-restore backup))

               ;; Try to handle the implicit case.
               ((mv implicit-err implicit-val tokstream)
                (seq tokstream
                     ;; Try to match the implicit data type case.
                     ;;    implicit_data_type ::= [ signing ] { packed_dimension }
                     (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
                       (signing := (vl-match)))
                     (when (vl-is-token? :vl-lbrack)
                       ;; BOZO for now just try to match packed dimensions
                       (dims := (vl-parse-0+-packed-dimensions)))
                     (assigns := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
                     (:= (vl-match-token :vl-semi))
                     (return
                      (vl-build-vardecls :temps    assigns
                                         :constp   (if const t nil)
                                         :varp     (if var t nil)
                                         :lifetime lifetime
                                         ;; Per SystemVerilog-2012 Section 6.8,
                                         ;; if a data type is not specified or
                                         ;; if only a range and/or signing is
                                         ;; specified, then the data type is
                                         ;; implicitly declared as 'logic'.
                                         :type (make-vl-coretype
                                                :name :vl-logic
                                                :signedp (and signing
                                                              (eq (vl-token->type signing) :vl-kwd-signed))
                                                :pdims dims)
                                         :atts atts
                                         :loc loc))))
               ((unless implicit-err)
                (mv implicit-err implicit-val tokstream))

               (tokstream (vl-tokstream-restore backup)))

            ;; Blah, tricky case.  We have errors for both the explicit and
            ;; implicit attempts.  It's not clear that one error is better than
            ;; the other.  In module parsing we run into a similar thing and try
            ;; to take "whichever got farther."  I think, here, it's probably
            ;; not so bad to just go with the explicit error.
            (mv explicit-err explicit-val tokstream))))))

;; BOZO eventually support other allowed data declarations: type declarations,
;; package import declarations, and net type declarations.  But to do this
;; we'll probably first want to extend our notion of vl-blockitem-p to allow
;; imports and type declarations.


; -------------------------------------------------------------------------
;
;                            Block Items
;
; -------------------------------------------------------------------------

; Verilog-2005:
;
; block_item_declaration ::=
;    {attribute_instance} 'reg' ['signed'] [range] list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'integer' list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'time' list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'real' list_of_block_variable_identifiers ';'
;  | {attribute_instance} 'realtime' list_of_block_variable_identifiers ';'
;  | {attribute_instance} event_declaration
;  | {attribute_instance} local_parameter_declaration ';'
;  | {attribute_instance} parameter_declaration ';'
;
; list_of_block_variable_identifiers ::=
;    block_variable_type { ',' block_variable_type }
;
; block_variable_type ::= identifier { dimension }
;
; Of particular note is that the rules for reg, integer, time, real, and
; realtime above are different than reg_declaration, integer_declaration, etc.,
; using list_of_block_variable_identifiers versus list_of_variable_identifiers.
; Comparing these, we see that the only difference is that these declarations
; are not allowed to have initial values assigned to them.  That is, "reg foo =
; 1" is okay as a module item, but not as a block item.
;
; With this in mind, our approach is to reuse our parsers above and simply walk
; through to ensure that none of the variables have been given initial values.

(defund vl-find-vardecl-with-initval (x)
  ; Verilog-2005 Only.
  (declare (xargs :guard (vl-vardecllist-p x)))
  (if (consp x)
      (if (vl-vardecl->initval (car x))
          (car x)
        (vl-find-vardecl-with-initval (cdr x)))
    nil))

(defparser vl-2005-parse-block-item-declaration-noatts (atts)
  ; Verilog-2005 Only.
  :guard (vl-atts-p atts)
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (type := (mv nil
                     (let ((tokens (vl-tokstream->tokens)))
                       (and (consp tokens)
                            (vl-token->type (car tokens))))
                     tokstream))
        (elements := (case type
                       (:vl-kwd-reg      (vl-parse-reg-declaration atts))
                       (:vl-kwd-integer  (vl-parse-integer-declaration atts))
                       (:vl-kwd-time     (vl-parse-time-declaration atts))
                       (:vl-kwd-real     (vl-parse-real-declaration atts))
                       (:vl-kwd-realtime (vl-parse-realtime-declaration atts))
                       (:vl-kwd-event    (vl-parse-event-declaration atts))
                       ((:vl-kwd-localparam :vl-kwd-parameter)
                        ;; Bug found on 2011-08-26 here.  We forgot to eat the
                        ;; semicolon, before.  This fix is ugly, since the
                        ;; other cases above do their own semicolon-handling,
                        ;; but we don't want the param parser to eat the semi
                        ;; because, e.g., a module_parameter_port_list has
                        ;; parameter declarations separated by commas instead.
                        (seq tokstream
                              (elems := (vl-parse-param-or-localparam-declaration
                                         atts
                                         '(:vl-kwd-localparam
                                           :vl-kwd-parameter)))
                              (:= (vl-match-token :vl-semi))
                              (return elems)))
                       (t
                        (vl-parse-error "Invalid block item."))))
        (return-raw
         (let ((search (case type
                         ((:vl-kwd-reg :vl-kwd-integer :vl-kwd-time
                           :vl-kwd-real :vl-kwd-realtime)
                          (vl-find-vardecl-with-initval elements))
                         (t
                          nil))))
           (if search
               (vl-parse-error "Block item declarations are not allowed to have initial values.")
             (mv nil elements tokstream))))))

; SystemVerilog-2012 version:
;
;   block_item_declaration ::=
;      {attribute_instance} data_declaration                          // no semicolon
;    | {attribute_instance} local_parameter_declaration ';'
;    | {attribute_instance} parameter_declaration       ';'
;    | {attribute_instance} overload_declaration                      // no semicolon
;    | {attribute_instance} let_declaration                           // no semicolon
;
; The data_declaration subsumes the reg, integer, time, real, realtime, and
; event cases in Verilog-2005.
;
; We don't yet support overload or let declarations, but we have:
;
;   overload_declaration ::= 'bind' ...
;   let_declaration ::= 'let' ...
;
; So we can easily identify when these things occur. Moreover we know that a
; parameter or local_parameter declaration always starts with 'parameter' or
; 'localparam', so we can at least gracefully fail if we encounter anything we
; don't support.

(defparser vl-2012-parse-block-item-declaration-noatts (atts)
  :guard (vl-atts-p atts)
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-token? :vl-kwd-bind)
          (return-raw (vl-parse-error "overload declarations (\"bind ...\") are not yet supported")))
        (when (vl-is-token? :vl-kwd-let)
          (return-raw (vl-parse-error "let declarations are not yet supported")))
        (when (vl-is-some-token? '(:vl-kwd-localparam :vl-kwd-parameter))
          ;; Do not eat the token.
          (elems := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-localparam :vl-kwd-parameter)))
          ;; Unusual case: have to explicitly eat a semicolon here.
          (:= (vl-match-token :vl-semi))
          (return elems))
        (when (vl-is-token? :vl-kwd-import)
          (return-raw (vl-parse-package-import-declaration atts)))
        ;; Otherwise, we are presumably in the data_declaration case.  Eventually we will
        ;; need to extend this to handle typedefs, etc., but for now we'll at least
        ;; get the main data declarations.
        (elems := (vl-parse-main-data-declaration atts))
        (return elems)))

(defparser vl-parse-block-item-declaration-noatts (atts)
  :guard (vl-atts-p atts)
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (if (eq (vl-loadconfig->edition config) :verilog-2005)
      (vl-2005-parse-block-item-declaration-noatts atts)
    (vl-2012-parse-block-item-declaration-noatts atts)))

(defparser vl-parse-block-item-declaration ()
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (decls := (vl-parse-block-item-declaration-noatts atts))
        (return decls)))

(defparser vl-parse-0+-block-item-declarations ()
  ;; Tries to eat as many block items as it can find.
  ;; We use backtracking to know when to stop, because these declarations can be
  ;; followed by arbitrary statements, hence it's not clear whether (* ... *) is
  ;; the start of a new block item declaration or a statement.
  :result (vl-blockitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails never
  :count strong-on-value
  (b* ((backup (vl-tokstream-save))
       ((mv erp first tokstream) (vl-parse-block-item-declaration))
       ((when erp)
        (b* ((tokstream (vl-tokstream-restore backup)))
          (mv nil nil tokstream))))
    (seq tokstream
         (rest := (vl-parse-0+-block-item-declarations))
         (return (append first rest)))))

