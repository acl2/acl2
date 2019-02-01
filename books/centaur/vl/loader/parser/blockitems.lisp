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
(include-book "classes") ;; just for vl-maybe-parse-lifetime
(include-book "../descriptions")
(local (include-book "../../util/arithmetic"))
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not generalize fertilize))


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
<li>package import statements and typedefs are also considered data declarations, for whatever reason.</li>
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

    dynamic_array_new ::= 'new' '[' expression ']' [ '(' expression ')' ]

    class_new ::= [ class_scope ] 'new' [ '(' list_of_arguments ')' ]
                | 'new' expression


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
                               :initval  temp1.rhs
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

(defprojection vl-ranges->dimensions ((x vl-rangelist-p))
  :returns (dims vl-dimensionlist-p)
  (vl-range->dimension x))


(defparser vl-parse-variable-type ()
  :short "Match @('variable_type') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              variable_type ::= identifier { range }
                              | identifier '=' expression
         })"
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
                                         :rhs (make-vl-rhsexpr :guts expr))))
        (arrdims := (vl-parse-0+-ranges))
        (return (make-vl-vardeclassign :id (vl-idtoken->name id)
                                       :dims (vl-ranges->dimensions arrdims)
                                       :rhs nil))))

(defparser vl-parse-list-of-variable-identifiers ()
  :short "Match @('list_of_variable_identifiers') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              list_of_variable_identifiers ::= variable_type { ',' variable_type }
         })"
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
  :short "Match @('integer_declaration') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              integer_declaration ::= 'integer' list_of_variable_identifiers ';'
         })"
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
  :short "Match @('real_declaration') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              real_declaration ::= 'real' list_of_variable_identifiers ';'
         })"
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
  :short "Match @('time_declaration') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              time_declaration ::= 'time' list_of_variable_identifiers ';'
         })"
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
  :short "Match @('realtime_declaration') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
             realtime_declaration ::= 'realtime' list_of_variable_identifiers ';'
         })"
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
  :short "Match @('reg_declaration') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              reg_declaration ::= 'reg' [ 'signed' ] [ range ] list_of_variable_identifiers ';'
         })"
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
                                                                       (list (vl-range->dimension range))
                                                                     nil)))
                                   :atts atts
                                   :loc (vl-token->loc kwd)))))

(defparser vl-parse-list-of-event-identifiers (atts)
  :short "Match @('list_of_event_identifiers') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
             list_of_event_identifiers ::= identifier {range} { ',' identifier {range} }
         })"
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
        (return
         (b* ((udims-from-arrdims (vl-ranges->dimensions arrdims)))
           (cons (make-vl-vardecl :type (make-vl-coretype :name :vl-event
                                                          :udims udims-from-arrdims)
                                  :name (vl-idtoken->name id)
                                  :loc (vl-token->loc id)
                                  :atts atts)
                 rest)))))

(defparser vl-parse-event-declaration (atts)
  :short "Match @('event_declaration') for Verilog-2005."
  :long "<p>Grammar:</p>
         @({
              event_declaration ::= 'event' list_of_event_identifiers ';'
         })"
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
;       SystemVerilog-2012 Style Variables
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


(encapsulate nil ;; vl-parse-main-data-declaration
  (local (in-theory (disable not iff
                             acl2::lower-bound-of-len-when-sublistp
                             acl2::len-when-prefixp
                             acl2::len-when-atom)))

  (defparser vl-parse-main-data-declaration (atts)
    :short "Parse the main variable declaration part of a @('data_declaration') for SystemVerilog-2012."
    :long "<p>Grammar:</p>
           @({
               data_declaration ::=
                   ['const'] ['var'] [lifetime] data_type_or_implicit list_of_variable_decl_assignments ';'
                 | ...
           })"
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



; -------------------------------------------------------------------------
;
;       SystemVerilog-2012 Typedefs
;
; -------------------------------------------------------------------------

;; type_declaration ::=
;;    'typedef' data_type type_identifier { variable_dimension } ';'
;;  | 'typedef' interface_instance_identifier constant_bit_select '.' type_identifier type_identifier ';'
;;  | 'typedef' [ 'enum' | 'struct' | 'union' | 'class' | 'interface class' ] type_identifier ';'

(defparser vl-parse-fwd-typedef (atts)
  :short "Match a forward @('type_declaration') for SystemVeriog-2012."
  :long "<p>The SystemVerilog-2012 grammar groups ``forward'' type declarations
         in with other type declarations.  Here we're just parsing:</p>

         @({
             type_declaration ::=
               'typedef' [ 'enum' | 'struct' | 'union' | 'class' | 'interface class' ] type_identifier ';'
         })

         <p>We don't match the other forms of @('type_declaration') here.</p>"
  :guard (and (vl-atts-p atts)
              (vl-is-token? :vl-kwd-typedef))
  :result (vl-fwdtypedef-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (typedef := (vl-match))  ;; guard ensures it starts with 'typedef'

       (when (vl-is-token? :vl-kwd-interface)
         (:= (vl-match))
         (:= (vl-match-token :vl-kwd-class))
         (name := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-semi))
         (return-raw
          (b* ((val (make-vl-fwdtypedef :kind :vl-interfaceclass
                                        :name (vl-idtoken->name name)
                                        :loc (vl-token->loc typedef)
                                        :atts atts)))
            (mv nil val tokstream))))

       (when (vl-is-some-token? '(:vl-kwd-enum :vl-kwd-struct :vl-kwd-union :vl-kwd-class))
         (type := (vl-match))
         (name := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-semi))
         (return-raw
          (b* ((val   (make-vl-fwdtypedef :kind (case (vl-token->type type)
                                                  (:vl-kwd-enum   :vl-enum)
                                                  (:vl-kwd-struct :vl-struct)
                                                  (:vl-kwd-union  :vl-union)
                                                  (:vl-kwd-class  :vl-class))
                                          :name (vl-idtoken->name name)
                                          :loc (vl-token->loc typedef)
                                          :atts atts)))
            (mv nil val tokstream))))

       (return-raw
        (vl-parse-error "Not a valid forward typedef."))))

(defparser vl-parse-type-declaration (atts)
  :short "Match any kind of @('type_declaration') for SystemVerilog-2012."
  :long "<p>The grammar mixes both forward and regular type declarations:</p>
         @({

              type_declaration ::=
                 'typedef' data_type type_identifier { variable_dimension } ';'
               | 'typedef' interface_instance_identifier constant_bit_select '.' type_identifier type_identifier ';'
               | 'typedef' [ 'enum' | 'struct' | 'union' | 'class' | 'interface class' ] type_identifier ';'
         })

         <p>We match either kind of type declaration and return it as a @(see
         vl-description-p).</p>"
  :guard (and (vl-atts-p atts)
              (vl-is-token? :vl-kwd-typedef))
  :result (vl-description-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; We use backtracking to figure out if it's a forward or regular type
  ;; declaration.  We try forward declarations first because they're less
  ;; likely to have problems, and we'd probably rather see errors about
  ;; full type declarations.
  (b* ((backup (vl-tokstream-save))
       ((mv erp fwd tokstream)
        (vl-parse-fwd-typedef atts))
       ((unless erp)
        ;; Got a valid fwd typedef, so return it.
        (mv erp fwd tokstream))

       (tokstream (vl-tokstream-restore backup)))

    ;; Else, not a fwd typedef, so try to match a full one.
    (seq tokstream
          (typedef := (vl-match))  ;; guard ensures it starts with 'typedef'

          ;; BOZO the following probably isn't right for the 2nd production.
          (datatype := (vl-parse-datatype))
          (id := (vl-match-token :vl-idtoken))
          (udims := (vl-parse-0+-variable-dimensions))
          (semi := (vl-match-token :vl-semi))
          (return-raw
           (b* ((val (make-vl-typedef :name (vl-idtoken->name id)
                                      :type (vl-datatype-update-udims udims datatype)
                                      :minloc (vl-token->loc typedef)
                                      :maxloc (vl-token->loc semi)
                                      :atts atts)))
             (mv nil val tokstream)))))
  ///
  (local (defthm tag-of-vl-parse-fwd-typedef
           (b* (((mv err val ?tokstream) (vl-parse-fwd-typedef atts)))
             (implies (not err)
                      (equal (tag val) :vl-fwdtypedef)))
           :hints(("Goal" :in-theory (enable vl-parse-fwd-typedef)))))

  (defthm vl-typedef-p-of-vl-parse-type-declaration
    (b* (((mv err val ?tokstream) (vl-parse-type-declaration atts)))
      (implies (not err)
               (equal (vl-typedef-p val)
                      (eq (tag val) :vl-typedef))))
    :hints(("Goal" :in-theory (enable tag-reasoning)))))




; -------------------------------------------------------------------------
;
;                            Block Items
;
; -------------------------------------------------------------------------

(defund vl-find-vardecl-with-initval (x)
  (declare (xargs :guard (vl-vardecllist-p x)))
  (if (consp x)
      (if (vl-vardecl->initval (car x))
          (car x)
        (vl-find-vardecl-with-initval (cdr x)))
    nil))

(defparser vl-2005-parse-block-item-declaration-noatts (atts)
  :short "Match a whole @('block_item_declaration'), except for any attributes, for Verilog-2005."
  :long "<p>Verilog-2005 Grammar:</p>
         @({
              block_item_declaration ::=
                 {attribute_instance} 'reg' ['signed'] [range] list_of_block_variable_identifiers ';'
               | {attribute_instance} 'integer' list_of_block_variable_identifiers ';'
               | {attribute_instance} 'time' list_of_block_variable_identifiers ';'
               | {attribute_instance} 'real' list_of_block_variable_identifiers ';'
               | {attribute_instance} 'realtime' list_of_block_variable_identifiers ';'
               | {attribute_instance} event_declaration
               | {attribute_instance} local_parameter_declaration ';'
               | {attribute_instance} parameter_declaration ';'

              list_of_block_variable_identifiers ::=
                 block_variable_type { ',' block_variable_type }

              block_variable_type ::= identifier { dimension }
         })

         <p>Of particular note is that the rules for @('reg') through
         @('realtime') above differ from the module-level @('reg_declaration'),
         @('integer_declaration'), etc., in that they use
         @('list_of_block_variable_identifiers') instead of
         @('list_of_variable_identifiers').  Comparing these, we see that the
         only difference is that block item declarations are not allowed to
         have initial values assigned to them.  That is, @('reg foo = 1') is
         okay as a module item, but not as a block item.</p>

         <p>With this in mind, our approach is to reuse our module-level
         parsers, but then walk through to ensure that none of the variables
         have been given initial values.</p>"
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

(defparser vl-2012-parse-block-item-declaration-noatts (atts)
  :short "Match a whole @('block_item_declaration'), except for any attributes,
          for SystemVerilog-2012."
  :long "<p>SystemVerilog-2012 Grammar:</p>

         @({
              block_item_declaration ::=
                  {attribute_instance} data_declaration                          // no semicolon
                | {attribute_instance} local_parameter_declaration ';'
                | {attribute_instance} parameter_declaration       ';'
                | {attribute_instance} overload_declaration                      // no semicolon
                | {attribute_instance} let_declaration                           // no semicolon
         })

         <p>The data_declaration subsumes the reg, integer, time, real,
         realtime, and event cases in Verilog-2005.</p>

         <p>We don't yet support overload or let declarations, but we have:</p>

         @({
              overload_declaration ::= 'bind' ...
              let_declaration ::= 'let' ...
         })

         <p>So we can easily identify when these things occur. Moreover we know
         that a parameter or local parameter declaration always starts with
         'parameter' or 'localparam', so we can at least gracefully fail if we
         encounter anything we don't support.</p>"
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
          ;; Kind of hacky -- to make sure the guard is satisfied we need to
          ;; look ahead.  This excessive guard is meant to avoid any possible
          ;; confusion with DPI imports, but we don't have to worry about DPI
          ;; imports here.
          (return-raw (if (vl-plausible-start-of-package-import-p)
                          (vl-parse-package-import-declaration atts)
                        (vl-parse-error "Expected package name after import."))))

        ;; Otherwise we are in the data_declaration case.

        ;; BOZO it's a little ugly to explicitly look for typedefs here,
        ;; instead of writing a proper parse-data-declaration function.  But in
        ;; the special case of block items, I don't think we really want to
        ;; support forward typedefs?
        (when (vl-is-token? :vl-kwd-typedef)
          (ans := (vl-parse-type-declaration atts))
          (return-raw (if (eq (tag ans) :vl-typedef)
                          (mv nil (list ans) tokstream)
                        (vl-parse-error "Not implemented: forward typedefs as block items."))))

          ;; Otherwise, we are presumably in the data_declaration case.  Eventually we will
        ;; need to extend this to handle typedefs, etc., but for now we'll at least
        ;; get the main data declarations.
        (elems := (vl-parse-main-data-declaration atts))
        (return elems)))

(defparser vl-parse-block-item-declaration-noatts (atts)
  :short "Match a whole @('block_item_declaration'), except for any attributes."
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
  :short "Match a whole @('block_item_declaration'), including initial attributes."
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
  :short "Match as many @('block_item_declaration')s as we can find."
  :long "<p>We use backtracking to know when to stop, because these
         declarations can be followed by arbitrary statements, hence it's not
         clear whether something like <tt>(* ... *)</tt> attributes are for the
         start of a new block item declaration or for a statement.</p>"
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

