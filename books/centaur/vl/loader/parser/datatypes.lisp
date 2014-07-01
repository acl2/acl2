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
(include-book "ranges")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))


; BOZO eventually need variable_dimension stuff

;    variable_dimension ::= unsized_dimension
;                         | unpacked_dimension
;                         | associative_dimension
;                         | queue_dimension
;
;    unsized_dimension ::= '[' ']'
;
;    unpacked_dimension ::= '[' constant_range ']'
;                         | '[' constant_expression ']'
;
;    associative_dimension ::= '[' data_type ']'
;                            | '[' '*' ']'
;
;    queue_dimension ::= '[' '$' [ ':' constant_expression ] ']'




;; unsized_dimension ::= '[' ']'
;; packed_dimension ::= '[' constant_range ']' | unsized_dimension

(defparser vl-parse-packeddimension ()
  :result (vl-packeddimension-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-lbrack))
        (when (vl-is-token? :vl-rbrack)
          (:= (vl-match))
          (return :vl-unsized-dimension))
        (msb := (vl-parse-expression))
        (:= (vl-match-token :vl-colon))
        (lsb := (vl-parse-expression))
        (:= (vl-match-token :vl-rbrack))
        (return (make-vl-range :msb msb :lsb lsb))))

(defparser vl-parse-0+-packed-dimensions ()
  ;; Match { packed_dimension }
  :result (vl-packeddimensionlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (unless (vl-is-token? :vl-lbrack)
          (return nil))
        (first := (vl-parse-packeddimension))
        (rest  := (vl-parse-0+-packed-dimensions))
        (return (cons first rest))))


(defaggregate vl-coredatatype-info
  :parents (vl-parse-core-data-type)
  :tag nil
  :legiblep nil
  ((coretypename      vl-coretypename-p   "what to translate it into")
   (default-signedp   booleanp            "what's the default signedness?")
   (takes-signingp    booleanp            "does it have an optional [signing] part?")
   (takes-dimensionsp booleanp            "does it optionally take dimensions?")))

(defval *vl-core-data-type-table*
  :parents (vl-parse-core-data-type)
  ;; data_type ::=
  ;;    integer_vector_type [signing] { packed_dimension }
  ;;  | integer_atom_type [signing]
  ;;  | non_integer_type
  ;;  | 'string'
  ;;  | 'chandle'
  ;;  | 'event'
  (list ;; Note: for default signedness see Table 6-8, "integer data types", page 68.
    ;; special extra core types                                      default signed      [signing]?    dimensions?
    (cons :vl-kwd-string    (vl-coredatatype-info   :vl-string         nil                 nil           nil))
    (cons :vl-kwd-event     (vl-coredatatype-info   :vl-event          nil                 nil           nil))
    (cons :vl-kwd-chandle   (vl-coredatatype-info   :vl-chandle        nil                 nil           nil))
    ;; non-integer types                                             N/A
    (cons :vl-kwd-shortreal (vl-coredatatype-info   :vl-shortreal      nil                 nil           nil))
    (cons :vl-kwd-real      (vl-coredatatype-info   :vl-real           nil                 nil           nil))
    (cons :vl-kwd-realtime  (vl-coredatatype-info   :vl-realtime       nil                 nil           nil))
    ;; integer atom types
    (cons :vl-kwd-byte      (vl-coredatatype-info   :vl-byte           t                   t             nil))
    (cons :vl-kwd-shortint  (vl-coredatatype-info   :vl-shortint       t                   t             nil))
    (cons :vl-kwd-int       (vl-coredatatype-info   :vl-int            t                   t             nil))
    (cons :vl-kwd-longint   (vl-coredatatype-info   :vl-longint        t                   t             nil))
    (cons :vl-kwd-integer   (vl-coredatatype-info   :vl-integer        t                   t             nil))
    (cons :vl-kwd-time      (vl-coredatatype-info   :vl-time           nil                 t             nil))
    ;; integer vector types
    (cons :vl-kwd-bit       (vl-coredatatype-info   :vl-bit            nil                 t             t))
    (cons :vl-kwd-logic     (vl-coredatatype-info   :vl-logic          nil                 t             t))
    (cons :vl-kwd-reg       (vl-coredatatype-info   :vl-reg            nil                 t             t))))

(defval *vl-core-data-type-keywords*
  :parents (vl-parse-core-data-type)
  :showval t
  (alist-keys *vl-core-data-type-table*))

(defsection vl-parse-core-data-type
  ;; Parses the simple, non-recursive core data types
  :parents nil

  (local (in-theory (enable vl-is-some-token?)))

  (defparser vl-parse-core-data-type ()
    :guard (vl-is-some-token? *vl-core-data-type-keywords*)
    :result (vl-datatype-p val)
    :resultp-of-nil nil
    :fails gracefully
    :count strong
    (b* ((entry (cdr (assoc (vl-token->type (car tokens)) *vl-core-data-type-table*)))
         ((vl-coredatatype-info entry) entry))
      (seqw tokens warnings
            (:= (vl-match-any)) ;; guard ensures there's at least one token
            (when (and entry.takes-signingp
                       (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned)))
              (signing := (vl-match)))
            (when entry.takes-dimensionsp
              (dims := (vl-parse-0+-packed-dimensions)))
            (return
             (make-vl-coretype :name entry.coretypename
                               :signedp (if signing
                                            (if (eq (vl-token->type signing) :vl-kwd-signed)
                                                t
                                              nil)
                                          entry.default-signedp)
                               :dims dims))))))




;; enum_base_type ::=
;;     integer_atom_type [signing]
;;   | integer_vector_type [signing] [packed_dimension]
;;   | type_identifier [packed_dimension]

(defthm vl-enumbasekind-p-when-stringp
  (implies (stringp x)
           (vl-enumbasekind-p x))
  :hints(("Goal" :in-theory (enable vl-enumbasekind-p))))

(defparser vl-parse-enum-base-type ()
  :result (vl-enumbasetype-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings

        (when (vl-is-token? :vl-idtoken)
          ;; type_identifier [packed_dimension]
          (name := (vl-match))
          (when (vl-is-token? :vl-lbrack)
            (dim := (vl-parse-packeddimension)))
          (return (make-vl-enumbasetype :kind (vl-idtoken->name name)
                                        :dim dim)))

        (when (vl-is-some-token? '(:vl-kwd-bit :vl-kwd-logic :vl-kwd-reg))
          ;; integer vector types.
          ;;   integer_vector_type [signing] [packed_dimension]
          (type := (vl-match))
          (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
            (signing := (vl-match)))
          (when (vl-is-token? :vl-lbrack)
            (dim := (vl-parse-packeddimension)))
          (return
           ;; Subtle notes about signing.  These types are by default unsigned.
           ;; I'm unclear about how the type's signedness is supposed to
           ;; interact with this signedness keyword or what the default is
           ;; supposed to be if the user doesn't provide any signed/unsigned
           ;; keyword.  I guess it seems most sensible for them to default to
           ;; the signedness of the base type, but BOZO it would be good to
           ;; check this against commercial tools.
           (make-vl-enumbasetype :kind (case (vl-token->type type)
                                         (:vl-kwd-bit   :vl-bit)
                                         (:vl-kwd-logic :vl-logic)
                                         (:vl-kwd-reg   :vl-reg))
                                 :signedp (and signing
                                               (eq (vl-token->type signing) :vl-kwd-signed))
                                 :dim dim)))

        ;; else, integer atom types:
        (type := (vl-match-some-token '(:vl-kwd-byte :vl-kwd-shortint :vl-kwd-int
                                        :vl-kwd-longint :vl-kwd-integer :vl-kwd-time)))
        ;; integer_atom_type [signing]
        (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
          (signing := (vl-match)))

        ;; BOZO again the signing here is very unclear!  The integer types are
        ;; signed by default and time is unsigned by default.  Maybe that's what
        ;; we should use?
        (return (make-vl-enumbasetype :kind (case (vl-token->type type)
                                              (:vl-kwd-byte     :vl-byte)
                                              (:vl-kwd-shortint :vl-shortint)
                                              (:vl-kwd-int      :vl-int)
                                              (:vl-kwd-longint  :vl-longint)
                                              (:vl-kwd-integer  :vl-integer)
                                              (:vl-kwd-time     :vl-time))
                                      :signedp
                                      (cond (signing ;; Has explicit signing directive, respect it
                                             (eq (vl-token->type signing) :vl-kwd-signed))
                                            ((eq (vl-token->type type) :vl-kwd-time) ;; unsigned by default
                                             nil)
                                            (t ;; signed by default
                                             t))
                                      ;; No dimension here
                                      :dim nil))))



;; enum_name_declaration ::=
;;   enum_identifier [ '[' integral_number [ ':' integral_number ] ']' ]
;;                   [ '=' constant_expression ]

(defparser vl-parse-enum-name-declaration ()
  :result (vl-enumitem-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (name := (vl-match-token :vl-idtoken))

        (when (vl-is-token? :vl-lbrack)
          (:= (vl-match))

          (left := (vl-match-token :vl-inttoken))
          (when (or (not (vl-inttoken->value left))
                    (member #\' (vl-echarlist->chars (vl-inttoken->etext left))))
            ;; Horrible gross hack, as in vl-parse-delay-value
            (return-raw (vl-parse-error "Illegal enum index")))

          (when (vl-is-token? :vl-colon)
            (:= (vl-match))
            (right := (vl-match-token :vl-inttoken))
            (when (or (not (vl-inttoken->value right))
                      (member #\' (vl-echarlist->chars (vl-inttoken->etext right))))
              ;; Horrible gross hack, as in vl-parse-delay-value
              (return-raw (vl-parse-error "Illegal enum index"))))

          (:= (vl-match-token :vl-rbrack)))

        (when (vl-is-token? :vl-equalsign)
          (:= (vl-match))
          (value := (vl-parse-expression)))

        (return (make-vl-enumitem
                 :name (vl-idtoken->name name)
                 :range (cond ((not left)
                               nil)
                              ((not right)
                               (make-vl-range :msb (vl-make-index (vl-inttoken->value left))
                                              :lsb (vl-make-index (vl-inttoken->value left))))
                              (t
                               (make-vl-range :msb (vl-make-index (vl-inttoken->value left))
                                              :lsb (vl-make-index (vl-inttoken->value right)))))
                 :value value))))

(defparser vl-parse-1+-enum-name-declarations-separated-by-commas ()
  :result (vl-enumitemlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-enum-name-declaration))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-enum-name-declarations-separated-by-commas)))
        (return (cons first rest))))



;; variable_decl_assignment ::=
;;       variable_identifier { variable_dimension } [ '=' expression ]
;;     | dynamic_array_variable_identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
;;     | class_variable_identifier [ '=' class_new ]
;;
;;  --->
;; variable_decl_assignment ::=
;;     identifier { variable_dimension }                   [ '=' expression ]
;;   | identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
;;   | identifier                                          [ '=' class_new ]
;;
;; But for now we're just going to not deal with these dimensions!

(defaggregate vl-vardeclassign
  :parents (vl-parse-datatype vl-build-vardecls)
  :short "Temporary structure used when parsing variable declarations."
  :legiblep nil
  ((id   stringp :rule-classes :type-prescription)
   (dims vl-packeddimensionlist-p "BOZO not sufficiently general.")
   (expr vl-maybe-expr-p          "BOZO not sufficiently general."))

:long "<p>This captures something like a @('variable_type') from
Verilog-2005:</p>

@({
    variable_type ::= identifier { range }
                    | identifier '=' expression
})

<p>Or @('variable_decl_assignment') from SystemVerilog-2012, except that
<b>BOZO</b> we don't yet support @('new') sorts of stuff or certain kinds of
dimensions.</p>

@({
    variable_decl_assignment ::=
         identifier { variable_dimension } [ '=' expression ]
       | identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
       | identifier [ '=' class_new ]
})")

(deflist vl-vardeclassignlist-p (x)
  (vl-vardeclassign-p x)
  :elementp-of-nil nil)

(defparser vl-parse-variable-decl-assignment ()
  ;; SystemVerilog-2012 Only.
  :result (vl-vardeclassign-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (when (vl-is-token? :vl-lbrack)
          ;; BOZO this doesn't yet support all the possible variable_dimension things, but
          ;; we'll at least support arbitrary lists of packed dimensions.
          (dims := (vl-parse-0+-packed-dimensions)))

        (when (vl-is-token? :vl-equalsign)
          (:= (vl-match))
          (expr := (vl-parse-expression))
          (when (or (vl-is-token? :vl-kwd-new)
                    (and (vl-is-token? :vl-scope)
                         (vl-is-token? :vl-kwd-new :tokens (cdr tokens))))
            (return-raw (vl-parse-error "Implement support for 'new' in struct/union members!"))))

        (return (make-vl-vardeclassign
                 :id (vl-idtoken->name id)
                 :dims dims
                 :expr expr))))

(defparser vl-parse-1+-variable-decl-assignments-separated-by-commas ()
  ;; SystemVerilog-2012 Only.
  ;;
  ;;   list_of_variable_decl_assignments ::= variable_decl_assignment { ',' variable_decl_assignment }
  :result (vl-vardeclassignlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-variable-decl-assignment))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-variable-decl-assignments-separated-by-commas)))
        (return (cons first rest))))

(define vl-make-structmembers ((atts vl-atts-p)
                               (rand vl-randomqualifier-p)
                               (type vl-datatype-p)
                               (decls vl-vardeclassignlist-p))
  :returns (decls vl-structmemberlist-p :hyp :fguard)
  (if (atom decls)
      nil
    (cons (make-vl-structmember :atts atts
                                :rand rand
                                :type type
                                :name (vl-vardeclassign->id (car decls))
                                :dims (vl-vardeclassign->dims (car decls))
                                :rhs  (vl-vardeclassign->expr (car decls)))
          (vl-make-structmembers atts rand type (cdr decls)))))




(local (defthm narrow-down-to-union
         (equal (EQUAL (VL-TYPE-OF-MATCHED-TOKEN '(:VL-KWD-STRUCT :VL-KWD-UNION) TOKENS)
                       :VL-KWD-UNION)
                (vl-is-token? :vl-kwd-union))
         :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                           vl-is-token?)))))


(defparsers parse-datatype
  :parents (parser)
  :short "Parser for SystemVerilog-2012 data types."
  :flag-local nil
  :hints(("Goal"
          :do-not-induct t
          :do-not '(generalize fertilize)))

  (defparser vl-parse-datatype-or-void ()
    ;; data_type_or_void ::= data_type | 'void'
    ;; We represent 'void' as just another kind of vl-datatype-p
    :measure (two-nats-measure (len tokens) 1)
    (seqw tokens warnings
          (when (vl-is-token? :vl-kwd-void)
            (:= (vl-match-any))
            (return (make-vl-coretype :name :vl-void)))
          (type :s= (vl-parse-datatype))
          (return type)))

  (defparser vl-parse-datatype ()
    :measure (two-nats-measure (len tokens) 0)
    :verify-guards nil
    (seqw tokens warnings

          (when (vl-is-token? :vl-kwd-type)
            ;; data_type ::= ... | type_reference
            ;;
            ;; type_reference ::= 'type' '(' expression ')'
            ;;                  | 'type' data_type
            (return-raw (vl-parse-error "type references are not yet implemented.")))

          (when (vl-is-token? :vl-kwd-virtual)
            ;; data_type ::= ... | 'virtual' [ 'interface' ] ...
            (return-raw (vl-parse-error "virtual interfaces are not yet implemented.")))

          (when (vl-is-some-token? *vl-core-data-type-keywords*)
            (ret := (vl-parse-core-data-type))
            (return ret))

          (when (vl-is-some-token? '(:vl-kwd-struct :vl-kwd-union))
            ;; data_type ::= ... | struct_union [ 'packed' [signing] ] '{'
            ;;                       struct_union_member { struct_union_member }
            ;;                     '}' { packed_dimension }
            ;;
            ;; struct_union ::= 'struct' | 'union' [ 'tagged' ]
            (kind := (vl-match))
            (when (and (vl-is-token? :vl-kwd-tagged)
                       (eq (vl-token->type kind) :vl-kwd-union))
              (tagged := (vl-match)))
            (when (vl-is-token? :vl-kwd-packed)
              (packed := (vl-match))
              ;; signed is only allowed when packed is given
              (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
                (signed := (vl-match))))
            (:= (vl-match-token :vl-lcurly))
            (members := (vl-parse-structmembers))
            (:= (vl-match-token :vl-rcurly))
            (dims := (vl-parse-0+-packed-dimensions))
            (return
             (b* (;; structures are unpacked by default (SystemVerilog-2012 Section 7.2)
                  ;; unions are unpacked by default     (SystemVerilog-2012 Section 7.3)
                  (packedp (acl2::bool-fix packed))
                  ;; structures are unsigned by default (SystemVerilog-2012 Section 7.2.1)
                  ;;   "by default, structures are unpacked"
                  ;; packed unions are unsigned by default (SystemVerilog-2012 Section 7.3.1)
                  ;;   "signed or unsigned, the latter being the default"
                  (signedp (and signed (eq (vl-token->type signed) :vl-kwd-signed)))
                  ((when (eq (vl-token->type kind) :vl-kwd-struct))
                   (make-vl-struct :packedp packedp
                                   :signedp signedp
                                   :members members
                                   :dims dims)))
               ;; Else it's a union.
               (make-vl-union :packedp packedp
                              :signedp signedp
                              :taggedp (acl2::bool-fix tagged)
                              :members members
                              :dims dims))))

          (when (vl-is-token? :vl-kwd-enum)
            ;; data_type ::= ... | 'enum' [ enum_base_type ] '{'
            ;;                        enum_name_declaration { ',' enum_name_declaration }
            ;;                     '}' { packed_dimension }
            (:= (vl-match))
            (unless (vl-is-token? :vl-lcurly)
              (basetype := (vl-parse-enum-base-type)))
            (:= (vl-match-token :vl-lcurly))
            (items := (vl-parse-1+-enum-name-declarations-separated-by-commas))
            (:= (vl-match-token :vl-rcurly))
            (dims := (vl-parse-0+-packed-dimensions))
            (return (make-vl-enum
                     :basetype (or basetype
                                   ;; Per SystemVerilog-2012 Section 6.19, in the absence of a
                                   ;; data type declaration, the default type is "int".  Moreover
                                   (make-vl-enumbasetype
                                    :kind :vl-int
                                    ;; BOZO is this right?  Ints are signed by default, so maybe?
                                    :signedp t
                                    :dim nil))
                     :items items
                     :dims dims)))

          ;; At this point we've ruled out: basic types, structs, unions, enums, type references,
          ;; virtual interfaces.  What remains are:

          ;; data_type ::= ...
          ;;   | [ class_scope | package_scope ] type_identifier { packed_dimension }
          ;;   | class_type
          ;;   | ps_covergroup_identifier
          ;;
          ;; Where:
          ;;
          ;; class_scope ::= class_type '::'
          ;;
          ;; package_scope ::= identifier '::'
          ;;                 | '$unit' '::'
          ;;
          ;; class_type ::= ps_class_identifier [ parameter_value_assignment ]
          ;;                   { :: class_identifier [ parameter_value_assignment ] }
          ;;
          ;; ps_covergroup_identifier ::= [package_scope] 'identifier'
          ;;
          ;; ps_class_identifier ::= [package_scope] class_identifier
          ;;
          ;; parameter_value_assignment ::= '#' ...
          ;;
          ;; This is fairly restrictive but is *almost* a subset of, e.g.,
          ;; vl-parse-simple-type.  BOZO, for now, I'm going to just permit any
          ;; simple_type to occur here, followed by a packed dimension.
          (expr := (vl-parse-simple-type))
          (dims := (vl-parse-0+-packed-dimensions))
          (return (make-vl-usertype :kind expr
                                    :dims dims))))


  (defparser vl-parse-structmembers ()
    ;; matches struct_union_member { struct_union_member }
    :measure (two-nats-measure (len tokens) 3)
    (seqw tokens warnings
          (first :s= (vl-parse-structmember))
          (when (vl-is-token? :vl-rcurly)
            (return first))
          (rest := (vl-parse-structmembers))
          (return (append first rest))))

  (defparser vl-parse-structmember ()
    :measure (two-nats-measure (len tokens) 2)
    ;; struct_union_member ::=  { attribute_instance } [random_qualifier]
    ;;                          data_type_or_void
    ;;                          list_of_variable_decl_assignments ';'
    (seqw tokens warnings
          (atts := (vl-parse-0+-attribute-instances))
          (when (vl-is-some-token? '(:vl-kwd-rand :vl-kwd-randc))
            (rand := (vl-match)))
          (type :s= (vl-parse-datatype-or-void))
          (decls := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
          (:= (vl-match-token :vl-semi))
          (return
           (let ((rand (and rand (case (vl-token->type rand)
                                   (:vl-kwd-rand  :vl-rand)
                                   (:vl-kwd-randc :vl-randc)))))
             (vl-make-structmembers atts rand type decls))))))

(defsection val-when-error
  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-val-when-error
        ,(vl-val-when-error-claim vl-parse-datatype-or-void)
        ,(vl-val-when-error-claim vl-parse-datatype)
        ,(vl-val-when-error-claim vl-parse-structmembers)
        ,(vl-val-when-error-claim vl-parse-structmember)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(defsection tokenlist
  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-tokenlist
        ,(vl-tokenlist-claim vl-parse-datatype-or-void)
        ,(vl-tokenlist-claim vl-parse-datatype)
        ,(vl-tokenlist-claim vl-parse-structmembers)
        ,(vl-tokenlist-claim vl-parse-structmember)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(defsection warninglist
  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-warninglist
        ,(vl-warninglist-claim vl-parse-datatype-or-void)
        ,(vl-warninglist-claim vl-parse-datatype)
        ,(vl-warninglist-claim vl-parse-structmembers)
        ,(vl-warninglist-claim vl-parse-structmember)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(defsection progress
  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-progress
        ,(vl-progress-claim vl-parse-datatype-or-void)
        ,(vl-progress-claim vl-parse-datatype)
        ,(vl-progress-claim vl-parse-structmembers)
        ,(vl-progress-claim vl-parse-structmember)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(defsection eof

  (local (defthm crock
           (implies (vl-is-token? type)
                    (consp tokens))
           :rule-classes :forward-chaining))

  (local (defthm crock2
           (implies (consp (mv-nth 2 (vl-parse-0+-attribute-instances)))
                    (consp tokens))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-parse-0+-attribute-instances)))))

  (local (defthm crock3
           (implies (vl-is-some-token? types)
                    (consp tokens))
           :rule-classes :forward-chaining))

  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-eof
        ,(vl-eof-claim vl-parse-datatype-or-void :error)
        ,(vl-eof-claim vl-parse-datatype :error)
        ,(vl-eof-claim vl-parse-structmembers :error)
        ,(vl-eof-claim vl-parse-structmember :error)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))


(defsection result

  (local (defthm crock
           (implies (vl-is-token? type)
                    (not (mv-nth 0 (vl-match-any))))
           :hints(("Goal" :in-theory (enable vl-match-any)))))

  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-result
        (vl-parse-datatype-or-void
         (implies (force (not (mv-nth 0 (vl-parse-datatype-or-void))))
                  (vl-datatype-p (mv-nth 1 (vl-parse-datatype-or-void)))))

        (vl-parse-datatype
         (implies (force (not (mv-nth 0 (vl-parse-datatype))))
                  (vl-datatype-p (mv-nth 1 (vl-parse-datatype)))))

        (vl-parse-structmembers
         (implies (force (not (mv-nth 0 (vl-parse-structmembers))))
                  (vl-structmemberlist-p (mv-nth 1 (vl-parse-structmembers)))))

        (vl-parse-structmember
         (implies (force (not (mv-nth 0 (vl-parse-structmember))))
                  (vl-structmemberlist-p (mv-nth 1 (vl-parse-structmember)))))

        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))


(defsection true-listp

  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag true-listp
        (vl-parse-datatype-or-void t :rule-classes nil)
        (vl-parse-datatype t :rule-classes nil)
        (vl-parse-structmembers (true-listp (mv-nth 1 (vl-parse-structmembers)))
                                :rule-classes :type-prescription)
        (vl-parse-structmember (true-listp (mv-nth 1 (vl-parse-structmember)))
                               :rule-classes :type-prescription)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(with-output
 :off prove
 :gag-mode :goals
 (verify-guards vl-parse-datatype-fn))


