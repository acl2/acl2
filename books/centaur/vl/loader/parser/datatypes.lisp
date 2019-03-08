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
(include-book "../../mlib/coretypes")
(local (include-book "tools/do-not" :dir :system))
(local (include-book "../../util/arithmetic"))
(local (acl2::do-not generalize fertilize))


(defxdoc parse-datatypes
  :parents (parser)
  :short "Functions for parsing SystemVerilog data types.")

(local (xdoc::set-default-parents parse-datatypes))

;; accumulated persistence hacking
(local (in-theory (disable acl2::prefixp-when-equal-lengths
                           acl2::lower-bound-of-len-when-sublistp
                           acl2::consp-when-member-equal-of-cons-listp
                           acl2::consp-when-member-equal-of-atom-listp
                           acl2::len-when-prefixp
                           acl2::consp-under-iff-when-true-listp
                           ;; consp-when-member-equal-of-vl-commentmap-p
                           ;; consp-when-member-equal-of-vl-caselist-p
                           acl2::consp-when-member-equal-of-keyval-alist-p
                           vl-tokenlist-p-when-not-consp
                           not
                           acl2::consp-by-len
                           acl2::listpos-upper-bound-strong-2
                           double-containment
                           member-equal-when-member-equal-of-cdr-under-iff)))


;    variable_dimension ::= unsized_dimension
;                         | unpacked_dimension
;                         | associative_dimension       // mutually recursive with datatypes
;                         | queue_dimension
;
;    unsized_dimension ::= '[' ']'
;
;    unpacked_dimension ::= '[' constant_range ']'
;                         | '[' constant_expression ']'
;
;    associative_dimension ::= '[' data_type ']'        // mutually recursive with datatypes
;                            | '[' '*' ']'
;
;    queue_dimension ::= '[' '$' [ ':' constant_expression ] ']'



;; unsized_dimension ::= '[' ']'
;; packed_dimension ::= '[' constant_range ']' | unsized_dimension

(defparser vl-parse-packeddimension ()
  :result (vl-dimension-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-lbrack))
        (when (vl-is-token? :vl-rbrack)
          (:= (vl-match))
          (return :vl-unsized-dimension))
        (msb := (vl-parse-expression))
        (:= (vl-match-token :vl-colon))
        (lsb := (vl-parse-expression))
        (:= (vl-match-token :vl-rbrack))
        (return (vl-range->dimension (make-vl-range :msb msb :lsb lsb)))))

(defparser vl-parse-0+-packed-dimensions ()
  ;; Match { packed_dimension }
  :result (vl-dimensionlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
        (unless (vl-is-token? :vl-lbrack)
          (return nil))
        (first := (vl-parse-packeddimension))
        (rest  := (vl-parse-0+-packed-dimensions))
        (return (cons first rest))))

(defparser vl-parse-unpacked-dimension ()
  ;; Matches unpacked_dimension ::= '[' constant_range ']'
  ;;                              | '[' constant_expression ']'
  ;;
  ;; Note (SystemVerilog-2012 page 109): unpacked dimensions like [size] are
  ;; the same as [0:size-1].  We therefore convert them into
  ;; vl-dimension-p structures like [0:size-1].
  :result (vl-range-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-lbrack))
        ;; [Jared] bozo we used to do this, but does this make any sense?
        ;; The grammar appears to require a range or expression here.
        ;; (when (vl-is-token? :vl-rbrack)
        ;;   (:= (vl-match))
        ;;   (return (make-vl-dimension-unsized)))
        (msb := (vl-parse-expression))
        (when (vl-is-token? :vl-colon)
          (:= (vl-match))
          (lsb := (vl-parse-expression)))
        (:= (vl-match-token :vl-rbrack))
        (return (if lsb
                    ;; Regular [msb:lsb] range
                    (make-vl-range :msb msb :lsb lsb)
                  ;; Single dimension [msb], meaning [0:msb-1]
                  (make-vl-range
                   :msb (vl-make-index 0)
                   :lsb (make-vl-binary
                         :op :vl-binary-minus
                         :left msb
                         :right (vl-make-index 1))))))
  ///
  (defthm vl-dimension-p-of-vl-parse-unpacked-dimension
    ;; Gross, for compatibility with older code
    (b* (((mv err val ?tokstream) (vl-parse-unpacked-dimension)))
      (implies (not err)
               (vl-dimension-p val)))
    :hints(("Goal" :in-theory (enable vl-dimension-p)))))

(defparser vl-parse-0+-unpacked-dimensions ()
  ;; Match { unpacked_dimension }
  :result (vl-rangelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
        (unless (vl-is-token? :vl-lbrack)
          (return nil))
        (first := (vl-parse-unpacked-dimension))
        (rest  := (vl-parse-0+-unpacked-dimensions))
        (return (cons first rest)))
  ///
  (defthm vl-dimensionlist-p-of-vl-parse-0+-unpacked-dimensions
    (b* (((mv ?err val ?tokstream) (vl-parse-0+-unpacked-dimensions)))
      (vl-dimensionlist-p val))))

(defparser vl-parse-queue-dimension ()
  ;; queue_dimension ::= '[' '$' [ ':' constant_expression ] ']'
  :result (vl-dimension-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-lbrack))
       (:= (vl-match-token :vl-$))
       (when (vl-is-token? :vl-colon)
         (:= (vl-match))
         (maxsize := (vl-parse-expression)))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-dimension-queue :maxsize maxsize))))  


  ;; data_type ::=
  ;;    integer_vector_type [signing] { packed_dimension }
  ;;  | integer_atom_type [signing]
  ;;  | non_integer_type
  ;;  | 'string'
  ;;  | 'chandle'
  ;;  | 'event'


(encapsulate nil
  (local (defun vl-coredatatype-infolist->keywords (x)
           (if (atom x)
               nil
             (cons (vl-coredatatype-info->keyword (car x))
                   (vl-coredatatype-infolist->keywords (cdr x))))))
  (make-event
   `(defconst *vl-core-data-type-keywords*
      ',(remove nil (vl-coredatatype-infolist->keywords *vl-core-data-type-table*)))))

(define vl-coretypekwd->info ((x keywordp))
  :guard (member-eq x *vl-core-data-type-keywords*)
  :short "Find the properties (@(see vl-coredatatype-info) structure) for a coretype
          by its token name (for parsing)."
  :returns (info vl-coredatatype-info-p :hyp :guard
                 :hints(("Goal" :in-theory (enable vl-coredatatype-infolist-find-type)
                         :cases ((vl-coretypename-p x)))))
  (vl-coredatatype-infolist-find-kwd x *vl-core-data-type-table*))

(defsection vl-parse-core-data-type
  ;; Parses the simple, non-recursive core data types
  :parents nil

  (local (in-theory (enable vl-is-some-token?
                            vl-type-of-matched-token
                            vl-match-any)))

  (defparser vl-parse-core-data-type ()
    :guard (vl-is-some-token? *vl-core-data-type-keywords*)
    :result (vl-datatype-p val)
    :resultp-of-nil nil
    :fails gracefully
    :count strong
    (b* ((entry (vl-coretypekwd->info (vl-token->type (car (vl-tokstream->tokens)))))
         ((vl-coredatatype-info entry) entry))
      (seq tokstream
            (:= (vl-match-any)) ;; guard ensures there's at least one token
            (when (and entry.takes-signingp
                       (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned)))
              (signing := (vl-match)))
            (when entry.takes-dimensionsp
              (dims := (vl-parse-0+-packed-dimensions)))
            (return
             (let ((ans (make-vl-coretype :name entry.coretypename
                                    :signedp (if signing
                                                 (if (eq (vl-token->type signing) :vl-kwd-signed)
                                                     t
                                                   nil)
                                               entry.default-signedp)
                                    :pdims dims)))
               (mbe :logic ans
                    :exec (if (atom dims) (hons-copy ans) ans))))))))



;; enum_base_type ::=
;;     integer_atom_type [signing]
;;   | integer_vector_type [signing] [packed_dimension]
;;   | type_identifier [packed_dimension]

(defparser vl-parse-enum-base-type ()
  :result (vl-datatype-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream

        (when (vl-is-token? :vl-idtoken)
          ;; type_identifier [packed_dimension]
          (name := (vl-match))
          (when (vl-is-token? :vl-lbrack)
            (dim := (vl-parse-packeddimension)))
          (return (make-vl-usertype :name
                                    (make-vl-scopeexpr-end
                                     :hid (make-vl-hidexpr-end :name (vl-idtoken->name name)))
                                    :pdims (and dim (list dim)))))

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
           (make-vl-coretype :name (case (vl-token->type type)
                                     (:vl-kwd-bit   :vl-bit)
                                     (:vl-kwd-logic :vl-logic)
                                     (:vl-kwd-reg   :vl-reg))
                             :signedp (and signing
                                           (eq (vl-token->type signing) :vl-kwd-signed))
                             :pdims (and dim (list dim)))))

        ;; else, integer atom types:
        (type := (vl-match-some-token '(:vl-kwd-byte :vl-kwd-shortint :vl-kwd-int
                                        :vl-kwd-longint :vl-kwd-integer :vl-kwd-time)))
        ;; integer_atom_type [signing]
        (when (vl-is-some-token? '(:vl-kwd-signed :vl-kwd-unsigned))
          (signing := (vl-match)))

        ;; BOZO again the signing here is very unclear!  The integer types are
        ;; signed by default and time is unsigned by default.  Maybe that's what
        ;; we should use?
        (return (make-vl-coretype :name (case (vl-token->type type)
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
                                  ))))



;; enum_name_declaration ::=
;;   enum_identifier [ '[' integral_number [ ':' integral_number ] ']' ]
;;                   [ '=' constant_expression ]

(defparser vl-parse-enum-name-declaration ()
  :result (vl-enumitem-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
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

        (when (and left
                   (not right)
                   (equal (vl-inttoken->value left) 0))
          ;; See Table 6-10 on Page 80.  A special case is that a single index,
          ;; like foo[3], should introduce names foo0, foo1, foo2 (but not
          ;; foo3).  A corner case is foo[0].  Per the table, "N shall be a
          ;; positive integral number."  If it isn't, it doesn't make sense.
          (return-raw
           (vl-parse-error "Illegal enum item index [0].")))

        (return
         (make-vl-enumitem
          :name (vl-idtoken->name name)
          :range (cond ((not left)
                        nil)
                       ((not right)
                        (make-vl-range :msb (vl-make-index 0)
                                       :lsb (vl-make-index (- (vl-inttoken->value left) 1))))
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
  (seq tokstream
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
  :layout :fulltree
  ((id   stringp :rule-classes :type-prescription)
   (dims vl-dimensionlist-p)
   (rhs  vl-maybe-rhs-p           "BOZO not sufficiently general."))

:long "<p>This captures something like a @('variable_type') from
Verilog-2005:</p>

@({
    variable_type ::= identifier { range }
                    | identifier '=' expression
})

<p>Or @('variable_decl_assignment') from SystemVerilog-2012, which is
richer and supports @('new') invocations,</p>

@({
    variable_decl_assignment ::=
         identifier { variable_dimension } [ '=' expression ]
       | identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
       | identifier [ '=' class_new ]

    dynamic_array_new ::= 'new' '[' expression ']' [ '(' expression ')' ]

    class_new ::= [ class_scope ] 'new' [ '(' list_of_arguments ')' ]
                | 'new' expression
})

<p>Except that <b>BOZO</b> we currently don't support @('class_scope') or some
kinds of @('list_of_arguments').</p>")

(deflist vl-vardeclassignlist-p (x)
  (vl-vardeclassign-p x)
  :elementp-of-nil nil)

(defparser vl-parse-rhs ()
  :result (vl-rhs-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       ;; BOZO implement class_scope
       (unless (vl-is-token? :vl-kwd-new)
         (expr := (vl-parse-expression))
         (return (make-vl-rhsexpr :guts expr)))
       (:= (vl-match)) ;; eat the 'new'

       (when (vl-is-token? :vl-lbrack)
         ;; dynamic_array_new ::= 'new' '[' expression ']' [ '(' expression ')' ]
         (:= (vl-match))
         (arrsize := (vl-parse-expression))
         (:= (vl-match-token :vl-rbrack))
         (when (vl-is-token? :vl-lparen)
           (:= (vl-match))
           (arg1 := (vl-parse-expression))
           (:= (vl-match-token :vl-rparen))
           (return (make-vl-rhsnew :arrsize arrsize :args (list arg1))))
         (return (make-vl-rhsnew :arrsize arrsize)))

       ;; class_new ::= [ class_scope ] 'new' [ '(' list_of_arguments ')' ]
       ;;             | 'new' expression
       ;;
       ;; This is a bit tricky/ambiguous.
       ;;
       ;;  - Since it's legal to nest parens in an expression, if we write "new
       ;;    (5)" is that supposed to be a list_of_arguments or an expression?
       ;;    Strategy: always try to parse a list_of_arguments, but then fall
       ;;    back on parsing a single expression if that fails.
       ;;
       ;;  - The list_of_arguments is itself optional, so there's really a case
       ;;    of just "new" all by itself to support.  Strategy: if we fail to
       ;;    parse either of the above, fall back and assume it's an empty "new"
       (return-raw
        (b* ((backup (vl-tokstream-save))
             ;; Try parsing a list_of_arguments.  BOZO we currently only
             ;; handle plain expression lists.
             ((mv err1 args tokstream)
              (seq tokstream
                   (:= (vl-match-token :vl-lparen))
                   (args := (vl-parse-1+-expressions-separated-by-commas))
                   (:= (vl-match-token :vl-rparen))
                   (return args)))
             ((unless err1)
              (mv nil (make-vl-rhsnew :arrsize nil :args args) tokstream))

             ;; Else, try parsing a plain expression.
             (tokstream (vl-tokstream-restore backup))
             ((mv err2 arg1 tokstream) (vl-parse-expression))
             ((unless err2)
              (mv nil (make-vl-rhsnew :arrsize nil :args (list arg1)) tokstream))

             ;; Else, must just be a plain "new" with no arguments.
             (tokstream (vl-tokstream-restore backup)))
          (mv nil (make-vl-rhsnew :arrsize nil :args nil) tokstream)))))



;; Curiously the grammar allows for the use of 'new' right-hand-sides in struct
;; member initializers.  But this appears to be illegal (probably?), since per
;; SystemVerilog-2012 section 7.2.2, "the assigned expression shall be a
;; constant expression."  We will explicitly check for use of "new" here at
;; parse time and cause an error.  This behavior allows us to keep vl-rhs out
;; of the datatype/expression mutual recursion, which seems nice.

(define vl-vardeclassignlist-newfree-p ((x vl-vardeclassignlist-p))
  (or (atom x)
      (and (let ((rhs1 (vl-vardeclassign->rhs (car x))))
             (or (not rhs1)
                 (vl-rhs-case rhs1 :vl-rhsexpr)))
           (vl-vardeclassignlist-newfree-p (cdr x))))
  ///
  (defthm vl-vardeclassignlist-newfree-p-when-atom
    (implies (atom x)
             (vl-vardeclassignlist-newfree-p x)))
  (defthm vl-vardeclassignlist-newfree-p-of-cons
    (equal (vl-vardeclassignlist-newfree-p (cons a x))
           (and (let ((rhs1 (vl-vardeclassign->rhs a)))
                  (or (not rhs1)
                      (vl-rhs-case rhs1 :vl-rhsexpr)))
                (vl-vardeclassignlist-newfree-p x)))))



(define vl-make-structmembers ((atts vl-atts-p)
                               (rand vl-randomqualifier-p)
                               (type vl-datatype-p)
                               (decls vl-vardeclassignlist-p))
  :guard (vl-vardeclassignlist-newfree-p decls)
  :returns (decls vl-structmemberlist-p)
  :prepwork ((local (in-theory (enable vl-vardeclassignlist-newfree-p))))
  (b* (((when (atom decls))
        nil)
       ((vl-vardeclassign decl) (car decls)))
    (cons (make-vl-structmember :atts atts
                                :rand rand
                                :type (vl-datatype-update-udims decl.dims type)
                                :name decl.id
                                :rhs  (and decl.rhs (vl-rhsexpr->guts decl.rhs)))
          (vl-make-structmembers atts rand type (cdr decls)))))

(local (defthm narrow-down-to-union
         (equal (EQUAL (VL-TYPE-OF-MATCHED-TOKEN '(:VL-KWD-STRUCT :VL-KWD-UNION)
                                                 (vl-tokstream->TOKENS))
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
    :measure (two-nats-measure (vl-tokstream-measure) 1)
    (seq tokstream
          (when (vl-is-token? :vl-kwd-void)
            (:= (vl-match-any))
            (return (make-vl-coretype :name :vl-void)))
          (type :s= (vl-parse-datatype))
          (return type)))

  (defparser vl-parse-datatype ()
    :measure (two-nats-measure (vl-tokstream-measure) 0)
    :verify-guards nil
    (seq tokstream

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
                                   :pdims dims)))
               ;; Else it's a union.
               (make-vl-union :packedp packedp
                              :signedp signedp
                              :taggedp (acl2::bool-fix tagged)
                              :members members
                              :pdims dims))))

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
                                   (make-vl-coretype :name :vl-int :signedp t))
                     :items items
                     :pdims dims)))

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
          (type := (vl-parse-simple-type))
          (dims := (vl-parse-0+-packed-dimensions))
          (return (vl-datatype-update-pdims dims type))))


  (defparser vl-parse-structmembers ()
    ;; matches struct_union_member { struct_union_member }
    :measure (two-nats-measure (vl-tokstream-measure) 3)
    (seq tokstream
          (first :s= (vl-parse-structmember))
          (when (vl-is-token? :vl-rcurly)
            (return first))
          (rest := (vl-parse-structmembers))
          (return (append first rest))))

  (defparser vl-parse-structmember ()
    :measure (two-nats-measure (vl-tokstream-measure) 2)
    ;; struct_union_member ::=  { attribute_instance } [random_qualifier]
    ;;                          data_type_or_void
    ;;                          list_of_variable_decl_assignments ';'
    (seq tokstream
          (atts := (vl-parse-0+-attribute-instances))
          (when (vl-is-some-token? '(:vl-kwd-rand :vl-kwd-randc))
            (rand := (vl-match)))
          (type :s= (vl-parse-datatype-or-void))
          (decls := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
          (:= (vl-match-token :vl-semi))
          (unless (vl-vardeclassignlist-newfree-p decls)
            (return-raw
             (vl-parse-error "Illegal use of 'new' in a struct or union member initial value")))
          (return
           (let ((rand (and rand (case (vl-token->type rand)
                                   (:vl-kwd-rand  :vl-rand)
                                   (:vl-kwd-randc :vl-randc)))))
             (vl-make-structmembers atts rand type decls)))))


  (defparser vl-parse-variable-dimension ()
    :measure (two-nats-measure (vl-tokstream-measure) 10)
    ;; Matches variable_dimension ::= unsized_dimension
    ;;                              | unpacked_dimension
    ;;                              | associative_dimension
    ;;                              | queue_dimension
    (seq tokstream
         ;; unsized_dimension ::= '[' ']'
         (when (and (vl-is-token? :vl-lbrack)
                    (vl-lookahead-is-token? :vl-rbrack (cdr (vl-tokstream->tokens))))
           (:= (vl-match))
           (:= (vl-match))
           (return (make-vl-dimension-unsized)))

         ;; queue_dimension ::= '[' '$' [ ':' constant_expression ] ']'
         (when (and (vl-is-token? :vl-lbrack)
                    (vl-lookahead-is-token? :vl-$ (cdr (vl-tokstream->tokens))))
           (ans := (vl-parse-queue-dimension))
           (return ans))

         (return-raw
          ;; Use backtracking to resolve either an unpacked_dimension or an
          ;; associative_dimension.  Almost always it will be an
          ;; unpacked_dimension, so try that first.
          (b* ((backup (vl-tokstream-save))
               ((mv erp val tokstream)
                (vl-parse-unpacked-dimension))
               ((unless erp)
                (mv erp val tokstream))
               ;; Failed to parse an unpacked_dimension, so try an
               ;; associative_dimension instead.
               (tokstream (vl-tokstream-restore backup)))
            (vl-parse-associative-dimension)))))

  (defparser vl-parse-associative-dimension ()
    :measure (two-nats-measure (vl-tokstream-measure) 9)
    ;;    associative_dimension ::= '[' data_type ']'
    ;;                            | '[' '*' ']'
    (seq tokstream
         (:= (vl-match-token :vl-lbrack))
         (when (vl-is-token? :vl-times)
           (:= (vl-match))
           (:= (vl-match-token :vl-rbrack))
           (return (make-vl-dimension-star)))
         (type := (vl-parse-datatype))
         (:= (vl-match-token :vl-rbrack))
         (return (make-vl-dimension-datatype :type type))))

  (defparser vl-parse-0+-variable-dimensions ()
    :measure (two-nats-measure (vl-tokstream-measure) 11)
    ;; Match { variable_dimension }
    (seq tokstream
         (unless (vl-is-token? :vl-lbrack)
           (return nil))
         (first :s= (vl-parse-variable-dimension))
         (rest  := (vl-parse-0+-variable-dimensions))
         (return (cons first rest))))

  (defparser vl-parse-variable-decl-assignment ()
    ;; SystemVerilog-2012 Only.
    :measure (two-nats-measure (vl-tokstream-measure) 12)
    (seq tokstream
         (id := (vl-match-token :vl-idtoken))
         (when (vl-is-token? :vl-lbrack)
           (dims := (vl-parse-0+-variable-dimensions)))
         (when (vl-is-token? :vl-equalsign)
           (:= (vl-match))
           (rhs := (vl-parse-rhs)))
         (return (make-vl-vardeclassign
                  :id (vl-idtoken->name id)
                  :dims dims
                  :rhs rhs))))

  (defparser vl-parse-1+-variable-decl-assignments-separated-by-commas ()
    :measure (two-nats-measure (vl-tokstream-measure) 13)
    ;; SystemVerilog-2012 Only.
    ;;
    ;;   list_of_variable_decl_assignments ::= variable_decl_assignment { ',' variable_decl_assignment }
    (seq tokstream
         (first :s= (vl-parse-variable-decl-assignment))
         (when (vl-is-token? :vl-comma)
           (:= (vl-match))
           (rest := (vl-parse-1+-variable-decl-assignments-separated-by-commas)))
         (return (cons first rest))))
  )




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
        ,(vl-val-when-error-claim vl-parse-variable-dimension)
        ,(vl-val-when-error-claim vl-parse-associative-dimension)
        ,(vl-val-when-error-claim vl-parse-0+-variable-dimensions)
        ,(vl-val-when-error-claim vl-parse-variable-decl-assignment)
        ,(vl-val-when-error-claim vl-parse-1+-variable-decl-assignments-separated-by-commas)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(defsection warning
  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-warning
        ,(vl-warning-claim vl-parse-datatype-or-void)
        ,(vl-warning-claim vl-parse-datatype)
        ,(vl-warning-claim vl-parse-structmembers)
        ,(vl-warning-claim vl-parse-structmember)
        ,(vl-warning-claim vl-parse-variable-dimension)
        ,(vl-warning-claim vl-parse-associative-dimension)
        ,(vl-warning-claim vl-parse-0+-variable-dimensions)
        ,(vl-warning-claim vl-parse-variable-decl-assignment)
        ,(vl-warning-claim vl-parse-1+-variable-decl-assignments-separated-by-commas)
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
        ,(vl-progress-claim vl-parse-variable-dimension)
        ,(vl-progress-claim vl-parse-associative-dimension)
        ,(vl-progress-claim vl-parse-0+-variable-dimensions :strongp nil)
        ,(vl-progress-claim vl-parse-variable-decl-assignment)
        ,(vl-progress-claim vl-parse-1+-variable-decl-assignments-separated-by-commas)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(defsection eof

  (local (defthm crock
           (implies (vl-is-token? type)
                    (consp (vl-tokstream->tokens)))
           :rule-classes :forward-chaining))

  (local (defthm crock2
           (implies (consp (vl-tokstream->tokens :tokstream (mv-nth 2 (vl-parse-0+-attribute-instances))))
                    (consp (vl-tokstream->tokens)))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (enable vl-parse-0+-attribute-instances)))))

  (local (defthm crock3
           (implies (vl-is-some-token? types)
                    (consp (vl-tokstream->tokens)))
           :rule-classes :forward-chaining))

  (local (defthm crock4
           (implies (vl-type-of-matched-token types tokens)
                    (consp tokens))
           :rule-classes :forward-chaining))

  (local (defthm crock5
           (implies (not (vl-is-token? :vl-lbrack))
                    (mv-nth 0 (vl-parse-unpacked-dimension)))
           :hints(("Goal" :in-theory (enable vl-parse-unpacked-dimension)))))

  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag vl-parse-datatype-eof
        ,(vl-eof-claim vl-parse-datatype-or-void :error)
        ,(vl-eof-claim vl-parse-datatype :error)
        ,(vl-eof-claim vl-parse-structmembers :error)
        ,(vl-eof-claim vl-parse-structmember :error)
        ,(vl-eof-claim vl-parse-variable-dimension :error)
        ,(vl-eof-claim vl-parse-associative-dimension :error)
        ,(vl-eof-claim vl-parse-0+-variable-dimensions nil)
        ,(vl-eof-claim vl-parse-variable-decl-assignment :error)
        ,(vl-eof-claim vl-parse-1+-variable-decl-assignments-separated-by-commas :error)
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

        (vl-parse-variable-dimension
         (implies (force (not (mv-nth 0 (vl-parse-variable-dimension))))
                  (vl-dimension-p (mv-nth 1 (vl-parse-variable-dimension)))))

        (vl-parse-associative-dimension
         (implies (force (not (mv-nth 0 (vl-parse-associative-dimension))))
                  (vl-dimension-p (mv-nth 1 (vl-parse-associative-dimension)))))

        (vl-parse-0+-variable-dimensions
         (implies (force (not (mv-nth 0 (vl-parse-0+-variable-dimensions))))
                  (vl-dimensionlist-p (mv-nth 1 (vl-parse-0+-variable-dimensions)))))

        (vl-parse-variable-decl-assignment
         (implies (force (not (mv-nth 0 (vl-parse-variable-decl-assignment))))
                  (vl-vardeclassign-p (mv-nth 1 (vl-parse-variable-decl-assignment)))))

        (vl-parse-1+-variable-decl-assignments-separated-by-commas
         (implies (force (not (mv-nth 0 (vl-parse-1+-variable-decl-assignments-separated-by-commas))))
                  (vl-vardeclassignlist-p
                   (mv-nth 1 (vl-parse-1+-variable-decl-assignments-separated-by-commas)))))

        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))


(defsection true-listp

  (with-output
    :off prove
    :gag-mode :goals
    (make-event
     `(defthm-parse-datatype-flag datatypes-true-listp
        (vl-parse-datatype-or-void t :rule-classes nil)
        (vl-parse-datatype t :rule-classes nil)
        (vl-parse-structmembers (true-listp (mv-nth 1 (vl-parse-structmembers)))
                                :rule-classes :type-prescription)
        (vl-parse-structmember (true-listp (mv-nth 1 (vl-parse-structmember)))
                               :rule-classes :type-prescription)
        (vl-parse-variable-dimension t :rule-classes nil)
        (vl-parse-associative-dimension t :rule-classes nil)
        (vl-parse-0+-variable-dimensions (true-listp (mv-nth 1 (vl-parse-0+-variable-dimensions)))
                                         :rule-classes :type-prescription)
        (vl-parse-variable-decl-assignment t :rule-classes nil)
        (vl-parse-1+-variable-decl-assignments-separated-by-commas
         (true-listp (mv-nth 1 (vl-parse-1+-variable-decl-assignments-separated-by-commas)))
         :rule-classes :type-prescription)
        :hints((and acl2::stable-under-simplificationp
                    (flag::expand-calls-computed-hint
                     acl2::clause
                     ',(flag::get-clique-members 'vl-parse-datatype-fn (w state)))))))))

(with-output
 :off prove
 :gag-mode :goals
 (verify-guards vl-parse-datatype-fn))


(defsection no-unpacked-dimensions-after-vl-parse-datatype

  (local (defthm l0
           (b* (((mv err val ?tokstream) (vl-parse-core-data-type)))
             (implies (not err)
                      (and (equal (vl-datatype-kind val) :vl-coretype)
                           (not (vl-datatype->udims val)))))
           :hints(("Goal" :in-theory (enable vl-parse-core-data-type)))))

  (local (defthm l1
           (b* (((mv err val ?tokstream) (vl-parse-simple-type)))
             (implies (not err)
                      (not (vl-datatype->udims val))))
           :hints(("Goal" :expand ((vl-parse-simple-type)
                                   (vl-parse-very-simple-type))))))

  (defthm no-unpacked-dimensions-after-vl-parse-datatype
    (b* (((mv err val ?tokstream) (vl-parse-datatype)))
      (implies (not err)
               (not (vl-datatype->udims val))))
    :hints(("Goal"
            ;; :in-theory (enable vl-datatype->udims)
            :expand ((vl-parse-datatype))))))


(defparser vl-parse-datatype-or-implicit ()
  :result (vl-datatype-p val)
  :fails gracefully
  :count weak
  (b* (((when (or (vl-is-token? :vl-kwd-signed)
                  (vl-is-token? :vl-lbrack)))
        ;; shortcut to implicit data type
        (seq tokstream
             (signing := (vl-maybe-match-token :vl-kwd-signed))
             (dims := (vl-parse-0+-packed-dimensions))
             (return (make-vl-coretype :name :vl-logic
                                       :pdims dims
                                       :signedp (and signing t)))))
       (backup (vl-tokstream-save))
       ((mv erp type tokstream) (vl-parse-datatype))
       ((unless erp)
        (mv nil type tokstream))

       ;; Couldn't parse a datatype: back to the implicit case.  But since the
       ;; stream doesn't start with signed or [, there's nothing we can parse,
       ;; so the datatype must be unsigned, undimensioned logic.
       (tokstream (vl-tokstream-restore backup)))
    (mv nil (make-vl-coretype :name :vl-logic) tokstream)))

