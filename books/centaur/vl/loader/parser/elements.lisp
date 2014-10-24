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
(include-book "statements")
(include-book "ports")      ;; vl-portdecllist-p, vl-portlist-p
(include-book "nets")       ;; vl-assignlist-p, vl-netdecllist-p
(include-book "blockitems") ;; vl-vardecllist-p, vl-paramdecllist-p
(include-book "insts")      ;; vl-modinstlist-p
(include-book "gates")      ;; vl-gateinstlist-p
(include-book "functions")  ;; vl-fundecllist-p
(include-book "modports")
(include-book "typedefs")
(include-book "../../mlib/port-tools")  ;; vl-ports-from-portdecls
(local (include-book "../../util/arithmetic"))




(defparser vl-parse-1+-alias-rhses (atts lhs loc)
  :guard (and (vl-atts-p atts)
              (vl-expr-p lhs)
              (vl-location-p loc))
  :result (vl-aliaslist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-equalsign))
        (rhs1 := (vl-parse-lvalue))
        (when (vl-is-token? :vl-equalsign)
          (rest := (vl-parse-1+-alias-rhses atts lhs loc)))
        (return (cons (make-vl-alias :lhs lhs
                                       :rhs rhs1
                                       :atts atts
                                       :loc loc)
                      rest))))


(defparser vl-parse-alias (atts)
  :guard (vl-atts-p atts)
  :result (vl-aliaslist-p val)
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
        (loc := (vl-current-loc))
        (:= (vl-match-token :vl-kwd-alias))
        (lhs := (vl-parse-lvalue))
        (aliases := (vl-parse-1+-alias-rhses atts lhs loc))
        (return aliases)))





(defparser vl-parse-initial-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-initiallist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (kwd := (vl-match-token :vl-kwd-initial))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-initial :loc (vl-token->loc kwd)
                                       :stmt stmt
                                       :atts atts)))))

(defparser vl-parse-alwaystype ()
  :result (vl-alwaystype-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (when (eq (vl-loadconfig->edition config) :verilog-2005)
          (:= (vl-match-token :vl-kwd-always))
          (return :vl-always))
        (kwd := (vl-match-some-token '(:vl-kwd-always
                                       :vl-kwd-always_comb
                                       :vl-kwd-always_latch
                                       :vl-kwd-always_ff)))
        (return (case (vl-token->type kwd)
                  (:vl-kwd-always       :vl-always)
                  (:vl-kwd-always_comb  :vl-always-comb)
                  (:vl-kwd-always_latch :vl-always-latch)
                  (:vl-kwd-always_ff    :vl-always-ff)))))

(defparser vl-parse-always-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-alwayslist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (loc  := (vl-current-loc))
        (type := (vl-parse-alwaystype))
        (stmt := (vl-parse-statement))
        (return (list (make-vl-always :loc  loc
                                      :type type
                                      :stmt stmt
                                      :atts atts)))))




;                           UNIMPLEMENTED PRODUCTIONS
;
; Eventually we may implement some more of these.  For now, we just cause
; an error if any of them is used.
;
; BOZO consider changing some of these to skip tokens until 'endfoo' and issue
; a warning.
;

(defparser vl-parse-specify-block-aux ()
  ;; BOZO this is really not implemented.  We just read until endspecify,
  ;; throwing away any tokens we encounter until it.
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (when (vl-is-token? :vl-kwd-endspecify)
          (:= (vl-match))
          (return nil))
        (:s= (vl-match-any))
        (:= (vl-parse-specify-block-aux))
        (return nil)))

(defparser vl-parse-specify-block ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (if (not (consp (vl-tokstream->tokens)))
      (vl-parse-error "Unexpected EOF.")
    (seq tokstream
         (:= (vl-parse-warning :vl-warn-specify
                               "Specify blocks are not yet implemented.  Ignoring everything until 'endspecify'."))
         (ret := (vl-parse-specify-block-aux))
         (return ret))))


(defparser vl-parse-specparam-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-genvar-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (seq tokstream
        (:= (vl-parse-warning :vl-warn-genvar "Genvar declarations are not implemented, we are just skipping this genvar."))
        (:= (vl-match-token :vl-kwd-genvar))
        (:= (vl-parse-1+-identifiers-separated-by-commas))
        (:= (vl-match-token :vl-semi))
        (return nil)))

(defparser vl-parse-parameter-override (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))



(defconst *vl-netdecltypes-kwds*
  (strip-cars *vl-netdecltypes-kwd-alist*))


(defthm vl-modelement-p-of-vl-parse-fwd-typedef
  (implies (and (force (vl-atts-p atts))
                (force (vl-is-token? :vl-kwd-typedef)))
           (b* (((mv err res) (vl-parse-fwd-typedef atts)))
             (equal (vl-modelement-p res)
                    (not err))))
  :hints(("Goal" :in-theory (enable vl-parse-fwd-typedef))))

(defthm vl-modelement-p-of-vl-parse-type-declaration
  (implies (and (force (vl-atts-p atts))
                (force (vl-is-token? :vl-kwd-typedef)))
           (b* (((mv err res) (vl-parse-type-declaration atts)))
             (equal (vl-modelement-p res)
                    (not err))))
  :hints(("Goal" :in-theory (enable vl-parse-type-declaration))))


(encapsulate nil
  (local (in-theory (enable vl-is-token?)))
  (local (in-theory (disable MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                             VL-PARSE-EXPRESSION-EOF-VL-PARSE-0+-ATTRIBUTE-INSTANCES
                             double-containment
                             acl2::subsetp-when-atom-left
                             acl2::subsetp-when-atom-right
                             acl2::lower-bound-of-len-when-sublistp
                             acl2::len-when-prefixp
                             acl2::len-when-atom
                             default-car)))

  (local (defthm vl-modelement-p-when-vl-blockitem-p
           (implies (vl-blockitem-p x)
                    (vl-modelement-p x))
           :hints(("Goal" :in-theory (enable vl-blockitem-p vl-modelement-p)))))

  (local (defthm vl-modelementlist-p-when-vl-blockitemlist-p
           (implies (vl-blockitemlist-p x)
                    (vl-modelementlist-p x))
           :hints(("Goal" :induct (len x)))))

  (defparser vl-parse-modelement-aux (atts)
    :guard (vl-atts-p atts)
    :result (vl-modelementlist-p val)
    :resultp-of-nil t
    :true-listp t
    :fails gracefully
    :count strong
    (b* ((tokens (vl-tokstream->tokens))
         ((when (atom tokens))
          (vl-parse-error "Unexpected EOF."))
         (type1 (vl-token->type (car tokens)))
         ((when (member-eq type1 *vl-directions-kwds*))
          (seq tokstream
                ((portdecls . netdecls) := (vl-parse-port-declaration-noatts atts))
                (:= (vl-match-token :vl-semi))
                ;; Should be fewer netdecls so this is the better order for the append.
                (return (append netdecls portdecls))))
         ((when (eq type1 :vl-kwd-specify))
          (if atts
              (vl-parse-error "'specify' is not allowed to have attributes.")
            (vl-parse-specify-block)))
         ((when (eq type1 :vl-kwd-parameter))
          (seq tokstream
                ;; localparams are handled in parse-module-or-generate-item
                (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-parameter)))
                (:= (vl-match-token :vl-semi))
                (return ret)))
         ((when (eq type1 :vl-kwd-specparam))
          (vl-parse-specparam-declaration atts))
         ((when (member type1 *vl-netdecltypes-kwds*))
          (seq tokstream
                ((assigns . decls) := (vl-parse-net-declaration atts))
                ;; Note: this order is important, the decls have to come first
                ;; or we'll try to infer implicit nets from the assigns.
                (return (append decls assigns))))
         ((when (member type1 *vl-gate-type-keywords*))
          (vl-parse-gate-instantiation atts))
         ((when (eq type1 :vl-kwd-genvar))
          (vl-parse-genvar-declaration atts))
         ((when (eq type1 :vl-kwd-task))
          (seq tokstream
                (task := (vl-parse-task-declaration atts))
                (return (list task))))
         ((when (eq type1 :vl-kwd-function))
          (seq tokstream
                (fun := (vl-parse-function-declaration atts))
                (return (list fun))))
         ((when (eq type1 :vl-kwd-localparam))
          (seq tokstream
                ;; Note: non-local parameters not allowed
                (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-localparam)))
                (:= (vl-match-token :vl-semi))
                (return ret)))
         ((when (eq type1 :vl-kwd-defparam))
          (vl-parse-parameter-override atts))
         ((when (eq type1 :vl-kwd-assign))
          (vl-parse-continuous-assign atts))
         ((when (eq type1 :vl-kwd-initial))
          (vl-parse-initial-construct atts))
         ((when (eq type1 :vl-kwd-always))
          (vl-parse-always-construct atts))

         ((when (and (vl-is-token? :vl-idtoken)
                     (not (vl-parsestate-is-user-defined-type-p
                           (vl-idtoken->name (car (vl-tokstream->tokens)))
                           (vl-tokstream->pstate)))))
          (vl-parse-udp-or-module-instantiation atts))


         ((when (eq (vl-loadconfig->edition config) :verilog-2005))
          (case type1
            (:vl-kwd-reg        (vl-parse-reg-declaration atts))
            (:vl-kwd-integer    (vl-parse-integer-declaration atts))
            (:vl-kwd-real       (vl-parse-real-declaration atts))
            (:vl-kwd-time       (vl-parse-time-declaration atts))
            (:vl-kwd-realtime   (vl-parse-realtime-declaration atts))
            (:vl-kwd-event      (vl-parse-event-declaration atts))
            (t (vl-parse-error "Invalid module or generate item."))))

         ;; SystemVerilog extensions ----
         ((when (eq type1 :vl-kwd-typedef))
          (seq tokstream
                (typedef := (vl-parse-type-declaration atts))
                (return (list typedef))))

         ((when (eq type1 :vl-kwd-modport))
          (seq tokstream
                (modports := (vl-parse-modport-decl atts))
                (return modports)))

         ((when (eq type1 :vl-kwd-alias))
          (seq tokstream
                (aliases := (vl-parse-alias atts))
                (return aliases)))

         ((when (or (eq type1 :vl-kwd-always_ff)
                    (eq type1 :vl-kwd-always_latch)
                    (eq type1 :vl-kwd-always_comb)))
          (vl-parse-always-construct atts)))
      ;; SystemVerilog -- BOZO haven't thought this through very thoroughly, but it's
      ;; probably a fine starting place.
      (vl-parse-block-item-declaration-noatts atts))))


(defparser vl-parse-modelement ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
        (atts := (vl-parse-0+-attribute-instances))
        (return-raw
         (vl-parse-modelement-aux atts))))

(define vl-inc-or-dec-expr ((var stringp) (op (member op '(:vl-plusplus :vl-minusminus))))
  :returns (expr vl-expr-p)
  :guard-debug t
  (make-vl-nonatom
   :op (if (eq op :vl-plusplus)
           :vl-binary-plus
         :vl-binary-minus)
   :args (list (vl-idexpr var nil nil)
               (make-vl-atom :guts
                             (make-vl-constint
                              :origwidth 32
                              :value 1
                              :origtype :vl-unsigned
                              :wasunsized t)))))

(defconst *vl-assignment-operators*
  '(:vl-equalsign
    :vl-pluseq
    :vl-minuseq
    :vl-timeseq
    :vl-diveq
    :vl-remeq
    :vl-andeq
    :vl-oreq
    :vl-xoreq
    :vl-shleq
    :vl-shreq
    :vl-ashleq
    :vl-ashreq))

(define vl-assign-op-expr ((var stringp)
                           (op (member op *vl-assignment-operators*))
                           (rhs vl-expr-p))
  ;; Given an expression like a = b, returns b.
  ;; Given a %= b, returns a % b.
  :returns (expr vl-expr-p)
  :guard-debug t
  (if (eq op :vl-equalsign)
      (vl-expr-fix rhs)
    (make-vl-nonatom
     :op (case op
           (:vl-pluseq  :vl-binary-plus)
           (:vl-minuseq :vl-binary-minus)
           (:vl-timeseq :vl-binary-times)
           (:vl-diveq   :vl-binary-div)
           (:vl-remeq   :vl-binary-rem)
           (:vl-andeq   :vl-binary-bitand)
           (:vl-oreq    :vl-binary-bitor)
           (:vl-xoreq   :vl-binary-xor)
           (:vl-shleq   :vl-binary-shl)
           (:vl-shreq   :vl-binary-shr)
           (:vl-ashleq  :vl-binary-ashl)
           (:vl-ashreq  :vl-binary-ashr))
     :args (list (vl-idexpr var nil nil) rhs))))


(defparser vl-parse-genvar-iteration ()
  ;; Parses:
  ;; genvar_iteration ::=
  ;;    genvar_identifier assignment_operator genvar_expression
  ;;    | inc_or_dec_operator genvar_identifier
  ;;    | genvar_identifier inc_or_dec_operator
  ;; Produces (var . next-expr) where var is the name of the assigned variable
  ;; and next-expr is an expression representing its next value.
  :result (and (consp val)
               (stringp (car val))
               (vl-expr-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-some-token? '(:vl-plusplus :vl-minusminus))
         ;; inc_or_dec_operator case
         (op := (vl-match))
         (id := (vl-match-token :vl-idtoken))
         (return (cons (vl-idtoken->name id)
                       (vl-inc-or-dec-expr (vl-idtoken->name id)
                                           (vl-token->type op)))))
       (id := (vl-match-token :vl-idtoken))
       (when (vl-is-some-token? '(:vl-plusplus :vl-minusminus))
         ;; inc_or_dec_operator case
         (op := (vl-match))
         (return (cons (vl-idtoken->name id)
                       (vl-inc-or-dec-expr (vl-idtoken->name id)
                                           (vl-token->type op)))))
       (eq := (vl-match-some-token *vl-assignment-operators*))
       (rhs := (vl-parse-expression))
       (return (cons (vl-idtoken->name id)
                     (vl-assign-op-expr (vl-idtoken->name id)
                                        (vl-token->type eq)
                                        rhs)))))




(encapsulate nil
  (local (in-theory (disable acl2::len-when-atom
                             acl2::len-when-prefixp
                             acl2::lower-bound-of-len-when-sublistp
                             not)))
  (defparser vl-parse-genloop-header ()
    ;; Parses the "for (init; continue; incr)" header of a generate loop.
    ;; Returns a genloop structure but with an empty body.
    :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-for))
    :result (and (vl-genelement-p val)
                 (equal (vl-genelement-kind val) :vl-genloop))
    :fails gracefully
    :count strong

    ;; loop_generate_construct ::=
    ;;   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
    ;;      generate_block
    ;; genvar_initialization ::=
    ;;    [ genvar ] genvar_identifier = constant_expression
    ;; genvar_iteration ::=
    ;;    genvar_identifier assignment_operator genvar_expression
    ;;    | inc_or_dec_operator genvar_identifier
    ;;    | genvar_identifier inc_or_dec_operator
    (seq tokstream
         (loc := (vl-current-loc))
         (:= (vl-match))
         (:= (vl-match-token :vl-lparen))
         (:= (vl-maybe-match-token :vl-kwd-genvar)) ;; skip genvar
         (id := (vl-match-token :vl-idtoken))
         (:= (vl-match-token :vl-equalsign))
         (init := (vl-parse-expression))
         (:= (vl-match-token :vl-semi))
         (continue := (vl-parse-expression))
         (:= (vl-match-token :vl-semi))
         ((id2 . next) := (vl-parse-genvar-iteration))
         (when (not (equal (vl-idtoken->name id) id2))
           (return-raw
            (vl-parse-error "For loop: the initialized variable differed from the incremented variable.")))
         (:= (vl-match-token :vl-rparen))
         (return (make-vl-genloop :var (make-vl-id :name (vl-idtoken->name id))
                                  :initval init
                                  :continue continue
                                  :nextval next
                                  :genblock (make-vl-generateblock)
                                  :loc loc)))))


(encapsulate nil
  (table acl2::acl2-defaults-table :ruler-extenders :all)
  (local (in-theory (disable acl2::len-when-atom
                             acl2::len-when-prefixp
                             acl2::lower-bound-of-len-when-sublistp
                             vl-is-token?-fn-when-atom-of-tokens
                             vl-parse-expression-eof-vl-parse-expression
                             double-containment
                             acl2::consp-of-car-when-alistp)))

  (with-output :off (prove)
    (defparsers vl-genelements
      :parents (parser)
      :short "Parser for elements contained within modules, interfaces, etc., including generate constructs."
      :flag-local nil
      (defparser vl-parse-genelement ()
        ;; :result (vl-genelementlist-p val)
        ;; :resultp-of-nil t
        ;; :true-listp t
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 5)
        :verify-guards nil
        (declare (xargs :measure-debug t))
        (seq tokstream
             (when (vl-is-token? :vl-kwd-for)
               (loopblk := (vl-parse-genloop))
               (return (list loopblk)))
             (when (vl-is-token? :vl-kwd-if)
               (ifblk := (vl-parse-genif))
               (return (list ifblk)))
             (when (vl-is-token? :vl-kwd-case)
               (caseblk := (vl-parse-gencase))
               (return (list caseblk)))
             (when (vl-is-token? :vl-kwd-generate)
               (:= (vl-match))
               (elems := (vl-parse-0+-genelements))
               (:= (vl-match-token :vl-kwd-endgenerate))
               (return elems))
             (items := (vl-parse-modelement))
             (return (vl-modelementlist->genelements items)) ))

      (defparser vl-parse-0+-genelements ()
        ;;:result (vl-genelementlist-p val)
        ;; :resultp-of-nil t
        ;; :true-listp t
        ;; :fails never
        ;; :count weak
        :measure (two-nats-measure (vl-tokstream-measure) 8)
        (declare (xargs :ruler-extenders :all))
        (seq-backtrack tokstream
                       ((first :s= (vl-parse-genelement))
                        (rest := (vl-parse-0+-genelements))
                        (return (append first rest)))
                       ((return nil))))

      (defparser vl-parse-generate-block ()
        ;; :result (vl-generateblock-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 8)
        (seq tokstream
             (when (vl-is-token? :vl-kwd-begin)
               (:= (vl-match))
               (when (vl-is-token? :vl-colon)
                 (:= (vl-match))
                 (blkname := (vl-match-token :vl-idtoken)))
               (elts := (vl-parse-0+-genelements))
               (return (make-vl-generateblock :name (and blkname
                                                         (vl-idtoken->name blkname))
                                              :elems elts)))
             (elts := (vl-parse-genelement))
             (return (make-vl-generateblock :elems elts))))

      (defparser vl-parse-genloop ()
        :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-for))
        ;; :result (vl-genelement-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 4)

        ;; loop_generate_construct ::=
        ;;   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
        ;;      generate_block
        ;; genvar_initialization ::=
        ;;    [ genvar ] genvar_identifier = constant_expression
        ;; genvar_iteration ::=
        ;;    genvar_identifier assignment_operator genvar_expression
        ;;    | inc_or_dec_operator genvar_identifier
        ;;    | genvar_identifier inc_or_dec_operator
        (seq tokstream
             (header := (vl-parse-genloop-header))
             (genblock := (vl-parse-generate-block))
             (return (change-vl-genloop header
                                        :genblock genblock))))

      (defparser vl-parse-genif ()
        :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-if))
        ;; :result (vl-genelement-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 4)
        ;; if_generate_construct ::=
        ;;   if ( constant_expression ) generate_block [ else generate_block ]
        (seq tokstream
             (loc := (vl-current-loc))
             (:= (vl-match))
             (:= (vl-match-token :vl-lparen))
             (test := (vl-parse-expression))
             (:= (vl-match-token :vl-rparen))
             (then :w= (vl-parse-generate-block))
             (when (and (consp (vl-tokstream->tokens))
                        (vl-is-token? :vl-kwd-else))
               (:= (vl-match))
               (else := (vl-parse-generate-block)))
             (return (make-vl-genif
                      :test test
                      :then then
                      :else (or else
                                (make-vl-generateblock))
                      :loc loc))))

      (defparser vl-parse-gencase ()
        :guard (and (consp (vl-tokstream->tokens)) (vl-is-token? :vl-kwd-case))
        ;; :result (vl-genelement-p val)
        ;; :resultp-of-nil nil
        ;; :fails gracefully
        ;; :count strong
        :measure (two-nats-measure (vl-tokstream-measure) 4)
        ;; case_generate_construct ::=
        ;;    case ( constant_expression ) case_generate_item { case_generate_item } endcase
        ;; case_generate_item ::=
        ;;    constant_expression { , constant_expression } : generate_block
        ;;    | default [ : ] generate_block
        (seq tokstream
             (loc := (vl-current-loc))
             (:= (vl-match))
             (:= (vl-match-token :vl-lparen))
             (test := (vl-parse-expression))
             (:= (vl-match-token :vl-rparen))
             ((caselist . default) := (vl-parse-gencaselist))
             (return (make-vl-gencase
                       :test test
                       :cases caselist
                       :default (or default (make-vl-generateblock))
                       :loc loc))))

      (defparser vl-parse-gencaselist ()
        ;; :result (and (consp val)
        ;;              (vl-gencaselist-p (car val))
        ;;              (iff (vl-generateblock-p (cdr val))
        ;;                   (cdr val)))
        :measure (two-nats-measure (vl-tokstream-measure) 5)
        (seq tokstream
             (when (vl-is-token? :vl-kwd-default)
               (:= (vl-match))
               (:= (vl-match-token :vl-colon))
               (blk :w= (vl-parse-generate-block))
               ((rest . rdefault) := (vl-parse-gencaselist))
               (when rdefault
                 (return-raw (vl-parse-error "Multiple default cases in generate case")))
               (return (cons rest blk)))
             (exprs := (vl-parse-1+-expressions-separated-by-commas))
             (:= (vl-match-token :vl-colon))
             (blk :w= (vl-parse-generate-block))
             ((rest . default) := (vl-parse-gencaselist))
             (return (cons (cons (cons exprs blk) rest) default))))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-val-when-error
      ,(vl-val-when-error-claim vl-parse-genelement)
      ,(vl-val-when-error-claim vl-parse-0+-genelements)
      ,(vl-val-when-error-claim vl-parse-generate-block)
      ,(vl-val-when-error-claim vl-parse-genloop)
      ,(vl-val-when-error-claim vl-parse-genif)
      ,(vl-val-when-error-claim vl-parse-gencase)
      ,(vl-val-when-error-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-val-when-error
      ,(vl-val-when-error-claim vl-parse-genelement)
      ,(vl-val-when-error-claim vl-parse-0+-genelements)
      ,(vl-val-when-error-claim vl-parse-generate-block)
      ,(vl-val-when-error-claim vl-parse-genloop)
      ,(vl-val-when-error-claim vl-parse-genif)
      ,(vl-val-when-error-claim vl-parse-gencase)
      ,(vl-val-when-error-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-warning
      ,(vl-warning-claim vl-parse-genelement)
      ,(vl-warning-claim vl-parse-0+-genelements)
      ,(vl-warning-claim vl-parse-generate-block)
      ,(vl-warning-claim vl-parse-genloop)
      ,(vl-warning-claim vl-parse-genif)
      ,(vl-warning-claim vl-parse-gencase)
      ,(vl-warning-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-progress
      ,(vl-progress-claim vl-parse-genelement)
      ,(vl-progress-claim vl-parse-0+-genelements :strongp nil)
      ,(vl-progress-claim vl-parse-generate-block)
      ,(vl-progress-claim vl-parse-genloop)
      ,(vl-progress-claim vl-parse-genif)
      ,(vl-progress-claim vl-parse-gencase)
      ,(vl-progress-claim vl-parse-gencaselist)
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (local
   (defmacro vl-genelement-claim (name type &key args true-listp)
     (let ((main `(implies (not (mv-nth 0 (,name . ,args)))
                           (,type (mv-nth 1 (,name . ,args))))))
       `'(,name ,(if true-listp
                     `(and (true-listp (mv-nth 1 (,name . ,args)))
                           ,main)
                   main)))))

  (make-event
   `(defthm-vl-genelements-flag vl-parse-genelement-type
      ,(vl-genelement-claim vl-parse-genelement     vl-genelementlist-p :true-listp t)
      ,(vl-genelement-claim vl-parse-0+-genelements vl-genelementlist-p :true-listp t)
      ,(vl-genelement-claim vl-parse-generate-block vl-generateblock-p)
      ,(vl-genelement-claim vl-parse-genloop        vl-genelement-p)
      ,(vl-genelement-claim vl-parse-genif          vl-genelement-p)
      ,(vl-genelement-claim vl-parse-gencase        vl-genelement-p)
      ,(vl-genelement-claim vl-parse-gencaselist    (lambda (val)
                                                      (and (consp val)
                                                           (vl-gencaselist-p (car val))
                                                           (iff (vl-generateblock-p (cdr val))
                                                                (cdr val)))))
      :hints ('(:do-not '(preprocess))
              (flag::expand-calls-computed-hint
               acl2::clause
               ',(flag::get-clique-members 'vl-parse-genelement-fn (w state)))
              (and stable-under-simplificationp
                   '(:do-not nil)))))

  (verify-guards vl-parse-genelement-fn
    :guard-debug t))


(defines vl-genelement-findbad
  :parents (vl-genelement)
  :short "Find the first occurrence of any @(see vl-genelement) that isn't
among the listed types."
  :long "<p>This is useful for reusing the generic element parsing code in
contexts where some of the items aren't allowed.</p>"

  (define vl-genelement-findbad ((x       vl-genelement-p)
                                 (allowed symbol-listp))
    :measure (vl-genelement-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (b* ((x (vl-genelement-fix x)))
      (vl-genelement-case x
        :vl-genloop (if (member :vl-generate allowed)
                        (vl-generateblock-findbad x.genblock allowed)
                      x)
        :vl-genif   (if (member :vl-generate allowed)
                        (or (vl-generateblock-findbad x.then allowed)
                            (vl-generateblock-findbad x.else allowed))
                      x)
        :vl-gencase (if (member :vl-generate allowed)
                        (or (vl-gencaselist-findbad x.cases allowed)
                            (vl-generateblock-findbad x.default allowed))
                      x)
        :vl-genbase (if (member (tag x.item) allowed)
                        nil
                      x))))

  (define vl-genelementlist-findbad ((x vl-genelementlist-p)
                                     (allowed symbol-listp))
    :measure (vl-genelementlist-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (if (atom x)
        nil
      (or (vl-genelement-findbad (car x) allowed)
          (vl-genelementlist-findbad (cdr x) allowed))))

  (define vl-gencaselist-findbad ((x vl-gencaselist-p)
                                  (allowed symbol-listp))
    :measure (vl-gencaselist-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x))
          nil)
         ((cons (cons ?expr block) rest) x))
      (or (vl-generateblock-findbad block allowed)
          (vl-gencaselist-findbad rest allowed))))

  (define vl-generateblock-findbad ((x vl-generateblock-p)
                                    (allowed symbol-listp))
    :measure (vl-generateblock-count x)
    :guard (subsetp-equal allowed (cons :vl-generate *vl-modelement-tagnames*))
    :returns (firstbad (iff (vl-genelement-p firstbad) firstbad))
    (b* (((vl-generateblock x)))
      (vl-genelementlist-findbad x.elems allowed))))
