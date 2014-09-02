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
(include-book "../../mlib/context")  ;; vl-modelement-p, sorting modelements
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
  (seqw tokens warnings
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
  (seqw tokens pstate
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
  (seqw tokens pstate
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
  (seqw tokens pstate
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
  (seqw tokens pstate
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
  (seqw tokens pstate
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
  (if (not (consp tokens))
      (vl-parse-error "Unexpected EOF.")
    (seqw tokens pstate
          (:= (vl-parse-warning :vl-warn-specify
                                (cat "Specify blocks are not yet implemented.  "
                                     "Instead, we are simply ignoring everything "
                                     "until 'endspecify'.")))
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
  (seqw tokens pstate
        (:= (vl-parse-warning :vl-warn-genvar
                              (cat "Genvar declarations are not implemented, we are just skipping this genvar.")))
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

(defparser vl-parse-loop-generate-construct (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (declare (ignore atts))
  (vl-unimplemented))

(defparser vl-parse-conditional-generate-construct (atts)
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

(local (defthm vl-modelement-p-when-vl-blockitem-p
         (implies (vl-blockitem-p x)
                  (vl-modelement-p x))
         :hints(("Goal" :in-theory (enable vl-blockitem-p)))))

(local (defthm vl-modelementlist-p-when-vl-blockitemlist-p
         (implies (vl-blockitemlist-p x)
                  (vl-modelementlist-p x))
         :hints(("Goal" :induct (len x)))))


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
  (defparser vl-parse-modelement-aux (atts)
    (declare (xargs :guard-hints (("goal" :in-theory (enable vl-is-token?)))))
    :result (vl-modelementlist-p val)
    :guard (vl-atts-p atts)
    :resultp-of-nil t
    :true-listp t
    :fails gracefully
    :count strong
    (b* (((when (atom tokens))
          (vl-parse-error "Unexpected EOF."))
         (type1 (vl-token->type (car tokens)))
         ((when (member-eq type1 *vl-directions-kwds*))
          (seqw tokens pstate
                ((portdecls . netdecls) := (vl-parse-port-declaration-noatts atts))
                (:= (vl-match-token :vl-semi))
                ;; Should be fewer netdecls so this is the better order for the append.
                (return (append netdecls portdecls))))
         ((when (eq type1 :vl-kwd-specify))
          (if atts
              (vl-parse-error "'specify' is not allowed to have attributes.")
            (vl-parse-specify-block)))
         ((when (eq type1 :vl-kwd-parameter))
          (seqw tokens pstate
                ;; localparams are handled in parse-module-or-generate-item
                (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-parameter)))
                (:= (vl-match-token :vl-semi))
                (return ret)))
         ((when (eq type1 :vl-kwd-specparam))
          (vl-parse-specparam-declaration atts))
         ((when (member type1 *vl-netdecltypes-kwds*))
          (seqw tokens pstate
                ((assigns . decls) := (vl-parse-net-declaration atts))
                ;; Note: this order is important, the decls have to come first
                ;; or we'll try to infer implicit nets from the assigns.
                (return (append decls assigns))))
         ((when (member type1 *vl-gate-type-keywords*))
          (vl-parse-gate-instantiation atts))
         ((when (eq type1 :vl-kwd-genvar))
          (vl-parse-genvar-declaration atts))
         ((when (eq type1 :vl-kwd-task))
          (seqw tokens pstate
                (task := (vl-parse-task-declaration atts))
                (return (list task))))
         ((when (eq type1 :vl-kwd-function))
          (seqw tokens pstate
                (fun := (vl-parse-function-declaration atts))
                (return (list fun))))
         ((when (eq type1 :vl-kwd-localparam))
          (seqw tokens pstate
                ;; Note: non-local parameters not allowed
                (ret := (vl-parse-param-or-localparam-declaration atts '(:vl-kwd-localparam)))
                (:= (vl-match-token :vl-semi))
                (return ret)))
         ((when (eq type1 :vl-kwd-defparam))
          (vl-parse-parameter-override atts))
         ((when (eq type1 :vl-kwd-assign))
          (vl-parse-continuous-assign atts))
         ((when (eq type1 :vl-idtoken))
          (vl-parse-udp-or-module-instantiation atts))
         ((when (eq type1 :vl-kwd-initial))
          (vl-parse-initial-construct atts))
         ((when (eq type1 :vl-kwd-always))
          (vl-parse-always-construct atts))

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
          (seqw tokens pstate
                (typedef := (vl-parse-type-declaration atts))
                (return (list typedef))))

         ((when (eq type1 :vl-kwd-modport))
          (seqw tokens pstate
                (modports := (vl-parse-modport-decl atts))
                (return modports)))

         ((when (eq type1 :vl-kwd-alias))
          (seqw tokens pstate
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
  (seqw tokens warnings
        (atts := (vl-parse-0+-attribute-instances))
        (return-raw
         (vl-parse-modelement-aux atts))))


(defparser vl-parse-modelements ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count weak
  (declare (xargs :ruler-extenders :lambdas))
  (seqw-backtrack tokens pstate
                  ((first := (vl-parse-modelement))
                   (rest := (vl-parse-modelements))
                   (return (append first rest)))
                  ((return nil))))





(defparser vl-parse-module-item (atts)
  :guard (vl-atts-p atts)
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  :hint-chicken-switch t
  (cond ((vl-is-token? :vl-kwd-generate)
         (if atts
             (vl-parse-error "'generate' is not allowed to have attributes.")
           (vl-parse-generate-region)))
        ((vl-is-token? :vl-kwd-specify)
         (if atts
             (vl-parse-error "'specify' is not allowed to have attributes.")
           (vl-parse-specify-block)))
        
        (t
         (vl-parse-module-or-generate-item atts))))

(defparser vl-parse-module-item ()
  :result (vl-modelementlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens pstate
        (atts := (vl-parse-0+-attribute-instances))
        (when (vl-is-some-token? *vl-directions-kwds*)
          ((portdecls . netdecls) := (vl-parse-port-declaration-noatts atts))
          (:= (vl-match-token :vl-semi))
          ;; Should be fewer netdecls so this is the better order for the append.
          (return (append netdecls portdecls)))
        (ret := (vl-parse-non-port-module-item atts))
        (return ret)))
