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
(include-book "datatypes")
(include-book "lvalues")
(include-book "delays")
(include-book "strengths")
(local (include-book "../../util/arithmetic"))

;; BOZO some of these are expensive; consider backchain limits.
(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           acl2::consp-when-member-equal-of-cons-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr)))


; net_type ::= supply0 | supply1 | tri | triand | trior | tri0 | tri1
;            | uwire | wire | wand | wor


;; BOZO SystemVerilog adds trireg as a valid net_type.  We aren't accounting
;; for this correctly.

(defconst *vl-nettypes-kwd-alist*
  '((:vl-kwd-wire    . :vl-wire)    ; we put wire first since it's most common
    (:vl-kwd-supply0 . :vl-supply0)
    (:vl-kwd-supply1 . :vl-supply1)
    (:vl-kwd-tri     . :vl-tri)
    (:vl-kwd-triand  . :vl-triand)
    (:vl-kwd-trior   . :vl-trior)
    (:vl-kwd-tri0    . :vl-tri0)
    (:vl-kwd-tri1    . :vl-tri1)
    (:vl-kwd-uwire   . :vl-uwire)
    (:vl-kwd-wand    . :vl-wand)
    (:vl-kwd-wor     . :vl-wor)))

(defconst *vl-nettypes-kwds*
  (strip-cars *vl-nettypes-kwd-alist*))

(defparser vl-parse-optional-nettype ()
  :result (vl-maybe-nettypename-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (seq tokstream
        (when (vl-is-some-token? *vl-nettypes-kwds*)
          (type := (vl-match)))
        (return (and type
                     (cdr (assoc-eq (vl-token->type type)
                                    *vl-nettypes-kwd-alist*))))))



; This is not a real production in the Verilog grammar, but we imagine:
;
; netdecltype ::= net_type | trireg
;
; Which is useful for parsing net declarations, where you can either
; have a net_type or trireg.

(defconst *vl-netdecltypes-kwd-alist*
  (append *vl-nettypes-kwd-alist*
          (list '(:vl-kwd-trireg . :vl-trireg))))

(defconst *vl-netdecltype-kwd-types*
  (strip-cars *vl-netdecltypes-kwd-alist*))

(defparser vl-parse-netdecltype ()
  :result (consp val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (ret := (vl-match-some-token *vl-netdecltype-kwd-types*))
       (return (cons (cdr (assoc-eq (vl-token->type ret) *vl-netdecltypes-kwd-alist*))
                     (vl-token->loc ret)))))

(defthm vl-netdecltype-p-of-vl-parse-netdecltype
  (implies (not (mv-nth 0 (vl-parse-netdecltype)))
           (vl-nettypename-p (car (mv-nth 1 (vl-parse-netdecltype)))))
  :hints(("Goal" :in-theory (enable vl-parse-netdecltype))))

(defthm vl-location-p-of-vl-parse-netdecltype
  (implies (not (mv-nth 0 (vl-parse-netdecltype)))
           (vl-location-p (cdr (mv-nth 1 (vl-parse-netdecltype)))))
  :hints(("Goal" :in-theory (enable vl-parse-netdecltype))))





;                      PARSING CONTINUOUS ASSIGNMENTS
;
; continuous_assign ::=
;    'assign' [drive_strength] [delay3] list_of_net_assignments ';'
;
; list_of_net_assignments ::=
;    net_assignment { ',' net_assignment }
;
; net_assignment ::=
;    lvalue '=' expression

(defparser vl-parse-list-of-net-assignments ()
  ;; Returns a list of (lvalue . expr) pairs
  :result (and (alistp val)
               (vl-exprlist-p (strip-cars val))
               (vl-exprlist-p (strip-cdrs val)))
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seq tokstream
       (first := (vl-parse-assignment))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-list-of-net-assignments)))
       (return (cons first rest))))


(define vl-build-assignments ((loc      vl-location-p)
                              (pairs    (and (alistp pairs)
                                             (vl-exprlist-p (strip-cars pairs))
                                             (vl-exprlist-p (strip-cdrs pairs))))
                              (strength vl-maybe-gatestrength-p)
                              (delay    vl-maybe-gatedelay-p)
                              (atts     vl-atts-p))
  :returns (assigns vl-assignlist-p :hyp :fguard)
  (if (atom pairs)
      nil
    (cons (make-vl-assign :loc loc
                          :lvalue (caar pairs)
                          :expr (cdar pairs)
                          :strength strength
                          :delay delay
                          :atts atts)
          (vl-build-assignments loc (cdr pairs) strength delay atts))))

(encapsulate
  ()
  (local (in-theory (enable vl-maybe-gatedelay-p vl-maybe-gatestrength-p)))
  (defparser vl-parse-continuous-assign (atts)
    :guard (vl-atts-p atts)
    :result (vl-assignlist-p val)
    :true-listp t
    :resultp-of-nil t
    :fails gracefully
    :count strong
    (seq tokstream
         (assignkwd := (vl-match-token :vl-kwd-assign))
         (when (vl-is-token? :vl-lparen)
           (strength := (vl-parse-drive-strength-or-charge-strength)))
         (when (vl-cstrength-p strength)
           (return-raw
            (vl-parse-error "Assign statement illegally contains a charge strength.")))
         (when (vl-is-token? :vl-pound)
           (delay := (vl-parse-delay3)))
         (pairs := (vl-parse-list-of-net-assignments))
         (:= (vl-match-token :vl-semi))
         (return (vl-build-assignments (vl-token->loc assignkwd)
                                       pairs strength delay atts)))))




;                            PARSING NET DECLARATIONS
;
; Pardon the wide column, but it makes this more clear.
;
; net_declaration ::=
;    net_type                                           ['signed']       [delay3] list_of_net_identifiers ';'
;  | net_type                   ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_identifiers ';'
;  | net_type [drive_strength]                          ['signed']       [delay3] list_of_net_decl_assignments ';'
;  | net_type [drive_strength]  ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_decl_assignments ';'
;  | 'trireg' [charge_strength]                         ['signed']       [delay3] list_of_net_identifiers ';'
;  | 'trireg' [charge_strength] ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_identifiers ';'
;  | 'trireg' [drive_strength]                          ['signed']       [delay3] list_of_net_decl_assignments ';'
;  | 'trireg' [drive_strength]  ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_decl_assignments ';'
;
; list_of_net_identifiers ::=
;    identifier { range } { ',' identifier { range } }
;
; list_of_net_decl_assignments ::=
;    net_decl_assignment { ',' net_decl_assignment }
;
; net_decl_assignment ::= identifier '=' expression




(defparser vl-parse-list-of-net-identifiers ()
  ;; Matches: identifier { range } { ',' identifier { range } }
  ;; Returns: a list of (idtoken . range-list) pairs
  :result (and (alistp val)
               (vl-idtoken-list-p (strip-cars val))
               (vl-rangelist-list-p (strip-cdrs val)))
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seq tokstream
       (id := (vl-match-token :vl-idtoken))
       (ranges := (vl-parse-0+-ranges))
       (when (vl-is-token? :vl-comma)
         (:= (vl-match))
         (rest := (vl-parse-list-of-net-identifiers)))
       (return (cons (cons id ranges) rest))))

(define vl-build-netdecls
  ((loc         vl-location-p)
   (x           vl-vardeclassignlist-p)
   (nettype     vl-nettypename-p)
   (type        vl-datatype-p)
   (atts        vl-atts-p)
   (vectoredp   booleanp)
   (scalaredp   booleanp)
   (delay       vl-maybe-gatedelay-p)
   (cstrength   vl-maybe-cstrength-p)
   (gstrength   vl-maybe-gatestrength-p))
  :returns (mv (nets vl-vardecllist-p)
               (assigns vl-assignlist-p))
  :guard-hints (("goal" :in-theory (disable (force))))
  (if (atom x)
      (mv nil nil)
    (b* (((vl-vardeclassign x1) (car x))
         (type (vl-datatype-update-udims x1.dims type))
         (vardecl (make-vl-vardecl :loc loc
                                   :name x1.id
                                   :type type
                                   :nettype nettype
                                   :atts atts
                                   :vectoredp vectoredp
                                   :scalaredp scalaredp
                                   :delay (and (not x1.expr) delay)
                                   :cstrength cstrength))
         (assign (and x1.expr
                      (make-vl-assign :loc loc
                                      :lvalue (vl-idexpr x1.id nil nil)
                                      :expr x1.expr
                                      :strength gstrength
                                      :delay delay
                                      :atts atts)))
         ((mv rest-decls rest-assigns)
          (vl-build-netdecls loc (cdr x) nettype type atts
                             vectoredp scalaredp delay cstrength gstrength)))
      (mv (cons vardecl rest-decls)
          (if assign
              (cons assign rest-assigns)
            rest-assigns))))

  :prepwork
  ((local (defthm l0
            (implies (vl-rangelist-p x)
                     (vl-packeddimensionlist-p x))
            :hints(("Goal" :induct (len x))))))

  ///
  (more-returns
   (nets :name true-listp-of-vl-build-netdecls-nets
         true-listp :rule-classes :type-prescription)
   (assigns :name true-listp-of-vl-build-netdecls-assigns
            true-listp :rule-classes :type-prescription)))



;; (deflist vl-atomlist-p (x)
;;   (vl-atom-p x)
;;   :guard t
;;   :elementp-of-nil nil)

;; (defthm vl-exprlist-p-when-vl-atomlist-p
;;   (implies (vl-atomlist-p x)
;;            (vl-exprlist-p x))
;;   :hints(("Goal" :induct (len x))))

;; (defprojection vl-atomlist-from-vl-idtoken-list (x)
;;   (vl-atom x nil nil)
;;   :guard (vl-idtoken-list-p x)
;;   :nil-preservingp nil)

;; (defthm vl-atomlist-p-of-vl-atomlist-from-vl-idtoken-list
;;   (implies (force (vl-idtoken-list-p x))
;;            (vl-atomlist-p (vl-atomlist-from-vl-idtoken-list x)))
;;   :hints(("Goal" :induct (len x))))

(define vl-atomify-assignpairs ((x (and (alistp x)
                                        (vl-idtoken-list-p (strip-cars x))
                                        (vl-exprlist-p (strip-cdrs x)))))
  (if (atom x)
      nil
    (cons (cons (make-vl-atom
                 :guts (make-vl-id :name (vl-idtoken->name (caar x))))
                (cdar x))
          (vl-atomify-assignpairs (cdr x))))
  ///
  (defthm alistp-of-vl-atomify-assignpairs
    (alistp (vl-atomify-assignpairs x)))

  (defthm vl-exprlist-p-of-strip-cars-of-vl-atomify-assignpairs
    (implies (force (vl-idtoken-list-p (strip-cars x)))
             (vl-exprlist-p (strip-cars (vl-atomify-assignpairs x)))))

  (defthm vl-exprlist-p-of-strip-cdrs-of-vl-atomify-assignpairs
    (implies (force (vl-exprlist-p (strip-cdrs x)))
             (vl-exprlist-p (strip-cdrs (vl-atomify-assignpairs x))))))

(define vl-netdeclassigns-check-array-assigns ((x vl-vardeclassignlist-p))
  ;; Checks that there is no declaration that has both dimensions and an expression.
  (b* (((when (atom x)) nil)
       ((vl-vardeclassign x1) (car x))
       ((when (and x1.dims x1.expr))
        "We don't support the combination of a declaration assignment and unpacked
         dimensions on a net declaration."))
    (vl-netdeclassigns-check-array-assigns (cdr x))))

(define vl-netdeclassigns-characterize ((x vl-vardeclassignlist-p))
  ;; Returns either :all-assigns, :no-assigns, :both, or nil if empty.
  (b* (((when (atom x)) nil)
       ((vl-vardeclassign x1) (car x))
       (rest (vl-netdeclassigns-characterize (cdr x)))
       (first (if x1.expr :all-assigns :no-assigns))
       ((when (or (not rest) (eq first rest))) first))
    :both))

(defund vl-netdecls-error (nettype cstrength gstrength vectoredp scalaredp type delay assigns)
  ;; Semantic checks for okay net declarations.  These were part of
  ;; vl-parse-net-declaration before, but now I pull them out to reduce the
  ;; number of cases in its proofs.
  (declare (xargs :guard (and (vl-datatype-p type)
                              (vl-vardeclassignlist-p assigns))))
  (cond ((and (not (eq nettype :vl-trireg)) cstrength)
         "A non-trireg net illegally has a charge strength.")
        ((and vectoredp (not (vl-datatype->pdims type)))
         "A range-free net is illegally declared 'vectored'.")
        ((and scalaredp (not (vl-datatype->pdims type)))
         "A range-free net is illegally declared 'scalared'.")
        ;; Used to check that a drivestrength was only present if there was an
        ;; assignment.  In ncv, it seems to be an error if at least the first
        ;; decl doesn't have an assignment; in vcs, seems to be an error if not
        ;; all do.

        ((and (or (atom assigns)
                  (not (vl-vardeclassign->expr (car assigns))))
              gstrength)
         "A drive strength has been given to a net declaration, but is only
          valid on assignments.")
        ((vl-netdeclassigns-check-array-assigns assigns))
        ((and delay (eq (vl-netdeclassigns-characterize assigns) :both))
         "A delay has been given to a multiple net declaration where some of the
          nets have assignments and some do not; we don't know what this
          means.  Should the delay be on the nets or the assignments?")
        (t
         nil)))


;; (encapsulate
;;   ()
;;   ;; bozo horrible gross what why??
;;   (local
;;    (defthm crock
;;      (IMPLIES (NOT (CONSP (VL-TOKSTREAM->TOKENS)))
;;               (MV-NTH 0 (VL-PARSE-LIST-OF-NET-IDENTIFIERS)))
;;      :hints(("Goal" :in-theory (enable vl-parse-list-of-net-identifiers)))))

;;   (local
;;    (defthm crock2
;;      (IMPLIES (NOT (CONSP (VL-TOKSTREAM->TOKENS)))
;;               (NOT (CONSP (vl-tokstream->tokens :tokstream (MV-NTH 2 (VL-PARSE-LIST-OF-NET-IDENTIFIERS))))))
;;      :hints(("Goal" :in-theory (enable vl-match-token
;;                                        vl-parse-list-of-net-identifiers)))))

;;   (defparser vl-parse-net-declaration-aux ()
;;     ;; Matches either a list_of_net_identifiers or a list_of_decl_assignments.
;;     :result (and (consp val)
;;                  ;; Assignpairs
;;                  (alistp (car val))
;;                  (vl-exprlist-p (strip-cars (car val)))
;;                  (vl-exprlist-p (strip-cdrs (car val)))
;;                  ;; Declpairs
;;                  (alistp (cdr val))
;;                  (vl-idtoken-list-p (strip-cars (cdr val)))
;;                  (vl-rangelist-list-p (strip-cdrs (cdr val))))
;;     :fails gracefully
;;     :count strong
;;     (seq tokstream

;;          (varassigns := (vl-parse-1+-variable-decl-assignments-separated-by-commas))

;;          (return
;;           (cons (vl-atomify-assignpairs (if assignsp pairs nil))
;;                 (if assignsp (pairlis$ (strip-cars pairs) nil) pairs))))))






(local (in-theory (disable ;args-exist-when-unary-op
                           ;args-exist-when-binary-op
                           ;args-exist-when-ternary-op
                           VL-PARSE-DRIVE-STRENGTH-OR-CHARGE-STRENGTH-FORWARD
                           acl2::subsetp-when-atom-left)))


(defund vl-is-token-of-type-p (x type)
  ;; Hides an if from vl-parse-net-declaration.
  (declare (xargs :guard t))
  (and (vl-token-p x)
       (eq (vl-token->type x) type)))

(defund vl-disabled-gstrength (x)
  ;; Hides an if from vl-parse-net-declaration.
  (declare (xargs :guard t))
  (and (vl-gatestrength-p x)
       x))

(defund vl-disabled-cstrength (x)
  ;; Hides an if from vl-parse-net-declaration.
  (declare (xargs :guard t))
  (and (vl-cstrength-p x)
       x))

(defthm vl-maybe-gatestrength-p-of-vl-disabled-gstrength
  (vl-maybe-gatestrength-p (vl-disabled-gstrength x))
  :hints(("Goal" :in-theory (enable vl-disabled-gstrength))))

(defthm vl-maybe-cstrength-p-of-vl-disabled-cstrength
  (vl-maybe-cstrength-p (vl-disabled-cstrength x))
  :hints(("Goal" :in-theory (enable vl-disabled-cstrength))))

(defparser vl-parse-net-declaration-finish (nettype loc strength rtype type atts)
  :guard (and (vl-nettypename-p nettype)
              (vl-location-p loc)
              (or (not strength)
                  (vl-gatestrength-p strength)
                  (vl-cstrength-p strength))
              (or (not rtype) (vl-token-p rtype))
              (vl-datatype-p type)
              (vl-atts-p atts))
  :result (and (consp val)
               (vl-assignlist-p (car val))
               (vl-vardecllist-p (cdr val)))
  :fails gracefully
  :count strong
  (seq tokstream
       (when (vl-is-token? :vl-pound)
         (delay := (vl-parse-delay3)))
       (declassigns := (vl-parse-1+-variable-decl-assignments-separated-by-commas))
       (:= (vl-match-token :vl-semi))
       (return-raw
        (b* ((vectoredp   (vl-is-token-of-type-p rtype :vl-kwd-vectored))
             (scalaredp   (vl-is-token-of-type-p rtype :vl-kwd-scalared))
             (gstrength   (vl-disabled-gstrength strength))
             (cstrength   (vl-disabled-cstrength strength))

; Subtle!  See the documentation for vl-netdecl-p and vl-assign-p.  If there
; are assignments, then the delay is ONLY about the assignments and NOT to
; be given to the decls.

             ((mv decls assigns)
              (vl-build-netdecls loc declassigns nettype type atts vectoredp
                                 scalaredp delay cstrength gstrength))

             (errorstr    (vl-netdecls-error nettype cstrength gstrength
                                             vectoredp scalaredp type delay
                                             declassigns)))
          (if errorstr
              (vl-parse-error errorstr)
            (mv nil (cons assigns decls) tokstream))))))


(local (in-theory (enable vl-parse-drive-strength-or-charge-strength-forward)))

(defparser vl-parse-net-declaration (atts)

; We combine all eight productions for net_declaration into this single
; function.  We do some checks at the end to ensure that we haven't matched
; something more permissive than the grammar
;
; net_declaration ::=
;    net_type                                           ['signed']       [delay3] list_of_net_identifiers ';'
;  | net_type                   ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_identifiers ';'
;  | net_type [drive_strength]                          ['signed']       [delay3] list_of_net_decl_assignments ';'
;  | net_type [drive_strength]  ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_decl_assignments ';'
;  | 'trireg' [charge_strength]                         ['signed']       [delay3] list_of_net_identifiers ';'
;  | 'trireg' [charge_strength] ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_identifiers ';'
;  | 'trireg' [drive_strength]                          ['signed']       [delay3] list_of_net_decl_assignments ';'
;  | 'trireg' [drive_strength]  ['vectored'|'scalared'] ['signed'] range [delay3] list_of_net_decl_assignments ';'
;

  :verify-guards nil ;; takes too long, so we do it afterwards.
  :guard (vl-atts-p atts)
  :result (and (consp val)
               (vl-assignlist-p (car val))
               (vl-vardecllist-p (cdr val)))
  :fails gracefully
  :count strong

; Note.  Historically this function has caused a lot of problems for the
; proofs.  Generally accumulated-persistence has not been very helpful, and the
; problem seems to be something to do with how the cases get expanded out.
;
; During the introduction of the new warnings system, I found that the proofs
; were so slow that I profiled them with (profile-all).  This led to
; discovering that the too-many-ifs function was very slow.  I ended up writing
; a patch to memoize pieces of that, which is now found in too-many-ifs.lisp.
;
; Even so, the proofs were still slow.  It was to fix this that I disabled the
; functions in parse-utils.lisp and proved theorems about them, in an effort to
; hide their ifs from functions like this.
;
; We also disabled the functions above to hide additional ifs.  Finally the
; proofs are getting down to a reasonable time.

  (seq tokstream
       ((nettype . loc) := (vl-parse-netdecltype))
       (when (vl-is-token? :vl-lparen)
         (strength := (vl-parse-drive-strength-or-charge-strength)))
       (when (vl-is-some-token? '(:vl-kwd-vectored :vl-kwd-scalared))
         (rtype := (vl-match)))
       (return-raw
        (b* ((backup (vl-tokstream-save))
             ;; Even though vl-parse-datatype-or-implicit tries both ways, it
             ;; can still be wrong if, e.g., the datatype was supposed to be
             ;; implicit but it instead found something (identifier) that it
             ;; could parse as a datatype.  So we still may need to backtrack
             ;; here.
             ((mv erp type tokstream) (vl-parse-datatype-or-implicit))
             ((when erp) ;; try without parsing any datatype
              (b* ((tokstream (vl-tokstream-restore backup)))
                (vl-parse-net-declaration-finish
                 nettype loc strength rtype (make-vl-coretype :name :vl-logic) atts)))
             ((mv erp decl tokstream)
              (vl-parse-net-declaration-finish
               nettype loc strength rtype type atts))
             ((when erp) ;; try without parsing any datatype
              (b* ((tokstream (vl-tokstream-restore backup)))
                (vl-parse-net-declaration-finish
                 nettype loc strength rtype (make-vl-coretype :name :vl-logic) atts))))
          (mv erp decl tokstream)))))

(with-output
 :gag-mode :goals
 (verify-guards vl-parse-net-declaration-fn))

(with-output
 :gag-mode :goals
 (defthm true-listp-of-vl-parse-net-declaration-finish-assigns
   (true-listp (car (mv-nth 1 (vl-parse-net-declaration-finish
                               nettype loc strength rtype type atts))))
   :rule-classes (:type-prescription)
   :hints(("Goal" :in-theory (enable vl-parse-net-declaration-finish)))))

(with-output
 :gag-mode :goals
 (defthm true-listp-of-vl-parse-net-declaration-assigns
   (true-listp (car (mv-nth 1 (vl-parse-net-declaration atts))))
   :rule-classes (:type-prescription)
   :hints(("Goal" :in-theory (enable vl-parse-net-declaration)))))

(with-output
 :gag-mode :goals
 (defthm true-listp-of-vl-parse-net-declaration-finish-decls
   (true-listp (cdr (mv-nth 1 (vl-parse-net-declaration-finish
                               nettype loc strength rtype type atts))))
   :rule-classes (:type-prescription)
   :hints(("Goal" :in-theory (enable vl-parse-net-declaration-finish)))))

(with-output
 :gag-mode :goals
 (defthm true-listp-of-vl-parse-net-declaration-decls
   (true-listp (cdr (mv-nth 1 (vl-parse-net-declaration atts))))
   :rule-classes (:type-prescription)
   :hints(("Goal" :in-theory (enable vl-parse-net-declaration)))))

