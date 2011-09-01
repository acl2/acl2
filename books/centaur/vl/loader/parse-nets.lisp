; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "parse-ranges")
(include-book "parse-lvalues")
(include-book "parse-delays")
(include-book "parse-strengths")
(local (include-book "../util/arithmetic"))

;; BOZO some of these are expensive; consider backchain limits.
(local (in-theory (disable consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr)))


; net_type ::= supply0 | supply1 | tri | triand | trior | tri0 | tri1
;            | uwire | wire | wand | wor

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

(defparser vl-parse-optional-nettype (tokens warnings)
  :result (vl-maybe-netdecltype-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (seqw tokens warnings
        (when (vl-is-some-token? *vl-nettypes-kwds*)
          (type := (vl-match-some-token *vl-nettypes-kwds*)))
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

(defparser vl-parse-netdecltype (tokens warnings)
  :result (consp val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (ret := (vl-match-some-token *vl-netdecltype-kwd-types*))
        (return (cons (cdr (assoc-eq (vl-token->type ret) *vl-netdecltypes-kwd-alist*))
                      (vl-token->loc ret)))))

(defthm vl-netdecltype-p-of-vl-parse-netdecltype
  (implies (not (mv-nth 0 (vl-parse-netdecltype)))
           (vl-netdecltype-p (car (mv-nth 1 (vl-parse-netdecltype)))))
  :hints(("Goal" :in-theory (enable vl-parse-netdecltype))))

(defthm vl-location-p-of-vl-parse-netdecltype
  (implies (and (not (mv-nth 0 (vl-parse-netdecltype)))
                (force (vl-tokenlist-p tokens)))
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

(defparser vl-parse-list-of-net-assignments (tokens warnings)
  ;; Returns a list of (lvalue . expr) pairs
  :result (and (alistp val)
               (vl-exprlist-p (strip-cars val))
               (vl-exprlist-p (strip-cdrs val)))
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-assignment))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-net-assignments)))
        (return (cons first rest))))

(defund vl-build-assignments (loc pairs strength delay atts)
  (declare (xargs :guard (and (vl-location-p loc)
                              (alistp pairs)
                              (vl-exprlist-p (strip-cars pairs))
                              (vl-exprlist-p (strip-cdrs pairs))
                              (vl-maybe-gatestrength-p strength)
                              (vl-maybe-gatedelay-p delay)
                              (vl-atts-p atts))))
  (if (consp pairs)
      (cons (make-vl-assign :loc loc
                            :lvalue (caar pairs)
                            :expr (cdar pairs)
                            :strength strength
                            :delay delay
                            :atts atts)
            (vl-build-assignments loc (cdr pairs) strength delay atts))
    nil))

(defthm vl-assignlist-p-of-vl-build-assignments
  (implies (and (force (vl-location-p loc))
                (force (alistp pairs))
                (force (vl-exprlist-p (strip-cars pairs)))
                (force (vl-exprlist-p (strip-cdrs pairs)))
                (force (vl-maybe-gatestrength-p strength))
                (force (vl-maybe-gatedelay-p delay))
                (force (vl-atts-p atts)))
           (vl-assignlist-p (vl-build-assignments loc pairs strength delay atts)))
  :hints(("Goal" :in-theory (enable vl-build-assignments))))

(encapsulate
 ()
 (local (in-theory (enable vl-maybe-gatedelay-p vl-maybe-gatestrength-p)))
 (defparser vl-parse-continuous-assign (atts tokens warnings)
   :guard (vl-atts-p atts)
   :result (vl-assignlist-p val)
   :true-listp t
   :resultp-of-nil t
   :fails gracefully
   :count strong
   (seqw tokens warnings
         (assignkwd := (vl-match-token :vl-kwd-assign))
         (when (vl-is-token? :vl-lparen)
           (strength := (vl-parse-drive-strength-or-charge-strength)))
         (when (vl-cstrength-p strength)
           (return-raw
            (vl-parse-error "Assign statement illegally contains a charge strength.")))
         (when (vl-is-token? :vl-pound)
           (delay := (vl-parse-delay3)))
         (pairs := (vl-parse-list-of-net-assignments))
         (semi := (vl-match-token :vl-semi))
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

(defparser vl-parse-list-of-net-decl-assignments (tokens warnings)
  ;; Matches: identifier '=' expression { ',' identifier '=' expression }
  ;; Returns: a list of (idtoken . expr) pairs
  :result (and (alistp val)
               (vl-idtoken-list-p (strip-cars val))
               (vl-exprlist-p (strip-cdrs val)))
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (:= (vl-match-token :vl-equalsign))
        (expr := (vl-parse-expression))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-net-decl-assignments)))
        (return (cons (cons id expr) rest))))

(defparser vl-parse-list-of-net-identifiers (tokens warnings)
  ;; Matches: identifier { range } { ',' identifier { range } }
  ;; Returns: a list of (idtoken . range-list) pairs
  :result (and (alistp val)
               (vl-idtoken-list-p (strip-cars val))
               (vl-rangelist-list-p (strip-cdrs val)))
  :true-listp t
  :resultp-of-nil t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (id := (vl-match-token :vl-idtoken))
        (ranges := (vl-parse-0+-ranges))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match-token :vl-comma))
          (rest := (vl-parse-list-of-net-identifiers)))
        (return (cons (cons id ranges) rest))))



(defund vl-build-netdecls (loc pairs type range atts vectoredp scalaredp signedp delay cstrength)
  (declare (xargs :guard (and (vl-location-p loc)
                              (alistp pairs)
                              (vl-idtoken-list-p (strip-cars pairs))
                              (vl-rangelist-list-p (strip-cdrs pairs))
                              (vl-netdecltype-p type)
                              (vl-maybe-range-p range)
                              (vl-atts-p atts)
                              (booleanp vectoredp)
                              (booleanp scalaredp)
                              (booleanp signedp)
                              (vl-maybe-gatedelay-p delay)
                              (vl-maybe-cstrength-p cstrength))))
  (if (consp pairs)
      (cons (make-vl-netdecl :loc loc
                             :name (vl-idtoken->name (caar pairs))
                             :type type
                             :range range
                             :arrdims (cdar pairs)
                             :atts atts
                             :vectoredp vectoredp
                             :scalaredp scalaredp
                             :signedp signedp
                             :delay delay
                             :cstrength cstrength)
            (vl-build-netdecls loc (cdr pairs) type range atts
                               vectoredp scalaredp signedp delay cstrength))
    nil))

(defthm vl-netdecllist-p-of-vl-build-netdecls
  (implies (and (force (vl-location-p loc))
                (force (alistp pairs))
                (force (vl-idtoken-list-p (strip-cars pairs)))
                (force (vl-rangelist-list-p (strip-cdrs pairs)))
                (force (vl-netdecltype-p type))
                (force (vl-maybe-range-p range))
                (force (vl-atts-p atts))
                (force (booleanp vectoredp))
                (force (booleanp scalaredp))
                (force (booleanp signedp))
                (force (vl-maybe-gatedelay-p delay))
                (force (vl-maybe-cstrength-p cstrength)))
           (vl-netdecllist-p (vl-build-netdecls loc pairs type range atts vectoredp
                                                scalaredp signedp delay
                                                cstrength)))
  :hints(("Goal" :in-theory (enable vl-build-netdecls))))









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

(defund vl-atomify-assignpairs (x)
  (declare (xargs :guard (and (alistp x)
                              (vl-idtoken-list-p (strip-cars x))
                              (vl-exprlist-p (strip-cdrs x)))))
  (if (consp x)
      (cons (cons (make-vl-atom
                   :guts (make-vl-id :name (vl-idtoken->name (caar x))))
                  (cdar x))
            (vl-atomify-assignpairs (cdr x)))
    nil))

(defthm alistp-of-vl-atomify-assignpairs
  (alistp (vl-atomify-assignpairs x))
  :hints(("Goal" :in-theory (enable vl-atomify-assignpairs))))

(defthm vl-exprlist-p-of-strip-cars-of-vl-atomify-assignpairs
  (implies (force (vl-idtoken-list-p (strip-cars x)))
           (vl-exprlist-p (strip-cars (vl-atomify-assignpairs x))))
  :hints(("Goal" :in-theory (enable vl-atomify-assignpairs))))

(defthm vl-exprlist-p-of-strip-cdrs-of-vl-atomify-assignpairs
  (implies (force (vl-exprlist-p (strip-cdrs x)))
           (vl-exprlist-p (strip-cdrs (vl-atomify-assignpairs x))))
  :hints(("Goal" :in-theory (enable vl-atomify-assignpairs))))



(defund vl-netdecls-error (type cstrength gstrength vectoredp scalaredp range assigns)
  ;; Semantic checks for okay net declarations.  These were part of
  ;; vl-parse-net-declaration before, but now I pull them out to reduce the
  ;; number of cases in its proofs.
  (declare (xargs :guard t))
  (cond ((and (not (eq type :vl-trireg)) cstrength)
         "A non-trireg net illegally has a charge strength.")
        ((and vectoredp (not range))
         "A range-free net is illegally declared 'vectored'.")
        ((and scalaredp (not range))
         "A range-free net is illegally declared 'scalared'.")
        ((and (not assigns) gstrength)
         "A drive strength has been given to a net declaration, but is only
          valid on assignments.")
        (t
         nil)))

(defparser vl-parse-net-declaration-aux (tokens warnings)
  ;; Matches either a list_of_net_identifiers or a list_of_decl_assignments.
  :result (and (consp val)
               ;; Assignpairs
               (alistp (car val))
               (vl-exprlist-p (strip-cars (car val)))
               (vl-exprlist-p (strip-cdrs (car val)))
               ;; Declpairs
               (alistp (cdr val))
               (vl-idtoken-list-p (strip-cars (cdr val)))
               (vl-rangelist-list-p (strip-cdrs (cdr val))))
  :fails gracefully
  :count strong
  (seqw tokens warnings
        ;; Assignsp is t when this is a list_of_net_decl_assignments.  We detect
        ;; this by looking ahead to see if an equalsign follows the first
        ;; identifier in the list.
        (assignsp := (if (and (consp tokens)
                              (vl-is-token? :vl-equalsign (cdr tokens)))
                         (mv nil t tokens warnings)
                       (mv nil nil tokens warnings)))
        (pairs := (if assignsp
                      (vl-parse-list-of-net-decl-assignments)
                    (vl-parse-list-of-net-identifiers)))
        (return
         (cons (vl-atomify-assignpairs (if assignsp pairs nil))
               (if assignsp (pairlis$ (strip-cars pairs) nil) pairs)))))






(local (in-theory (disable ;args-exist-when-unary-op
                           ;args-exist-when-binary-op
                           ;args-exist-when-ternary-op
                           VL-PARSE-DRIVE-STRENGTH-OR-CHARGE-STRENGTH-FORWARD
                           subsetp-equal-when-not-consp)))




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

(defparser vl-parse-net-declaration (atts tokens warnings)

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
                (vl-netdecllist-p (cdr val)))
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

   (seqw tokens warnings
         ((type . loc) := (vl-parse-netdecltype))
         (when (vl-is-token? :vl-lparen)
           (strength := (vl-parse-drive-strength-or-charge-strength)))
         (when (vl-is-some-token? '(:vl-kwd-vectored :vl-kwd-scalared))
           (rtype := (vl-match-some-token '(:vl-kwd-vectored :vl-kwd-scalared))))
         (when (vl-is-token? :vl-kwd-signed)
           (signed := (vl-match-token :vl-kwd-signed)))
         (when (vl-is-token? :vl-lbrack)
           (range := (vl-parse-range)))
         (when (vl-is-token? :vl-pound)
           (delay := (vl-parse-delay3)))
         ((assignpairs . declpairs) := (vl-parse-net-declaration-aux))
         (semi := (vl-match-token :vl-semi))
         (return-raw
          (let* ((vectoredp   (vl-is-token-of-type-p rtype :vl-kwd-vectored))
                 (scalaredp   (vl-is-token-of-type-p rtype :vl-kwd-scalared))
                 (signedp     (if signed t nil))
                 (gstrength   (vl-disabled-gstrength strength))
                 (cstrength   (vl-disabled-cstrength strength))

; Subtle!  See the documentation for vl-netdecl-p and vl-assign-p.  If there
; are assignments, then the delay is ONLY about the assignments and NOT to
; be given to the decls.

                 (assigns     (vl-build-assignments loc assignpairs gstrength delay atts))
                 (decls       (vl-build-netdecls loc declpairs type range atts vectoredp
                                                 scalaredp signedp
                                                 (if assignpairs nil delay)
                                                 cstrength))

                 (errorstr    (vl-netdecls-error type cstrength gstrength
                                                 vectoredp scalaredp range
                                                 assignpairs)))
            (if errorstr
                (vl-parse-error errorstr)
              (mv nil (cons assigns decls) tokens warnings))))))

(with-output
 :gag-mode :goals
 (verify-guards vl-parse-net-declaration-fn))

(with-output
 :gag-mode :goals
 (defthm true-listp-of-vl-parse-net-declaration-assigns
   (true-listp (car (mv-nth 1 (vl-parse-net-declaration atts))))
   :rule-classes (:type-prescription)
   :hints(("Goal" :in-theory (enable vl-parse-net-declaration)))))

(with-output
 :gag-mode :goals
 (defthm true-listp-of-vl-parse-net-declaration-decls
   (true-listp (cdr (mv-nth 1 (vl-parse-net-declaration atts))))
   :rule-classes (:type-prescription)
   :hints(("Goal" :in-theory (enable vl-parse-net-declaration)))))



(local
 (encapsulate
  ()

  (local (include-book "lexer"))

  (program)

  (defun test-assign-aux (assigns lvalues exprs str rise fall high atts)
    (if (atom assigns)
        (debuggable-and (atom lvalues)
                        (atom exprs))
      (debuggable-and
       (consp lvalues)
       (consp exprs)
       (not (cw "Inspecting ~x0.~%" (car assigns)))
       (not (cw "Lvalue: ~x0.~%" (car lvalues)))
       (not (cw "Expr: ~x0.~%" (car exprs)))
       (vl-assign-p (car assigns))
       (equal (car lvalues) (vl-pretty-expr (vl-assign->lvalue (car assigns))))
       (equal (car exprs) (vl-pretty-expr (vl-assign->expr (car assigns))))
       (equal str (vl-assign->strength (car assigns)))
       (equal atts (vl-assign->atts (car assigns)))
       (equal rise (and (vl-assign->delay (car assigns))
                        (vl-pretty-expr (vl-gatedelay->rise (vl-assign->delay (car assigns))))))
       (equal fall (and (vl-assign->delay (car assigns))
                        (vl-pretty-expr (vl-gatedelay->fall (vl-assign->delay (car assigns))))))
       (equal high (and (vl-assign->delay (car assigns))
                        (vl-gatedelay->high (vl-assign->delay (car assigns)))
                        (vl-pretty-expr (vl-gatedelay->high (vl-assign->delay (car assigns))))))
       (test-assign-aux (cdr assigns) (cdr lvalues) (cdr exprs)
                        str rise fall high atts))))

  (defmacro test-assign (&key input lvalues exprs str rise fall high atts (successp 't))
    `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                (mv-let (erp val tokens warnings)
                        (vl-parse-continuous-assign ',atts tokens nil)
                        (declare (ignorable tokens warnings))
                        (if erp
                            (prog2$ (cw "ERP: ~x0.~%" erp)
                                    (not ,successp))
                          (debuggable-and
                           ,successp
                           (test-assign-aux val ',lvalues ',exprs ,str ',rise ',fall ',high ',atts)))))))

  (test-assign :input "assign w = 1 ; "
               :lvalues ((id "w"))
               :exprs   (1)
               :atts (("some") ("atts"))
               :str nil
               :rise nil
               :fall nil
               :high nil)

  (test-assign :input "assign w = 1, v = 2 ; "
               :lvalues ((id "w") (id "v"))
               :exprs   (1        2)
               :atts (("some") ("atts"))
               :str nil
               :rise nil
               :fall nil
               :high nil)

  (test-assign :input "assign {x, y, z} = 1, v = 2 ; "
               :lvalues ((:vl-concat nil (id "x") (id "y") (id "z"))
                         (id "v"))
               :exprs   (1 2)
               :atts (("some") ("atts"))
               :str nil
               :rise nil
               :fall nil
               :high nil)

  (test-assign :input "assign #36 a[0] = 1 ; "
               :lvalues ((:vl-bitselect nil (id "a") 0))
               :exprs   (1)
               :atts (("some") ("atts"))
               :str nil
               :rise 36
               :fall 36
               :high 36)

  (test-assign :input "assign (small) #36 a[0] = 1 ; "
               :successp nil)

  (test-assign :input "assign (strong0, pull1) #36 a[7:0] = 1 ; "
               :lvalues ((:vl-partselect-colon nil (id "a") 7 0))
               :exprs   (1)
               :atts (("some") ("atts"))
               :str (make-vl-gatestrength :zero :vl-strong
                                          :one :vl-pull)
               :rise 36
               :fall 36
               :high 36)

  (test-assign :input "assign #36 (strong0, pull1) a[7:0] = 1 ; "
               :successp nil)

  (test-assign :input "assign #(5,10,1:2:3) w = 1, v = 2, a = w & v ; "
               :lvalues ((id "w") (id "v") (id "a"))
               :exprs   (1        2        (:vl-binary-bitand nil (id "w") (id "v")))
               :atts (("some") ("atts"))
               :str nil
               :rise 5
               :fall 10
               :high (:vl-mintypmax nil 1 2 3))




  (defun test-decls-aux (decls ids type range arrdims vectoredp scalaredp signedp rise
                               fall high cstrength)
    (if (atom decls)
        (debuggable-and (not arrdims)
                        (not ids))
      (debuggable-and
       (consp arrdims)
       (consp ids)
       (not (cw "Inspecting Decl: ~x0.~%" (car decls)))
       (vl-netdecl-p (car decls))
       (equal (car ids) (vl-netdecl->name (car decls)))
       (equal type (vl-netdecl->type (car decls)))
       (equal range (vl-pretty-maybe-range (vl-netdecl->range (car decls))))
       (equal (car arrdims) (vl-pretty-range-list (vl-netdecl->arrdims (car decls))))
       (equal vectoredp (vl-netdecl->vectoredp (car decls)))
       (equal scalaredp (vl-netdecl->scalaredp (car decls)))
       (equal signedp (vl-netdecl->signedp (car decls)))
       (equal rise (and (vl-netdecl->delay (car decls))
                        (vl-pretty-expr (vl-gatedelay->rise (vl-netdecl->delay (car decls))))))
       (equal fall (and (vl-netdecl->delay (car decls))
                        (vl-pretty-expr (vl-gatedelay->fall (vl-netdecl->delay (car decls))))))
       (equal high (and (vl-netdecl->delay (car decls))
                        (vl-gatedelay->high (vl-netdecl->delay (car decls)))
                        (vl-pretty-expr (vl-gatedelay->high (vl-netdecl->delay (car decls))))))
       (equal cstrength (vl-netdecl->cstrength (car decls)))
       (test-decls-aux (cdr decls) (cdr ids)  type range (cdr arrdims) vectoredp scalaredp
                       signedp rise fall high cstrength))))

  (defmacro test-netdecl (&key input atts
                               ;; stuff for assignments
                               lvalues exprs str assign-rise assign-fall assign-high
                               ;; stuff for decl parts
                               ids type range arrdims vectoredp scalaredp signedp decl-rise decl-fall decl-high cstrength
                               (successp 't))
    `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                (mv-let (erp val tokens warnings)
                        (vl-parse-net-declaration ',atts tokens nil)
                        (declare (ignorable tokens warnings))
                        (if erp
                            (prog2$ (cw "ERP: ~x0.~%" erp)
                                    (not ,successp))
                          (debuggable-and
                           ,successp
                           (implies (not (car val))
                                    (debuggable-and (not ',lvalues)
                                                    (not ',exprs)))
                           (test-assign-aux (car val) ',lvalues ',exprs ,str ',assign-rise ',assign-fall ',assign-high ',atts)
                           (test-decls-aux (cdr val) ',ids ',type ',range ',arrdims ',vectoredp
                                           ',scalaredp ',signedp ',decl-rise ',decl-fall ',decl-high
                                           ',cstrength)))))))

  (test-netdecl :input "wire w ; "
                :ids ("w")
                :lvalues nil
                :exprs nil
                :str nil
                :assign-rise nil
                :assign-fall nil
                :assign-high nil
                :decl-rise nil
                :decl-fall nil
                :decl-high nil
                :type :vl-wire
                :atts (("some") ("atts"))
                :arrdims (nil)
                :range (no-range)
                :vectoredp nil
                :scalaredp nil
                :signedp nil
                :cstrength nil)

  (test-netdecl :input "triand signed w1, w2 ; "
                :ids ("w1" "w2")
                :lvalues nil
                :exprs nil
                :str nil
                :assign-rise nil
                :assign-fall nil
                :assign-high nil
                :decl-rise nil
                :decl-fall nil
                :decl-high nil
                :type :vl-triand
                :atts (("some") ("atts"))
                :arrdims (nil nil)
                :range (no-range)
                :vectoredp nil
                :scalaredp nil
                :signedp t
                :cstrength nil)

  (test-netdecl :input "wor scalared [4:0] #(3, 4, 5) w1, w2 ; "
                :ids ("w1" "w2")
                :lvalues nil
                :exprs nil
                :str nil
                ;; This delay is for the decls, since there are no assigns.
                :assign-rise nil
                :assign-fall nil
                :assign-high nil
                :decl-rise 3
                :decl-fall 4
                :decl-high 5
                :type :vl-wor
                :atts (("some") ("atts"))
                :arrdims (nil nil)
                :range (range 4 0)
                :vectoredp nil
                :scalaredp t
                :signedp nil
                :cstrength nil)

  (test-netdecl :input "uwire vectored signed [4:0] #3 w1 [3:0][4:1][5:2], w2 ; "
                :ids ("w1" "w2")
                :lvalues nil
                :exprs nil
                :str nil
                ;; This delay is for the decls, since there are no assigns.
                :assign-rise nil
                :assign-fall nil
                :assign-high nil
                :decl-rise 3
                :decl-fall 3
                :decl-high 3
                :type :vl-uwire
                :atts (("some") ("atts"))
                :arrdims (((range 3 0) (range 4 1) (range 5 2)) nil)
                :range (range 4 0)
                :vectoredp t
                :scalaredp nil
                :signedp t
                :cstrength nil)

  ;; Need a semicolon
  (test-netdecl :input "wire w1 "
                :successp nil)

  ;; Not allowed to use vectored without a range.
  (test-netdecl :input "wire vectored signed w1 [3:0][4:1][5:2], w2 ; "
                :successp nil)

  ;; Not allowed to use scalared without a range
  (test-netdecl :input "wire scalared w1; "
                :successp nil)

  ;; Not allowed to have a charge strength on a non-trireg
  (test-netdecl :input "wire (small) w ; "
                :successp nil)

  ;; Not allowed to have a strength without assignments
  (test-netdecl :input "wire (supply0, pull1) w1; "
                :successp nil)

  (test-netdecl :input "trireg (small) w ; "
                :ids ("w")
                :lvalues nil
                :exprs nil
                :str nil
                :decl-rise nil
                :decl-fall nil
                :decl-high nil
                :assign-rise nil
                :assign-fall nil
                :assign-high nil
                :type :vl-trireg
                :atts (("some") ("atts"))
                :arrdims (nil)
                :range (no-range)
                :vectoredp nil
                :scalaredp nil
                :signedp nil
                :cstrength :vl-small)

  (test-netdecl :input "wire w = 1 ; "
                :ids ("w")
                :lvalues ((id "w"))
                :exprs   (1)
                :str nil
                :decl-rise nil
                :decl-fall nil
                :decl-high nil
                :assign-rise nil
                :assign-fall nil
                :assign-high nil
                :type :vl-wire
                :atts (("some") ("atts"))
                :arrdims (nil)
                :range (no-range)
                :vectoredp nil
                :scalaredp nil
                :signedp nil
                :cstrength nil)

  ;; no arrays with assignments
  (test-netdecl :input "wire w [1] = 1 ; "
                :successp nil)

  ;; no mixing assignments and plain decls
  (test-netdecl :input "wire w, a = 1 ; "
                :successp nil)

  (test-netdecl :input "wire (supply1,strong0) vectored signed [4:0] #(3) w1 = 1, w2 = 2 ; "
                :ids ("w1" "w2")
                :lvalues ((id "w1") (id "w2"))
                :exprs   (1 2)
                :str (make-vl-gatestrength :zero :vl-strong
                                           :one :vl-supply)
                ;; The delay is for the assignments, since there are assignments.
                :assign-rise 3
                :assign-fall 3
                :assign-high 3
                :decl-rise nil
                :decl-fall nil
                :decl-high nil
                :type :vl-wire
                :atts (("some") ("atts"))
                :arrdims (nil nil)
                :range (range 4 0)
                :vectoredp t
                :scalaredp nil
                :signedp t
                :cstrength nil)))
