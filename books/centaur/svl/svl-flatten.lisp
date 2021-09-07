; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "type-defs")

(include-book "svex-simplify")

(include-book "svl-flatten-simplify-lemmas")

(local
 (Include-Book "projects/rp-rewriter/proofs/extract-formula-lemmas" :dir :system))

(local
 (Include-Book "projects/rp-rewriter/proofs/rp-state-functions-lemmas" :dir :system))

(set-ignore-ok t)

(progn
  (defun vl-insouts-get-range (vl-logic)
    (b* (((unless (or (equal (car vl-logic)
                             ':VL-LOGIC)
                      (equal (car vl-logic)
                             'VL::PDIMS)))
          (progn$ (hard-error 'vl-smodule-get-range
                              "Unknown data type ~%"
                              nil)
                  (mv t nil)))
         (range (assoc-equal ':VL-RANGE (cdr vl-logic)))
         ((unless range)
          (mv t (cons '? '?)))
         (endp (cdadr (cadadr range)))
         (startp (cdadr (cadddr range))))

      (mv nil (cons (- (1+ (abs (- endp startp)))
                       0;(min endp startp)
                       )
                    0))))

  (define vl-insouts-assocwire (name wires)
    (if (atom wires)
        nil
      (if (and (consp (car wires))
               (consp (caar wires))
               (equal name (caaar wires)))
          (car wires)
        (vl-insouts-assocwire name (cdr wires)))))

  (defun vl-smodule-to-insouts (smodule )
    (if (atom smodule)
        (mv nil nil t)
      (b* ((c (car smodule))
           (type (car c))
           ((mv inrest outrest success)
            (vl-smodule-to-insouts (cdr smodule) ))
           ((when (not (equal type ':VL-PORTDECL)))
            (mv inrest outrest success))
           (porttype (cddr (cadr c)))
           (portname (caadr c))
           (- (and (equal porttype ':VL-INOUT)
                   (cw "Warning! a module has port-type of ':vl-inout ~%")))
           ((when (and (not (equal porttype ':VL-INPUT))
                       (not (equal porttype ':VL-OUTPUT))
                       (not (equal porttype ':VL-INOUT))))
            (mv (cw "Unknown porttype. ~p0 ~%" porttype)
                nil
                nil))
           #|((mv & range) (vl-insouts-get-range (cadar (caddr c))))||#
           #|(wire (vl-insouts-getwire portname wires))||#
           (ins (if (or (equal porttype ':VL-INPUT)
                        (equal porttype ':VL-INOUT))
                    (cons portname inrest)
                  inrest))
           (outs (if (or (equal porttype ':VL-OUTPUT)
                         (equal porttype ':VL-INOUT))
                     (cons portname outrest)
                   outrest)))
        (mv ins outs (and (not (equal porttype ':VL-INOUT))
                          success)))))

  (defun vl-ansi-ports-to-insouts (ports  most-recent-type )
    ;; For modules whose port types are declared right in the port list are
    ;; scanned here.
    (if (atom ports)
        (mv nil nil t)
      (b* ((port (car ports))
           ((unless (equal (car port) ':VL-ANSI-PORTDECL))
            (progn$ (cw  "Unexpected happened!! car of port is ~p0 ~%" (car port))
                    (mv nil nil nil)))
           (port (cdr port))
           (portname (cdr (assoc-equal 'vl::NAME port)))
           (porttype (cdr (assoc-equal 'vl::dir port)))
           (porttype (if porttype porttype
                       most-recent-type))
           (- (and (equal porttype ':VL-INOUT)
                   (cw "Warning! a module has port-type of ':vl-inout ~%")))
           ((unless (or (equal porttype ':VL-INPUT)
                        (equal porttype ':VL-OUTPUT)
                        (equal porttype ':VL-INOUT)))
            (progn$
             (cw "Unknown port type! port-type is: ~p0~%" porttype)
             (mv nil nil nil)))
           ((mv rest-ins rest-outs success)
            (vl-ansi-ports-to-insouts (cdr ports)  porttype)))
        (mv (if (or (equal porttype ':VL-INPUT)
                    (equal porttype ':VL-INOUT))
                (cons portname rest-ins)
              rest-ins)
            (if (or (equal porttype ':VL-OUTPUT)
                    (equal porttype ':VL-INOUT))
                (cons portname rest-outs)
              rest-outs)
            (and (not (equal porttype ':VL-INOUT))
                 success)))))

  (defun vl-module-to-insouts-aux (module-name mod-names)
    (if (atom mod-names)
        nil
      (or (equal module-name (car mod-names))
          (str::strprefixp module-name (car mod-names))
          (vl-module-to-insouts-aux module-name (cdr mod-names)))))

  (defun vl-module-to-insouts (vl-module mod-names)
    (and
     (consp vl-module)
     (equal (car vl-module) ':VL-MODULE)
     (consp (cadr vl-module))
     (consp (caadr vl-module))
     (consp (caaadr vl-module))
     (b* ((smodule (caadr vl-module))
          (module-name (caaar smodule))
          ((when (and (not (vl-module-to-insouts-aux module-name
                                                     mod-names))
                      mod-names))
           nil)
          ((mv ins outs success1)
           (vl-smodule-to-insouts (caadr smodule)))
          ((mv ins2 outs2 success2)
           (vl-ansi-ports-to-insouts
            (cdr (assoc-equal 'vl::ansi-ports
                              (cadddr (cdddr vl-module))))
            nil))
          (- (or (and success1
                      success2)
                 (cw "Warning issued for module ~p0. Flattening this module may
           be useful. ~%" module-name))))
       (list* module-name (append ins ins2) (append outs outs2)))))

  (defun vl-modules-to-insouts (vl-modules mod-names)
    (if (atom vl-modules)
        nil
      (b* ((cur (vl-module-to-insouts (car vl-modules) mod-names))
           (rest (vl-modules-to-insouts (cdr vl-modules) mod-names)))
        (if cur
            (cons cur rest)
          rest))))

  (defun insouts-add-missing-modules-aux (sv-module-name insouts)
    (if (atom insouts)
        nil
      (b* ((cur (car insouts))
           (name (car cur))
           ((when (and (stringp sv-module-name)
                       (stringp name)
                       (str::strprefixp (concatenate 'string name "$") sv-module-name)))
            (list* sv-module-name (cadr cur) (cddr cur))))
        (insouts-add-missing-modules-aux sv-module-name (cdr insouts)))))

  (defun insouts-add-missing-modules (insouts sv-modules)
    ;; some modules created with parameters for example width for input signals
    ;; does not show up in the original insouts lists. It is because sv-design
    ;; appends the parameter to the module's name whereas vl design does
    ;; not. SV design does this appending with $ sign so we search the existing
    ;; insouts list to find the origin of that missing module.
    (declare (ignorable sv-modules))
    (if (atom sv-modules)
        insouts
      (b* ((cur-sv-module (car sv-modules))
           (name (car cur-sv-module))
           ((when (assoc-equal name insouts))
            (insouts-add-missing-modules insouts (cdr sv-modules)))
           (new-insout (insouts-add-missing-modules-aux name insouts)))
        (if new-insout
            (insouts-add-missing-modules (cons new-insout insouts)
                                         (cdr sv-modules))
          (insouts-add-missing-modules insouts
                                       (cdr sv-modules))))))

  (define vl-design-to-insouts (vl-design sv-design mod-names)
    :verify-guards nil
    (and (consp vl-design)
         (equal (car vl-design) ':VL-DESIGN)
         (consp (cadr vl-design))
         (consp (cadr vl-design))
         (consp (caadr vl-design))
         (consp (caaadr vl-design))
         (or (equal (car (caaadr vl-design)) "VL Syntax 2016-08-26")
             (hard-error "VL Syntax version is different exiting just in case ~
  ~%" nil nil))
         (b* ((insouts (vl-modules-to-insouts (cdr (caaadr vl-design)) mod-names))
              (insouts (insouts-add-missing-modules insouts
                                                    (cdr (assoc-equal
                                                          'SV::MODALIST sv-design)))))
           insouts)))

  (define vl-design-to-insouts-wrapper (vl-design sv-design modnames state)
    :returns (val vl-insouts-p)
    (b* (((mv err val)
          (magic-ev-fncall 'vl-design-to-insouts
                           (list vl-design sv-design modnames)
                           state
                           nil
                           t)))
      (if err
          (progn$ (hard-error 'vl-design-to-insouts-wrapper
                              "vl-design-to-insouts-wrapper error for syntaxp check. val: ~p0 ~%"
                              (list (cons #\0 val)))
                  nil)
        (if (vl-insouts-p val)
            val
          nil)))))

(progn

  (define vl-insouts-insert-wire-sizes-aux ((sigs)
                                            (wires SV::WIRELIST-P))
    :prepwork
    ((local
      (defthm sv-wire-p-of-vl-insouts-assocwire
        (implies (and (sv::wirelist-p wires)
                      (vl-insouts-assocwire sigs1 wires))
                 (sv::wire-p (vl-insouts-assocwire sigs1 wires)))
        :hints (("goal"
                 :in-theory (e/d (vl-insouts-assocwire) ())))))
     #|(local
     (defthm lemma1
     (implies (and
     (SV::WIRELIST-P wires)
     (vl-insouts-assocwire cur wires))
     (sv::svar-p cur))
     :hints (("Goal"
     :in-theory (e/d (SV::WIRELIST-P
     SV::WIRE-P
     SV::NAME-P
     vl-insouts-assocwire)
     ())))))||#)

    :returns (res-wires wire-list-p
                        :hyp (and ;;(string-listp sigs)
                              (SV::WIRELIST-P wires)))
    (if (atom sigs)
        nil
      (b* ((cur (car sigs))
           (cur-wire (vl-insouts-assocwire cur wires))
           ((Unless (and cur-wire
                         (sv::svar-p cur)))
            (hard-error 'vl-insouts-insert-wire-sizes
                        "Signal ~p0 cannot be found in wires ~p1 ~%"
                        (list (cons #\0 cur)
                              (cons #\1 wires))))
           (w (sv::wire->width cur-wire)))
        (cons `(,cur ,w . 0)
              (vl-insouts-insert-wire-sizes-aux (cdr sigs)
                                                wires)))))

  (define vl-insouts-insert-wire-sizes ((vl-insouts vl-insouts-p)
                                        (sv-design sv::design-p)
                                        (module-names sv::modnamelist-p))
    ;;:verify-guards nil
    :guard-hints (("Goal"
                   :in-theory (e/d (VL-INSOUTS-P
                                    SV::DESIGN->MODALIST
                                    assoc-equal
                                    SV::MODALIST-FIX) ())))
    :returns (sized-wires vl-insouts-sized-p
                          :hyp (and (vl-insouts-p vl-insouts)
                                    (sv::design-p sv-design)
                                    (sv::modnamelist-p module-names))
                          :hints (("Goal"
                                   :in-theory (e/d (VL-INSOUTS-SIZED-P) ()))))
    :prepwork
    ((local
      (defthm lemma1
        (Implies (VL-INSOUTS-P x)
                 (alistp x))
        :hints (("Goal"
                 :in-theory (e/d (VL-INSOUTS-P) ())))))
     (local
      (defthm lemma2
        (implies (alistp x)
                 (iff (consp (hons-assoc-equal k x))
                      (hons-assoc-equal k x)))))

     (local
      (defthm lemma3
        (implies (and (SV::MODALIST-p alist)
                      (hons-assoc-equal k alist))
                 (SV::MODULE-P (cdr (hons-assoc-equal k alist))))))

     #|(local
     (defthm lemma4
     (implies (and (true-listp alist)
     (SV::MODALIST-p alist))
     (alistp alist))))||#
     )
    (if (atom module-names)
        nil
      (b* ((cur (car module-names))
           (this-vl-insouts (hons-assoc-equal cur vl-insouts))
           (rest (vl-insouts-insert-wire-sizes vl-insouts
                                               sv-design
                                               (cdr module-names)))
           ((unless this-vl-insouts)
            rest)
           (modalist (sv::design->modalist sv-design))
           (sv-module (hons-assoc-equal cur modalist))
           ((unless sv-module)
            rest)
           (sv-module (cdr sv-module))
           (wires (sv::module->wires sv-module))
           (ins (cadr this-vl-insouts))
           (ins (vl-insouts-insert-wire-sizes-aux ins wires))
           (outs (cddr this-vl-insouts))
           (outs (vl-insouts-insert-wire-sizes-aux outs wires)))
        (cons `(,cur ,ins . ,outs)
              rest)))))

(acl2::defines
 free-svl-aliasdb
 :hints (("Goal"
          :in-theory (e/d (rp::measure-lemmas
                           svl-aliasdb->sub
                           SVL-ALIASDB-FIX
                           SVL-ALIASDB-p
                           svl-aliasdb-alist-p
                           svl-aliasdb-alist-fix) ())))
 :prepwork
 ((local
   (defthm lemma1
     (implies (consp x)
              (o< (cons-count (cdr (car x)))
                  (cons-count x)))
     :hints (("goal"
              :in-theory (e/d (cons-count) ()))))))

 (define free-svl-aliasdb ((svl-aliasdb svl-aliasdb-p))
   :measure (cons-count (svl-aliasdb-fix svl-aliasdb))
   (b* ((svl-aliasdb (mbe :logic (svl-aliasdb-fix svl-aliasdb)
                          :exec svl-aliasdb))
        (- (fast-alist-free (svl-aliasdb->this svl-aliasdb)))
        (- (fast-alist-free (svl-aliasdb->sub svl-aliasdb)))
        (- (free-svl-aliasdb-alist (svl-aliasdb->sub svl-aliasdb))))
     nil))
 (define free-svl-aliasdb-alist ((subs svl-aliasdb-alist-P))
   :measure (cons-count (svl-aliasdb-alist-fix subs))
   (b* ((subs (mbe :logic (svl-aliasdb-alist-fix subs)
                   :exec subs)))
     (if (atom subs)
         nil
       (b* ((- (free-svl-aliasdb (cdar subs))))
         (free-svl-aliasdb-alist (cdr subs)))))))

(define update-var-with-trace ((var1 sv::svar-p)
                               (trace trace-p))
  :guard-hints (("Goal"
                 :in-theory (e/d (trace-p
                                  SV::SVAR-P
                                  SV::SVAR->NAME) ())))
  :returns (res sv::svar-p)
  (b* (((sv::svar var) var1)
       (var.name
        (case-match var.name
          ((':address n & depth)
           (let ((prefix (nth (nfix depth) trace)))
             (if prefix (cons prefix n) n)))
          (& (let ((prefix (car trace)))
               (if prefix (cons prefix var.name) var.name))))))
    (sv::change-svar var1 :name var.name)))

#|
(update-var-with-trace '(:VAR (:ADDRESS "padded_multiplier" NIL 3)
                              . 0)
                       '(("m1" "m2" . "m3")
                         ("m1" . "m2")
                         "m1"))
||#

(local
 (defthm svar-implies-svex-p
   (implies (sv::Svar-p x)
            (sv::svex-p x))
   :hints (("Goal"
            :in-theory (e/d (sv::svex-p
                             sv::Svar-p)
                            ())))))

(acl2::defines
 update-svex-vars-with-trace
 :prepwork
 ((local
   (in-theory (e/d (svex-kind
                    svex-p
                    sv::svar-p)
                   ()))))

 (define update-svex-vars-with-trace ((svex sv::svex-p)
                                      (trace trace-p))

   :hints (("Goal"
            :in-theory (e/d (svex-kind) ())))

   :returns (res sv::svex-p :hyp (and (sv::svex-p svex)
                                      (trace-p trace)))

   (b* ((kind (sv::svex-kind svex)))
     (case-match kind
       (':var
        (update-var-with-trace svex trace))
       (':quote
        svex)
       (& (cons (car svex)
                (update-svex-vars-with-trace-lst (cdr svex)
                                                 trace))))))
 (define update-svex-vars-with-trace-lst ((svex-lst svexlist-p)
                                          (trace trace-p))
   :returns (res-lst sv::svexlist-p :hyp (and (svexlist-p svex-lst)
                                              (trace-p trace)))
   (if (atom svex-lst)
       nil
     (cons (update-svex-vars-with-trace (car svex-lst) trace)
           (update-svex-vars-with-trace-lst (cdr svex-lst) trace)))))

;; (update-svex-vars-with-trace '(CONCAT 65
;;                                  (RSH 1040
;;                                       (:VAR (:ADDRESS "padded_multiplier" NIL 2)
;;                                             . 0))
;;                                  '(0 . -1))
;;                         '(("m1" "m2" . "m3")
;;                           ("m1" . "m2")
;;                           "m1"))

(defun cons-to-end (acl2::x acl2::y)
  (declare (xargs :guard t))
  (cond ((atom acl2::x) (cons acl2::x acl2::y))
        (t (cons (car acl2::x)
                 (cons-to-end (cdr acl2::x)
                              acl2::y)))))

(define aliaspair->alias ((alias-1 sv::lhs-p)
                          (alias-2 sv::lhs-p)
                          (trace trace-p)
                          (aliases svl-aliasdb-p))
  :guard-hints (("Goal"
                 :in-theory (e/d (sv::lhs-p
                                  svl-aliasdb-p) ())))
  :returns (mv (place)
               (newname sv::svar-p)
               (svex2 sv::svex-p :hyp (and (sv::lhs-p alias-1)
                                           (sv::lhs-p alias-2)
                                           (trace-p trace)
                                           (svl-aliasdb-p aliases))
                      :hints (("Goal"
                               :in-theory (e/d (sv::svex-p) ())))))
  (b* (;; flig the alias pairs
       ((mv alias-1 alias-2)
        (if (and (equal (len alias-2) 1)
                 (equal (sv::lhatom-kind (sv::lhrange->atom (car alias-2))) ':var)
                 (equal (sv::lhatom-var->name (sv::lhrange->atom (car alias-2)))
                        ':self))
            (mv alias-2 alias-1)
          (mv alias-1 alias-2)))

       ((when (or (> (len alias-1) 1)
                  (atom alias-1)
                  (equal (sv::lhatom-kind (sv::lhrange->atom (car alias-1)))
                         :z)))
        (progn$
         (hard-error 'aliaspair->alias
                     "This alias pairs (~p0) is unexpected Fix ~
                          aliaspair->alias"
                     (list (cons #\0 alias-1)
                           ))
         (mv nil "" 0)))

       (lhrange1 (car alias-1))
       (w1 (sv::lhrange->w lhrange1))
       ((sv::lhatom-var atom1) (sv::lhrange->atom lhrange1))

       (varname (sv::svar->name atom1.name))
       (newname (if (consp varname)
                    (sv::change-svar atom1.name :name (cdr varname))
                  atom1.name))
       (place (if (consp varname) (car varname) nil))
       (- (if (and (consp varname)
                   (consp (cdr varname)))
              (hard-error 'aliaspair->alias
                          "Unexpected varname for aliaspairs (~p0 ~p1). ~%"
                          (list (cons #\0 alias-1)
                                (cons #\1 alias-2)))
            nil))
       (svex2-old-val (if (equal place nil)
                          aliases
                        (cdr (hons-get place (svl-aliasdb->sub aliases)))))
       (svex2-old-val (if svex2-old-val
                          (hons-get newname (svl-aliasdb->this
                                             svex2-old-val))
                        nil))
       (svex2-old-val (cond (svex2-old-val (cdr svex2-old-val))
                            ((consp trace)
                             (sv::change-svar
                              atom1.name
                              :name
                              (if (consp varname)
                                  (cons (cons-to-end (car trace) (car varname))
                                        (cdr varname))
                                (cons (car trace) varname))))
                            (t atom1.name)))
       (svex2 (sv::lhs->svex alias-2))
       (svex2 (update-svex-vars-with-trace svex2 trace))
       (svex2 `(sv::partinst ,atom1.rsh ,w1 ,svex2-old-val ,svex2)))
    (mv place newname svex2)))

#|

(aliaspair->alias '((3 :VAR
                       ("partial_product_mux" . "multiplier_bits")
                       . 0))
                  '((2 (:VAR (:ADDRESS "padded_multiplier" NIL 3)
                             . 0)
                       . 25)
                    ((:VAR (:ADDRESS "padded_multiplier" NIL 3)
                             . 0)
                       . 27))
                  '(("m1" "m2" . "m3")
                    ("m1" . "m2")
                    "m1")
                    (make-svl-aliasdb))

(aliaspair->alias '((65 :VAR 16 . 0))
                  '((65 :SELF . 1040))
                  '(("m1" "m2" . "m3")
                    ("m1" . "m2")
                    "m1")
                  (make-svl-aliasdb))
||#

(define insert-into-svl-aliasdb ((place)
                                 (key sv::svar-p)
                                 (val sv::svex-p)
                                 (svl-aliasdb SVL-ALIASDB-P))
  :returns (res svl-aliasdb-p)
  ;; place can be nil or consed module names.
  (cond ((not place)
         (change-svl-aliasdb svl-aliasdb
                             :this
                             (hons-acons key val
                                         (svl-aliasdb->this svl-aliasdb))))
        ((atom place)
         (b* ((sub-svl-aliasdb (hons-get place (svl-aliasdb->sub svl-aliasdb)))
              (sub-svl-aliasdb (if sub-svl-aliasdb (cdr sub-svl-aliasdb) (make-svl-aliasdb)))
              (sub-svl-aliasdb
               (change-svl-aliasdb
                sub-svl-aliasdb
                :this
                (hons-acons key val
                            (svl-aliasdb->this sub-svl-aliasdb)))))
           (change-svl-aliasdb
            svl-aliasdb
            :sub
            (hons-acons place
                        sub-svl-aliasdb
                        (svl-aliasdb->sub svl-aliasdb))
            )))
        (t (b* ((curplace (car place))
                (cur-sub (hons-get curplace (svl-aliasdb->sub svl-aliasdb)))
                (cur-sub (if cur-sub (cdr cur-sub) (make-svl-aliasdb)))
                (cur-sub (insert-into-svl-aliasdb (cdr place) key val cur-sub)))
             (change-svl-aliasdb svl-aliasdb
                                 :sub
                                 (hons-acons curplace
                                             cur-sub
                                             (svl-aliasdb->sub svl-aliasdb)))))))

(define aliaspair-lst->svl-aliasdb ((aliaspairs sv::lhspairs-p)
                                    (trace trace-p))
  :returns (res svl-aliasdb-p)
  (if (atom aliaspairs)
      (make-svl-aliasdb)
    (b* ((rest (aliaspair-lst->svl-aliasdb (cdr aliaspairs) trace))
         ((mv cur-place cur-name cur-svex)
          (aliaspair->alias (caar aliaspairs)
                            (cdar aliaspairs)
                            trace
                            rest)))
      (insert-into-svl-aliasdb cur-place cur-name cur-svex rest))))

#|
(wet
 (aliaspair-lst->svl-aliasdb '((((65 :var 16 . 0)) (65 :self . 1040))
                       (((65 :var 15 . 0)) (65 :self . 975))
                       (((65 :var 14 . 0)) (65 :self . 910))
                       (((65 :var 13 . 0)) (65 :self . 845))
                       (((65 :var 12 . 0)) (65 :self . 780))
                       (((65 :var 11 . 0)) (65 :self . 715))
                       (((65 :var 10 . 0)) (65 :self . 650))
                       (((65 :var 9 . 0)) (65 :self . 585))
                       (((65 :var 8 . 0)) (65 :self . 520))
                       (((65 :var 7 . 0)) (65 :self . 455))
                       (((65 :var 6 . 0)) (65 :self . 390))
                       (((65 :var 5 . 0)) (65 :self . 325))
                       (((65 :var 4 . 0)) (65 :self . 260))
                       (((65 :var 3 . 0)) (65 :self . 195))
                       (((65 :var 2 . 0)) (65 :self . 130))
                       (((65 :var 1 . 0)) (65 :self . 65))
                       (((65 :var 0 . 0)) (65 . :self)))
                     '(("m1" "m2" . "m3")
                       ("m1" . "m2")
                       "m1")))

(aliaspair-lst->svl-aliasdb '((((3 :VAR
                           ("partial_product_mux" . "multiplier_bits")
                           . 0))
                       (3 (:VAR (:ADDRESS "padded_multiplier" NIL 3)
                                . 0)
                          . 25))
                      (((64 :VAR
                            ("partial_product_mux" . "multiplicand")
                            . 0))
                       (64 :VAR (:ADDRESS "multiplicand" NIL 3)
                           . 0))
                      (((:VAR ("partial_product_mux" . "multiplicand_sign")
                              . 0))
                       (:VAR (:ADDRESS "multiplicand_sign" NIL 3)
                             . 0))
                      (((:VAR ("partial_product_mux" . "partial_product_sign")
                              . 0))
                       ((:VAR (:ADDRESS "partial_product_signs" NIL 3)
                              . 0)
                        . 13))
                      (((:VAR ("partial_product_mux" . "partial_product_inverted")
                              . 0))
                       ((:VAR (:ADDRESS "partial_product_increments" NIL 3)
                              . 0)
                        . 13))
                      (((65 :VAR
                            ("partial_product_mux" . "partial_product")
                            . 0))
                       (65 (:VAR (:ADDRESS "partial_products" NIL 1)
                                 . 0)
                           . 845)))
                    '(
                      ("m1" "m2" . "m3")
                      ("m1" . "m2")
                      "m1"))

||#

(local
 (progn
   (defthm cdr-last-is-nil
     (implies (true-listp x)
              (equal
               (CDR (LAST x))
               nil)))

   (defthm ALIAS-ALIST-P-of-FAST-ALIST-fork
     (implies (and (alias-alist-p f)
                   (alias-alist-p e))
              (alias-alist-p (fast-alist-fork f e)))
     :hints (("Goal"
              :in-theory (e/d (alias-alist-p) ()))))

   (defthm ALIAS-ALIST-P-of-FAST-ALIST-clean
     (implies (and (alias-alist-p f))
              (alias-alist-p (fast-alist-clean f)))
     :hints (("Goal"
              :in-theory (e/d () (fast-alist-fork)))))

   (defthm svl-aliasdb-alist-p-of-FAST-ALIST-fork
     (implies (and (svl-aliasdb-alist-p f)
                   (svl-aliasdb-alist-p e))
              (svl-aliasdb-alist-p (fast-alist-fork f e)))
     :hints (("Goal"
              :in-theory (e/d (alias-alist-p) ()))))

   (defthm svl-aliasdb-alist-p-of-FAST-ALIST-clean
     (implies (and (svl-aliasdb-alist-p f))
              (svl-aliasdb-alist-p (fast-alist-clean f)))
     :hints (("Goal"
              :in-theory (e/d () (fast-alist-fork)))))))

(define merge-this-insts-svl-aliasdb ((sub-svl-aliasdb svl-aliasdb-alist-p)
                                      (insts-svl-aliasdb-alist svl-aliasdb-alist-p))
  :prepwork
  ((local
    (in-theory (e/d () (fast-alist-clean)))))
  :returns (res svl-aliasdb-alist-p
                :hyp (and (svl-aliasdb-alist-p sub-svl-aliasdb)
                          (svl-aliasdb-alist-p insts-svl-aliasdb-alist)))
  (if (atom insts-svl-aliasdb-alist)
      (fast-alist-clean sub-svl-aliasdb)
    (b* ((cur (car insts-svl-aliasdb-alist))
         (name (car cur))
         (cur-svl-aliasdb (cdr cur))
         (cursub (hons-get name sub-svl-aliasdb))
         (cursub (if cursub (cdr cursub) (make-svl-aliasdb)))
         (- (if (svl-aliasdb->sub cursub)
                (hard-error 'merge-this-insts-svl-aliasdb
                            "Unexpected sub entry while merge ~p0~%"
                            (list (cons #\0 cursub)))
              nil))
         (- (fast-alist-free (svl-aliasdb->this cursub)))
         (- (fast-alist-free (svl-aliasdb->this cur-svl-aliasdb)))
         (cursub-this (append (svl-aliasdb->this cursub)
                              (svl-aliasdb->this cur-svl-aliasdb)))
         (cursub-this (fast-alist-clean (make-fast-alist cursub-this)))
         (cursub (change-svl-aliasdb cursub
                                     :this cursub-this
                                     :sub (svl-aliasdb->sub cur-svl-aliasdb)))
         (sub-svl-aliasdb (hons-acons name cursub sub-svl-aliasdb)))
      (merge-this-insts-svl-aliasdb sub-svl-aliasdb
                                    (cdr insts-svl-aliasdb-alist)))))

(acl2::defines
 add-delay-to-vars-in-svex
 :prepwork ((local
             (in-theory (e/d (sv::svex-kind
                              sv::svex-p
                              sv::svar-p)))))
 (define add-delay-to-vars-in-svex ((svex sv::svex-p))
   :returns (res sv::svex-p :hyp (sv::svex-p svex))
   (cond ((equal (sv::svex-kind svex) ':quote)
          svex)
         ((equal (sv::svex-kind svex) ':var)
          (sv::change-svar svex :delay 1))
         (t
          (cons (car svex)
                (add-delay-to-vars-in-svex-lst (cdr svex))))))

 (define add-delay-to-vars-in-svex-lst ((lst sv::svexlist-p))
   :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
   (if (atom lst)
       nil
     (cons (add-delay-to-vars-in-svex (car lst))
           (add-delay-to-vars-in-svex-lst (cdr lst))))))

(define get-svex-from-svl-aliasdb ((name)
                                   (trace-name)
                                   (delay natp)
                                   (svl-aliasdb svl-aliasdb-p))
  :measure (acl2-count trace-name)
  (cond ((not trace-name)
         (b* ((var (sv::make-svar :name name
                                  :delay 0))
              (res (hons-get var (svl-aliasdb->this svl-aliasdb))))
           (cond ((and res (equal delay 0))
                  (cdr res))
                 ((and res (equal delay 1))
                  (add-delay-to-vars-in-svex (cdr res)))
                 (t
                  nil))))
        ((atom trace-name)
         (b* ((instname trace-name)
              (subaliases (svl-aliasdb->sub svl-aliasdb))
              (subsvl-aliasdb (hons-get instname subaliases)))
           (if subsvl-aliasdb
               (b* ((var (sv::make-svar :name  name :delay 0))
                    (res (hons-get var (svl-aliasdb->this (cdr subsvl-aliasdb)))))
                 (cond ((and res (equal delay 0))
                        (cdr res))
                       ((and res (equal delay 1))
                        (add-delay-to-vars-in-svex (cdr res)))
                       (t
                        nil)))
             nil)))
        (t (b* ((instname (car trace-name))
                (subaliases (svl-aliasdb->sub svl-aliasdb))
                (subsvl-aliasdb (hons-get instname subaliases)))
             (if subsvl-aliasdb
                 (get-svex-from-svl-aliasdb name
                                            (cdr trace-name)
                                            delay
                                            (cdr subsvl-aliasdb))
               nil))))
  ///

  (defthm return-val-of-get-svex-from-svl-aliasdb
    (implies (and (svl-aliasdb-p svl-aliasdb)
                  (get-svex-from-svl-aliasdb name trace-name delay
                                             svl-aliasdb))
             (sv::svex-p (get-svex-from-svl-aliasdb name trace-name delay
                                                    svl-aliasdb)))))

(defun nthcdr2 (acl2::n acl2::l)
  (declare (xargs :guard (and (integerp acl2::n)
                              (<= 0 acl2::n))))
  (if (zp acl2::n)
      acl2::l
    (if (atom acl2::l)
        nil
      (nthcdr2 (+ acl2::n -1) (cdr acl2::l)))))

(acl2::defines
 update-svex-with-svl-aliasdb
 :prepwork ((local
             (in-theory (e/d (svex-kind
                              sv::svar-p
                              svex-p) ()))))

 (define update-svex-with-svl-aliasdb ((svex sv::svex-p)
                                       (svl-aliasdb svl-aliasdb-p)
                                       (skip-var-name)
                                       (trace-size natp))
   :returns (res sv::svex-p
                 :hyp (and (sv::svex-p svex)
                           (svl-aliasdb-p svl-aliasdb)
                           (natp trace-size)))
   (let ((kind (sv::svex-kind svex)))
     (cond ((eq kind ':quote)
            svex)
           ((eq kind ':var)
            (b* ((var-name (sv::svar->name svex))
                 (var-delay (sv::svar->delay svex))
                 (place (if (consp var-name) (car var-name) nil))
                 (name (if (consp var-name) (cdr var-name) var-name))
                 (place (nthcdr2 trace-size place))
                 ((when (equal var-name skip-var-name)) svex)
                 (res (get-svex-from-svl-aliasdb name place var-delay svl-aliasdb)))
              (if res
                  res
                svex)))
           (t
            (cons-with-hint (car svex)
                            (update-svex-with-svl-aliasdb-lst (cdr svex)
                                                              svl-aliasdb
                                                              skip-var-name
                                                              trace-size)
                            svex)))))

 (define update-svex-with-svl-aliasdb-lst ((lst sv::svexlist-p)
                                           (svl-aliasdb svl-aliasdb-p)
                                           (skip-var-name)
                                           (trace-size natp))
   :returns (res-lst sv::svexlist-p
                     :hyp (and (sv::svexlist-p lst)
                               (svl-aliasdb-p svl-aliasdb)
                               (natp trace-size)))
   (if (atom lst)
       nil
     (cons-with-hint
      (update-svex-with-svl-aliasdb (car lst)
                                    svl-aliasdb skip-var-name trace-size)
      (update-svex-with-svl-aliasdb-lst (cdr lst)
                                        svl-aliasdb skip-var-name trace-size)
      lst))))

(define fix-this-aliases ((this-aliases alias-alist-p)
                          (trace-size natp)
                          (svl-aliasdb svl-aliasdb-p))
  :returns (res alias-alist-p
                :hyp (and (alias-alist-p this-aliases)
                          (natp trace-size)
                          (svl-aliasdb-p svl-aliasdb)))
  (if (atom this-aliases)
      nil
    (b* ((cur (car this-aliases))
         (cur-name (car cur))
         (cur-svex (cdr cur))
         (cur-svex (update-svex-with-svl-aliasdb cur-svex
                                                 svl-aliasdb
                                                 cur-name
                                                 trace-size)))
      (hons-acons cur-name
                  cur-svex
                  (fix-this-aliases (cdr this-aliases)
                                    trace-size
                                    svl-aliasdb)))))

(acl2::defines
 mod-aliaspairs->svl-aliasdb-pt1
 (define mod-aliaspairs->svl-aliasdb-pt1 ((modname sv::modname-p)
                                          (modalist sv::modalist-p)
                                          ;;  (proc-history )
                                          (trace trace-p)
                                          (mods-to-skip sv::modnamelist-p)
                                          (limit natp "To prove termination"))
   :returns (res svl-aliasdb-p)
   :verify-guards nil
   :measure (nfix limit)
   (cond ((zp limit)
          (progn$ (hard-error 'mod-aliaspairs->svl-aliasdb-pt1
                              "Limit Reached! ~%"
                              nil)
                  (make-svl-aliasdb)))
         ;; ((hons-get modname proc-history)
         ;;  (cdr (hons-get modname proc-history)))
         (t
          (b* ((module (hons-get modname modalist))
               ((unless module)
                (progn$
                 (hard-error 'mod-aliaspairs->svl-aliasdb-pt1
                             "Module not found in modalist ~p0 ~%"
                             (list (cons #\0 modname)))
                 (make-svl-aliasdb)))
               (module (cdr module))
               ((sv::module module) module)
               (svl-aliasdb (aliaspair-lst->svl-aliasdb module.aliaspairs trace))
               (insts-svl-aliasdb-alist
                (mod-aliaspairs->svl-aliasdb-pt1-lst module.insts
                                                     modalist
                                                     ;;proc-history
                                                     trace
                                                     mods-to-skip
                                                     (1- limit)))
               (merged-sub (merge-this-insts-svl-aliasdb (svl-aliasdb->sub svl-aliasdb)
                                                         insts-svl-aliasdb-alist))
               (svl-aliasdb (change-svl-aliasdb svl-aliasdb :sub merged-sub))
               (this-aliases (svl-aliasdb->this svl-aliasdb))
               (this-aliases (fix-this-aliases this-aliases
                                               (len (car trace))
                                               svl-aliasdb))
               (- (fast-alist-free (svl-aliasdb->this svl-aliasdb))))
            (change-svl-aliasdb svl-aliasdb :this this-aliases)))))

 (define mod-aliaspairs->svl-aliasdb-pt1-lst ((insts sv::modinstlist-p)
                                              (modalist sv::modalist-p)
                                              (trace trace-p)
                                              (mods-to-skip sv::modnamelist-p)
                                              (limit natp "To prove
                                              termination"))
   :returns (res-alist svl-aliasdb-alist-p)
   :measure (nfix limit)
   (cond ((zp limit)
          (progn$ (hard-error 'mod-aliaspairs->svl-aliasdb-pt1
                              "Limit Reached! ~%"
                              nil)
                  nil))
         ((atom insts)
          nil)
         (t (b* (((sv::modinst inst) (car insts))
                 (rest (mod-aliaspairs->svl-aliasdb-pt1-lst (cdr insts)
                                                            modalist
                                                            trace
                                                            mods-to-skip
                                                            (1- limit)))
                 ((when (member-equal inst.modname mods-to-skip))
                  rest)
                 (trace- (cons (if trace
                                   (cons-to-end (car trace) inst.instname)
                                 inst.instname)
                               trace)))
              (acons inst.instname
                     (mod-aliaspairs->svl-aliasdb-pt1 inst.modname
                                                      modalist
                                                      trace-
                                                      mods-to-skip
                                                      (1- limit))
                     rest)))))
 ///
 (verify-guards mod-aliaspairs->svl-aliasdb-pt1
   :hints (("Goal"
            :in-theory (e/d (trace-p) ())))))

#|

(mod-aliaspairs->svl-aliasdb-pt1 "mul_test1"
                             (make-fast-alist (sv::design->modalist *booth-sv-design*))
                             nil
                             (expt 2 30))

(mod-aliaspairs->svl-aliasdb-pt1 "booth2_multiplier_signed_64x32_97"
                             (make-fast-alist (sv::design->modalist *big-sv-design*))
                             nil
                             '("booth2_reduction_dadda_17x65_97")
                             (expt 2 30))
||#

(acl2::defines
 update-svex-with-aliases-alist
 :guard-hints (("Goal"
                :in-theory (e/d (svex-kind
                                 sv::svar-p
                                 svex-p) ())))
 :hints (("Goal"
          :in-theory (e/d (svex-kind) ())))
 :prepwork ((local
             (in-theory (enable svex-p
                                svex-kind
                                sv::svexlist-p
                                SV::SVAR-P))))

 (define update-svex-with-aliases-alist ((svex sv::svex-p)
                                         (aliases-alist alias-alist-p))
   :returns (res svex-p :hyp (and (sv::svex-p svex)
                                  (alias-alist-p aliases-alist)))
   (let ((kind (sv::svex-kind svex)))
     (cond ((eq kind ':quote)
            svex)
           ((eq kind ':var)
            (b* ((res (hons-get svex aliases-alist)))
              (if res (cdr res) svex)))
           (t
            (cons-with-hint (car svex)
                            (update-svex-with-aliases-alist-lst (cdr svex)
                                                                aliases-alist)
                            svex)))))

 (define update-svex-with-aliases-alist-lst ((lst sv::svexlist-p)
                                             (aliases-alist alias-alist-p))
   :returns (res-lst sv::svexlist-p
                     :hyp (and (sv::svexlist-p lst)
                               (alias-alist-p aliases-alist)) )
   (if (atom lst)
       nil
     (cons-with-hint
      (update-svex-with-aliases-alist (car lst) aliases-alist)
      (update-svex-with-aliases-alist-lst (cdr lst) aliases-alist)
      lst))))

(define add-to-aliases-alist ((this-alias-alist alias-alist-p)
                              (aliases-alist alias-alist-p)
                              (trace trace-p))
  :guard-hints (("Goal"
                 :in-theory (e/d () ())))
  :returns (mv (res-alist alias-alist-p
                          :hyp (and (alias-alist-p this-alias-alist)
                                    (alias-alist-p aliases-alist)
                                    (trace-p trace)))
               (res-alist-2 alias-alist-p
                            :hyp (and (alias-alist-p this-alias-alist)
                                      (alias-alist-p aliases-alist)
                                      (trace-p trace))))

  (if (atom this-alias-alist)
      (mv aliases-alist nil)
    (b* ((cur (car this-alias-alist))
         (cur-svar (car cur))
         (cur-svex (cdr cur))
         (cur-svex (update-svex-with-aliases-alist cur-svex aliases-alist))
         (new-svar (if (consp trace)
                       (cons (car trace) cur-svar)
                     cur-svar))
         (aliases-alist
          (hons-acons (sv::change-svar cur-svar :name new-svar)
                      cur-svex
                      aliases-alist))
         ((mv aliases-alist rest)
          (add-to-aliases-alist (cdr this-alias-alist)
                                aliases-alist
                                trace)))
      (mv aliases-alist
          (hons-acons cur-svar cur-svex
                      rest)))))

(acl2::defines
 mod-aliaspairs->svl-aliasdb-pt2
 :prepwork
 ((local
   (defthm lemma1
     (O< (CONS-COUNT (SVL-ALIASDB-ALIST-FIX (CADR SVL-ALIASDB)))
         (CONS-COUNT (SVL-ALIASDB-FIX SVL-ALIASDB)))
     :hints (("Goal"
              :in-theory (e/d (cons-count
                               SVL-ALIASDB-FIX
                               SVL-ALIASDB-ALIST-FIX) ())))))
  (local
   (defthm lemma2
     (implies (consp x)
              (o< (cons-count (cdr (car x)))
                  (cons-count x)))
     :hints (("Goal"
              :in-theory (e/d (cons-count) ())))))

  (local
   (in-theory (e/d (trace-p)
                   ()))))

 (define mod-aliaspairs->svl-aliasdb-pt2 ((svl-aliasdb svl-aliasdb-p)
                                          (aliases-alist alias-alist-p)
                                          (trace trace-p))
   :hints (("Goal"
            :in-theory (e/d (SVL-ALIASDB->SUB
                             SVL-ALIASDB-ALIST-FIX
                             rp::measure-lemmas) ())))
   :measure (cons-count (svl-aliasdb-fix svl-aliasdb))
   :verify-guards nil
   :returns (mv (res-alist-db svl-aliasdb-p)
                (res-alias-alist alias-alist-p
                                 :hyp (and (alias-alist-p aliases-alist)
                                           (svl-aliasdb-p svl-aliasdb)
                                           (trace-p trace))))

   (b* (((svl-aliasdb svl-aliasdb) svl-aliasdb)
        ((mv aliases-alist new-this)
         (add-to-aliases-alist svl-aliasdb.this aliases-alist trace))
        (- (fast-alist-free svl-aliasdb.this))
        (- (fast-alist-free svl-aliasdb.sub))
        ((mv new-sub aliases-alist)
         (mod-aliaspairs->svl-aliasdb-pt2-lst svl-aliasdb.sub aliases-alist trace)))
     (mv (change-svl-aliasdb svl-aliasdb
                             :this new-this
                             :sub new-sub)
         aliases-alist)))

 (define mod-aliaspairs->svl-aliasdb-pt2-lst ((svl-aliasdb.sub svl-aliasdb-alist-p)
                                              (aliases-alist alias-alist-p)
                                              (trace trace-p))
   :measure (cons-count (svl-aliasdb-alist-fix svl-aliasdb.sub))

   :returns (mv (res-alist-db-alist svl-aliasdb-alist-p)
                (res-alias-alist alias-alist-p
                                 :hyp (and (alias-alist-p aliases-alist)
                                           (svl-aliasdb-alist-p
                                            svl-aliasdb.sub)
                                           (trace-p trace))))

   (b* ((svl-aliasdb.sub (mbe :logic (svl-aliasdb-alist-fix svl-aliasdb.sub)
                              :exec svl-aliasdb.sub)))
     (if (atom svl-aliasdb.sub)
         (mv nil aliases-alist)
       (b* ((trace-tmp (cons (if (consp trace)
                                 (cons-to-end (car trace) (caar svl-aliasdb.sub))
                               (caar svl-aliasdb.sub))
                             trace))
            ((mv new-sub-entry aliases-alist)
             (mod-aliaspairs->svl-aliasdb-pt2 (cdar svl-aliasdb.sub)
                                              aliases-alist
                                              trace-tmp))
            ((mv rest-subs aliases-alist)
             (mod-aliaspairs->svl-aliasdb-pt2-lst (cdr svl-aliasdb.sub)
                                                  aliases-alist
                                                  trace)))
         (mv (hons-acons (caar svl-aliasdb.sub) new-sub-entry rest-subs)
             aliases-alist)))))

 ///

 (verify-guards mod-aliaspairs->svl-aliasdb-pt2))

(define mod-aliaspairs->svl-aliasdb ((modname sv::modname-p)
                                     (modalist sv::modalist-p)
                                     (mods-to-skip sv::modnamelist-p))

  :returns (res svl-aliasdb-p)
  (b* ((svl-aliasdb (mod-aliaspairs->svl-aliasdb-pt1 modname modalist nil
                                                     mods-to-skip
                                                     (expt 2 59)))
       ((mv svl-aliasdb aliases-alist)
        (mod-aliaspairs->svl-aliasdb-pt2 svl-aliasdb
                                         nil
                                         nil))
       (- (fast-alist-free aliases-alist)))
    svl-aliasdb))

#|

(mod-aliaspairs->svl-aliasdb "mul_test1"
                         (make-fast-alist (sv::design->modalist *booth-sv-design*))
                         nil)

;; not unfree fast-alist
(b* ((modalist (make-fast-alist (sv::design->modalist *signed64-sv-design*))))
  (progn$ (free-svl-aliasdb (mod-aliaspairs->svl-aliasdb "S_SP_64_64"
                                                modalist
                                                nil))
         (fast-alist-free modalist)
          nil))

(mod-aliaspairs->svl-aliasdb "booth2_multiplier_signed_64x32_97"
                         (make-fast-alist (sv::design->modalist *big-sv-design*))
                         '("booth2_reduction_dadda_17x65_97"))
||#

;; (vl-design-to-insouts *big-vl-design2* *big-sv-design*)

(acl2::defines
 update-svex-with-svl-aliasdb-and-trace
 :guard-hints (("Goal"
                :in-theory (e/d (svex-kind
                                 sv::svar-p
                                 trace-p
                                 svex-p) ())))
 :hints (("Goal"
          :in-theory (e/d (svex-kind) ())))
 :prepwork
 ((local
   (in-theory (e/d (svex-p
                    svex-kind)
                   ()))))

 (define update-svex-with-svl-aliasdb-and-trace ((svex sv::svex-p)
                                                 (svl-aliasdb svl-aliasdb-p)
                                                 (trace trace-p))
   :verify-guards nil
   :returns (res sv::svex-p
                 :hyp (and (sv::svex-p svex)
                           (svl-aliasdb-p svl-aliasdb)
                           (trace-p trace)))
   (let ((kind (sv::svex-kind svex)))
     (cond ((equal svl-aliasdb `(,(make-svl-aliasdb)))
            svex)
           ((eq kind ':quote)
            svex)
           ((eq kind ':var)
            (b* ((var-name (sv::svar->name svex))
                 (var-delay (sv::svar->delay svex))
                 ((mv var-name address)
                  (case-match var-name
                    ((':address n & depth) (mv n depth))
                    (& (mv var-name 0))))

                 (cur-trace (nth (nfix address) trace))

                 (place (if (consp var-name) (car var-name) nil))
                 (place (if place
                            (if cur-trace
                                (cons-to-end cur-trace place)
                              place)
                          cur-trace))

                 (name (if (consp var-name) (cdr var-name) var-name))
                 (res (get-svex-from-svl-aliasdb name place var-delay svl-aliasdb))
                 ((when res) res)

                 (svar (sv::change-svar svex :name (if place (cons place name) name))))
              svar))
           (t
            (cons-with-hint (car svex)
                            (update-svex-with-svl-aliasdb-and-trace-lst (cdr svex)
                                                                        svl-aliasdb
                                                                        trace)
                            svex)))))

 (define update-svex-with-svl-aliasdb-and-trace-lst ((lst sv::svexlist-p)
                                                     (svl-aliasdb svl-aliasdb-p)
                                                     (trace trace-p))
   :returns (res-lst sv::svexlist-p
                     :hyp (and (sv::svexlist-p lst)
                               (svl-aliasdb-p svl-aliasdb)
                               (trace-p trace)))
   (if (atom lst)
       nil
     (cons-with-hint
      (update-svex-with-svl-aliasdb-and-trace (car lst)
                                              svl-aliasdb trace)
      (update-svex-with-svl-aliasdb-and-trace-lst (cdr lst)
                                                  svl-aliasdb trace)
      lst)))
 ///
 (verify-guards update-svex-with-svl-aliasdb-and-trace
   :hints (("Goal"
            :in-theory (e/d (trace-p) ())))))

(define get-lhs-w ((lhs sv::lhs-p))
  :returns (res natp)
  (if (atom lhs)
      0
    (+ (sv::lhrange->w (car lhs))
       (get-lhs-w (cdr lhs)))))

(define svex->lhs ((svex))
  ;; example input :
  ;; (CONCAT
  ;;  65
  ;;  (PARTSEL 0 65 (:VAR ("partial_products" . 2) . 0))
  ;;  (CONCAT
  ;;   61
  ;;   (PARTSEL 4 61 (:VAR ("partial_products" . 2) . 0))
  ;;   (PARTSEL 65 5 (:VAR ("x" . "out") . 0))))

  :prepwork ((local
              (in-theory (e/d (sv::lhs-p
                               sv::svex-p)
                              ()))))
  :returns (res sv::lhs-p :hyp (sv::svex-p svex))

  (case-match svex
    (('sv::partsel start size var)
     (b* (((unless (sv::svar-p var))
           (progn$ (hard-error 'svex->lhs
                               "something is wrong with the svex ~p0~%"
                               (list (cons #\0 svex)))
                   nil))
          (start (nfix start))
          (size (if (posp size) size 1))
          (lhatom (sv::make-lhatom-var :name var
                                       :rsh start))
          (lhrange (sv::make-lhrange :w size
                                     :atom lhatom)))
       (list lhrange)))
    (('sv::concat concat-size ('sv::partsel & size &) term2)
     (b* ((concat-size (nfix concat-size))
          (size (nfix size)))
       (cond ((eql concat-size size)
              (append (svex->lhs (caddr svex))
                      (svex->lhs term2)))
             ((< concat-size size)
              (hard-error 'svex->lhs
                          "Unexpected size combination ~p0 ~%."
                          (list (cons #\0 svex))))
             (t (append (svex->lhs (caddr svex))
                        (list (sv::make-lhrange :w (- concat-size size)
                                                :atom (sv::make-lhatom-z)))
                        (svex->lhs term2))))))
    (&
     (hard-error 'svex->lhs
                 "Unexpected Expression~ ~p0 ~%"
                 (list (cons #\0 svex))))))

#|
(svex->lhs
 '(CONCAT
   68
   (PARTSEL 0 65 (:VAR ("partial_products" . 2) . 0))
   (CONCAT
    61
    (PARTSEL 4 61 (:VAR ("partial_products" . 2) . 0))
    (PARTSEL 65 5 (:VAR ("x" . "out") . 0)))))
||#

(define lhs-to-svl-wirelist ((lhs sv::lhs-p))
  :returns (wires wire-list-p :hyp (sv::lhs-p lhs))
  (if (atom lhs)
      nil
    (b* (((sv::lhrange lhrange) (car lhs))
         (wire-name (if (equal (sv::lhatom-kind lhrange.atom) :z)
                        :z
                      (sv::lhatom-var->name lhrange.atom)))
         (wire-start (if (equal (sv::lhatom-kind lhrange.atom) :z)
                         0
                       (sv::lhatom-var->rsh lhrange.atom)))
         (wire-size lhrange.w)
         (wire `(,wire-name ,wire-size . ,wire-start)))
      (cons wire
            (lhs-to-svl-wirelist (cdr lhs))))))

#|

(lhs-to-svl-wirelist '((65 :VAR ("partial_products" . 2) . 0)
                       (3 . :Z)
                       (61 (:VAR ("partial_products" . 2) . 0)
                           . 4)
                       (5 (:VAR ("x" . "out") . 0) . 65)))
||#

(acl2::defines
 get-inputs-for-svex
 :prepwork
 ((local
   (in-theory (enable SV::SVARLIST-P
                      SVEX-P

                      svex-kind)))
  (local
   (defthm wire-list-p-implies-true-listp
     (implies (wire-list-p wires)
              (true-listp wires))))
  (local
   (defthm SVarLIST-P-implies-true-listp
     (implies (sv::SVarLIST-P wires)
              (true-listp wires)))))

 (define get-inputs-for-svex ((svex sv::svex-p)
                              (modname sv::modname-p)
                              (modalist sv::modalist-p))
   :verify-guards nil
   :returns (mv (wires wire-list-p
                       :hyp (sv::svex-p svex))
                (delayed sv::svarlist-p
                         :hyp (sv::svex-p svex))
                (success booleanp))
   (declare (ignorable modname modalist)) ;; will use these when var is not in
   ;; partsel. If so, will see if the wire is of size 1. Then it's all good..
   (b* ((kind (sv::svex-kind svex)))
     (cond ((eq kind ':quote)
            (mv nil nil t))
           ((eq kind ':var)
            (b* ((delayed (eql (sv::svar->delay svex) 1)))
              (mv (if delayed nil (list `(,svex)))
                  (if delayed (list svex) nil)
                  (if delayed t
                    (cw "~% Reached a var that was not in a partsel ~p0 ~%" svex)))))
           ((case-match svex (('sv::partsel start size sub-svex)
                              (and (sv::svar-p sub-svex)
                                   (natp start)
                                   (natp size)))
              (& nil))
            (b* ((start (cadr svex))
                 (size (caddr svex))
                 (svar (cadddr svex))
                 (delayed (eql (sv::svar->delay svar) 1)))
              (mv (if delayed nil (list `(,svar ,size . ,start)))
                  (if delayed (list svar) nil)
                  t)))
           (t
            (get-inputs-for-svex-lst (cdr svex) modname modalist)))))

 (define get-inputs-for-svex-lst ((lst sv::svexlist-p)
                                  (modname sv::modname-p)
                                  (modalist sv::modalist-p))
   :returns (mv (wires wire-list-p
                       :hyp (sv::svexlist-p lst))
                (delayed sv::svarlist-p
                         :hyp (sv::svexlist-p lst))
                (success booleanp))
   (if (atom lst)
       (mv nil nil t)
     (b* (((mv rest rest-delayed success1)
           (get-inputs-for-svex (car lst) modname modalist))
          ((mv rest2 rest-delayed2 success2)
           (get-inputs-for-svex-lst (cdr lst) modname modalist)))
       (mv (append rest rest2)
           (append rest-delayed
                   rest-delayed2)
           (and success1 success2)))))

 ///

 (verify-guards get-inputs-for-svex))

(define assign-occ-merge-ins ((ins wire-list-p))
  :verify-guards nil
  :returns (res wire-list-p :hyp (wire-list-p ins))
  :prepwork
  ((local
    (defthm wire-p-implies-fc-1
      (implies (and (wire-p wire)
                    (and (consp wire) (consp (cdr wire))))
               (and (sv::svar-p (car wire))
                    (and (natp (cadr wire))
                         (integerp (cadr wire))
                         (acl2-numberp (cadr wire))
                         (rationalp (cadr wire)))
                    (natp (cddr wire))
                    (integerp (cddr wire))
                    (acl2-numberp (cddr wire))
                    (rationalp (cddr wire))))))

   (local
    (defthm wire-p-implies-fc-2
      (implies (and (wire-p wire)
                    (and (consp wire) (eq (cdr wire) nil)))

               (sv::svar-p (car wire)))))
   (local
    (defthm lemma1
      (implies (and (natp a)
                    (natp b)
                    (integerp c)
                    (or (< c a)
                        (<= c a)))
               (natp (+ b a (- c))))
      :hints (("goal"
               :in-theory (e/d (natp) ())))))

   (local
    (defthm lemma1-2
      (implies (and (natp a)
                    (natp b)
                    (integerp c)
                    (<= c a))
               (natp (+ (- c) b a)))
      :hints (("goal"
               :in-theory (e/d (natp) ())))))
   (local
    (defthm lemma2
      (implies (and (consp (assoc-equal name lst))
                    (wire-list-p lst))
               (wire-p (assoc-equal name lst)))
      ))

   (local
    (defthm lemma3
      (implies (and (assoc-equal name lst)
                    (wire-list-p lst))
               (wire-p (assoc-equal name lst)))
      )))

  (if (atom ins)
      nil
    (b* ((rest (assign-occ-merge-ins (cdr ins)))
         (cur (car ins))
         ((mv wire-name size start)
          (case-match cur
            ((wire-name size . start) (mv wire-name size start))
            ((wire-name) (mv wire-name -1 -1))
            (& (mv "" 0 0))))
         (other (assoc-equal wire-name rest))
         ((unless other)
          (cons-with-hint cur rest ins))
         ((mv o-size o-start)
          (case-match other
            ((& size . start) (mv size start))
            ((&) (mv -1 -1))
            (& (mv 0 0))))
         ((when (or (eql start -1) (eql o-start -1)))
          (cons `(,wire-name) rest))
         (end (+ start size))
         (o-end (+ o-start o-size))
         (new-start (min o-start start))
         (new-end (max o-end end))
         (new-size (- new-end new-start)))
      (cons `(,wire-name ,new-size . ,new-start)
            rest)))

  ///

  (defthm alistp-assign-occ-merge-ins
    (implies (wire-list-p ins)
             (alistp (assign-occ-merge-ins ins))))

  (verify-guards assign-occ-merge-ins
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (min max) ())))))

(define assign-occ-unify-ins ((ins wire-list-p))
  :prepwork
  ((local
    (defthm WIRE-LIST-P-FAST-ALIST-FORK
      (implies (and (wire-list-p ins)
                    (wire-list-p x))
               (wire-list-p (FAST-ALIST-FORk ins x)))
      :hints (("Goal"
               :in-theory (e/d (FAST-ALIST-FORK) ())))))
   (local
    (defthm lemma2
      (implies (and (wire-list-p ins))
               (wire-list-p (cdr (last ins))))
      :hints (("Goal"
               :in-theory (e/d (last) ()))))))

  :returns (res wire-list-p :hyp (wire-list-p ins))

  (fast-alist-clean (assign-occ-merge-ins ins)))

(define assign-to-tmp-occ ((lhs sv::lhs-p)
                           (rhs-svex sv::svex-p)
                           (modname sv::modname-p)
                           (modalist sv::modalist-p))
  :returns (res tmp-occ-p)
  (b* ((outs (lhs-to-svl-wirelist lhs))
       ((mv ins prev-ins success)
        (get-inputs-for-svex rhs-svex modname modalist))
       (- (or success
              (cw "Warning issued (assign-to-tmp-occ) for this svex: ~p0 ~
it may help to add a rewrite rule for this. ~%" rhs-svex)))

       (ins (assign-occ-unify-ins ins))
       (- (fast-alist-free ins)))
    (make-tmp-occ-assign
     :inputs ins
     :delayed-inputs prev-ins
     :outputs outs
     :svex rhs-svex)))

(define create-assign-occ-names ((trace trace-p)
                                 (prefix)
                                 (cnt natp))
  :prepwork ((local
              (in-theory (e/d (trace-p
                               sv::svar-p) ()))))
  :inline t
  (if (car trace)
      (cons (car trace) (sa prefix cnt))
    (sa prefix cnt)))

(define sv-mod->svl-occs-assigns ((assigns sv::assigns-p)
                                  (trace trace-p)
                                  (svl-aliasdb svl-aliasdb-p)
                                  (cnt natp)
                                  (modname sv::modname-p)
                                  (modalist sv::modalist-p)
                                  &key
                                  (rp::rp-state 'rp::rp-state)
                                  (state 'state))
  ;; Goal: convert all the assignsments into svl-type occs by replacing all the
  ;; aliases and adding the trace for flattening.
  ;; Also call svex-simplify for both lhs and rhs of assignments.
  :stobjs (state rp::rp-state)
  :guard (valid-rp-state-syntaxp rp-state)
  :verify-guards nil
  :returns (mv (tmp-occs tmp-occ-alist-p
                         :hyp (and (sv::assigns-p assigns)
                                   (trace-p trace)
                                   (svl-aliasdb-p svl-aliasdb)
                                   (sv::modname-p modname)
                                   (sv::modalist-p modalist)))
               (cnt-new natp :hyp (natp cnt))
               (rp::rp-state-res valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp::rp-state)))
  :prepwork
  ((local
    (in-theory (e/d (sv::Svex-p)
                    (rp::rp-statep
                     state-p)))))
  (cond
   ((atom assigns)
    (mv nil cnt rp::rp-state))
   (t
    (b* (;;(- (cw "Starting sv-mod->svl-occs-assigns ~%"))
         (cur (car assigns))
         ((sv::driver driver) (cdr cur))
         #|(- (if (not (equal driver.strength 6))
         (cw "Driver strength is not 6. For this assignment ~p0 ~%" cur) ;
         nil))||#
         (lhs-w (get-lhs-w (car cur)))

         ;; Prepare lhs-svex
         (lhs-svex (sv::lhs->svex (car cur)))

         ;;(- (cw "Calling update-svex-with-svl-aliasdb-and-trace ~%"))
         (lhs-svex (update-svex-with-svl-aliasdb-and-trace lhs-svex
                                                           svl-aliasdb
                                                           trace))

         ;;(- (cw "Calling svex-simplify ~%"))
         (lhs-svex `(sv::partsel 0 ,lhs-w ,lhs-svex))
         ((mv lhs-svex rp::rp-state) (svex-simplify lhs-svex
                                                    :reload-rules nil
                                                    :runes nil))

         ;; lhs svex to lhs
         (lhs (svex->lhs lhs-svex))

         ;; prepare rhs svex
         (rhs-svex driver.value)

         ;;(- (cw "hons-copy of rhs-svex... ~%"))
         ;;(rhs-svex (hons-copy rhs-svex))
         ;;(- (cw "calculating the size of rhs-svex... ~%"))
         ;;(- (cw "rhs-svex size: ~p0 ~%" (rp::cons-count rhs-svex)))

         ;;(- (cw "Calling update-svex-with-svl-aliasdb-and-trace ~%"))
         (rhs-svex (update-svex-with-svl-aliasdb-and-trace rhs-svex
                                                           svl-aliasdb
                                                           trace))

         ;;(- (cw "Calling svex-simplify ~%"))
         (rhs-svex `(sv::partsel 0 ,lhs-w ,rhs-svex))
         ((mv rhs-svex rp::rp-state) (svex-simplify rhs-svex
                                                    :reload-rules nil
                                                    :runes nil
                                                    :linearize :auto))

         ;;(- (cw "Calling svex->lhs ~%"))

         ;;(- (cw "Calling assign-to-occ ~%"))
         ;; convert lhs and rhs-svex to svl style occ object
         (tmp-occ (assign-to-tmp-occ lhs rhs-svex modname modalist))

         ;;(- (cw "Done: sv-mod->svl-occs-assigns ~%"))
         ((mv rest cnt-new rp::rp-state) (sv-mod->svl-occs-assigns (cdr assigns)
                                                                   trace
                                                                   svl-aliasdb
                                                                   (1+ cnt)
                                                                   modname
                                                                   modalist))
         #|(- (cw "Even more done: sv-mod->svl-occs-assigns ~%"))||#)
      ;; save and return the object.
      (mv (acons (create-assign-occ-names trace 'assign cnt) tmp-occ rest)
          cnt-new rp::rp-state))))
  ///

  (local
   (defthm tmp-occ-alist-p-implies-alistp
     (implies (tmp-occ-alist-p alist)
              (alistp alist))
     :hints (("Goal"
              :in-theory (e/d (tmp-occ-alist-p) ())))))

  (verify-guards sv-mod->svl-occs-assigns-fn))

(define sv-mod->svl-occs-module-aux ((sigs wire-list-p)
                                     (svl-aliasdb svl-aliasdb-p)
                                     (place)

                                     &key
                                     (rp::rp-state 'rp::rp-state)
                                     (state 'state))
  :prepwork ((local
              (in-theory (e/d ()
                              (rp::rp-statep)))))
  :guard (valid-rp-state-syntaxp rp-state)
  :verify-guards nil
  :returns (mv (res-outs module-occ-wire-list-p :hyp (wire-list-p sigs))
               (rp::rp-state-res valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp::rp-state)))
  (if (atom sigs)
      (mv nil rp::rp-state)
    (b* (((mv rest rp::rp-state)
          (sv-mod->svl-occs-module-aux (cdr sigs)
                                       svl-aliasdb
                                       place
                                       ))
         (cur (car sigs))
         (cur-name (car cur))
         (cur-w (if (and (consp (cdr cur))
                         (posp (cadr cur)))
                    (cadr cur)
                  (progn$ (cw "Warning! Unexpected wire without size in
                                     sv-mod->svl-occs-module-aux ~p0, place=~p1
                                     ~%"
                              cur place)
                          1)))

         (alias-svex (get-svex-from-svl-aliasdb cur-name place 0 svl-aliasdb))

         ((unless alias-svex)
          (mv (acons cur-name `(,(sv::make-lhrange
                                  :atom (sv::make-lhatom-var
                                         :name
                                         (sv::make-svar :name (if place
                                                                  (cons place cur-name)
                                                                cur-name)
                                                        :delay 0)
                                         :rsh 0)
                                  :w cur-w))
                     rest)
              rp::rp-state))
         (alias-svex `(sv::partsel 0 ,cur-w ,alias-svex))
         ((mv alias-svex rp::rp-state)
          (svex-simplify alias-svex
                         :reload-rules nil
                         :runes nil))
         (alias-lhs (svex->lhs alias-svex)))
      (mv (acons cur-name alias-lhs rest)
          rp::rp-state)))

  ///

  (verify-guards sv-mod->svl-occs-module-aux-fn
    :hints (("Goal"
             :in-theory (e/d (sv::svex-p)
                             ())))))

(define sv-mod->svl-occs-module ((modname sv::modname-p)
                                 (svl-aliasdb svl-aliasdb-p)
                                 (trace trace-p)
                                 (vl-insouts vl-insouts-sized-p)
                                 &key
                                 (rp::rp-state 'rp::rp-state)
                                 (state 'state))
  :prepwork ((local
              (in-theory (e/d (trace-p
                               vl-insouts-sized-p)
                              (RP::RP-STATEP)))))
  :returns (mv (tmp-occ tmp-occ-p)
               (rp::rp-state-res valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp::rp-state)))
  :guard (valid-rp-state-syntaxp rp-state)

  (declare (ignorable modname
                      trace
                      svl-aliasdb
                      vl-insouts
                      state
                      rp::rp-state))
  (b* ((this-vl-insouts (assoc-equal modname vl-insouts))
       ((unless this-vl-insouts)
        (progn$ (hard-error 'sv-mod->svl-occs-module
                            "Ins-outs for module ~p0 is missing ~%"
                            (list (cons #\0 modname)))
                (mv (make-tmp-occ-module :name modname) rp::rp-state)))
       (in-names (cadr this-vl-insouts))
       (out-names (cddr this-vl-insouts))
       (place (car trace))
       ((mv ins rp::rp-state) (sv-mod->svl-occs-module-aux in-names
                                                           svl-aliasdb
                                                           place
                                                           ))
       ((mv outs rp::rp-state) (sv-mod->svl-occs-module-aux out-names
                                                            svl-aliasdb
                                                            place
                                                            ))
       (tmp-occ (make-tmp-occ-module :inputs ins
                                     :outputs outs
                                     :name modname)))

    (mv tmp-occ rp::rp-state)))

(set-state-ok t)
;; :i-am-here
(acl2::defines
 sv-mod->svl-occs

 :prepwork
 ((local
   (in-theory (e/d (trace-p)
                   (rp::rp-statep
                    (:DEFINITION ALWAYS$)
                    (:DEFINITION MEMBER-EQUAL)
                    (:REWRITE ACL2::PLAIN-UQI-INTEGER-LISTP)
                    (:REWRITE ACL2::APPLY$-SYMBOL-ARITY-1)
                    (:REWRITE ACL2::APPLY$-PRIMITIVE)
                    (:META ACL2::APPLY$-PRIM-META-FN-CORRECT)
                    (:DEFINITION INTEGER-LISTP)
                    (:REWRITE ACL2::PLAIN-UQI-ACL2-NUMBER-LISTP)
                    (:DEFINITION ACL2::APPLY$-BADGEP)
                    (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                    (:REWRITE ACL2::NATP-OF-CAR-WHEN-NAT-LISTP)
                    (:DEFINITION RATIONAL-LISTP)
                    (:DEFINITION ACL2-NUMBER-LISTP)
                    (:REWRITE ACL2::RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))))))

 (define sv-mod->svl-occs ((modname sv::modname-p)
                           (modalist sv::modalist-p)
                           (svl-aliasdb svl-aliasdb-p)
                           (trace trace-p)
                           (mods-to-skip sv::modnamelist-p)
                           (vl-insouts vl-insouts-sized-p)

                           (limit natp "To prove termination")
                           &key
                           (rp::rp-state 'rp::rp-state)
                           (state 'state))
   :stobjs (state rp::rp-state)

   :verify-guards nil
   :measure (nfix limit)
   :guard (valid-rp-state-syntaxp rp-state)

   :returns (mv (tmp-occs tmp-occ-alist-p
                          :hyp (and (sv::modname-p modname)
                                    (sv::modalist-p modalist)
                                    (svl-aliasdb-p svl-aliasdb)
                                    (trace-p trace)
                                    (sv::modnamelist-p mods-to-skip)
                                    (vl-insouts-sized-p vl-insouts)))
                (rp::rp-state-res valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp::rp-state)))

   ;; Goal: by flattening, create all the occs including assigns and modules.
   (cond ((zp limit)
          (progn$ (hard-error 'mod-assigns->occs
                              "Limit Reached! ~%"
                              nil)
                  (mv nil rp::rp-state)))
         (t
          (b* ((module (hons-get modname modalist))
               ((unless module)
                (progn$
                 (hard-error 'mod-aliaspairlis$->svl-aliasdb-pt1
                             "Module not found in modalist ~p0 ~%"
                             (list (cons #\0 modname)))
                 (mv nil rp::rp-state)))
               (module (cdr module))
               ((sv::module module) module)
               ((mv assign-occs ?cnt rp::rp-state)
                (sv-mod->svl-occs-assigns module.assigns trace svl-aliasdb
                                          0
                                          modname modalist))
               ((mv insts-occs  rp::rp-state)
                (sv-mod->svl-occs-insts module.insts
                                        modalist
                                        svl-aliasdb
                                        trace
                                        mods-to-skip
                                        vl-insouts
                                        (1- limit))))
            (mv (append assign-occs insts-occs)  rp::rp-state)))))

 (define sv-mod->svl-occs-insts ((insts sv::modinstlist-p)
                                 (modalist sv::modalist-p)
                                 (svl-aliasdb svl-aliasdb-p)
                                 (trace trace-p)
                                 (mods-to-skip sv::modnamelist-p)
                                 (vl-insouts vl-insouts-sized-p)

                                 (limit natp "To prove termination")
                                 &key
                                 (rp::rp-state 'rp::rp-state)
                                 (state 'state))
   :stobjs (state rp::rp-state)
   :returns (mv
             (tmp-occs tmp-occ-alist-p
                       :hyp (and (sv::modinstlist-p insts)
                                 (sv::modalist-p modalist)
                                 (svl-aliasdb-p svl-aliasdb)
                                 (trace-p trace)
                                 (sv::modnamelist-p mods-to-skip)
                                 (vl-insouts-sized-p vl-insouts)))
             (rp::rp-state-res valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp::rp-state)))
   :guard (valid-rp-state-syntaxp rp-state)
   :measure (nfix limit)

   (cond ((zp limit)
          (progn$ (hard-error 'mod-assigns->occs
                              "Limit Reached! ~%"
                              nil)
                  (mv nil  rp::rp-state)))
         ((atom insts)
          (mv nil  rp::rp-state))
         (t
          (b* (((sv::modinst inst) (car insts))
               ((mv rest  rp::rp-state)
                (sv-mod->svl-occs-insts (cdr insts)
                                        modalist
                                        svl-aliasdb
                                        trace
                                        mods-to-skip
                                        vl-insouts

                                        (1- limit)))
               (trace-tmp (cons (if (consp trace)
                                    (cons-to-end (car trace) inst.instname)
                                  inst.instname)
                                trace))
               ((when (member-equal inst.modname mods-to-skip))
                (b* (((mv this-occ rp::rp-state)
                      (sv-mod->svl-occs-module inst.modname svl-aliasdb trace-tmp
                                               vl-insouts )))
                  (mv (acons (car trace-tmp)
                             this-occ
                             rest)
                      rp::rp-state)))
               ((svl-aliasdb svl-aliasdb) svl-aliasdb)
               #|(svl-aliasdb-tmp (hons-get inst.instname svl-aliasdb.sub))
               (svl-aliasdb-tmp (if svl-aliasdb (cdr svl-aliasdb) (make-svl-aliasdb)))||#

               ((mv cur-inst-occs  rp::rp-state)
                (sv-mod->svl-occs inst.modname
                                  modalist
                                  svl-aliasdb
                                  trace-tmp
                                  mods-to-skip
                                  vl-insouts

                                  (1- limit))))
            (mv (append cur-inst-occs rest)
                rp::rp-state)))))

 ///

 (local
  (defthm tmp-occ-alist-p-implies-true-listp
    (implies (tmp-occ-alist-p alist)
             (true-listp alist))))

 (local
  (defthm tmp-occ-alist-p-implies-alistp
    (implies (tmp-occ-alist-p alist)
             (alistp alist))))

 (verify-guards sv-mod->svl-occs-fn))

;;;;;; verify-guards checkpoint

(progn

  ;; Input or output signals might be aliased to some other signals.
  ;; If it is the case, then we'd have to create assignments for input and
  ;; output signals to assign those aliases for the main module.

  (define svl-flatten-mod-insert-assigns-for-inputs-aux ((input-wire wire-p)
                                                         (lhs sv::lhs-p)
                                                         (rsh natp)
                                                         (cnt natp)
                                                         (acc tmp-occ-alist-p))
    :prepwork
    ((local
      (in-theory (enable occ-name-p
                         sym-app-fnc
                         intern-in-package-of-symbol
                         svex-p
                         sv::svar-p)))
     (local
      (defthm tmp-occ-alist-p-is-alistp
        (implies (tmp-occ-alist-p alist)
                 (alistp$ alist)))))
    :returns (mv (res tmp-occ-alist-p :hyp (tmp-occ-alist-p acc))
                 (cnt-res natp :hyp (natp cnt)))
    :verify-guards nil
    (if (atom lhs)
        (mv acc cnt)
      (b* (((sv::lhrange cur-range) (car lhs))
           ((mv acc cnt)
            (svl-flatten-mod-insert-assigns-for-inputs-aux input-wire
                                                           (cdr lhs)
                                                           (+ rsh cur-range.w)
                                                           cnt
                                                           acc))
           ((when (eq (sv::lhatom-kind cur-range.atom) ':z))
            (mv acc cnt))
           (assign-rsh `(sv::partsel ,rsh
                                     ,cur-range.w
                                     ,(wire-name input-wire)))
           (assign-ins `((,(wire-name input-wire) ,cur-range.w . ,rsh)))
           (assign-outs `((,(sv::lhatom-var->name cur-range.atom)
                           ,cur-range.w
                           .
                           ,(sv::lhatom-var->rsh cur-range.atom))))
           (tmp-occ (make-tmp-occ-assign :inputs assign-ins
                                         :delayed-inputs nil
                                         :outputs assign-outs
                                         :svex assign-rsh)))
        (mv (acons (sa 'init_assign cnt)
                   tmp-occ
                   acc)
            (1+ cnt))))
    ///
    (verify-guards svl-flatten-mod-insert-assigns-for-inputs-aux))

  (define svl-flatten-mod-insert-assigns-for-inputs ((this-aliases alias-alist-p)
                                                     (inputs wire-list-p)
                                                     (cnt natp)

                                                     &key
                                                     (rp::rp-state 'rp::rp-state)
                                                     (state 'state))
    :guard (valid-rp-state-syntaxp rp-state)
    :verify-guards nil
    :returns (mv
              (assigns tmp-occ-alist-p)
              (cnt-res natp :hyp (natp cnt))
              (res-rp-state
               valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp-state)))
    (if (atom inputs)
        (mv nil cnt rp::rp-state)
      (b* (((mv rest cnt rp::rp-state)
            (svl-flatten-mod-insert-assigns-for-inputs this-aliases
                                                       (cdr inputs)
                                                       cnt
                                                       ))
           (cur (car inputs))
           (alias (hons-get (wire-name cur) this-aliases))
           ((unless alias)
            (mv rest cnt rp::rp-state))

           (alias-svex (cdr alias))
           (alias-svex `(sv::partsel 0 ,(acl2::pos-fix (wire-size cur)) ,alias-svex))
           ((mv alias-svex rp::rp-state)
            (svex-simplify alias-svex
                           :Reload-rules nil
                           :runes nil))
           (alias-lhs (svex->lhs alias-svex))
           ((mv assigns cnt)
            (svl-flatten-mod-insert-assigns-for-inputs-aux cur
                                                           alias-lhs
                                                           0
                                                           cnt
                                                           rest)))
        (mv assigns cnt rp::rp-state)))
    ///
    (verify-guards svl-flatten-mod-insert-assigns-for-inputs-fn
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (svex-p sv::svar-p) ())))))

  (define svl-flatten-mod-insert-assigns-for-outputs ((this-aliases alias-alist-p)
                                                      (outputs wire-list-p)
                                                      (cnt natp)

                                                      (modname sv::modname-p)
                                                      (modalist sv::modalist-p)
                                                      &key
                                                      (rp::rp-state 'rp::rp-state)
                                                      (state 'state))
    :guard (valid-rp-state-syntaxp rp-state)
    :verify-guards nil
    :returns (mv
              (res-tmp-occs tmp-occ-alist-p)
              (cnt-res natp :hyp (natp cnt))
              (res-rp-state
               valid-rp-state-syntaxp :hyp (valid-rp-state-syntaxp rp-state)))
    (if (atom outputs)
        (mv nil cnt rp::rp-state)
      (b* (((mv rest cnt rp::rp-state)
            (svl-flatten-mod-insert-assigns-for-outputs this-aliases
                                                        (cdr outputs)
                                                        cnt

                                                        modname
                                                        modalist))
           (cur (car outputs))

           (alias (hons-get (wire-name cur) this-aliases))
           ((unless alias)
            (mv rest cnt rp::rp-state))

           (alias-svex (cdr alias))
           (alias-svex `(sv::partsel 0 ,(acl2::pos-fix (wire-size cur)) ,alias-svex))
           ((mv alias-svex rp::rp-state)
            (svex-simplify alias-svex
                           :Reload-rules nil
                           :runes nil))
           ((mv ins prev-ins success)
            (get-inputs-for-svex alias-svex modname modalist))
           (- (or success
                  (cw "Warning issued (in alias-pairs) for this svex  ~p0 ~
it may help to add a rewrite rule for this. ~%" alias-svex)))
           (tmp-occ (make-tmp-occ-assign :inputs ins
                                         :delayed-inputs prev-ins
                                         :outputs `(,cur)
                                         :svex alias-svex)))
        (mv (acons (sa 'out_assign cnt) tmp-occ rest)
            (1+ cnt)
            rp::rp-state)))
    ///
    (verify-guards svl-flatten-mod-insert-assigns-for-outputs-fn
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (svex-p sv::svar-p) ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Create listeners...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sv->svl-listeners-uncovered-occs-get-added-occs-aux (occs alist)

  (if (atom occs)
      alist
    (sv->svl-listeners-uncovered-occs-get-added-occs-aux
     (cdr occs)
     (if (hons-get (car occs) alist)
         alist
       (hons-acons (car occs) nil alist)))))

(define sv->svl-listeners-uncovered-occs-get-added-occs (listeners)
  (if (atom listeners)
      nil
    (sv->svl-listeners-uncovered-occs-get-added-occs-aux
     (and (consp (car listeners)) (cdar listeners))
     (sv->svl-listeners-uncovered-occs-get-added-occs (cdr listeners)))))

(define sv->svl-listeners-get-missing-occs (added (all tmp-occ-alist-p))
  (if (atom all)
      nil
    (b* ((rest (sv->svl-listeners-get-missing-occs added (cdr all))))
      (if (hons-get (car (car all)) added)
          rest
        (cons (car (car all))
              rest)))))

(define sv->svl-listeners-uncovered-occs (listeners (all-occs tmp-occ-alist-p))
  ;; get the names of the unrefered occs by any listener in the listeners list.
  ;; they need to be executed initially because they may drive constants or something.
  (b* ((added-occs (sv->svl-listeners-uncovered-occs-get-added-occs
                    listeners))
       ;; added-occs is a fast-alist for quick membership lookup.
       (unadded-occs (sv->svl-listeners-get-missing-occs added-occs all-occs)))
    (progn$
     (fast-alist-free added-occs)
     unadded-occs)))

;; signals to occ listeners.
(progn
  (define create-signals-to-occ-listeners-module-aux ((lhs sv::lhs-p)
                                                      (occ-name occ-name-p)
                                                      (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom lhs)
        alist
      (b* ((atom (sv::lhrange->atom (car lhs)))
           ((when (equal (sv::lhatom-kind atom) ':z))
            (create-signals-to-occ-listeners-module-aux (cdr lhs)
                                                        occ-name
                                                        alist))
           (name (sv::lhatom-var->name atom))
           (entry (hons-get name alist))
           (alist (hons-acons name (cons occ-name (cdr entry)) alist)))
        (create-signals-to-occ-listeners-module-aux (cdr lhs)
                                                    occ-name
                                                    alist))))

  (define create-signals-to-occ-listeners-module ((module-ins
                                                   module-occ-wire-list-p)
                                                  (occ-name occ-name-p)
                                                  (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom module-ins)
        alist
      (b* ((cur-lhs (if (sv::lhs-p (cdar module-ins)) (cdar module-ins) nil))
           (alist (create-signals-to-occ-listeners-module-aux cur-lhs occ-name alist)))
        (create-signals-to-occ-listeners-module (cdr module-ins)
                                                occ-name
                                                alist))))

  (define create-signals-to-occ-listeners-assign ((wires wire-list-p)
                                                  (occ-name occ-name-p)
                                                  (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom wires)
        alist
      (b* ((wire (car wires))
           ((when (equal (wire-name wire) ':z))
            (create-signals-to-occ-listeners-assign (cdr wires)
                                                    occ-name
                                                    alist))
           (entry (hons-get (wire-name wire) alist))
           (alist (hons-acons (wire-name wire) (cons occ-name (cdr entry)) alist)))
        (create-signals-to-occ-listeners-assign (cdr wires)
                                                occ-name
                                                alist))))

  (define create-signal-to-occ-listeners ((occs tmp-occ-alist-p)
                                          (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom occs)
        alist
      (b* ((occ-name (caar occs))
           (tmp-occ (cdar occs))
           (alist
            (if (eq (tmp-occ-kind tmp-occ) ':module)
                (create-signals-to-occ-listeners-module (tmp-occ-module->inputs tmp-occ)
                                                        occ-name
                                                        alist)
              (create-signals-to-occ-listeners-assign (tmp-occ-assign->inputs tmp-occ)
                                                      occ-name
                                                      alist))))
        (create-signal-to-occ-listeners (cdr occs) alist)))))

;;;;

(progn
  (define check-intersection-for-lhs ((wire-name sv::svar-p)
                                      (start natp)
                                      (w natp)
                                      (lhs sv::lhs-p))
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   ((:e tau-system)))))
    (if (atom lhs)
        nil
      (b* (((sv::lhrange lhrange) (car lhs))
           ((when (eq (sv::lhatom-kind lhrange.atom) :z))
            (check-intersection-for-lhs wire-name
                                        start
                                        w
                                        (cdr lhs)))
           ((sv::lhatom-var var) lhrange.atom)

           (end (+ w start))
           (start2 var.rsh)
           (end2 (+ start2 lhrange.w)))
        (or (and (equal var.name wire-name)
                 (or (and (<= end2 end)
                          (< start end2))
                     (and (< start2 end)
                          (<= start start2))
                     (and (<= end end2)
                          (< start2 end))
                     (and (< start end2)
                          (<= start2 start))))
            (check-intersection-for-lhs wire-name
                                        start
                                        w
                                        (cdr lhs))))))

  (define check-intersection-for-wire-list ((wire-name sv::svar-p)
                                            (start natp)
                                            (w natp)
                                            (wires wire-list-p))
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   ((:e tau-system)))))
    (if (atom wires)
        nil
      (b* ((end (+ w start))
           (start2 (wire-start (car wires)))
           ((unless start2)
            (or (equal (wire-name (car wires)) wire-name)
                (check-intersection-for-wire-list wire-name
                                                  start
                                                  w
                                                  (cdr wires))))
           (end2 (+ start2 (wire-size (car wires))))
           #|(- (cw "start ~p0, end ~p1, start2 ~p2, end2 ~p3 ~%" start end
           start2 end2))||#)
        (or (and (equal (wire-name (car wires)) wire-name)
                 (or (and (<= end2 end)
                          (< start end2))
                     (and (< start2 end)
                          (<= start start2))
                     (and (<= end end2)
                          (< start2 end))
                     (and (< start end2)
                          (<= start2 start))
                     ))
            (check-intersection-for-wire-list wire-name
                                              start
                                              w
                                              (cdr wires))))))

  #|(check-intersection-for-wire-list '(:VAR ("product_terms" . 0) . 0)
  91 1
  '(((:VAR ("product_terms" . 0) . 0)
  97 . 0)
  ((:VAR ("product_terms" . 1) . 0)
  97 . 0)))||#

  (defun binary-append2 (acl2::x acl2::y)
    (declare (xargs :guard t))
    (cond ((atom acl2::x) acl2::y)
          (t (cons (car acl2::x)
                   (binary-append2 (cdr acl2::x)
                                   acl2::y)))))

  (define module-occ-wires->lhs ((inputs module-occ-wire-list-P))
    (if (atom inputs)
        nil
      (binary-append2
       (cdar inputs)
       (module-occ-wires->lhs (cdr inputs)))))

  (define does-intersect-occ-to-occ-listener ((wire-name sv::svar-p)
                                              (start natp)
                                              (w natp)
                                              (occ tmp-occ-p))
    (cond ((eq (tmp-occ-kind occ) ':module)
           (let ((lhs (module-occ-wires->lhs (tmp-occ-module->inputs occ))))
             (check-intersection-for-lhs wire-name
                                         start
                                         w
                                         (if (sv::lhs-p lhs)
                                             lhs
                                           nil))))
          (t
           (check-intersection-for-wire-list wire-name
                                             start
                                             w
                                             (tmp-occ-assign->inputs occ)))))

  #|(does-intersect-occ-to-occ-listener '(:VAR ("product_terms" . 0) . 0)
  91 1
  '(:ASSIGN
  (((:VAR ("product_terms" . 0) . 0)
  97 . 0)
  ((:VAR ("product_terms" . 1) . 0)
  97 . 0))
  NIL (("product_terms" 194 . 0))
  (CONCAT 97
  (PARTSEL 0 97 (:VAR ("product_terms" . 0) . 0))
  (PARTSEL 0 97 (:VAR
  ("product_terms" . 1) . 0)))))||#

  #| (define does-wires-intesect-with-occ ((wires wire-list-p)
  (occ occ-p)) ; ;
  (if (atom wires) ; ;
  nil ; ;
  (or (b* ((wire (car wire)) ; ;
  ((mv name start size) ; ;
  (mv (wire-name wire) (wire-start wire) (wire-size wire))) ; ;
  ((unless start) ; ;
  (hard-error 'does-wires-intesect-with-occ ; ;
  "Unexpected wire type ~p0 ~%" ; ;
  (list (cons #\0 wire))))) ; ;
  (does-intersect-occ-to-occ-listener name ; ;
  start ; ;
  size ; ;
  occ)) ; ;
  (does-wires-intesect-with-occ (cdr wires) ; ;
  occ)))) ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  (define does-lhs-intersect-with-occ ((lhs sv::lhs-p) ; ;
  (occ occ-p)) ; ;
  (if (atom lhs) ; ;
  nil ; ;
  (or (b* (((sv::lhrange lhrange) (car lhs)) ; ;
  ((unless (eq (sv::lhatom-kind lhrange.atom) ':z)) ; ;
  (does-lhs-intersect-with-occ (cdr lhs) occ))) ; ;
  (does-intersect-occ-to-occ-listener (sv::lhatom-var->name lhrange.atom) ; ;
  (sv::lhatom-var->rsh lhrange.atom) ; ;
  lhrange.rsh ; ;
  occ)) ; ;
  (does-lhs-intersect-with-occ (cdr lhs) ; ;
  occ))))||#

  (define member-equal-wrapper ((x)
                                (lst true-listp))
    :enabled t
    (member-equal x lst))

  (define get-intersecting-occs ((wire-name sv::svar-p)
                                 (start natp)
                                 (w natp)
                                 (occ-names occ-name-list-p)
                                 (all-tmp-occs tmp-occ-alist-p)
                                 (acc true-listp)
                                 &key
                                 (duplicate 'nil))
    :returns (res true-listp
                  :hyp (true-listp acc))
    (if (atom occ-names)
        acc
      (b* ((tmp-occ (hons-get (car occ-names) all-tmp-occs))
           (acc (get-intersecting-occs wire-name
                                       start
                                       w
                                       (cdr occ-names)
                                       all-tmp-occs
                                       acc
                                       :duplicate duplicate)))
        (if (and tmp-occ
                 (does-intersect-occ-to-occ-listener wire-name
                                                     start
                                                     w
                                                     (cdr tmp-occ))
                 (or duplicate
                     (not (member-equal (car occ-names) acc))))
            (cons (car occ-names) acc)
          acc))))

  #|(get-intersecting-occs '(:VAR ("product_terms" . 0) . 0)
  91
  1
  '(OUT_ASSIGN_0)
  '((OUT_ASSIGN_0 :ASSIGN
  (((:VAR ("product_terms" . 0) . 0)
  97 . 0)
  ((:VAR ("product_terms" . 1) . 0)
  97 . 0))
  NIL (("product_terms" 194 . 0))
  (CONCAT 97
  (PARTSEL 0 97 (:VAR ("product_terms" . 0) . 0))
  (PARTSEL 0 97 (:VAR
  ("product_terms" . 1) . 0)))))
  nil)||#

  (define get-intersecting-occ-for-lhs ((lhs sv::lhs-p)
                                        (sig-to-occ-listeners)
                                        (all-tmp-occs tmp-occ-alist-p))
    (if (atom lhs)
        nil
      (b* ((rest (get-intersecting-occ-for-lhs (cdr lhs)
                                               sig-to-occ-listeners
                                               all-tmp-occs))
           ((sv::lhrange range) (car lhs))
           ((when (eq (sv::lhatom-kind range.atom) ':z))
            rest)
           ((sv::lhatom-var atom) range.atom))
        (get-intersecting-occs atom.name
                               atom.rsh
                               range.w
                               (cdr (hons-get atom.name sig-to-occ-listeners))
                               all-tmp-occs
                               rest))))

  (define get-intersecting-occ-for-wires ((wires wire-list-p)
                                          (sig-to-occ-listeners)
                                          (all-tmp-occs tmp-occ-alist-p)
                                          &key
                                          (duplicate 'nil))
    :returns (res true-listp)
    (if (atom wires)
        nil
      (b* ((rest (get-intersecting-occ-for-wires (cdr wires)
                                                 sig-to-occ-listeners
                                                 all-tmp-occs
                                                 :duplicate duplicate))
           (wire (car wires))
           ((mv name start size)
            (mv (wire-name wire) (wire-start wire) (wire-size wire)))
           ((unless start)
            (hard-error 'get-intersecting-occ-for-wires
                        "Unexpected wire type ~p0 ~%"
                        (list (cons #\0 wire)))))
        (get-intersecting-occs name
                               start
                               size
                               (cdr (hons-get name sig-to-occ-listeners))
                               all-tmp-occs
                               rest
                               :duplicate duplicate))))

  (define create-occ-to-occ-listeners ((tmp-occs tmp-occ-alist-p)
                                       (all-tmp-occs tmp-occ-alist-p)
                                       (sig-to-occ-listeners))
    (if (atom tmp-occs)
        nil
      (b* ((occ-name (caar tmp-occs))
           (tmp-occ (cdar tmp-occs))
           (value (if (equal (tmp-occ-kind tmp-occ) ':assign)
                      (get-intersecting-occ-for-wires (tmp-occ-assign->outputs tmp-occ)
                                                      sig-to-occ-listeners
                                                      all-tmp-occs)
                    (b* ((lhs (module-occ-wires->lhs (tmp-occ-module->outputs tmp-occ))))
                      (get-intersecting-occ-for-lhs
                       (if (sv::lhs-p lhs) lhs
                         (hard-error
                          'create-occ-to-occ-listeners
                          "This should not have happened ~%"
                          nil))
                       sig-to-occ-listeners
                       all-tmp-occs))))
           #|(- (if (and (equal (occ-kind occ) ':assign)
           (equal occ-name 'ASSIGN_26))
           (cw "value ~p0, outputs ~p1, listeners ~p2, intersecting ~p3 ~%"
           value
           (occ-assign->outputs occ)
           (cdr (hons-get '(:VAR
           ("product_terms" . 0) . 0)
           sig-to-occ-listeners))
           (get-intersecting-occs '(:VAR ("product_terms" . 0) . 0)
           91
           1
           (cdr (hons-get '(:VAR
           ("product_terms" . 0) . 0)
           sig-to-occ-listeners))
           all-occs
           nil))
           nil))||#
           (rest (create-occ-to-occ-listeners (cdr tmp-occs)
                                              all-tmp-occs
                                              sig-to-occ-listeners)))
        (if value
            (acons occ-name value rest)
          rest)))))

(progn
  (define fast-unify-list ((vals true-listp))
    :returns (ret-val true-listp)
    (b* ((vals (pairlis$ vals nil))
         (vals (make-fast-alist vals))
         (vals (fast-alist-clean vals))
         (vals (fast-alist-free vals)))
      (if (alistp vals)
          (strip-cars vals)
        nil)))

  (define add-initial-to-occ-listeners ((input-wires wire-list-p)
                                        (all-tmp-occs tmp-occ-alist-p)
                                        (sig-to-occ-listeners)
                                        (occ-to-occ-listeners))
    ;;(declare (xargs :mode :program))
    (b* ((val1 (get-intersecting-occ-for-wires input-wires
                                               sig-to-occ-listeners
                                               all-tmp-occs
                                               :duplicate t))
         (val1 (fast-unify-list val1))
         (occ-to-occ-listeners (hons-acons ':initial val1
                                           occ-to-occ-listeners))
         (val2 (sv->svl-listeners-uncovered-occs occ-to-occ-listeners
                                                 all-tmp-occs))
         (val (append val1 val2)))
      (fast-alist-clean (hons-acons ':initial val
                                    occ-to-occ-listeners)))))

(define cut-list-until (e lst)
  (if (atom lst)
      nil
    (if (equal e (car lst))
        (list e)
      (cons (car lst)
            (cut-list-until e (cdr lst))))))

(acl2::defines
 find-loop
 (define find-loop (occ-name occ-to-occ-listeners
                             (trace true-listp)
                             &optional
                             (limit '(expt 2 30)))
   :guard (natp limit)
   :measure (nfix limit)
   (b* ((member (member-equal occ-name trace))
        ((when (or member
                   (zp limit)))
         (b* ((trace-cut (cut-list-until occ-name trace)))
           (progn$ (cw "Loop found for ~p0 in this trace: ~p1 ~%" occ-name
                       trace-cut)
                   trace-cut)))
        (lst (cdr (hons-get occ-name occ-to-occ-listeners))))
     (find-loop-lst lst occ-to-occ-listeners (cons occ-name trace) (1- limit))))
 (define find-loop-lst (lst
                        occ-to-occ-listeners
                        (trace true-listp) &optional
                        (limit '(expt 2 30)))
   :guard (natp limit)
   :measure (nfix limit)
   (if (or (atom lst)
           (zp limit))
       nil
     (or (find-loop (car lst) occ-to-occ-listeners trace (1- limit))
         (find-loop-lst (cdr lst) occ-to-occ-listeners trace (1- limit))))))

(define in-node-count-accp (acc)
  :enabled t
  (if (atom acc)
      t
    (and (consp (car acc))
         (natp (cdar acc))
         (in-node-count-accp (cdr acc))))
  ///

  (defthm in-node-count-accp-hons-assoc-lemma
    (implies (and (HONS-ASSOC-EQUAL key ACC)
                  (in-node-count-accp acc))
             (natp (CDR (HONS-ASSOC-EQUAL key ACC))))))

(local
 (defthm dummy-natp
   (implies (natp x)
            (natp (1+ x)))))

(Local
 (defthm in-node-count-accp-fast-alist-clean
   (implies (and (in-node-count-accp acc)
                 (in-node-count-accp alist)
                 )
            (in-node-count-accp (FAST-ALIST-FORK alist acc)))))

(local
 (defthm IN-NODE-COUNT-ACCP-last-lemma
   (implies (and (in-node-count-accp acc)
                 (consp acc))
            (in-node-count-accp (cdr (last acc))))))

(progn
  (define create-occ-in-nodes-count-aux ((occ-names)
                                         (acc in-node-count-accp))
    :returns (acc-res in-node-count-accp :hyp (in-node-count-accp acc))
    :verify-guards :after-returns
    (if (atom occ-names)
        acc
      (b* ((this (car occ-names))
           (entry (hons-get this acc))
           (val (if entry (1+ (cdr entry)) 1))
           (acc (hons-acons this val acc)))
        (create-occ-in-nodes-count-aux (cdr occ-names)
                                       acc))))

  (define create-occ-in-nodes-count ((listeners)
                                     (acc in-node-count-accp))
    ;; create an alist
    ;; keys are occ-names
    ;; and values are total number of other occs that need to be evaluated before.
    :returns (acc-res in-node-count-accp :hyp (in-node-count-accp acc))
    :verify-guards :after-returns
    (if (atom listeners)
        (fast-alist-clean acc)
      (create-occ-in-nodes-count (cdr listeners)
                                 (create-occ-in-nodes-count-aux (and (consp
                                                                      (car listeners))
                                                                     (cdar listeners))
                                                                acc))))

  (acl2::defines
   svl-sort-occs
   (define svl-sort-occs ((occ-name occ-name-p)
                          (all-tmp-occs tmp-occ-alist-p)
                          (occ-to-occ-listeners)
                          (occ-in-nodes-count in-node-count-accp)
                          &optional
                          (limit '(expt 2 30)))
     :guard (natp limit)
     :measure (nfix limit)
     :verify-guards :after-returns
     :returns (mv (res-occs tmp-occ-alist-p :hyp (tmp-occ-alist-p all-tmp-occs))
                  (res-occ-in-nodes-count in-node-count-accp
                                          :hyp (in-node-count-accp occ-in-nodes-count)))
     (b* (((when (zp limit))
           (mv nil nil))
          (tmp-occ (hons-get occ-name all-tmp-occs))
          (candidates (cdr (hons-get occ-name occ-to-occ-listeners)))
          ((mv rest occ-in-nodes-count)
           (svl-sort-occs-lst candidates all-tmp-occs occ-to-occ-listeners
                              occ-in-nodes-count
                              (1- limit))))
       (mv (if tmp-occ
               (cons tmp-occ rest)
             rest)
           occ-in-nodes-count)))

   (define svl-sort-occs-lst ((candidates occ-name-list-p
                                          "Occs that might be ready to add")
                              (all-tmp-occs tmp-occ-alist-p)
                              (occ-to-occ-listeners)
                              (occ-in-nodes-count in-node-count-accp)
                              &optional
                              (limit '(expt 2 30)))
     :guard (natp limit)
     :measure (nfix limit)
     :returns (mv (res-occs tmp-occ-alist-p :hyp (tmp-occ-alist-p all-tmp-occs))
                  (res-occ-in-nodes-count in-node-count-accp
                                          :hyp (in-node-count-accp occ-in-nodes-count)))
     (cond
      ((or (atom candidates)
           (zp limit))
       (mv nil occ-in-nodes-count))
      (t
       (b* ((cur (car candidates))
            (in-node-cnt (nfix (1- (nfix (cdr (hons-get cur occ-in-nodes-count))))))
            (occ-in-nodes-count (hons-acons cur in-node-cnt occ-in-nodes-count))
            ((mv added-occs occ-in-nodes-count)
             (if (equal in-node-cnt 0)
                 (svl-sort-occs cur all-tmp-occs occ-to-occ-listeners
                                occ-in-nodes-count
                                (1- limit))
               (mv nil occ-in-nodes-count)))
            ((mv rest occ-in-nodes-count)
             (svl-sort-occs-lst (cdr candidates)
                                all-tmp-occs
                                occ-to-occ-listeners
                                occ-in-nodes-count
                                (1- limit))))
         (mv (append added-occs rest)
             occ-in-nodes-count)))))
   ///
   (verify-guards svl-sort-occs-fn))

  ;; to check and make sure that all the occ are added.
  (define count-not-added-occs ((occ-in-nodes-count in-node-count-accp))
    (if (atom occ-in-nodes-count)
        0
      (+ (if (not (equal (cdar occ-in-nodes-count) 0))
             1
           0)
         (count-not-added-occs (cdr occ-in-nodes-count)))))

  (define get-not-added-module-occs ((all-tmp-occs tmp-occ-alist-p)
                                     (occ-in-nodes-count in-node-count-accp))

    (if (atom occ-in-nodes-count)
        nil
      (b* ((rest (get-not-added-module-occs all-tmp-occs (cdr occ-in-nodes-count)))
           (not-added (not (equal (cdar occ-in-nodes-count) 0)))
           (is-module (and (hons-get (caar occ-in-nodes-count) all-tmp-occs)
                           (equal (svl::tmp-occ-kind
                                   (cdr (hons-get (caar occ-in-nodes-count) all-tmp-occs)))
                                  ':module)))
           (module-name (if is-module (svl::tmp-occ-module->name (cdr (hons-get (caar occ-in-nodes-count)
                                                                                all-tmp-occs)))
                          nil)))
        (if (and not-added
                 is-module
                 (not (member-equal module-name rest)))
            (cons module-name rest)
          rest))))

  (define assoc-equals (keys alist)
    (if (atom keys)
        nil
      (cons (hons-assoc-equal (car keys) alist)
            (assoc-equals (cdr keys) alist))))

  (define svl-sort-occs-main ((all-tmp-occs tmp-occ-alist-p)
                              (occ-to-occ-listeners))
    :returns (res-tmp-occs tmp-occ-alist-p
                           :hyp (tmp-occ-alist-p all-tmp-occs))
    (b* ((occ-in-nodes-count (create-occ-in-nodes-count occ-to-occ-listeners
                                                        'occ-in-nodes-count))
         ((mv sorted-occs occ-in-nodes-count)
          (svl-sort-occs-lst (cdr (hons-get ':initial occ-to-occ-listeners))
                             all-tmp-occs
                             occ-to-occ-listeners
                             occ-in-nodes-count))
         (occ-in-nodes-count (fast-alist-clean occ-in-nodes-count))
         (not-added-occs-count (count-not-added-occs occ-in-nodes-count))
         (- (and (not (equal not-added-occs-count 0))
                 (progn$
                  (cw "~% ~% Not added modules: ~p0 ~%"
                      (get-not-added-module-occs all-tmp-occs
                                                 occ-in-nodes-count))
                  (b* ((found-loop (find-loop ':initial occ-to-occ-listeners
                                              nil))
                       (-
                        (fmt-to-comment-window "These occs are: ~p0 ~%"
                                               (list
                                                (cons #\0
                                                      (assoc-equals
                                                       found-loop
                                                       all-tmp-occs)))
                                               0
                                               '(nil 10 12 nil)
                                               nil)))
                    nil)
                  (hard-error
                   'svl-sort-occs-main
                   "~p0 occs are not added! Possibly a combinational loop~% ~%"
                   (list (cons #\0 not-added-occs-count))))))
         (- (fast-alist-free occ-in-nodes-count)))
      sorted-occs)))

;;;;;;;;;;;;;;

(define lhs->svex ((acl2::x sv::lhs-p))
  :returns (sv::xx svex-p)
  (if (atom acl2::x)
      0
    (b* (((sv::lhrange sv::xf) (car acl2::x)))
      (sv::svex-concat sv::xf.w
                       (sv::lhatom->svex sv::xf.atom)
                       (lhs->svex (cdr acl2::x))))))

(define lhslist->svex ((lhslist sv::lhslist-p))
  (if (atom lhslist)
      nil
    (b* ((cur (lhs->svex (car lhslist)))
         (cur (case-match cur
                (('sv::concat size ('sv::rsh start name) '0)
                 `(sv::partsel ,start ,size ,name))
                (('sv::concat size name '0)
                 `(sv::partsel 0 ,size ,name))
                (& cur))))
      (cons cur
            (lhslist->svex (cdr lhslist)))))
  ///

  (local
   (defthm lemma1
     (implies (and (force (svex-p a))
                   (force (svex-p b))
                   (force (svex-p c)))
              (SVEX-P (LIST 'PARTSEL a b c)))
     :hints (("Goal"
              :expand (SVEX-P (LIST 'PARTSEL a b c))
              :in-theory (e/d () ())))))

  (local
   (defthm lemma2
     (implies (and (svex-p main)
                   (case-match main (('sv::concat & ('sv::rsh & &) '0) t)))
              (and (svex-p (cadr main))
                   (svex-p (cadr (caddr main)))
                   (svex-p (caddr (caddr main)))))
     :hints (("Goal"
              :in-theory (e/d (svex-p) ())))))

  (local
   (defthm lemma3
     (implies (and (svex-p main)
                   (case-match main (('sv::concat & & '0) t)))
              (and (svex-p (cadr main))
                   (svex-p (caddr main))))
     :hints (("Goal"
              :in-theory (e/d (svex-p) ())))))

  (defthm svexlist-p-of-ljslist->svex
    (sv::svexlist-p (lhslist->svex lhslst))
    :hints (("Goal"
             :induct (lhslist->svex lhslst)
             :do-not-induct t
             :expand (LHSLIST->SVEX LHSLST)
             :in-theory (e/d () ())))))

(local
 (defthm SV-WIRE-ALIST-P-lemma
   (implies (and (SV-WIRE-ALIST-P WIRE-ALIST)
                 (HONS-ASSOC-EQUAL key
                                   WIRE-ALIST))
            (SV::WIRE-P (CDR (HONS-ASSOC-EQUAL key
                                               WIRE-ALIST))))))

(local
 (defthm wire-p-implies-fc
   (implies (wire-p wire)
            (consp wire))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d () ())))))

(define tmp-occs->svl-occs-assign ((occ-name occ-name-p)
                                   (outputs wire-list-p)
                                   (svex sv::svex-p)
                                   (wire-alist sv-wire-alist-p)
                                   (rsh natp))
  :verify-guards nil
  :returns (res svl-occ-alist-p)
  (if (atom outputs)
      nil
    (b* ((cur-output (car outputs))
         (only-1-output (and (atom (cdr outputs))
                             (equal rsh 0)))
         (wire  (hons-get (wire-name cur-output) wire-alist))
         (whole-wire-covered (and
                              wire
                              (equal (- (nfix (sv::wire->width (cdr wire)))
                                        (nfix (sv::wire->low-idx (cdr wire))))
                                     (wire-size cur-output))
                              (equal (wire-start cur-output)
                                     0)))
         (wire-size (acl2::pos-fix (wire-size cur-output)))
         (wire-start (nfix (wire-start cur-output))))
      (if only-1-output
          (acons occ-name
                 (make-svl-occ-assign
                  :output (wire-name cur-output)
                  :svex (if whole-wire-covered
                            svex
                          `(sv::partinst ,wire-start
                                         ,wire-size
                                         ,(wire-name cur-output)
                                         ,svex)))
                 nil)
        (acons (cons occ-name rsh)
               (make-svl-occ-assign
                :output (wire-name cur-output)
                :svex (if whole-wire-covered
                          `(partsel ,rsh ,wire-size ,svex)
                        `(sv::partinst ,wire-start
                                       ,wire-size
                                       ,(wire-name cur-output)
                                       (partsel ,rsh ,wire-size
                                                ,svex))))
               (tmp-occs->svl-occs-assign occ-name
                                          (cdr outputs)
                                          svex
                                          wire-alist
                                          (+ rsh wire-size))))))
  ///
  (verify-guards tmp-occs->svl-occs-assign
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (svex-p sv::Svar-p) ())))))

(progn
  (define lhrange->wire ((range sv::lhrange-p))
    :Returns (res wire-p)
    (b* (((sv::lhrange range) range))
      (if (equal (sv::lhatom-kind range.atom) :z)
          `(:z ,range.w . 0)
        `(,(sv::lhatom-var->name range.atom)
          ,range.w
          .
          ,(sv::lhatom-var->rsh range.atom)))))

  (define lhs->wire-list ((lhs sv::lhs-p))
    :returns (res wire-list-p)
    (if (atom lhs)
        nil
      (cons (lhrange->wire (car lhs))
            (lhs->wire-list (cdr lhs)))))

  (define lhslist->wire-list ((lhslist sv::lhslist-p))
    :returns (res wire-list-listp)
    (if (atom lhslist)
        nil
      (cons (lhs->wire-list (car lhslist))
            (lhslist->wire-list (cdr lhslist))))))


(define sv-wires-to-sv-wire-alist ((wires sv::wirelist-p))
  :returns (res sv-wire-alist-p
                :hyp (sv::wirelist-p wires)
                :hints (("Goal"
                         :in-theory (e/d (SV::WIRELIST-P)
                                         (SV::SVAR-P)))))
  (if (atom wires)
      nil
    (if (AND (CONSP (CAR WIRES))
             (CONSP (CAAR WIRES))
             (wire-p (CAAAR WIRES)))
        (hons-acons (CAAAR WIRES)
                    (car wires)
                    (sv-wires-to-sv-wire-alist (cdr wires)))
      (sv-wires-to-sv-wire-alist (cdr wires)))))

(local
 (defthm wire-list-p-implies-alistp
   (implies (wire-list-p list)
            (alistp list))))

(local
 (defthm module-occ-wire-list-p-implies-alistp
   (implies (module-occ-wire-list-p list)
            (alistp list))))

(define lhslist-fix-wog (lst)
  :returns (lst-res SV::LHSLIST-P)
  (if (atom lst)
      nil
    (if (sv::lhs-p (car lst))
        (cons-with-hint
         (car lst)
         (lhslist-fix-wog (cdr lst))
         lst)
      (lhslist-fix-wog (cdr lst)))))

(define tmp-occs->svl-occs ((tmp-occs tmp-occ-alist-p)
                            (wire-alist sv-wire-alist-p))
;:returns (res svl-occ-alist :hyp (occ-alist-p occs))
  :verify-guards :after-returns
  :returns (res svl-occ-alist-p)
  (cond
   ((atom tmp-occs) nil)
   ((equal (tmp-occ-kind (cdar tmp-occs)) ':assign)
    (b* (((tmp-occ-assign tmp-occ) (cdar tmp-occs))
         (new-svl-occs (tmp-occs->svl-occs-assign (caar tmp-occs)
                                                  tmp-occ.outputs
                                                  tmp-occ.svex
                                                  wire-alist 0)))
      (append new-svl-occs
              (tmp-occs->svl-occs (cdr tmp-occs) wire-alist))))
   (t (b* (((tmp-occ-module tmp-occ) (cdar tmp-occs)))
        (acons (caar tmp-occs)
               (make-svl-occ-module
                :inputs (lhslist->svex (lhslist-fix-wog (strip-cdrs tmp-occ.inputs)))
                :outputs (lhslist->wire-list (lhslist-fix-wog (strip-cdrs tmp-occ.outputs)))
                :name tmp-occ.name)
               (tmp-occs->svl-occs (cdr tmp-occs)
                                   wire-alist))))))

(define union-equal2 ((lst1)
                      (lst2 true-listp))
  :prepwork
  ((local
    (in-theory (disable (:DEFINITION ALWAYS$)))))

  (if (atom lst1)
      lst2
    (b* ((rest (union-equal2 (cdr lst1) lst2)))
      (if (member-equal (car lst1) rest)
          rest
        (cons (car lst1) rest))))
  ///
  (defthm svarlist-p-of-union-equal2
    (implies (and (sv::svarlist-p lst1)
                  (sv::svarlist-p lst2))
             (sv::svarlist-p (union-equal2 lst1 lst2)))
    :hints (("Goal"
             :in-theory (e/d (sv::svarlist-p union-equal2) ())))))

(define svl-collect-delayed-inputs ((tmp-occs tmp-occ-alist-p))
  :verify-guards :after-returns
  :returns (res sv::svarlist-p)
  (if (atom tmp-occs)
      nil
    (b* ((rest (svl-collect-delayed-inputs (cdr tmp-occs)))
         (tmp-occ (cdar tmp-occs)))
      (if (equal (tmp-occ-kind tmp-occ) ':module)
          rest
        (union-equal2 (tmp-occ-assign->delayed-inputs tmp-occ)
                      rest)))))

(defun svl-module-alist-entry-p (term)
  (and (consp term)
       (sv::modname-p (car term))
       (svl-module-p (cdr term))))

(define svl-flatten-mod ((modname sv::modname-p)
                         (modalist sv::modalist-p)
                         (mods-to-skip sv::modnamelist-p)
                         (vl-insouts vl-insouts-sized-p)

                         &key
                         (rp::rp-state 'rp::rp-state)
                         (state 'state))

  :guard (valid-rp-state-syntaxp rp-state)
  :verify-guards nil
  :returns (mv (res-module SVL-MODULE-alist-entry-p :hyp (sv::modname-p modname))
               (rp-state-res
                valid-rp-state-syntaxp
                :hyp (valid-rp-state-syntaxp rp-state)))
  (b* ((- (cw "Now working on mod: ~p0 ~%" modname))
       ((unless (hons-assoc-equal modname vl-insouts))
        (progn$
         (hard-error 'svl-flatten-mod
                     "Input/Output wire information for Module:~p0 is not
  found. This is probably a bug. Cannot continue... ~%"
                     (list (cons #\0 modname)))
         (mv (cons modname (make-svl-module)) rp::rp-state)))
       ((unless (hons-assoc-equal modname modalist))
        (progn$
         (hard-error 'svl-flatten-mod
                     "Module:~p0 is not
  found in sv::modalist. This is probably a bug. Cannot continue... ~%"
                     (list (cons #\0 modname)))
         (mv (cons modname (make-svl-module)) rp::rp-state)))
       ((mv input-wires output-wires)
        (mv (cadr (hons-assoc-equal modname vl-insouts))
            (cddr (hons-assoc-equal modname vl-insouts))))

       (- (cw "Processing alias-pairs... ~%"))
       ;; Create svl-aliasdb
       (svl-aliasdb (mod-aliaspairs->svl-aliasdb modname modalist
                                                 mods-to-skip))

       (- (cw "Creating occs... ~%"))
       ;; Create tmp-occs
       ((mv tmp-occs rp::rp-state) (sv-mod->svl-occs modname
                                                     modalist
                                                     svl-aliasdb
                                                     nil
                                                     mods-to-skip
                                                     vl-insouts

                                                     (expt 2 30)))

       ;; Expand occs for cases where input and output signals are aliased to
       ;; other signals
       ((mv init-occs-for-aliased-inputs & rp::rp-state)
        (svl-flatten-mod-insert-assigns-for-inputs (svl-aliasdb->this svl-aliasdb)
                                                   input-wires
                                                   0
                                                   ))
       ((mv occs-for-outputs & rp::rp-state)
        (svl-flatten-mod-insert-assigns-for-outputs (svl-aliasdb->this svl-aliasdb)
                                                    output-wires
                                                    0

                                                    modname
                                                    modalist))
       (tmp-occs (append init-occs-for-aliased-inputs occs-for-outputs tmp-occs))
       ;;(- (gc$))
       (- (cw "Sorting occs... ~%"))
       ;; Create Listeners.
       (tmp-occs (make-fast-alist tmp-occs)) ;; necessary for occ-to-occ listeners.
       (sig-to-occ-listeners (fast-alist-clean (create-signal-to-occ-listeners tmp-occs 'sig-to-occ-listeners)))
       (occ-to-occ-listeners (create-occ-to-occ-listeners tmp-occs tmp-occs sig-to-occ-listeners))
       (occ-to-occ-listeners (make-fast-alist occ-to-occ-listeners))
       (occ-to-occ-listeners (add-initial-to-occ-listeners input-wires tmp-occs
                                                           sig-to-occ-listeners
                                                           occ-to-occ-listeners))
       ;; Sort occs
       (sorted-occs (svl-sort-occs-main tmp-occs occ-to-occ-listeners))

       ;; Convert occs to to svl-occs
       (wires (sv::module->wires (cdr (hons-assoc-equal modname modalist))))
       (sv-wire-alist (sv-wires-to-sv-wire-alist wires))
       (new-svl-occs (tmp-occs->svl-occs sorted-occs sv-wire-alist))

       (- (free-svl-aliasdb svl-aliasdb))
       (- (fast-alist-free sv-wire-alist))
       (- (fast-alist-free tmp-occs))
       (- (fast-alist-free sig-to-occ-listeners))
       (- (fast-alist-free occ-to-occ-listeners))
       (- (cw "Done! ~% ~%"))
       (?module (cons modname
                      (make-svl-module :inputs input-wires
                                       :delayed-inputs
                                       (svl-collect-delayed-inputs tmp-occs)
                                       :outputs output-wires
                                       :occs new-svl-occs))))
    (mv module rp::rp-state))
  ///

  (local
   (defthm lemma1
     (implies (and (VL-INSOUTS-SIZED-P VL-INSOUTS)
                   (HONS-ASSOC-EQUAL MODNAME VL-INSOUTS))
              (and (WIRE-LIST-P (CADR (HONS-ASSOC-EQUAL MODNAME VL-INSOUTS)))
                   (CDR (HONS-ASSOC-EQUAL MODNAME VL-INSOUTS))
                   (consp (CDR (HONS-ASSOC-EQUAL MODNAME VL-INSOUTS)))
                   (WIRE-LIST-P (CdDR (HONS-ASSOC-EQUAL MODNAME VL-INSOUTS)))))
     :hints (("Goal"
              :in-theory (e/d (VL-INSOUTS-SIZED-P) (WIRE-LIST-P))))))

  (verify-guards svl-flatten-mod-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ())))))

#|(b* ((vl-insouts (vl-design-to-insouts *big-vl-design2* *big-sv-design*))
     (vl-insouts2 (vl-insouts-insert-wire-sizes vl-insouts *big-sv-design*
                                                '("full_adder_1$WIDTH=1"
                                                  "full_adder$WIDTH=1"
                                                  "booth2_reduction_dadda_17x65_97")
                                                ))
     (svex-simplify-preloaded (svex-simplify-preload)))
  (svl-flatten-mod "booth2_reduction_dadda_17x65_97"
                    (make-fast-alist (sv::design->modalist *big-sv-design*))
                    '("full_adder_1$WIDTH=1" "full_adder$WIDTH=1")
                    vl-insouts2
                    svex-simplify-preloaded))||#

(define svl-flatten-mods ((modnames sv::modnamelist-p)
                          (modalist sv::modalist-p)
                          (mods-to-skip sv::modnamelist-p)
                          (vl-insouts vl-insouts-sized-p)

                          &key
                          (rp::rp-state 'rp::rp-state)
                          (state 'state))
  :guard (valid-rp-state-syntaxp rp-state)
  :returns (mv (res-modules svl-module-alist-p
                            :hyp (sv::modnamelist-p modnames)
                            :hints (("subgoal *1/2"
                                     :use ((:instance
                                            svl-module-alist-entry-p-of-svl-flatten-mod.res-module
                                            (modname (car modnames)))))
                                    ("subgoal *1/3"
                                     :use ((:instance
                                            svl-module-alist-entry-p-of-svl-flatten-mod.res-module
                                            (modname (car modnames)))))
                                    ("goal"
                                     :in-theory (e/d ()
                                                     (svl-module-alist-entry-p-of-svl-flatten-mod.res-module)))))
               (rp-state-res
                valid-rp-state-syntaxp
                :hyp (valid-rp-state-syntaxp rp-state)))
  (if (atom modnames)
      (mv nil rp::rp-state)
    (b* (;;(- (gc$))
         ((mv this rp::rp-state)
          (svl-flatten-mod (car modnames)
                           modalist
                           mods-to-skip
                           vl-insouts
                           ))
         ((mv rest rp::rp-state)
          (svl-flatten-mods (cdr modnames)
                            modalist
                            mods-to-skip
                            vl-insouts
                            )))
      (mv (cons this rest)
          rp::rp-state))))

(define ranks-alistp (alist)
  :enabled t
  (if (atom alist)
      (equal alist nil)
    (and (consp (car alist))
         (sv::modname-p (caar alist))
         (natp (cdar alist))
         (ranks-alistp (cdr alist)))))

(acl2::defines
 svl-mod-calculate-ranks
 :prepwork
 ((Local
   (in-theory (disable natp max)))

  (local
   (defthm lemma1
     (implies
      (and (assoc-equal key alist)
           (ranks-alistp alist))
      (and (integerp (cdr (assoc-equal key alist)))
           (RATIONALP (cdr (assoc-equal key alist)))
           (natp (cdr (assoc-equal key alist)))))))

  (local
   (defthm lemma2
     (implies (and (natp x1)
                   (natp x2))
              (natp (max x1 x2)))
     :hints (("Goal"
              :in-theory (e/d (max) ())))))

  )
 (define svl-mod-calculate-ranks ((modname sv::modname-p)
                                  (modules svl-module-alist-p)
                                  (ranks ranks-alistp)
                                  (trace true-listp) ;; to check for module instantiation loops
                                  (limit natp) ;; to easily prove termination
                                  )
   :verify-guards nil
   ;; to profile...
   :measure (nfix limit)
   :returns (ranks-res ranks-alistp :hyp (and (ranks-alistp ranks)
                                              (sv::modname-p modname)))
   (cond
    ((zp limit)
     ranks)
    ((member-equal modname trace)
     (hard-error 'svl-mod-calculate-ranks
                 "It seems there's a loop in module instances. Trace = ~p0,
                                  module = ~p1 ~%"
                 (list (cons #\0 trace)
                       (cons #\1 modname))))
    (t  (b* ((module (assoc-equal modname modules))
             ((unless module) ranks)
             (module (cdr module))
             (occs (svl-module->occs module))
             ((mv max-occ-rank ranks)
              (svl-mod-calculate-ranks-occs occs
                                            modules
                                            ranks
                                            (cons modname trace)
                                            (1- limit))))
          (acons modname (1+ max-occ-rank) ranks)))))

 (define svl-mod-calculate-ranks-occs ((occs svl-occ-alist-p)
                                       (modules svl-module-alist-p)
                                       (ranks ranks-alistp)
                                       (trace true-listp)
                                       (limit natp))
   :measure (nfix limit)
   :returns (mv (max natp :hyp (ranks-alistp ranks))
                (ranks-res ranks-alistp :hyp (ranks-alistp ranks)))
   (cond
    ((zp limit)
     (mv 0 ranks))
    ((atom occs)
     (mv 0 ranks))
    (t
     (b* (((mv rest-max ranks)
           (svl-mod-calculate-ranks-occs (cdr occs) modules ranks trace (1- limit)))
          ((when (equal (svl-occ-kind (cdar occs)) :assign))
           (mv rest-max ranks))
          (modname (svl-occ-module->name (cdar occs)))
          (module-rank (assoc-equal modname ranks))
          ((when module-rank)
           (mv (max (cdr module-rank) rest-max) ranks))
          (ranks (svl-mod-calculate-ranks modname modules ranks trace (1- limit)))
          (module-rank (assoc-equal modname ranks))
          ((when module-rank)
           (mv (max (cdr module-rank) rest-max) ranks)))
       (mv 0
           (hard-error 'svl-mod-calculate-ranks
                       "Something is wrong. Cannot calculate rank for module ~p0~%"
                       (list (cons #\0 modname))))))))
 ///

 (local
  (defthm lemma3
    (implies (ranks-alistp alist)
             (alistp alist))))

 (local
  (defthm lemma4
    (implies (and (ASSOC-EQUAL MODNAME MODULES)
                  (SVL-MODULE-ALIST-P MODULES))
             (and (SVL-MODULE-P (CDR (ASSOC-EQUAL MODNAME MODULES)))
                  (CONSP (ASSOC-EQUAL MODNAME MODULES))))))

 (local
  (defthm lemma5
    (implies (and
              (alistp y)
              (assoc-equal x y))
             (consp (assoc-equal x y)))))

 (verify-guards svl-mod-calculate-ranks
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d () ())))))

(define update-modules-with-ranks ((ranks alistp)
                                   (modules svl-module-alist-p))
  (if (atom modules)
      nil
    (acons (caar modules)
           (change-svl-module (cdar modules)
                              :rank (nfix (cdr (assoc-equal (caar modules)
                                                            ranks))))
           (update-modules-with-ranks ranks
                                      (cdr modules)))))

(define get-string-modnames ((modnames sv::modnamelist-p))
  :returns (res string-listp)
  (if (atom modnames)
      nil
    (if (stringp (car modnames))
        (cons (car modnames)
              (get-string-modnames (cdr modnames)))
      (get-string-modnames (cdr modnames)))))

;; (str::strprefixp (concatenate 'string name "$") sv-module-name)

(progn
  (define fix-dont-aflatten-aux ((base stringp)
                                 (sv-module-names string-listp))
    :returns (res string-listp
                  :hyp (string-listp sv-module-names))
    (if (atom sv-module-names)
        nil
      (b* ((sv-module-name (car sv-module-names))
           (rest (fix-dont-aflatten-aux base
                                        (cdr sv-module-names))))
        (if (str::strprefixp (concatenate 'string base "$") sv-module-name)
            (cons sv-module-name
                  rest)
          rest))))

  (local
   (defthm string-listp-of-append
     (implies (and (string-listp x)
                   (string-listp y))
              (string-listp (append x y)))))

  (define fix-dont-flatten ((dont-flatten string-listp)
                            (sv-module-names string-listp))
    :returns (res string-listp :hyp (and (string-listp dont-flatten)
                                         (string-listp sv-module-names)))
    (if (atom dont-flatten)
        nil
      (b* ((extra-mod-names (fix-dont-aflatten-aux (car dont-flatten)
                                                   sv-module-names)))
        (append
         extra-mod-names
         (cons (car dont-flatten)
               (fix-dont-flatten (cdr dont-flatten)
                                 sv-module-names)))))))

(define clean-dont-flatten ((dont-flatten string-listp)
                            (all-modnames string-listp))
  :returns (res string-listp
                :hyp (string-listp dont-flatten))
  (if (atom dont-flatten)
      nil
    (b* ((rest (clean-dont-flatten (cdr dont-flatten) all-modnames)))
      (if (member-equal (car dont-flatten) all-modnames)
          (cons (car dont-flatten)
                rest)
        rest))))

(define get-mod-names-from-insts ((lst SV::MODINSTLIST-P))
  :Returns (modnames sv::modnamelist-p)
  (If (atom lst)
      nil
      (cons (sv::modinst->modname (car lst))
            (get-mod-names-from-insts (cdr lst)))))

(acl2::defines
 get-sv-submodules

 (define get-sv-submodules ((modname sv::modname-p)
                            (modalist sv::modalist-p)
                            (acc sv::modnamelist-p)
                            &optional
                            (limit '(expt 2 40)))
   :measure (nfix limit)
   :guard (natp limit)
   :verify-guards nil
   :returns (mod-names SV::MODNAMELIST-P
                       :hyp (and (sv::modname-p modname)
                                 (sv::modalist-p modalist)
                                 (sv::modnamelist-p acc)))

   (b* (((when (or (zp limit)
                   (not (stringp modname))
                   (member-equal modname acc)))
         acc)
        (mod (hons-assoc-equal modname modalist))
        ((unless mod)
         acc)
        (mod (cdr mod))
        (acc (cons modname acc))
        (modname-lst (get-mod-names-from-insts (sv::module->insts mod))))
     (get-sv-submodules-lst modname-lst modalist acc (1- limit))))

 (define get-sv-submodules-lst ((modname-lst sv::modnamelist-p)
                                (modalist sv::modalist-p)
                                (acc sv::modnamelist-p)
                                &optional
                                (limit '(expt 2 40)))
   :measure (nfix limit)
   :guard (natp limit)
   :returns (mod-names SV::MODNAMELIST-P
                       :hyp (and (sv::modnamelist-p modname-lst)
                                 (sv::modalist-p modalist)
                                 (sv::modnamelist-p acc)))
   (if (or (atom modname-lst)
           (zp limit))
       acc
     (get-sv-submodules-lst (cdr modname-lst)
                            modalist
                            (get-sv-submodules (car modname-lst)
                                               modalist
                                               acc
                                               (1- limit))
                            (1- limit))))
 ///
 (local
  (defthm lemma2
    (implies (and  (hons-assoc-equal MODNAME MODALIST)
                   (SV::MODALIST-P MODALIST))
             (and (SV::MODULE-P (CDR (hons-assoc-equal MODNAME MODALIST)))
                  (consp (hons-assoc-equal MODNAME MODALIST))))
    :hints (("Goal"
             :in-theory (e/d (SV::MODALIST-P) ())))))

 (verify-guards get-sv-submodules-fn))


(define svex-simplify-rules-fn ()
  (acl2::append-without-guard
   *svex-simplify-meta-rules*
   *svex-simplify-rules*))

(in-theory (disable (:e svex-simplify-rules-fn)))

(define svl-flatten-design ((sv-design sv::design-p)
                            (vl-design)
                            &key
                            (rp::rp-state 'rp::rp-state)
                            (dont-flatten 'nil) ;; names of modules that
                            ;; should not be flattened. It should be the
                            ;; original name of the module from Verilog
                            ;; designs. (but not from SV designs)
                            (top 'nil) ;; can override the top module.
                            (state 'state))
  ;;(declare (xargs :mode :program))
  :verify-guards nil
  :guard (and (or (not top)
                  (stringp top))
              (or (equal dont-flatten :all)
                  (string-listp dont-flatten)))
  :parents (acl2::svl)
  :short "Generate SVL designs from SV and VL Designs"
  :long "<p>Using SV and  VL (to determine the size of  the module inputs only)
designs, creates an SVL design. </p>
<code>
@('
(svl-flatten-design sv-design
                    vl-design
                    :dont-flatten ...
                    :top ...)
')
</code>
<p> The sv-design and vl-design arguments are mandatory @(see
sv::sv-tutorial). </p>

<p> The SVL system allows some of the modules to be flattened, and some
untouched to remain circuit hierarchy </p>

<p> :dont-flatten  List of names of  the modules that should  not be flattened.
They should  be the  original names  of the modules  from the  original Verilog
designs, but not  from SV designs. If users  want to  not flatten  all of the
modules, they can pass :all. By default, this value is set to nil, which tells
the system to flatten all the modules. </p>

<p> :top By default, this is set to nil. It tells the program to get the top
module name from SV Design, if the users want to select another module as top,
then they can provide the name of that module here. Then, only that module and
its submodules will be processed. If you pass a module name in dont-flatten
that is not a submodule of top, that module will be processed anyway as well.</p>

<p> :rp-state and :state are STOBJs. Users do not need to make assignments to
them.
</p>
"
  (b* (((sv::design sv-design) sv-design)
       (sv-design.modalist (true-list-fix (make-fast-alist sv-design.modalist)))

       (all-modnames (get-string-modnames (strip-cars sv-design.modalist)))
       (dont-flatten-all (equal dont-flatten ':all))
       (top (if top top (progn$ (if (stringp sv-design.top)
                                    sv-design.top
                                  (or (hard-error 'svl-flatten-design
                                                  "sv-design.top name is not string~%" nil)
                                      "")))))
       (dont-flatten (if dont-flatten-all
                         (get-sv-submodules top sv-design.modalist nil)
                       (fix-dont-flatten
                        (union-equal dont-flatten
                                     (list top))
                        all-modnames)))

       (vl-insouts (vl-design-to-insouts-wrapper vl-design
                                                 sv-design
                                                 dont-flatten
                                                 state))

       (dont-flatten
        (if dont-flatten-all
            dont-flatten
          (clean-dont-flatten dont-flatten all-modnames)))

       (vl-insouts (vl-insouts-insert-wire-sizes vl-insouts sv-design
                                                 dont-flatten))

       (rp-state (rp::rp-state-new-run rp::rp-state))
       (rp-state (rp::rp-state-init-rules (svex-simplify-rules-fn) nil nil rp::rp-state state))

       (- (cw "Starting to flatten modules and create SVL design... ~%"))
       ((mv modules rp::rp-state)
        (svl-flatten-mods dont-flatten sv-design.modalist
                          dont-flatten vl-insouts
                          ))
       (- (hons-clear t))
       (- (cw "Inserting ranks to unflattened modules... ~%"))
       (ranks (svl-mod-calculate-ranks top
                                       modules
                                       nil
                                       nil
                                       (expt 2 30)))
       (modules (update-modules-with-ranks ranks
                                           modules))
       (- (cw "All done! ~%"))
       (- (fast-alist-free sv-design.modalist))

       ;;(- (gc$))
       )
    (mv modules rp::rp-state))
  ///

  (local
   (defthm lemma1
     (IMPLIES (and (true-listp alist)
                   (sv::modalist-p alist))
              (ALISTP alist))))

  (local
   (defthm lemma2
     (IMPLIES (AND (SV::MODALIST-P alist))
              (SV::MODNAMELIST-P (STRIP-CARS alist)))
     :hints (("Goal"
              :in-theory (e/d (SV::DESIGN->MODALIST
                               SV::MODNAMELIST-P)
                              ())))))

  (local
   (defthm lemma3
     (implies (and (string-listp x1)
                   (string-listp x2))
              (string-listp (UNION-EQUAL x1 x2)))))

  (local
   (defthm lemma4
     (implies (stringp top)
              (SV::MODNAME-P TOP))
     :hints (("Goal"
              :in-theory (e/d (SV::MODNAME-P) ())))))

  (local
   (defthm lemma5
     (implies (ranks-alistp alist)
              (alistp alist))))

  (local
   (defthm lemma6
     (implies (STRING-LISTP lst)
              (TRUE-LISTP lst))))

  (local
   (defthm lemma7
     (implies (STRING-LISTP lst)
              (SV::MODNAMELIST-P lst))
     :hints (("Goal"
              :in-theory (e/d (SV::MODNAMELIST-P
                               SV::MODNAME-P)
                              ())))))

  (verify-guards acl2::svl-flatten-design-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))


  )

(define svl-modules-port-info ((modules svl-module-alist-p))
  (if (atom modules)
      nil
    (acons (caar modules)
           `((:inputs . ,(svl-module->inputs (cdar modules)))
             (:outputs . ,(svl-module->outputs (cdar modules))))
           (svl-modules-port-info (cdr modules)))))

;;;

;;

;;;;

#|
:i-am-here

(b* ((modnames '("fa" "mul_test1" "partial")))
  (svl-flatten-design modnames
                       *booth-sv-design*
                       *booth-vl-design2*))

(b* ((modnames '("full_adder_1$WIDTH=1"
                 "full_adder$WIDTH=1"
                 "booth2_reduction_dadda_17x65_97"
                 "booth2_multiplier_signed_64x32_97")))
  (svl-flatten-design modnames
                       *big-sv-design*
                       *big-vl-design2*))

#|(svl-flatten-mod "booth_encoder"
                 (make-fast-alist (sv::design->modalist *booth-sv-design*))
nil)||#

(b* ((vl-insouts (vl-design-to-insouts *big-vl-design2* *big-sv-design*))
(vl-insouts2 (vl-insouts-insert-wire-sizes vl-insouts *big-sv-design*
'("full_adder_1$WIDTH=1"
"full_adder$WIDTH=1"
"booth2_reduction_dadda_17x65_97"
"booth2_multiplier_signed_64x32_97")
)))
(svl-flatten-mod "booth2_multiplier_signed_64x32_97"
(make-fast-alist (sv::design->modalist *big-sv-design*))
'("full_adder_1$WIDTH=1" "full_adder$WIDTH=1" "booth2_reduction_dadda_17x65_97")
vl-insouts2))

(b* ((vl-insouts (vl-design-to-insouts *big-vl-design2* *big-sv-design*))
(vl-insouts2 (vl-insouts-insert-wire-sizes vl-insouts *big-sv-design*
'("full_adder_1$WIDTH=1"
"full_adder$WIDTH=1"
"booth2_reduction_dadda_17x65_97")
))
(svex-simplify-preloaded (svex-simplify-preload)))
(svl-flatten-mod "booth2_reduction_dadda_17x65_97"
(make-fast-alist (sv::design->modalist *big-sv-design*))
'("full_adder_1$WIDTH=1" "full_adder$WIDTH=1")
vl-insouts2
svex-simplify-preloaded))
||#
