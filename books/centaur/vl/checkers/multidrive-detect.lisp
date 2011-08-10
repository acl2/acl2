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
(include-book "duplicate-detect")
(include-book "../mlib/lvalues")
(include-book "../mlib/wirealist")
(local (include-book "../util/arithmetic"))
(include-book "../../misc/fal-graphs")

;; bozo build me in earlier
(include-book "centaur/misc/hons-extra" :dir :system)

(local (in-theory (disable mergesort difference))) ;; bozo why is this enabled?





; Notes about our heuristics:
;
;  - Warnings are minor if "mux" is in the module name.
;  - Warnings are minor for wires whose names include "mux" or "ph1"
;
; BOZO It would be nice to also only issue minor warnings if the module has
; transistor-level stuff in it.  But that's kind of hard to define (e.g.,
; wrapper modules for transistors like upmos).  So, for now I don't try to do
; that.



; Most of the tools we need for finding multiply-driven wires are already
; available.  Recall, from xf-make-defm-command:
;
; (vl-module-wirealist mod warnings) -> (successp warnings walist)
;
;   * walist is a fast alist and must be freed
;
;   * only builds the walist for netdecls
;     (doesn't get regdecls, implicit wires)
;
;   * fails if resulting wires aren't unique
;     (should be extraordinarily unlikely)
;
; And also recall from mu-lvalue:
;
; (vl-msb-expr-bitlist x walist warnings) -> (mv successp warnings bitlist)
;
;   * x is an expression that can have:  constant/weird integers, bit/part
;     selects, concatenations, replications
;
;       NOTE: this is a superset of the valid lvalues
;
;   * fails gracefully (successp = nil, extends warnings) when x is not
;     of this form


(defsection vl-multidrive-filter-innocuous-wires

  (defund vl-multidrive-innocuous-wirename-p (x)
    (declare (xargs :guard (symbolp x)))
    (let ((name (symbol-name x)))
      (or (equal name "latchout")
          (equal name "vss0")
          (equal name "vdd0")
          (equal name "vdd3")
          (str::isubstrp "mux" name)
          (str::isubstrp "clk" name)
          (str::isubstrp "net" name)
          (str::isubstrp "ph1" name)
          (str::isubstrp "ph2" name))))

  (defund vl-multidrive-filter-innocuous-wires (x innocuous other)
    (declare (xargs :guard (symbol-listp x)))
    (b* (((when (atom x))
          (mv innocuous other))
         (car-innocuousp (vl-multidrive-innocuous-wirename-p (car x)))
         (innocuous (if car-innocuousp
                        (cons (car x) innocuous)
                      innocuous))
         (other (if car-innocuousp
                    other
                  (cons (car x) other))))
      (vl-multidrive-filter-innocuous-wires (cdr x) innocuous other)))

  (local (in-theory (enable vl-multidrive-filter-innocuous-wires)))

  (defthm vl-multidrive-filter-innocuous-wires-basics
    (implies
     (and (force (symbol-listp x))
          (force (symbol-listp innocuous))
          (force (symbol-listp other)))
     (let ((result (vl-multidrive-filter-innocuous-wires x innocuous other)))
       (and (symbol-listp (mv-nth 0 result))
            (symbol-listp (mv-nth 1 result)))))))



(defsection vl-multidrive-filter-exotic-wires

; We don't want to report multiple drivers of wires that have types like TRI
; and WOR, since they typically ought to have multiple drivers.

  (defund vl-multidrive-collect-exotic-netdecls (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (b* (((when (atom x))
          nil)
         (type1 (vl-netdecl->type (car x)))
         ((when (or (eq type1 :vl-tri)
                    (eq type1 :vl-triand)
                    (eq type1 :vl-trior)
                    (eq type1 :vl-tri0)
                    (eq type1 :vl-tri0)
                    (eq type1 :vl-trireg)
                    (eq type1 :vl-wand)
                    (eq type1 :vl-wor)))
          (cons (car x)
                (vl-multidrive-collect-exotic-netdecls (cdr x)))))
      (vl-multidrive-collect-exotic-netdecls (cdr x))))

  (defthm vl-netdecllist-p-of-vl-multidrive-collect-exotic-netdecls
    (implies (force (vl-netdecllist-p x))
             (vl-netdecllist-p (vl-multidrive-collect-exotic-netdecls x)))
    :hints(("Goal" :in-theory (enable vl-multidrive-collect-exotic-netdecls))))

  (defund vl-multidrive-exotic-bits (netdecls walist)
    ;; Build the set of all bits from exotic wires.
    (declare (xargs :guard (and (vl-netdecllist-p netdecls)
                                (vl-wirealist-p walist))))
    (b* ((exotic-decls (vl-multidrive-collect-exotic-netdecls netdecls))
         (exotic-names (vl-netdecllist->names exotic-decls))
         (exotic-fal   (acl2::fal-extract exotic-names walist))
         (exotic-bits  (append-domains exotic-fal)))
      exotic-bits)))


(defund vl-z-expr-p (x)
  (declare (Xargs :guard (vl-expr-p x)))
  (if (vl-atom-p x)
      (vl-zatom-p x)
    (b* (((vl-nonatom x) x))
      (and (eq x.op :vl-qmark)
           (or (and (vl-atom-p (cadr x.args))
                    (vl-zatom-p (cadr x.args)))
               (and (vl-atom-p (caddr x.args))
                    (vl-zatom-p (caddr x.args))))))))

(defund vl-z-assign-p (x)
  (declare (xargs :guard (vl-assign-p x)))
  (vl-z-expr-p (vl-assign->expr x)))

(defund vl-remove-z-assigns (x)
  (declare (Xargs :guard (vl-assignlist-p x)))
  (if (atom x)
      nil
    (if (vl-z-assign-p (car x))
        (vl-remove-z-assigns (cdr x))
      (cons (car x)
            (vl-remove-z-assigns (cdr x))))))

(defund vl-keep-z-assigns (x)
  (declare (Xargs :guard (vl-assignlist-p x)))
  (if (atom x)
      nil
    (if (vl-z-assign-p (car x))
        (cons (car x)
              (vl-keep-z-assigns (cdr x)))
      (vl-keep-z-assigns (cdr x)))))

(defthm vl-assignlist-p-of-vl-remove-z-assigns
  (implies (vl-assignlist-p x)
           (vl-assignlist-p (vl-remove-z-assigns x)))
  :hints(("Goal" :in-theory (enable vl-remove-z-assigns))))

(defthm vl-assignlist-p-of-vl-keep-z-assigns
  (implies (vl-assignlist-p x)
           (vl-assignlist-p (vl-keep-z-assigns x)))
  :hints(("Goal" :in-theory (enable vl-keep-z-assigns))))


(defund vl-z-gatetype-p (x)
  (declare (xargs :guard t))
  (member x '(:vl-cmos
              :vl-rcmos
              :vl-bufif0
              :vl-bufif1
              :vl-notif0
              :vl-notif1
              :vl-nmos
              :vl-pmos
              :vl-rnmos
              :vl-rpmos
              :vl-tranif0
              :vl-tranif1
              :vl-rtranif1
              :vl-rtranif0
              :vl-tran
              :vl-rtran
              :vl-pulldown
              :vl-pullup)))

(defund vl-z-gateinst-p (x)
  (declare (Xargs :guard (vl-gateinst-p x)))
  (b* (((vl-gateinst x) x))
    (vl-z-gatetype-p x.type)))

(defund vl-remove-z-gateinsts (x)
  (declare (Xargs :guard (vl-gateinstlist-p x)))
  (if (atom x)
      nil
    (if (vl-z-gateinst-p (car x))
        (vl-remove-z-gateinsts (cdr x))
      (cons (car x) (vl-remove-z-gateinsts (cdr x))))))

(defund vl-keep-z-gateinsts (x)
  (declare (Xargs :guard (vl-gateinstlist-p x)))
  (if (atom x)
      nil
    (if (vl-z-gateinst-p (car x))
        (cons (car x) (vl-keep-z-gateinsts (cdr x)))
      (vl-keep-z-gateinsts (cdr x)))))

(defthm vl-gateinstlist-p-of-vl-remove-z-gateinsts
  (implies (vl-gateinstlist-p x)
           (vl-gateinstlist-p (vl-remove-z-gateinsts x)))
  :hints(("Goal" :in-theory (enable vl-remove-z-gateinsts))))

(defthm vl-gateinstlist-p-of-vl-keep-z-gateinsts
  (implies (vl-gateinstlist-p x)
           (vl-gateinstlist-p (vl-keep-z-gateinsts x)))
  :hints(("Goal" :in-theory (enable vl-keep-z-gateinsts))))



; Treating some modinsts as "Z drivers"
;
; As a preprocessing step, we split module instances that have both inouts and
; output ports into two modinsts, one without any inouts (that we regard as a
; non-z driver) and one with only the inouts (that we regard as a z driver).
;
; We also consider the name of the module to be relevant.

(defund vl-z-modinst-p (x)
  ;; Modules we regard as Z drivers by name
  ;; BOZO maybe make me an attachable function someday
  (declare (xargs :guard (vl-modinst-p x)))
  (member-equal (vl-modinst->modname x)
                '("unmos"
                  "upmos"
                  "urnmos"
                  "urpmos"
                  "uwnmos"
                  "uwpmos"
                  "n_fdbk"
                  "n_pchg"
                  "p_fdbk"
                  "p_pchg"
                  "open"
                  "short"
                  "unmos_xtor"
                  "upmos_xtor"
                  "urnmos_xtor"
                  "urpmos_xtor"
                  "uwnmos_xtor"
                  "uwpmos_xtor"
                  "n_fdbk_xtor"
                  "n_pchg_xtor"
                  "p_fdbk_xtor"
                  "p_pchg_xtor"
                  "open_xtor"
                  "short_xtor")))


(defsection vl-zsplit-plainargs

  (defund vl-zsplit-plainargs (x)
    "Returns (MV OUTPUTS INOUTS)"
    (declare (xargs :guard (vl-plainarglist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-outs cdr-inouts)
          (vl-zsplit-plainargs (cdr x)))
         ((when (eq (vl-plainarg->dir (car x)) :vl-output))
          (mv (cons (car x) cdr-outs) cdr-inouts))
         ((when (eq (vl-plainarg->dir (car x)) :vl-inout))
          (mv cdr-outs (cons (car x) cdr-inouts))))
      (mv cdr-outs cdr-inouts)))

  (local (in-theory (enable vl-zsplit-plainargs)))

  (defthm vl-plainarglist-p-of-vl-zsplit-plainargs-0
    (implies (vl-plainarglist-p x)
             (vl-plainarglist-p (mv-nth 0 (vl-zsplit-plainargs x)))))

  (defthm vl-plainarglist-p-of-vl-zsplit-plainargs-1
    (implies (vl-plainarglist-p x)
             (vl-plainarglist-p (mv-nth 1 (vl-zsplit-plainargs x))))))

(defsection vl-zsplit-modinsts

  (defund vl-zsplit-modinsts (x)
    "Returns (MV ZINSTS NON-Z-INSTS)"
    (declare (xargs :guard (vl-modinstlist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-z cdr-nonz)
          (vl-zsplit-modinsts (cdr x)))
         ((when (vl-z-modinst-p (car x)))
          (mv (cons (car x) cdr-z) cdr-nonz))

         (args (vl-modinst->portargs (car x)))
         ((when (vl-arguments->namedp args))
          ;; It's broken anyway, just put it as non-z, we warn about it later
          (mv cdr-z (cons (car x) cdr-nonz)))
         ((mv out-args inout-args)
          (vl-zsplit-plainargs (vl-arguments->args args)))

         ((when (and (not out-args)
                     (not inout-args)))
          (mv cdr-z cdr-nonz))

         ((when (not inout-args))
          ;; All just normal outputs, so it's non-z.
          (mv cdr-z (cons (car x) cdr-nonz)))

         ((when (not out-args))
          ;; All inout outputs, so call it a z driver
          (mv (cons (car x) cdr-z) cdr-nonz))

         ;; Okay, make goofy modinsts that will just grab the outputs and the inouts
         ;; separately.
         (z-modinst (change-vl-modinst (car x) :portargs (vl-arguments nil inout-args)))
         (nonz-modinst (change-vl-modinst (car x) :portargs (vl-arguments nil out-args))))
      (mv (cons z-modinst cdr-z)
          (cons nonz-modinst cdr-nonz))))

  (local (in-theory (enable vl-zsplit-modinsts)))

  (defthm vl-modinstlist-p-of-vl-zsplit-modinst-0
    (implies (vl-modinstlist-p x)
             (vl-modinstlist-p (mv-nth 0 (vl-zsplit-modinsts x)))))

  (defthm vl-modinstlist-p-of-vl-zsplit-modinst-1
    (implies (vl-modinstlist-p x)
             (vl-modinstlist-p (mv-nth 1 (vl-zsplit-modinsts x))))))




; As another twist, we drop the instance names so we can detect instances that
; are identical except for their names.  We'll add a different kind of warning
; for these, along the lines of duplicate detection.

(defsection vl-modinst-name-drop-fix

  (defund vl-modinst-name-drop-fix (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (change-vl-modinst (vl-modinst-fix x)
                       :instname nil))

  (local (in-theory (enable vl-modinst-name-drop-fix)))

  (defthm vl-modinst-p-of-vl-modinst-name-drop-fix
    (implies (force (vl-modinst-p x))
             (vl-modinst-p (vl-modinst-name-drop-fix x)))))

(defprojection vl-modinstlist-name-drop-fix (x)
  (vl-modinst-name-drop-fix x)
  :guard (vl-modinstlist-p x)
  :result-type vl-modinstlist-p)

(defsection vl-modinst-same-warning

  (defund vl-modinst-same-warning (modname target-modname instname-list)
    (declare (xargs :guard (and (stringp modname)
                                ;; target-modname is a string
                                ;; instname-list is a string list
                                )))
    (make-vl-warning
     :type (if (ec-call (str::isubstrp "ph1" target-modname))
               :vl-warn-instances-same-minor
             :vl-warn-instances-same)
     :msg  "In module ~m0, found multiple instances of module ~m1 with ~
            identical arguments: ~&2."
     :args (list modname target-modname instname-list)
     :fatalp nil
     :fn 'vl-modinst-same-warning))

  (local (in-theory (enable vl-modinst-same-warning)))

  (defthm vl-warning-p-of-vl-modinst-same-warning
    (vl-warning-p (vl-modinst-same-warning modname target-modname instname-list))))

(defund vl-modinsts-same-warning (modname alist)
  (declare (xargs :guard (and (stringp modname)
                              ;; alist is the mapping from fixed-up instances
                              ;; to instance-name lists.
                              )))
  (if (atom alist)
      nil
    (if (atom (car alist))
        (vl-modinsts-same-warning modname (cdr alist))
      (cons (vl-modinst-same-warning modname
                                     (ec-call (vl-modinst->modname (caar alist)))
                                     (cdar alist))
            (vl-modinsts-same-warning modname (cdr alist))))))


(defthm vl-warninglist-p-of-vl-modinsts-same-warning
  (vl-warninglist-p (vl-modinsts-same-warning modname alist))
  :hints(("Goal" :in-theory (enable vl-modinsts-same-warning))))





(defsection vl-prepare-modinsts-for-multidrive

  (defund vl-prepare-modinsts-for-multidrive (modname modinsts)
    "Returns (MV MODINSTS WARNINGS)"
    (declare (xargs :guard (and (stringp modname)
                                (vl-modinstlist-p modinsts))))
    (b* ((names-dropped (vl-modinstlist-name-drop-fix modinsts))
         (dupes         (duplicated-members names-dropped))
         ((unless dupes)
          ;; No duplicates modulo names, so don't even do anything
          (mv modinsts nil))

         ;; If we get here, we found some instances that all have the
         ;; same names; issue warnings and consolidate them into a single
         ;; instance as far as multidrive detection is concerned.
         (names-dropped (hons-copy names-dropped))
         (dupes         (hons-copy dupes))
         (instnames     (vl-modinstlist->instnames modinsts))
         (alist
          ;; instance name --> fixed up inst (as singleton lists)
          (pairlis$ instnames (pairlis$ names-dropped nil)))
         (rev-alist
          ;; fixed up inst --> instance name list
          (acl2::graph-transpose alist nil))
         (prob-alist
          ;; fixed up inst --> instance name list with only problematic entries
          (acl2::with-fast-alist rev-alist
                                 (acl2::fal-extract dupes rev-alist)))
         (warnings (vl-modinsts-same-warning modname prob-alist)))
      (mv (mergesort names-dropped) warnings)))

  (local (in-theory (enable vl-prepare-modinsts-for-multidrive)))

  (defthm vl-warninglist-p-of-vl-prepare-modinsts-for-multidrive
    (vl-warninglist-p (mv-nth 1 (vl-prepare-modinsts-for-multidrive modname modinsts))))

  (defthm vl-modinstlist-p-of-vl-prepare-modinsts-for-multidrive
    (implies (force (vl-modinstlist-p modinsts))
             (vl-modinstlist-p (mv-nth 0 (vl-prepare-modinsts-for-multidrive modname modinsts))))))





(defsection vl-module-multidrive-detect

  (defund vl-module-multidrive-detect (x)
    "Returns x-prime"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)

         ;; Note: walist only includes net declarations (it omits registers)
         ((mv successp warnings walist)
          (vl-module-wirealist x x.warnings))
         ((unless successp)
          (fast-alist-free walist)
          (b* ((w (make-vl-warning
                   :type :vl-multidrive-detect-fail
                   :msg "Wire alist construction for ~m0 failed.  We will ~
                         not be able to detect multiply driven wires in ~
                         this module."
                   :args (list x.name)
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)))
            (change-vl-module x :warnings (cons w warnings))))

         ((mv modinsts extra-warnings)
          (vl-prepare-modinsts-for-multidrive x.name x.modinsts))
         (warnings (append-without-guard extra-warnings warnings))

         ;; We don't consider any initial/always statements because all
         ;; procedural assignments must be to registers instead of wires, and
         ;; this will cause problems since the registers aren't included in the
         ;; wire alist, and we also think it's pretty legitimate for registers
         ;; to be assigned to in multiple places (e.g., it could be given an
         ;; initial value in an initial statement, and be updated in an always
         ;; statement), so we don't want to cause any warnings about them.
         ((mv z-modinsts nonz-modinsts) (vl-zsplit-modinsts modinsts))

         (z-lvalexprs (append (vl-assignlist-lvalexprs
                               (vl-keep-z-assigns x.assigns))
                              (vl-gateinstlist-lvalexprs
                               (vl-keep-z-gateinsts x.gateinsts))
                              (vl-modinstlist-lvalexprs z-modinsts)))

         (nonz-lvalexprs (append (vl-assignlist-lvalexprs
                                  (vl-remove-z-assigns x.assigns))
                                 (vl-gateinstlist-lvalexprs
                                  (vl-remove-z-gateinsts x.gateinsts))
                                 (vl-modinstlist-lvalexprs nonz-modinsts)))

         ((mv successp1 warnings zbits)
          (vl-msb-exprlist-bitlist z-lvalexprs walist warnings))

         ((mv successp2 warnings nonzbits)
          (vl-msb-exprlist-bitlist nonz-lvalexprs walist warnings))

         (warnings
          (if (and successp1 successp2)
              warnings
            (cons (make-vl-warning
                   :type :vl-multidrive-detect-incomplete
                   :msg "Our detection of multiply-driven wires in ~m0 may be ~
                         incomplete because we failed to generate bit-lists for ~
                         all lvalues.  This is probably caused by a malformed ~
                         lvalue?  Check other warnings for vl-msb-*-bitlist.  ~
                         BOZO this error message is terrible, Jared should make ~
                         it better."
                   :args (list (vl-module->name x))
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)
                  warnings)))

         ;; A bit is multiply driven in a weird way if it is driven multiple
         ;; times by a non-Z driver, or if it is driven by both non-Z and Z
         ;; drivers, but not if it is only driven by multiple Z drivers.
         (badbits (duplicated-members (append nonzbits (mergesort zbits))))

         ;; Throw away bits that probably ought to be multiply driven due to
         ;; having types like wor/wand
         (exotic  (vl-multidrive-exotic-bits x.netdecls walist))
         (badbits (if exotic
                      (difference (redundant-mergesort badbits)
                                  (mergesort exotic))
                    badbits))

         ((mv minor-bad major-bad)
          ;; We treat everything as minor if it's in a module that has mux in
          ;; its name.
          (if (str::substrp "mux" x.name)
              (mv badbits nil)
            (vl-multidrive-filter-innocuous-wires badbits nil nil)))

         (minor-names
          (if (vl-emodwirelist-p minor-bad)
              (vl-verilogify-emodwirelist minor-bad)
            ;; Expect this not to happen but it wouldn't be too bad.
            (symbol-list-names minor-bad)))

         (major-names
          (if (vl-emodwirelist-p major-bad)
              (vl-verilogify-emodwirelist major-bad)
            ;; Expect this not to happen but it wouldn't be too bad.
            (symbol-list-names major-bad)))

         (warnings
          (if (not major-names)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-multidrive
                   :msg "Wires ~&0 are driven by multiple sources.  This might ~
                         be expected (e.g., for muxes), but could also suggest ~
                         a copy/paste error."
                   :args (list major-names)
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)
                  warnings)))

         (warnings
          (if (not minor-names)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-multidrive-minor
                   :msg "Wires ~&0 are driven by multiple sources.  This is a ~
                         minor warning because our heuristics say this wire ~
                         is probably supposed to have multiple drivers.  But in ~
                         rare cases, this might suggeset a copy/paste error."
                   :args (list minor-names)
                   :fatalp nil
                   :fn 'vl-module-multidrive-detect)
                  warnings))))

      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-multidrive-detect)))

  (defthm vl-module-p-of-vl-module-multidrive-detect
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-multidrive-detect x))))

  (defthm vl-module->name-of-vl-module-multidrive-detect
    (equal (vl-module->name (vl-module-multidrive-detect x))
           (vl-module->name x))))



(defsection vl-modulelist-multidrive-detect

  (defprojection vl-modulelist-multidrive-detect (x)
    (vl-module-multidrive-detect x)
    :guard (vl-modulelist-p x)
    :nil-preservingp nil)

  (local (in-theory (enable vl-modulelist-multidrive-detect)))

  (defthm vl-modulelist-p-of-vl-modulelist-multidrive-detect
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-multidrive-detect x))))

  (defthm vl-modulelist->names-of-vl-modulelist-multidrive-detect
    (equal (vl-modulelist->names (vl-modulelist-multidrive-detect x))
           (vl-modulelist->names x))))
