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
(include-book "../mlib/strip")
(include-book "../mlib/lvalues")
(include-book "centaur/esim/vltoe/wirealist" :dir :system)
(include-book "centaur/esim/vltoe/verilogify" :dir :system)
(include-book "../../misc/fal-graphs")
(local (include-book "../util/arithmetic"))
(local (in-theory (disable mergesort difference))) ;; bozo why is this enabled?


(defxdoc multidrive
  :parents (lint)
  :short "Check for multiply driven wires."

  :long "<p>This is a somewhat fancy check for multiply driven wires, carried
out at the bit level.  It is meant to be run relatively late in the
transformation sequence, after all assignments have already been sizes, module
instances have already been replicated, and so forth.</p>

<p>Most of the tools we need for finding multiply-driven wires are already
available.  Recall, from @(see e-conversion):</p>

<ul>

<li>@(see vl-module-wirealist) constructs a wire alist for the module, which
gives us a bit-level way to view the wires.</li>

<li>@(see vl-msb-expr-bitlist) gives us the individual bits for an
expression.</li>

</ul>

<p>Most of the complexity of this check is intended to provide better filtering
of warnings to avoid warning about situations where the multiple drivers were
probably intended.  Transistor-level modules often contain multiple wires, but
it's hard to generally define what a transistor-level module is.  Here are some
notes about our heuristics:</p>

<ul>

<li>The wire type declarations can be a good hint.  For instance, if a wire has
type @('wor') or @('tri'), then it's probably expected that it has multiple
drivers and there's no reason to issue a warning in this case.</li>

<li>The kinds of drivers are very suggestive.  If we find @('nmos') or
@('pullup') gates driving a wire, then there's a very good chance that it's
meant to be multiply driven.</li>

<li>Efficient one-hot muxes are often based on multiple drivers.  These muxes
might be written in many ways, e.g., with constructs like @('bufif1') or
assignments like @('sel ? a : 1'bz').  So we can at least look for these kinds
of constructs.</li>

<li>Module instances screw everything up (as usual).  It's hard to recognize
when a submodule is a transistor-level thing, e.g., the submodule might just be
a wrapper for a @('pmos') gate or something.  We can at least look at the
submodule's ports to identify inout wires, and look for certain names that
might indicate that the submodule is a transistor-level construct.</li>

</ul>")

(local (xdoc::set-default-parents multidrive))

(define vl-multidrive-innocuous-wirename-p
  :short "Recognize wires that we don't want to warn about because they
          are probably transistor-level things."
  ((x symbolp))
  :returns (innocuousp booleanp :rule-classes :type-prescription)
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

(define vl-multidrive-filter-innocuous-wires
  ((x symbol-listp "Wire names to filter.")
   (innocuous      "Accumulator for innocuous wire names.")
   (other          "Accumulator for regular wire names."))
  :returns
  (mv (innocuous symbol-listp :hyp (and (force (symbol-listp x))
                                        (force (symbol-listp innocuous))))
      (other     symbol-listp :hyp (and (force (symbol-listp x))
                                        (force (symbol-listp other)))))
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

(define vl-multidrive-collect-exotic-netdecls
  :short "Filter out wires that have types like TRI and WOR, since they
          typically ought to have multiple drivers."
  ((x vl-vardecllist-p))
  :returns (exotic vl-vardecllist-p)
  (b* (((when (atom x))
        nil)
       ((vl-vardecl x1) (vl-vardecl-fix (car x)))
       ((when (and (member x1.nettype
                           '(:vl-tri :vl-triand :vl-trior :vl-tri0 :vl-tri1
                             :vl-trireg :vl-wand :vl-wor))))
        (cons x1
              (vl-multidrive-collect-exotic-netdecls (cdr x)))))
    (vl-multidrive-collect-exotic-netdecls (cdr x))))

(define vl-multidrive-exotic-bits
  :short "Build the set of all bits from exotic wires."
  ((vardecls vl-vardecllist-p "The exotic wires.")
   (walist   vl-wirealist-p))
  :returns bits
  (b* ((exotic-decls (vl-multidrive-collect-exotic-netdecls vardecls))
       (exotic-names (vl-vardecllist->names exotic-decls))
       (exotic-fal   (acl2::fal-extract exotic-names walist))
       (exotic-bits  (append-alist-vals exotic-fal)))
    exotic-bits))




(define vl-z-expr-p ((x vl-expr-p))
  (if (vl-atom-p x)
      (vl-zatom-p x)
    (b* (((vl-nonatom x) x))
      (and (eq x.op :vl-qmark)
           (or (and (vl-atom-p (cadr x.args))
                    (vl-zatom-p (cadr x.args)))
               (and (vl-atom-p (caddr x.args))
                    (vl-zatom-p (caddr x.args))))))))

(define vl-z-assign-p ((x vl-assign-p))
  (vl-z-expr-p (vl-assign->expr x)))

(define vl-remove-z-assigns ((x vl-assignlist-p))
  :returns (non-z vl-assignlist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((vl-z-assign-p (car x))
         (vl-remove-z-assigns (cdr x)))
        (t
         (cons (car x)
               (vl-remove-z-assigns (cdr x))))))

(define vl-keep-z-assigns ((x vl-assignlist-p))
  :returns (z-assigns vl-assignlist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((vl-z-assign-p (car x))
         (cons (car x)
               (vl-keep-z-assigns (cdr x))))
        (t
         (vl-keep-z-assigns (cdr x)))))

(defenum vl-z-gatetype-p
  (:vl-cmos
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
   :vl-pullup))

(define vl-z-gateinst-p ((x vl-gateinst-p))
  (b* (((vl-gateinst x) x))
    (vl-z-gatetype-p x.type)))

(define vl-remove-z-gateinsts ((x vl-gateinstlist-p))
  :returns (non-z vl-gateinstlist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((vl-z-gateinst-p (car x))
         (vl-remove-z-gateinsts (cdr x)))
        (t
         (cons (car x) (vl-remove-z-gateinsts (cdr x))))))

(define vl-keep-z-gateinsts ((x vl-gateinstlist-p))
  :returns (z-gates vl-gateinstlist-p :hyp :fguard)
  (cond ((atom x)
         nil)
        ((vl-z-gateinst-p (car x))
         (cons (car x) (vl-keep-z-gateinsts (cdr x))))
        (t
         (vl-keep-z-gateinsts (cdr x)))))

(define vl-z-modinst-p ((x vl-modinst-p))
  :short "Modules we regard as Z drivers by name."
  :long "<p>BOZO this list is probably Centaur specific.  Maybe it should
         become an attachable function, instead.</p>"
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

(define vl-zsplit-plainargs ((x vl-plainarglist-p))
  :returns (mv (outputs vl-plainarglist-p :hyp :fguard)
               (inouts  vl-plainarglist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv cdr-outs cdr-inouts)
        (vl-zsplit-plainargs (cdr x)))
       ((when (eq (vl-plainarg->dir (car x)) :vl-output))
        (mv (cons (car x) cdr-outs) cdr-inouts))
       ((when (eq (vl-plainarg->dir (car x)) :vl-inout))
        (mv cdr-outs (cons (car x) cdr-inouts))))
    (mv cdr-outs cdr-inouts)))

(define vl-zsplit-modinsts ((x vl-modinstlist-p))
  :returns (mv (z-insts vl-modinstlist-p :hyp :fguard)
               (non-z   vl-modinstlist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv cdr-z cdr-nonz)
        (vl-zsplit-modinsts (cdr x)))
       ((when (vl-z-modinst-p (car x)))
        (mv (cons (car x) cdr-z) cdr-nonz))

       (args (vl-modinst->portargs (car x)))
       ((when (eq (vl-arguments-kind args) :vl-arguments-named))
        ;; It's broken anyway, just put it as non-z, we warn about it later
        (mv cdr-z (cons (car x) cdr-nonz)))
       ((mv out-args inout-args)
        (vl-zsplit-plainargs (vl-arguments-plain->args args)))

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
       (z-modinst (change-vl-modinst (car x) :portargs (make-vl-arguments-plain :args inout-args)))
       (nonz-modinst (change-vl-modinst (car x) :portargs (make-vl-arguments-plain :args out-args))))
    (mv (cons z-modinst cdr-z)
        (cons nonz-modinst cdr-nonz))))



; As another twist, we drop the instance names so we can detect instances that
; are identical except for their names.  We'll add a different kind of warning
; for these, along the lines of duplicate detection.

(define vl-modinst-name-drop-fix
  :short "Throw away a module instance's name."
  ((x vl-modinst-p))
  :returns (new-x vl-modinst-p :hyp :fguard)
  (change-vl-modinst (vl-modinst-strip x)
                     :instname nil))

(defprojection vl-modinstlist-name-drop-fix (x)
  (vl-modinst-name-drop-fix x)
  :guard (vl-modinstlist-p x)
  :result-type vl-modinstlist-p)

(define vl-modinst-same-warning
  ((modname stringp)
   target-modname ;; string
   instname-list  ;; string-listp
   )
  :returns (warning vl-warning-p)
  (make-vl-warning
   :type (if (ec-call (str::isubstrp$inline "ph1" target-modname))
             :vl-warn-instances-same-minor
           :vl-warn-instances-same)
   :msg  "In module ~m0, found multiple instances of module ~m1 with ~
            identical arguments: ~&2."
   :args (list modname target-modname instname-list)
   :fatalp nil
   :fn 'vl-modinst-same-warning))

(define vl-modinsts-same-warning
  ((modname stringp)
   (alist   "Maps fixed-up instances to instance-name lists."))
  :returns (warnings vl-warninglist-p)
  (cond ((atom alist)
         nil)
        ((atom (car alist))
         ;; Bad alist convention
         (vl-modinsts-same-warning modname (cdr alist)))
        (t
         (cons (vl-modinst-same-warning
                modname
                (ec-call (vl-modinst->modname$inline (caar alist)))
                (cdar alist))
               (vl-modinsts-same-warning modname (cdr alist))))))

(define vl-prepare-modinsts-for-multidrive
  ((modname  stringp)
   (modinsts vl-modinstlist-p))
  :returns
  (mv new-insts warnings)
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
       (warnings (vl-modinsts-same-warning modname prob-alist))
       (back-alist (pairlis$ names-dropped (list-fix modinsts)))
       ((acl2::with-fast back-alist)))
    (mv (alist-vals (acl2::fal-extract (mergesort names-dropped)
                                       back-alist))
        warnings))
  ///
  (local (defthm vl-modinst-p-of-hons-assoc-equal-pairlis$-modinstlist
           (implies (and (vl-modinstlist-p modinsts)
                         (equal (len keys) (len modinsts))
                         (hons-assoc-equal key (pairlis$ keys modinsts)))
                    (vl-modinst-p
                     (cdr (hons-assoc-equal key (pairlis$ keys modinsts)))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal pairlis$)))))

  (local (defthm vl-modinstlist-p-of-fal-extract-from-pairlis$-modinstlist
           (implies (and (vl-modinstlist-p modinsts)
                         (equal (len keys1) (len modinsts)))
                    (vl-modinstlist-p
                     (alist-vals (acl2::fal-extract keys (pairlis$ keys1 modinsts)))))
           :hints (("goal" :induct (len keys)
                    :in-theory (enable acl2::fal-extract alist-vals)))))

  (defthm vl-warninglist-p-of-vl-prepare-modinsts-for-multidrive
    (vl-warninglist-p (mv-nth 1 (vl-prepare-modinsts-for-multidrive modname modinsts))))

  (defthm vl-modinstlist-p-of-vl-prepare-modinsts-for-multidrive
    (implies (force (vl-modinstlist-p modinsts))
             (vl-modinstlist-p
              (mv-nth 0 (vl-prepare-modinsts-for-multidrive modname modinsts))))))


(define vl-module-multidrive-detect ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ;; Note: walist only includes net declarations (it omits registers)
       (warnings x.warnings)
       ((mv successp warnings walist) (vl-module-wirealist x warnings))
       ((with-fast walist))
       ((unless successp)
        (change-vl-module x
          :warnings (warn :type :vl-multidrive-detect-fail
                          :msg "Wire alist construction for ~m0 failed.  We ~
                                will not be able to detect multiply driven ~
                                wires in this module."
                          :args (list x.name))))

       ((mv modinsts extra-warnings)
        (vl-prepare-modinsts-for-multidrive x.name x.modinsts))
       (warnings (append-without-guard extra-warnings warnings))

       ;; We don't consider any initial/always statements because all
       ;; procedural assignments must be to registers instead of wires, and
       ;; this will cause problems since the registers aren't included in the
       ;; wire alist, and we also think it's pretty legitimate for registers to
       ;; be assigned to in multiple places (e.g., it could be given an initial
       ;; value in an initial statement, and be updated in an always
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
            (ok)
          (warn :type :vl-multidrive-detect-incomplete
                :msg "Our detection of multiply-driven wires in ~m0 may be ~
                      incomplete because we failed to generate bit-lists for ~
                      all lvalues.  This is probably caused by a malformed ~
                      lvalue?  Check other warnings for vl-msb-*-bitlist.  ~
                      BOZO this error message is terrible, Jared should make ~
                      it better."
                :args (list (vl-module->name x)))))

       ;; A bit is multiply driven in a weird way if it is driven multiple
       ;; times by a non-Z driver, or if it is driven by both non-Z and Z
       ;; drivers, but not if it is only driven by multiple Z drivers.
       (badbits (duplicated-members (append nonzbits (mergesort zbits))))

       ;; Throw away bits that probably ought to be multiply driven due to
       ;; having types like wor/wand
       (exotic  (vl-multidrive-exotic-bits x.vardecls walist))
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
            (ok)
          (warn :type :vl-warn-multidrive
                :msg "Wires ~&0 are driven by multiple sources.  This might ~
                      be expected (e.g., for muxes), but could also suggest a ~
                      copy/paste error."
                :args (list major-names))))

       (warnings
        (if (not minor-names)
            (ok)
          (warn :type :vl-warn-multidrive-minor
                :msg "Wires ~&0 are driven by multiple sources.  This is a ~
                      minor warning because our heuristics say this wire is ~
                      probably supposed to have multiple drivers.  But in ~
                      rare cases, this might suggeset a copy/paste error."
                :args (list minor-names)))))

    (change-vl-module x :warnings warnings)))


(defprojection vl-modulelist-multidrive-detect-aux (x)
  (vl-module-multidrive-detect x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :nil-preservingp nil)

(define vl-modulelist-multidrive-detect ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* ((ans (vl-modulelist-multidrive-detect-aux x)))
    (clear-memoize-table 'vl-module-wirealist)
    ans))

(define vl-design-multidrive-detect
  :short "Top-level @(see multidrive) check."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x
                      :mods (vl-modulelist-multidrive-detect x.mods))))


