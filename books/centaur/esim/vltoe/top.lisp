; ESIM Symbolic Hardware Simulator
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
(include-book "eocc-allnames")
(include-book "preliminary")
(include-book "add-res-modules")
(include-book "zdrivers")
(include-book "centaur/vl2014/mlib/remove-bad" :dir :system)
(include-book "centaur/vl2014/mlib/atts" :dir :system)
(local (include-book "esim-lemmas"))
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (non-parallel-book))

(defxdoc e-conversion
  :parents (esim)
  :short "Translation from simplified Verilog modules into E modules."

  :long "<p>The conversion from Verilog to E is mostly straightforward because
here we only try to support an extremely limited subset of Verilog.  The basic
idea is that other @(see transforms) should first be used to simplify more
complex, \"original\" input modules into this simple subset.</p>

<p>Here are some basic expectations:</p>

<ul>

<li>Each module we need to process will include net declarations and submodule
instances, but will not have any assignments, gates, always blocks, parameters,
registers, variables, etc.  These other constructs should be simplified away
before E conversion.</li>

<li>Each module instance will have well-formed port connections that contain
only <see topic='@(url expr-slicing)'>sliceable</see> expressions.  This lets
us deal with everything purely at the bit level.</li>

</ul>

<p>We have checks to ensure our assumptions hold, and these checks will result
in fatal @(see warnings) if the modules contain unsupported constructs.  See in
particular @(see vl-module-check-e-ok) and @(see vl-module-check-port-bits).</p>

<p>We process the modules in dependency order, and aside from sanity checking
there are basically two steps for each module we need to convert:</p>

<ol>

<li>We produce a <b>preliminary</b> E module by <see topic='@(url
exploding-vectors)'>exploding</see> the module's vectors into individual bits,
and converting the module instances into E occurrences for the submodules.</li>

<li>This preliminary E module is almost a proper E module, but it might have
some wires that are driven by multiple occurrences.  As a second step, we
rewrite the preliminary module to <see topic='@(url
resolving-multiple-drivers)'>resolve these multiply driven wires</see>.  This
ensures that every wire has exactly one driver.</li>

</ol>

<p>Some final sanity checking is done to ensure that the module's inputs and
outputs are properly marked and there is no \"backflow\" occurring.</p>

<p>The resulting E module for each Verilog module is saved in the @('esim')
field of each @(see vl-module-p).</p>")

(local (xdoc::set-default-parents e-conversion))

; -----------------------------------------------------------------------------
;
;                   Checking for Unsupported Constructs
;
; -----------------------------------------------------------------------------

(define vl-has-any-hid-netdecls ((x vl-vardecllist-p))
  :parents (vl-module-check-e-ok)
  (cond ((atom x)
         nil)
        ((assoc-equal "HID" (vl-vardecl->atts (car x)))
         t)
        (t
         (vl-has-any-hid-netdecls (cdr x)))))

(define vl-module-check-e-ok
  :short "Check for unsupported constructs."
  ((x        vl-module-p)
   (warnings vl-warninglist-p))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p
                         :hyp (force (vl-warninglist-p warnings))))
  (b* (((vl-module x) x)
       ;; Gather up a message about what unsupported constructs there are.
       (acc nil)
       ;; We used to check whether there were parameter declarations and fail
       ;; if so, because e doesn't really support them directly.  But it's
       ;; basically harmless to have parameter declarations in your module as
       ;; long as they're not used.  If unparameterization failed somewhere, it
       ;; should have produced a fatal warning, so we don't expect this check
       ;; to be necessary.
       ;; (acc (if x.paramdecls
       ;;          (cons (str::join (cons "parameter declarations: " (vl-paramdecllist->names x.paramdecls)) " ")
       ;;                acc)
       ;;        acc))
       (acc (if x.fundecls
                (cons (str::join (cons "function declarations: " (vl-fundecllist->names x.fundecls)) " ")
                      acc)
              acc))
       (acc (if x.taskdecls
                (cons (str::join (cons "task declarations: " (vl-taskdecllist->names x.taskdecls)) " ")
                      acc)
              acc))
       (acc (if x.assigns    (cons "assigns" acc)        acc))
       (acc (if x.gateinsts  (cons "gate instances" acc) acc))
       (acc (if x.alwayses   (cons "always blocks" acc)  acc))
       ;; We'll allow but ignore initial statements
       (acc (if (vl-has-any-hid-netdecls x.vardecls)
                (cons "hierarchical identifiers" acc)
              acc))
       ;; BOZO BOZO BOZO !!!!!
       ;; need to check netdecls for WOR, etc.

       (acc (if (vl-module->ifports x) (cons "interface ports" acc) acc))

       ((unless acc)
        (mv t warnings))

       (w (make-vl-warning
           :type :vl-unsupported
           :msg "Failing to build an E module for ~s0 because it still has ~
                 ~&1. We generally expect all constructs other than net ~
                 declarations and module instances to be simplified away by ~
                 other transforms before E module generation."
           :args (list x.name acc)
           :fatalp t
           :fn 'vl-module-check-e-ok)))
    (mv nil (cons w warnings))))


; -----------------------------------------------------------------------------
;
;                      Adding Design-Wires Annotations
;
; -----------------------------------------------------------------------------

(define vl-collect-msb-bits-for-wires
  :parents (vl-collect-design-wires)
  :short "Append together all the MSB bits for a list of wire names."
  ((names    string-listp)
   (walist   vl-wirealist-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp (vl-warninglist-p warnings))
               (wires vl-emodwirelist-p :hyp (vl-wirealist-p walist)))
  (b* (((when (atom names))
        (mv warnings nil))
       (name1  (car names))
       (entry1 (hons-get name1 walist))
       (wires1 (cdr entry1))
       ((mv warnings rest)
        (vl-collect-msb-bits-for-wires (cdr names) walist warnings))
       (warnings (if entry1
                     warnings
                   (warn :type :vl-design-wires
                         :msg "No walist entry for ~s0."
                         :args (list name1)))))
    (mv warnings (append wires1 rest))))

(define vl-collect-design-wires
  :short "Collect all symbols for design-visible wires and return them as a
          flat list of bits."
  ((x        vl-module-p)
   (walist   vl-wirealist-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp (vl-warninglist-p warnings))
               (wires vl-emodwirelist-p :hyp (vl-wirealist-p walist)))
  (b* (((when (atom x))
        (mv warnings nil))
       (vars       (vl-module->vardecls x))
       (dnets      (vl-gather-vardecls-with-attribute vars "VL_DESIGN_WIRE"))
       (dnet-names (vl-vardecllist->names dnets)))
    (vl-collect-msb-bits-for-wires dnet-names walist warnings)))



; -----------------------------------------------------------------------------
;
;                         Top-Level E Conversion
;
; -----------------------------------------------------------------------------

(define vl-module-make-esim
  :short "Convert a Verilog module into an E module."

  ((x vl-module-p
      "The module we want to convert into an E module.  We assume that the
       module has no unsupported constructs, okay port bits, etc, since these
       are checked in @(see vl-modulelist-make-esims).")
   (mods vl-modulelist-p
         "The list of all modules.  Note: this stays fixed as we recur, so the
          modules generally here don't have their @('esim') fields filled in
          yet.")
   (modalist (equal modalist (vl-modalist mods))
             "For fast module lookups.")
   (eal vl-ealist-p
        "The @(see vl-ealist-p) that we are constructing and extending.  This
         allows us to look up the E modules for previously processed modules."))

  :returns
  (mv (new-x vl-module-p :hyp (force (vl-module-p x))
             "New version of @('x') with its @('esim') field filled in,
              if possible.")
      (eal "Extended version of @('eal') with the @('esim') for @('x')."))

  :long "<p>We try to compute the @('esim') for @('x'), install it into @('x'),
and extend @('eal') with the newly produced @('esim').</p>"

  :prepwork
  ((local (defthm c0
            (implies (vl-emodwirelist-p (vl-eocclist-allnames occs))
                     (vl-emodwirelist-p (collect-signal-list :o occs)))
            :hints(("Goal" :in-theory (enable collect-signal-list
                                              vl-eocclist-allnames
                                              vl-eocc-allnames)))))

   (local (defthm c1
            (implies (vl-emodwirelist-p (vl-eocclist-allnames occs))
                     (vl-emodwirelist-p (collect-signal-list :i occs)))
            :hints(("Goal" :in-theory (enable collect-signal-list
                                              vl-eocclist-allnames
                                              vl-eocc-allnames)))))

   (local (defthm d0
            (implies (and (force (vl-emodwire-p out))
                          (force (vl-emodwire-p name)))
                     (vl-emodwirelist-p (vl-eocc-allnames (vl-make-z-occ name out))))
            :hints(("Goal" :in-theory (enable vl-make-z-occ
                                              vl-eocc-allnames)))))

   (local (defthm d1
            (implies (and (force (natp idx))
                          (force (vl-emodwirelist-p outs)))
                     (vl-emodwirelist-p (vl-eocclist-allnames (vl-make-z-occs idx outs))))
            :hints(("Goal" :in-theory (enable vl-make-z-occs)))))

   (local (defthm d2
            (implies (and (force (vl-emodwirelist-p (vl-eocclist-allnames occs)))
                          (force (vl-emodwirelist-p flat-ins))
                          (force (vl-emodwirelist-p flat-outs)))
                     (vl-emodwirelist-p (vl-eocclist-allnames (vl-add-zdrivers all-names flat-ins flat-outs occs))))
            :hints(("Goal" :in-theory (enable vl-add-zdrivers))))))

  (b* (((vl-module x) x)

       ((when x.esim)
        ;; This makes it easy for primitive modules to supply their own esim
        (if (good-esim-modulep x.esim)
            (mv x (hons-acons x.name x.esim eal))
          (b* ((w (make-vl-warning
                   :type :vl-bad-esim
                   :msg "~a0 already has an esim provided, but it does ~
                           not even satisfy good-esim-modulep."
                   :args (list x.name)
                   :fatalp t
                   :fn 'vl-module-make-esim)))
            ;; Goofy: we throw away the bad E module so that we can
            ;; unconditionally prove that if the ESIM field gets filled in,
            ;; then it's filled in with a good esim module.
            (mv (change-vl-module x
                                  :esim nil
                                  :warnings (cons w x.warnings))
                eal))))

       (warnings x.warnings)

       ;; Check for unsupported constructs
       ((mv okp warnings) (vl-module-check-e-ok x warnings))
       ((unless okp)
        (mv (change-vl-module x :warnings warnings) eal))

       ;; Wire alist
       ((mv okp warnings walist) (vl-module-wirealist x warnings))
       ((unless okp)
        (er hard? 'vl-module-make-esim
            "Wire-alist construction failed?  Shouldn't be possible: we ~
               should have already done this in vl-module-check-port-bits.")
        (mv x eal))

       ;; Build Name for :n
       (starname (vl-starname x.name))

       ;; Build Patterns for :i and :o
       ((mv okp & in out)
        (vl-portdecls-to-i/o x.portdecls walist))
       ((unless okp)
        (er hard? 'vl-module-make-esim
            "Portdecl i/o pattern construction failed?  Shouldn't be ~
               possible: we should have already done this in ~
               vl-module-check-port-bits.")
        (mv x eal))
       (flat-in  (pat-flatten1 in))
       (flat-out (pat-flatten1 out))
       (flat-ios (append flat-in flat-out))

       ;; Build preliminary :occs
       ((mv okp warnings occs)
        (vl-modinstlist-to-eoccs x.modinsts walist mods modalist eal warnings))
       ((unless okp)
        ;; Should have already explained why
        (mv (change-vl-module x :warnings warnings) eal))

       ;; BOZO eventually add a check for cross-connected outputs that are
       ;; being read inside their modules.


       ;; Collect up all the names used in :I, :O, and throughout :OCCS in
       ;; their :I and :O patterns, and in their :U patterns.
       (all-names (vl-eocclist-allnames-exec occs flat-ios))
       ((unless (vl-emodwirelist-p all-names))
        (er hard? 'vl-module-make-esim
            "Found names that are not emodwires in the list of allnames?  ~
               This shouldn't be possible because of how the occurrences and ~
               i/o patterns are constructed.")
        (mv x eal))

       ;; Note that after adding Z drivers, all-names is still "good enough"
       ;; after we add zdrivers.  This is because we only add wires named
       ;; vl_zdrive[k], and in the add-res-modules pass we know these wires
       ;; are okay.
       (occs (vl-add-zdrivers all-names flat-in flat-out occs))

       ;; Extra sanity check to make sure T and F aren't driven.  BOZO
       ;; probably kind of expensive.
       ((when (let ((driven-sigs (collect-signal-list :o occs)))
                (or (member 'acl2::t driven-sigs)
                    (member 'acl2::f driven-sigs))))
        (b* ((w (make-vl-warning
                 :type :vl-output-constant
                 :msg "In ~a0, somehow we have occurrences driving the ~
                         wires T and F. Is this module somehow trying to ~
                         drive a value onto a constant or something?"
                 :args (list x.name)
                 :fatalp t
                 :fn 'vl-module-make-esim)))
          (mv (change-vl-module x :warnings (cons w warnings)) eal)))

       ;; Special hack to drive T and F.  BOZO eventually it'd be nicer to
       ;; have a proper VL transform that eliminates constants, similar to
       ;; weirdint elimination.
       ((when (or (member 'acl2::vl-driver-for-constant-t all-names)
                  (member 'acl2::vl-driver-for-constant-f all-names)))
        (b* ((w (make-vl-warning
                 :type :vl-name-clash
                 :msg "~a0 contains a wire named vl-driver-for-constant-t or ~
                         vl-driver-for-constant-f, so we're dying badly."
                 :args (list x.name)
                 :fatalp t
                 :fn 'vl-module-make-esim)))
          (mv (change-vl-module x :warnings (cons w warnings)) eal)))

       (occs (list* (list :u 'acl2::vl-driver-for-constant-t
                          :op acl2::*esim-t*
                          :i nil
                          :o '((acl2::t)))
                    (list :u 'acl2::vl-driver-for-constant-f
                          :op acl2::*esim-f*
                          :i nil
                          :o '((acl2::f)))
                    occs))


       ;; Adding the T/F wires and drivers doesn't invalidate all-names,
       ;; since none of the names we've added are of the form vl_res[k].
       ;; Hence, it's okay to add RES modules now.
       (occs (vl-add-res-modules all-names occs))

       ;; Probably unnecessary (and perhaps somewhat expensive) sanity check
       ;; to make sure everything does indeed have only one driver.
       (driven-sigs (collect-signal-list :o occs))
       ((unless (uniquep driven-sigs))
        (b* ((w (make-vl-warning
                 :type :vl-programming-error
                 :msg "~a0: after resolving multiply driven wires, we ~
                         somehow have multiple drivers for ~&1."
                 :args (list x.name (duplicated-members driven-sigs))
                 :fatalp t
                 :fn 'vl-module-make-esim)))
          (mv (change-vl-module x :warnings (cons w warnings)) eal)))

       (in-driven (intersect (mergesort driven-sigs) (mergesort flat-in)))
       ((when in-driven)
        (b* ((w (make-vl-warning
                 :type :vl-backflow
                 :msg "~a0: input bits ~&1 are being driven from within ~
                         the module!"
                 :args (list x.name (vl-verilogify-emodwirelist in-driven))
                 :fatalp t
                 :fn 'vl-module-make-esim)))
          (mv (change-vl-module x :warnings (cons w warnings)) eal)))

       ((mv warnings dwires) (vl-collect-design-wires x walist warnings))

       (esim (list :n starname
                   :i in
                   :o out
                   :occs occs
                   :a (list (cons :design-wires  dwires)
                            (cons :wire-alist    walist))))

       ((unless (good-esim-modulep esim))
        ;; BOZO could eventually try to prove some of this away
        (b* (((cons details args) (bad-esim-modulep esim))
             (w (make-vl-warning
                 :type :vl-programming-error
                 :msg  (cat x.name ": failed to make a good esim module.  "
                            "Details: " details)
                 :args args
                 :fatalp t
                 :fn 'vl-module-make-esim)))
          (mv (change-vl-module x :warnings (cons w warnings)) eal)))

       (x-prime (change-vl-module x
                                  :warnings warnings
                                  :esim esim))

       (eal (hons-acons x.name esim eal)))
    (mv x-prime eal))

  ///


  (defthm vl-module->name-of-vl-module-make-esim
    (let ((ret (vl-module-make-esim x mods modalist eal)))
      (equal (vl-module->name (mv-nth 0 ret))
             (vl-module->name x))))

  (defthm good-esim-modulep-of-vl-module-make-esim
    (let ((ret (vl-module-make-esim x mods modalist eal)))
      (implies (and (vl-module->esim (mv-nth 0 ret)) ;; "success"
                    (force (vl-module-p x))
                    (force (vl-ealist-p eal)))
               (good-esim-modulep
                (vl-module->esim (mv-nth 0 ret))))))

  (defthm vl-ealist-p-vl-module-make-esim
    (let ((ret (vl-module-make-esim x mods modalist eal)))
      (implies (and (force (vl-module-p x))
                    (force (vl-ealist-p eal)))
               (vl-ealist-p (mv-nth 1 ret))))))


(define vl-modulelist-make-esims
  :short "Extend @(see vl-module-make-esim) across a list of modules."
  ((x vl-modulelist-p)
   (mods vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (eal vl-ealist-p))
  :returns (mv (new-x vl-modulelist-p :hyp (force (vl-modulelist-p x)))
               (eal   vl-ealist-p     :hyp (and (vl-modulelist-p x)
                                                (vl-ealist-p eal))))
  (b* (((when (atom x))
        (mv nil eal))
       ((mv car eal) (vl-module-make-esim (car x) mods modalist eal))
       ((mv cdr eal) (vl-modulelist-make-esims (cdr x) mods modalist eal)))
    (mv (cons car cdr) eal))
  ///
  (defmvtypes vl-modulelist-make-esims (true-listp nil))

  (defthm vl-modulelist->names-of-vl-modulelist-make-esims
    (let ((ret (vl-modulelist-make-esims x mods modalist eal)))
      (equal (vl-modulelist->names (mv-nth 0 ret))
             (vl-modulelist->names x)))))



(define vl-design-to-e-check-ports ((x vl-design-p))
  :returns (new-x vl-design-p)
  :short "Make sure that the module port/port-declarations agree and that there
          are no unsupported constructs."
  (b* (((vl-design x) (vl-design-fix x))
       (mods (vl-modulelist-check-port-bits x.mods)))
    (change-vl-design x :mods mods)))

(define vl-design-to-e-main ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (mods x.mods)
       (modalist (vl-modalist mods))
       ((mv mods eal) (vl-modulelist-make-esims mods mods modalist nil)))
    (fast-alist-free eal)
    (fast-alist-free modalist)
    (clear-memoize-table 'vl-make-n-bit-res-module)
    (clear-memoize-table 'vl-portdecls-to-i/o)
    (clear-memoize-table 'vl-portlist-msb-bit-pattern)
    (clear-memoize-table 'vl-module-wirealist)
    (change-vl-design x :mods mods)))

(define vl-design-to-e ((good vl-design-p)
                        (bad  vl-design-p))
  :short "Top-level function for E conversion."
  :returns (mv (good vl-design-p)
               (bad  vl-design-p))
  (b* ((good (vl-design-to-e-check-ports good))
       (bad  (vl-design-fix bad))

       ((mv good bad) (vl-design-propagate-errors good bad))
       ((mv okp good) (vl-design-deporder-modules good))
       ((unless okp)
        (raise "Somehow failed to dependency order sort the modules.")
        (mv good bad))

       (good (vl-design-to-e-main good))
       ((mv good bad) (vl-design-propagate-errors good bad)))
    (mv good bad)))
