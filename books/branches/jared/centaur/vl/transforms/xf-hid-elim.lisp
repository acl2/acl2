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
(include-book "../transforms/xf-resolve-ranges")
(include-book "../mlib/find-module")
(include-book "../mlib/find-item")
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/hid-tools")
(include-book "../wf-ranges-resolved-p")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


;; NOTE ----- This is now only used in the linter, I think!

(local (defthm crock3
         (implies (and (force (stringp name))
                       (force (vl-module-p x)))
                  (symbolp (tag (vl-find-moduleitem name x))))
         :hints(("Goal"
                 :in-theory (disable vl-find-moduleitem-type-when-nothing-else)
                 :use ((:instance vl-find-moduleitem-type-when-nothing-else))))))


(defxdoc hid-elim
  :parents (transforms)
  :short "Replace hierarchical identifiers with special wires."

  :long "<p>This transform replaces all uses of hierarchical identifiers
throughout a module with new wires.  Intuitively, if we see something
like:</p>

@({
 assign w = foo.bar.baz;
})

<p>We'll rewrite it into:</p>

@({
 wire (* special attributes *) \foo.bar.baz ;
 assign w = \foo.bar.baz ;
})

<p>This transformation has two phases that must occur separately.</p>

<ul>

<li>@(see vl-modulelist-follow-hids) should happen after implicit wire
declarations are added, but before any modules are thrown out.</li>

<li>@(see vl-modulelist-hid-elim) should happen after unparameterization and
range resolution, but before any expression sizing.</li>

</ul>


<h3>Motivation</h3>

<p>Hierarchical identifiers such as @('top.foo.bar.baz') seem very difficult to
synthesize.  Why?  Here are some scenarios.  In these diagrams, names represent
modules and lines represent instantiation.</p>

<h5>Scenario A: access unrelated data</h5>
@({
          1st-common-parent
               /    \\
              /      \\
            A1        B1
           /            \\
          /              \\
        A2                B2
       /                    \\
      /                      \\
  WHERE YOU ARE         THING YOU WANT
})

<h5>Scenario B: access submodule data</h5>
@({
              WHERE YOU ARE
                   |
                   |
                   C1
                   |
                   |
                   C2
                   |
                   |
             THING YOU WANT
})

<h5>Scenario C: access parent data</h5>
@({
      THING YOU WANT
            |
            |
            D1
            |
            |
            D2
            |
            |
      WHERE YOU ARE
})

<p>Restricting our attention to reading data, if you want to synthesize
something like Scenario A into a gate-level hardware description, you would
need to</p>

<ul>

<li>identify an output of each Bi module that has the thing you want, or add a
new output and drive it with what you want; then</li>

<li>identify an input of each A module that has what you want, or add a new
input driven by B.</li>

</ul>

<p>This is a change to every module up to the 1st-common-parent, and that's
only part of the story: if anyone else is instantiating A1, A2, B1, B2, etc.,
then you need to do even more work.  After all, the new Ai' you just made has
extra inputs, and the new Bi' that you've made have extra outputs.  So you
either need to</p>

<ul>

<li>duplicate and rename modules so that A1 and A1' are distinct, or</li>

<li>change everyone else who ever instantiates any Ai or Bi to include the
extra inputs/outputs.</li>

</ul>

<p>Handling the other scenarios is slightly simpler, but still require that we
add inputs or outputs to modules that might be instantiated all over the
place.</p>

<p>If we want to also consider writing to hierarchical identifiers, the story
becomes much crazier.  As before, we need to add some kind of pathway from
where you are to where you want to change, perhaps a data path for the value
you want to write, and a control path for whether you want to override its
value.  This just seems really, really hard.</p>

<p>Because of these considerations, we do <b>not</b> want to try to
\"synthesize\" hierarchical identifiers in our E translation.</p>

<p>On the other hand, hierarchical identifiers seem to be frequently used in
assertions, and it seems like a generally good idea for designers to be able to
add assertions without drastically changing their module interfaces.  So, we
would like to have some way to support hierarchical identifiers that does not
require us to actually synthesize them into gate-level modules.</p>

<p>This transform is intended to be compatible with various strategies for
supporting HIDs.  Historically we introduced special <b>externals</b> modules
that boxed up all the HID assignments into one place.  But in other tools that
flatten modules, HIDs may be straightforward to support.</p>


<h3>Eliminating HIDs</h3>

<p>In principle this is easy.</p>

<ol>

<li>Collect all of the hierarchical identifiers used in a module</li>

<li>Mangle their names so that they are ordinary identifiers that don't
   collide with any other names.</li>

<li>Figure out their sizes,</li>

<li>Introduce wire declarations.</li>

</ol>

<p>The really tricky part is #3.  First, we need to be able to figure out what
a hierarchical identifier is pointing at.  Then, we need to see how big that
wire is.</p>

<p>Here's the problem.  In order for all of the sizes to be computed, we will
have needed to carry out unparameterization and range resolution.  But by the
time we have gotten that far, we might have thrown some modules away already,
in particular we may have thrown away modules like @('top') that are part of
the hierarchical reference!  Ugh!</p>

<h4>Pre-Resolving HIDs</h4>

<p>To work around this, my first plan was the following:</p>

<p>Right after parsing, or at least alongside other annotation passes like
adding wire declarations for implicit wires, we are going to find every
hierarchical reference in the module list and figure out what module it points
at.  That is, given a hierarchical reference like:</p>

@({
top.foo.bar[3].baz.w;
})

<p>We are going to figure out what module is @('baz') an instance of.  Suppose
it is an instance of @('bazmod').  Then, we will annotate this hierarchical
identifier with the attribute:</p>

@({
VL_HID_RESOLVED_MODULE_NAME = \"bazmod\"
})

<p>Later on, when we go to figure out the size of our new flattened wire for
@('top.foo.bar[3].baz.w'), we don't have to traverse the hierarchy again.
Instead, we will just look up the resolved module name, and go find the size of
@('w') in that module.</p>

<p>Note that the resolved name is the <b>origname</b> of the module.  After we
unparameterize, the actual module name might have changed.</p>

<h4>Pre-Collecting Sizes</h4>

<p>After implementing this plan, I discovered a problem.  Many times, even the
module named by @('VL_HID_RESOLVED_MODULE_NAME') is unreasonable!  For
instance, many references point to things like clocks in @('processor'), so
waiting until after unparameterization and range resolution to try to detect
wire sizes seems difficult because these modules are going to be thrown
away.</p>

<p>To address this, I implemented the following tweak: when we do the initial
lookup, if the range we are looking at is already resolved, go ahead and record
additional attributes:</p>

<ul>

<li>@('VL_HID_RESOLVED_RANGE_P') is added if the width of the wire can already
be determined at name-resolution time.  In particular, we can determine the
range if it is already resolved, or if it is a single wire that has no range
declaration.</li>

</ul>

<p>And, if there is a range:</p>

<ul>

<li>@('VL_HID_RESOLVED_RANGE_LEFT') is associated with the expression for the
left-hand side of a range, and</li>

<li>@('VL_HID_RESOLVED_RANGE_RIGHT') is associated with the expression for the
right-hand side of the range.</li>

</ul>

<p>This way, in the second pass, we only need to try to look up the width if we
don't find these attributes already available.  In practice, almost all ranges
in unparameterized modules are already resolved, so this nicely handles
hierarchical references to wires inside of @('processor'), etc.</p>")


; For part 1, see xf-follow-hids.lisp.

; PART 2 --- REPLACING HIDS WITH FLATTENED NAMES
; BOZO add documentation

(defsection vl-hidexpr-hid-elim

; We eliminate an HID by replacing it with an ordinary identifier.  We also
; produce a net declaration that can be used to introduce the new wire.  The
; net declaration will have the appropriate size for the target wire!

  (defund vl-hidexpr-hid-elim (x mods modalist warnings netdecls)
    "Returns (MV WARNINGS-PRIME X-PRIME NETDECLS-PRIME)"
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (vl-warninglist-p warnings)
                                (vl-netdecllist-p netdecls))
                    :guard-debug t))
    (b* (((when (vl-fast-atom-p x))
          (prog2$
           (er hard? 'vl-hidexpr-hid-elim "Expect only non-atoms")
           (mv warnings x netdecls)))

         (atts       (vl-nonatom->atts x))
         (localp     (if (assoc-equal "VL_HID_LOCAL_P" atts) t nil))
         (globalp    (if (assoc-equal "VL_HID_GLOBAL_P" atts) t nil))
         (target-val (cdr (assoc-equal "VL_HID_RESOLVED_MODULE_NAME" atts)))
         (resolvedp  (assoc-equal "VL_HID_RESOLVED_RANGE_P" atts))
         (res-left   (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_LEFT" atts)))
         (res-right  (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_RIGHT" atts)))


         ((unless (vl-hidexpr-resolved-p x))
          (mv (cons (make-vl-warning
                     :type :vl-bad-hid
                     :msg "Not all hid indicies are resolved in ~a0."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-hidexpr-hid-elim)
                    warnings)
              x netdecls))

         ;; We are going to (hopefully) turn X into a flat, ordinary
         ;; identifier.  We keep all the atts and also say what the original
         ;; hierarchical identifier that X corresponds to is.

         (flat-name  (vl-flatten-hidexpr x))
         (id         (make-vl-id :name flat-name))
         (x-prime    (make-vl-atom :guts id))

         ;; New attributes must be consistent across multiple collections of
         ;; the same identifier.  So don't base them on the previous atts.
         (decl-atts nil)
         (decl-atts (if localp
                        (acons "VL_HID_LOCAL_P" nil decl-atts)
                      (acons "VL_HID_GLOBAL_P" nil decl-atts)))
         (decl-atts (acons "VL_HID_RESOLVED_MODULE_NAME" target-val decl-atts))
         (decl-atts (acons "HID" x decl-atts))

         ((unless (and (or localp globalp)
                       (or (not localp) (not globalp))
                       (and target-val
                            (vl-atom-p target-val)
                            (vl-string-p (vl-atom->guts target-val)))))
          (mv (cons (make-vl-warning
                     :type :vl-bad-hid
                     :msg "Expected all HIDs to be marked as local or global and ~
                           have resolved names, but this is not the case for ~a0."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-hidexpr-hid-elim)
                    warnings)
              x netdecls))

         ((unless (or (not resolvedp)
                      (and (not res-left) (not res-right))
                      (and res-left res-right
                           (vl-expr-resolved-p res-left)
                           (vl-expr-resolved-p res-right))))
          (mv (cons (make-vl-warning
                     :type :vl-programming-error
                     :msg "Expected resolved HIDs to have no range or resolved ~
                           ranges.  Resolvedp = ~x0, res-left = ~x1, res-right = ~x2.~
                           x = ~a3.~%"
                     :args (list resolvedp res-left res-right x)
                     :fatalp t
                     :fn 'vl-hidexpr-hid-elim)
                    warnings)
              x netdecls))

         ((when resolvedp)
          ;; We already determined the range of this hierarchical identifier
          ;; and it is known to be unsigned and have no arrdims.  We do not need
          ;; to look up its module.
          (b* ((signedp nil)
               (arrdims nil)
               (range   (if res-left
                            (make-vl-range :msb res-left :lsb res-right)
                          nil))
               (netdecl (make-vl-netdecl :name flat-name
                                         :type :vl-wire
                                         :range range
                                         :signedp signedp
                                         :arrdims arrdims
                                         :loc *vl-fakeloc*
                                         :atts decl-atts)))
              (mv warnings x-prime (cons netdecl netdecls))))

         ;; Otherwise, the range of X was previously unresolved.  Try to
         ;; resolve it now.

         (target-modname (vl-string->value (vl-atom->guts target-val)))
         (target-mod (vl-fast-find-module target-modname mods modalist))

         ((unless target-mod)
          (mv (cons (make-vl-warning
                     :type :vl-trans-bad
                     :msg "The hierarchical identifier ~a0 refers to a target in ~
                           module ~m1, but module ~m1 has been eliminated.  Hence, ~
                           this module is transitively bad. ~
                         BOZO -- this warning might not be quite right.  The other ~
                         possibility is that we had a hierarchical reference to a ~
                         wire in a parameterized module.  If the range of that wire ~
                         was not resolved when we followed HIDs, we might be looking ~
                         for foo instead of foo$size=10 or something like that."
                     :args (list x target-modname target-modname)
                     :fatalp t
                     :fn 'vl-hidexpr-hid-elim)
                    warnings)
              x netdecls))

         (itemname (vl-hid-final-name x))
         (item     (vl-find-moduleitem itemname target-mod))

         ((when (eq (tag item) :vl-netdecl))
          (b* (((vl-netdecl item) item)
               ((unless (vl-maybe-range-resolved-p item.range))
                (mv (cons (make-vl-warning
                           :type :vl-bad-hid
                           :msg "The hierarchical identifier ~a0 refers to ~
                                 ~s1 in module ~m2, which is a net with range ~
                                 ~a3.  Expected ranges to be resolved!"
                           :args (list x itemname target-modname item.range)
                           :fatalp t
                           :fn 'vl-hidexpr-hid-elim)
                          warnings)
                    x netdecls))
               (netdecl (make-vl-netdecl :name flat-name
                                         :type :vl-wire
                                         :range item.range
                                         :signedp item.signedp
                                         :arrdims item.arrdims
                                         :loc *vl-fakeloc*
                                         :atts decl-atts)))
            (mv warnings x-prime (cons netdecl netdecls))))

         ((when (eq (tag item) :vl-vardecl))
          (b* (((unless (vl-simplereg-p item))
                (mv (cons (make-vl-warning
                           :type :vl-bad-hid
                           :msg "The hierarchical identifier ~a0 refers to ~
                                 ~s1 in module ~m2, which is a variable of ~
                                 type ~a3.  But we only allow references to ~
                                 regs and nets."
                           :args (list x itemname target-modname (vl-vardecl->vartype item))
                           :fatalp t
                           :fn 'vl-hidexpr-hid-elim)
                          warnings)
                    x netdecls))
               (signedp (vl-simplereg->signedp item))
               (range   (vl-simplereg->range item))
               ((unless (vl-maybe-range-resolved-p range))
                (mv (cons (make-vl-warning
                           :type :vl-bad-hid
                           :msg "The hierarchical identifier ~a0 refers to ~
                                 ~s1 in module ~m2, which is a reg with range ~
                                 ~a3.  Expected ranges to be resolved!"
                           :args (list x itemname target-modname range)
                           :fatalp t
                           :fn 'vl-hidexpr-hid-elim)
                          warnings)
                    x netdecls))
               (netdecl   (make-vl-netdecl :name flat-name
                                           :type :vl-wire
                                           :range range
                                           :signedp signedp
                                           :arrdims nil ;; we know simpleregs have no arrdims
                                           :loc *vl-fakeloc*
                                           :atts decl-atts)))
            (mv warnings x-prime (cons netdecl netdecls)))))

      (mv (cons (make-vl-warning
                 :type :vl-bad-hid
                 :msg "The hierarchical identifier ~a0 refers to ~s1 in ~
                       module ~m2, which is a module item of type ~s3.  But ~
                       we only allow references to registers and nets."
                 :args (list x itemname target-modname (tag item))
                 :fatalp t
                 :fn 'vl-hidexpr-hid-elim)
                warnings)
          x netdecls)))

  (local (in-theory (enable vl-hidexpr-hid-elim)))

  (defthm vl-warninglist-p-of-vl-hidexpr-hid-elim
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-hidexpr-hid-elim x mods modalist warnings netdecls))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-expr-p-of-vl-hidexpr-hid-elim
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-expr-p (mv-nth 1 (vl-hidexpr-hid-elim x mods modalist warnings netdecls)))))

  (defthm vl-netdecllist-p-of-vl-hidexpr-hid-elim
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-netdecllist-p netdecls)))
             (vl-netdecllist-p (mv-nth 2 (vl-hidexpr-hid-elim x mods modalist warnings netdecls))))))




; Now we just need to extend vl-hidexpr-hid-elim throughout the whole module
; hierarchy.  Ugh.  Why am I not using ML again?

(defsection vl-expr-hid-elim

  (mutual-recursion

   (defund vl-expr-hid-elim (x mods modalist warnings netdecls)
     "Returns (MV WARNINGS-PRIME X-PRIME NETDECLS-PRIME)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (vl-warninglist-p warnings)
                                 (vl-netdecllist-p netdecls))
                     :hints(("Goal" :in-theory (disable (force))))
                     :verify-guards nil
                     :measure (vl-expr-count x)))
     (cond ((vl-hidexpr-p x)
            (vl-hidexpr-hid-elim x mods modalist warnings netdecls))

           ((vl-fast-atom-p x)
            (mv warnings x netdecls))

           (t
            (b* (((mv warnings args-prime netdecls)
                  (vl-exprlist-hid-elim (vl-nonatom->args x)
                                        mods modalist warnings netdecls))
                 (x-prime
                  (change-vl-nonatom x :args args-prime)))
                (mv warnings x-prime netdecls)))))

   (defund vl-exprlist-hid-elim (x mods modalist warnings netdecls)
     "Returns (MV WARNINGS-PRIME X-PRIME NETDECLS-PRIME)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (vl-warninglist-p warnings)
                                 (vl-netdecllist-p netdecls))
                     :measure (vl-exprlist-count x)))
     (if (atom x)
         (mv warnings nil netdecls)
       (b* (((mv warnings car-prime netdecls)
             (vl-expr-hid-elim (car x) mods modalist warnings netdecls))
            ((mv warnings cdr-prime netdecls)
             (vl-exprlist-hid-elim (cdr x) mods modalist warnings netdecls))
            (x-prime (cons car-prime cdr-prime)))
           (mv warnings x-prime netdecls)))))

  (defthm vl-exprlist-hid-elim-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-hid-elim x mods modalist warnings netdecls)
                    (mv warnings nil netdecls)))
    :hints(("Goal" :in-theory (enable vl-exprlist-hid-elim))))

  (defthm vl-exprlist-hid-elim-when-of-cons
    (equal (vl-exprlist-hid-elim (cons a x) mods modalist warnings netdecls)
           (b* (((mv warnings car-prime netdecls)
                 (vl-expr-hid-elim a mods modalist warnings netdecls))
                ((mv warnings cdr-prime netdecls)
                 (vl-exprlist-hid-elim x mods modalist warnings netdecls)))
               (mv warnings (cons car-prime cdr-prime) netdecls)))
    :hints(("Goal" :in-theory (enable vl-exprlist-hid-elim))))

  (local (defun my-induction (x mods modalist warnings netdecls)
           (if (atom x)
               (mv warnings nil netdecls)
             (b* (((mv warnings & netdecls)
                   (vl-expr-hid-elim (car x) mods modalist warnings netdecls)))
                 (my-induction (cdr x) mods modalist warnings netdecls)))))

  (defthm len-of-vl-exprlist-hid-elim
    (equal (len (mv-nth 1 (vl-exprlist-hid-elim x mods modalist warnings netdecls)))
           (len x))
    :hints(("Goal" :induct (my-induction x mods modalist warnings netdecls))))

  (defthm true-listp-of-vl-exprlist-hid-elim
    (true-listp (mv-nth 1 (vl-exprlist-hid-elim x mods modalist warnings netdecls)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-induction x mods modalist warnings netdecls))))

  (FLAG::make-flag vl-flag-expr-hid-elim
                   vl-expr-hid-elim
                   :flag-mapping ((vl-expr-hid-elim . expr)
                                  (vl-exprlist-hid-elim . list)))

  (defthm-vl-flag-expr-hid-elim lemma
    (expr (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-expr-hid-elim x mods modalist
                                                              warnings netdecls))))
          :name vl-warninglist-p-of-vl-expr-hid-elim)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-exprlist-hid-elim x mods modalist
                                                                  warnings netdecls))))
          :name vl-warninglist-p-of-vl-exprlist-hid-elim)
    :hints(("Goal"
            :induct (vl-flag-expr-hid-elim flag x mods modalist warnings netdecls)
            :expand ((vl-expr-hid-elim x mods modalist warnings netdecls)
                     (vl-exprlist-hid-elim x mods modalist warnings netdecls)))))

  (defthm-vl-flag-expr-hid-elim lemma
    (expr (implies (and (force (vl-expr-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-expr-p (mv-nth 1 (vl-expr-hid-elim x mods modalist
                                                        warnings netdecls))))
          :name vl-expr-p-of-vl-expr-hid-elim)
    (list (implies (and (force (vl-exprlist-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-exprlist-p (mv-nth 1 (vl-exprlist-hid-elim x mods modalist
                                                                warnings netdecls))))
          :name vl-exprlist-p-of-vl-exprlist-hid-elim)
    :hints(("Goal"
            :induct (vl-flag-expr-hid-elim flag x mods modalist warnings netdecls)
            :expand ((vl-expr-hid-elim x mods modalist warnings netdecls)
                     (vl-exprlist-hid-elim x mods modalist warnings netdecls)))))

  (defthm-vl-flag-expr-hid-elim lemma
    (expr (implies (and (force (vl-expr-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods)))
                        (force (vl-netdecllist-p netdecls)))
                   (vl-netdecllist-p (mv-nth 2 (vl-expr-hid-elim x mods modalist
                                                              warnings netdecls))))
          :name vl-netdecllist-p-of-vl-expr-hid-elim)
    (list (implies (and (force (vl-exprlist-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods)))
                        (force (vl-netdecllist-p netdecls)))
                   (vl-netdecllist-p (mv-nth 2 (vl-exprlist-hid-elim x mods modalist
                                                                  warnings netdecls))))
          :name vl-netdecllist-p-of-vl-exprlist-hid-elim)
    :hints(("Goal"
            :induct (vl-flag-expr-hid-elim flag x mods modalist warnings netdecls)
            :expand ((vl-expr-hid-elim x mods modalist warnings netdecls)
                     (vl-exprlist-hid-elim x mods modalist warnings netdecls)))))

  (verify-guards vl-expr-hid-elim))



;; Now we extend this across the modules, stupid stupid.

(defmacro def-vl-hid-elim (name &key type body)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-net-s  (cat "VL-NETDECLLIST-P-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-net    (intern-in-package-of-symbol thm-net-s name))
         )
  `(defsection ,name

    (defund ,name (x mods modalist warnings netdecls)
      (declare (xargs :guard (and (,type x)
                                  (vl-modulelist-p mods)
                                  (equal modalist (vl-modalist mods))
                                  (vl-warninglist-p warnings)
                                  (vl-netdecllist-p netdecls)))
               (ignorable mods modalist))
      ,body)

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x mods modalist warnings netdecls)))))

    (defthm ,thm-type
      (implies (and (force (,type x))
                    (force (vl-modulelist-p mods))
                    (force (equal modalist (vl-modalist mods))))
               (,type (mv-nth 1 (,name x mods modalist warnings netdecls)))))

    (defthm ,thm-net
      (implies (and (force (,type x))
                    (force (vl-modulelist-p mods))
                    (force (equal modalist (vl-modalist mods)))
                    (force (vl-netdecllist-p netdecls)))
               (vl-netdecllist-p (mv-nth 2 (,name x mods modalist warnings netdecls)))))

    )))


(defmacro def-vl-hid-elim-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-net-s  (cat "VL-NETDECLLIST-P-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name))
         (thm-net    (intern-in-package-of-symbol thm-net-s name))
         )

  `(defsection ,name

    (defund ,name (x mods modalist warnings netdecls)
      (declare (xargs :guard (and (,type x)
                                  (vl-modulelist-p mods)
                                  (equal modalist (vl-modalist mods))
                                  (vl-warninglist-p warnings)
                                  (vl-netdecllist-p netdecls))))
      (if (atom x)
          (mv warnings nil netdecls)
        (b* (((mv warnings car-prime netdecls)
              (,element (car x) mods modalist warnings netdecls))
             ((mv warnings cdr-prime netdecls)
              (,name (cdr x) mods modalist warnings netdecls)))
            (mv warnings (cons car-prime cdr-prime) netdecls))))

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x mods modalist warnings netdecls)))))

    (defthm ,thm-type
      (implies (and (force (,type x))
                    (force (vl-modulelist-p mods))
                    (force (equal modalist (vl-modalist mods))))
               (,type (mv-nth 1 (,name x mods modalist warnings netdecls)))))

    (defthm ,thm-true
      (true-listp (mv-nth 1 (,name x mods modalist warnings netdecls)))
      :rule-classes :type-prescription)

    (defthm ,thm-net
      (implies (and (force (,type x))
                    (force (vl-modulelist-p mods))
                    (force (equal modalist (vl-modalist mods)))
                    (force (vl-netdecllist-p netdecls)))
               (vl-netdecllist-p (mv-nth 2 (,name x mods modalist warnings netdecls)))))
    )))


(def-vl-hid-elim vl-maybe-expr-hid-elim
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv warnings nil netdecls)
          (vl-expr-hid-elim x mods modalist warnings netdecls)))

(def-vl-hid-elim vl-assign-hid-elim
  :type vl-assign-p
  :body (b* (((mv warnings lvalue-prime netdecls)
              (vl-expr-hid-elim (vl-assign->lvalue x) mods modalist warnings netdecls))
             ((mv warnings expr-prime netdecls)
              (vl-expr-hid-elim (vl-assign->expr x) mods modalist warnings netdecls))
             (x-prime (change-vl-assign x
                                        :lvalue lvalue-prime
                                        :expr expr-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-assignlist-hid-elim
  :type vl-assignlist-p
  :element vl-assign-hid-elim)


(def-vl-hid-elim vl-plainarg-hid-elim
  :type vl-plainarg-p
  :body (b* ((expr (vl-plainarg->expr x))
             ((when (not expr))
              (mv warnings x netdecls))
             ((mv warnings expr-prime netdecls)
              (vl-expr-hid-elim expr mods modalist warnings netdecls))
             (x-prime (change-vl-plainarg x :expr expr-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-plainarglist-hid-elim
  :type vl-plainarglist-p
  :element vl-plainarg-hid-elim)


(def-vl-hid-elim vl-namedarg-hid-elim
  :type vl-namedarg-p
  :body (b* ((expr (vl-namedarg->expr x))
             ((when (not expr))
              (mv warnings x netdecls))
             ((mv warnings expr-prime netdecls)
              (vl-expr-hid-elim expr mods modalist warnings netdecls))
             (x-prime (change-vl-namedarg x :expr expr-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-namedarglist-hid-elim
  :type vl-namedarglist-p
  :element vl-namedarg-hid-elim)

(def-vl-hid-elim vl-arguments-hid-elim
  :type vl-arguments-p
  :body
  (vl-arguments-case x
    :named (b* (((mv warnings args-prime netdecls)
                 (vl-namedarglist-hid-elim x.args mods modalist warnings netdecls))
                (x-prime (change-vl-arguments-named x :args args-prime)))
            (mv warnings x-prime netdecls))
    :plain (b* (((mv warnings args-prime netdecls)
                 (vl-plainarglist-hid-elim x.args mods modalist warnings netdecls))
                (x-prime (change-vl-arguments-plain x :args args-prime)))
            (mv warnings x-prime netdecls))))

(def-vl-hid-elim vl-modinst-hid-elim
  :type vl-modinst-p
  :body (b* (((mv warnings args-prime netdecls)
              (vl-arguments-hid-elim (vl-modinst->portargs x)
                                     mods modalist warnings netdecls))
             (x-prime (change-vl-modinst x :portargs args-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-modinstlist-hid-elim
  :type vl-modinstlist-p
  :element vl-modinst-hid-elim)

(def-vl-hid-elim vl-gateinst-hid-elim
  :type vl-gateinst-p
  :body (b* (((mv warnings args-prime netdecls)
              (vl-plainarglist-hid-elim (vl-gateinst->args x)
                                        mods modalist warnings netdecls))
             (x-prime (change-vl-gateinst x :args args-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-gateinstlist-hid-elim
  :type vl-gateinstlist-p
  :element vl-gateinst-hid-elim)

(def-vl-hid-elim vl-delaycontrol-hid-elim
  :type vl-delaycontrol-p
  :body (b* (((mv warnings value-prime netdecls)
              (vl-expr-hid-elim (vl-delaycontrol->value x)
                                mods modalist warnings netdecls))
             (x-prime (change-vl-delaycontrol x :value value-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-evatom-hid-elim
  :type vl-evatom-p
  :body (b* (((mv warnings expr-prime netdecls)
              (vl-expr-hid-elim (vl-evatom->expr x)
                                mods modalist warnings netdecls))
             (x-prime (change-vl-evatom x :expr expr-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-evatomlist-hid-elim
  :type vl-evatomlist-p
  :element vl-evatom-hid-elim)

(def-vl-hid-elim vl-eventcontrol-hid-elim
  :type vl-eventcontrol-p
  :body (b* (((mv warnings atoms-prime netdecls)
              (vl-evatomlist-hid-elim (vl-eventcontrol->atoms x)
                                      mods modalist warnings netdecls))
             (x-prime (change-vl-eventcontrol x :atoms atoms-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-repeateventcontrol-hid-elim
  :type vl-repeateventcontrol-p
  :body (b* (((mv warnings expr-prime netdecls)
              (vl-expr-hid-elim (vl-repeateventcontrol->expr x)
                                mods modalist warnings netdecls))
             ((mv warnings ctrl-prime netdecls)
              (vl-eventcontrol-hid-elim (vl-repeateventcontrol->ctrl x)
                                        mods modalist warnings netdecls))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime netdecls)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-hid-elim vl-delayoreventcontrol-hid-elim
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol
            (vl-delaycontrol-hid-elim x mods modalist warnings netdecls))
           (:vl-eventcontrol
            (vl-eventcontrol-hid-elim x mods modalist warnings netdecls))
           (:vl-repeat-eventcontrol
            (vl-repeateventcontrol-hid-elim x mods modalist warnings netdecls))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-hid-elim
                    "Impossible case.  This is not really an error.  We are just ~
                     using the guard mechanism to prove that all cases have been ~
                     covered.")
                x netdecls)))))

(def-vl-hid-elim vl-maybe-delayoreventcontrol-hid-elim
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-hid-elim x mods modalist warnings netdecls)
          (mv warnings nil netdecls)))

(defthm vl-maybe-delayoreventcontrol-hid-elim-under-iff
  (implies (and (force (vl-maybe-delayoreventcontrol-p x))
                (force (vl-modulelist-p mods))
                (force (equal modalist (vl-modalist mods))))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-hid-elim
                         x mods modalist warnings netdecls))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-hid-elim
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-hid-elim))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-hid-elim)))))

(defsection vl-stmt-hid-elim

  (mutual-recursion

   (defund vl-stmt-hid-elim (x mods modalist warnings netdecls)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (vl-warninglist-p warnings)
                                 (vl-netdecllist-p netdecls))
                     :verify-guards nil
                     :measure (vl-stmt-count x)))
     (b* ((x (vl-stmt-fix x))
          ((when (vl-atomicstmt-p x))
           (case (vl-stmt-kind x)
             (:vl-nullstmt
              (mv warnings x netdecls))

             (:vl-assignstmt
              (b* (((mv warnings lvalue-prime netdecls)
                    (vl-expr-hid-elim (vl-assignstmt->lvalue x) mods modalist warnings netdecls))
                   ((mv warnings expr-prime netdecls)
                    (vl-expr-hid-elim (vl-assignstmt->expr x) mods modalist warnings netdecls))
                   ((mv warnings ctrl-prime netdecls)
                    (vl-maybe-delayoreventcontrol-hid-elim (vl-assignstmt->ctrl x) mods modalist warnings netdecls))
                   (x-prime (change-vl-assignstmt x
                                                  :lvalue lvalue-prime
                                                  :expr expr-prime
                                                  :ctrl ctrl-prime)))
                (mv warnings x-prime netdecls)))

             (:vl-deassignstmt
              (b* (((mv warnings lvalue-prime netdecls)
                    (vl-expr-hid-elim (vl-deassignstmt->lvalue x) mods modalist warnings netdecls))
                   (x-prime (change-vl-deassignstmt x :lvalue lvalue-prime)))
                (mv warnings x-prime netdecls)))

             (:vl-enablestmt
              (b* (((mv warnings id-prime netdecls)
                    (vl-expr-hid-elim (vl-enablestmt->id x) mods modalist warnings netdecls))
                   ((mv warnings args-prime netdecls)
                    (vl-exprlist-hid-elim (vl-enablestmt->args x) mods modalist warnings netdecls))
                   (x-prime (change-vl-enablestmt x
                                                  :id id-prime
                                                  :args args-prime)))
                (mv warnings x-prime netdecls)))

             (:vl-disablestmt
              (b* (((mv warnings id-prime netdecls)
                    (vl-expr-hid-elim (vl-disablestmt->id x) mods modalist warnings netdecls))
                   (x-prime (change-vl-disablestmt x :id id-prime)))
                (mv warnings x-prime netdecls)))

             (otherwise
              (b* (((mv warnings id-prime netdecls)
                    (vl-expr-hid-elim (vl-eventtriggerstmt->id x) mods modalist warnings netdecls))
                   (x-prime (change-vl-eventtriggerstmt x :id id-prime)))
                (mv warnings x-prime netdecls)))))

          ((mv warnings exprs-prime netdecls)
           (vl-exprlist-hid-elim (vl-compoundstmt->exprs x)
                                 mods modalist warnings netdecls))
          ((mv warnings stmts-prime netdecls)
           (vl-stmtlist-hid-elim (vl-compoundstmt->stmts x)
                                 mods modalist warnings netdecls))
          ((mv warnings ctrl-prime netdecls)
           (vl-maybe-delayoreventcontrol-hid-elim (vl-compoundstmt->ctrl x)
                                                  mods modalist warnings netdecls))
          (x-prime
           (change-vl-compoundstmt x
                                   :exprs exprs-prime
                                   :stmts stmts-prime
                                   :ctrl ctrl-prime)))
       (mv warnings x-prime netdecls)))

   (defund vl-stmtlist-hid-elim (x mods modalist warnings netdecls)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (vl-warninglist-p warnings)
                                 (vl-netdecllist-p netdecls))
                     :measure (vl-stmtlist-count x)))
     (if (atom x)
         (mv warnings nil netdecls)
       (b* (((mv warnings car-prime netdecls)
             (vl-stmt-hid-elim (car x) mods modalist warnings netdecls))
            ((mv warnings cdr-prime netdecls)
             (vl-stmtlist-hid-elim (cdr x) mods modalist warnings netdecls))
            (x-prime (cons car-prime cdr-prime)))
           (mv warnings x-prime netdecls)))))

  (FLAG::make-flag vl-flag-stmt-hid-elim
                   vl-stmt-hid-elim
                   :flag-mapping ((vl-stmt-hid-elim . stmt)
                                  (vl-stmtlist-hid-elim . list)))

  (defthm-vl-flag-stmt-hid-elim lemma
    (stmt (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmt-hid-elim
                                           x mods modalist warnings netdecls))))
          :name vl-warninglist-p-of-vl-stmt-hid-elim-1)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmtlist-hid-elim
                                           x mods modalist warnings netdecls))))
          :name vl-warninglist-p-of-vl-stmtlist-hid-elim-1)
    :hints(("Goal"
            :induct (vl-flag-stmt-hid-elim flag x mods modalist warnings netdecls)
            :expand ((vl-stmt-hid-elim x mods modalist warnings netdecls)
                     (vl-stmtlist-hid-elim x mods modalist warnings netdecls)))))

  (defthm vl-stmtlist-hid-elim-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-hid-elim x mods modalist warnings netdecls)
                    (mv warnings nil netdecls)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-hid-elim))))

  (defthm vl-stmtlist-hid-elim-of-cons
    (equal (vl-stmtlist-hid-elim (cons a x) mods modalist warnings netdecls)
           (b* (((mv warnings car-prime netdecls)
                 (vl-stmt-hid-elim a mods modalist warnings netdecls))
                ((mv warnings cdr-prime netdecls)
                 (vl-stmtlist-hid-elim x mods modalist warnings netdecls)))
               (mv warnings (cons car-prime cdr-prime) netdecls)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-hid-elim))))

  (local (defun my-induction (x mods modalist warnings netdecls)
           (if (atom x)
               (mv warnings x netdecls)
             (b* (((mv warnings car-prime netdecls)
                   (vl-stmt-hid-elim (car x) mods modalist warnings netdecls))
                  ((mv warnings cdr-prime netdecls)
                   (my-induction (cdr x) mods modalist warnings netdecls)))
                 (mv warnings (cons car-prime cdr-prime) netdecls)))))

  (defthm len-of-vl-stmtlist-hid-elim
    (equal (len (mv-nth 1 (vl-stmtlist-hid-elim x mods modalist warnings netdecls)))
           (len x))
    :hints(("Goal" :induct (my-induction x mods modalist warnings netdecls))))

  (defthm-vl-flag-stmt-hid-elim lemma
    (stmt (implies (and (force (vl-stmt-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-stmt-p (mv-nth 1 (vl-stmt-hid-elim x mods modalist
                                                        warnings netdecls))))
          :name vl-stmt-p-of-vl-stmt-hid-elim)
    (list (implies (and (force (vl-stmtlist-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-stmtlist-p (mv-nth 1 (vl-stmtlist-hid-elim x mods modalist
                                                                warnings netdecls))))
          :name vl-stmtlist-p-of-vl-stmtlist-hid-elim)
    :hints(("Goal"
            :induct (vl-flag-stmt-hid-elim flag x mods modalist warnings netdecls)
            :expand ((vl-stmt-hid-elim x mods modalist warnings netdecls)
                     (vl-stmtlist-hid-elim x mods modalist warnings netdecls)))))

  (defthm-vl-flag-stmt-hid-elim lemma
    (stmt (implies (and (force (vl-stmt-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods)))
                        (force (vl-netdecllist-p netdecls)))
                   (vl-netdecllist-p (mv-nth 2 (vl-stmt-hid-elim x mods modalist
                                                              warnings netdecls))))
          :name vl-netdecllist-p-of-vl-stmt-hid-elim)
    (list (implies (and (force (vl-stmtlist-p x))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods)))
                        (force (vl-netdecllist-p netdecls)))
                   (vl-netdecllist-p (mv-nth 2 (vl-stmtlist-hid-elim x mods modalist
                                                                  warnings netdecls))))
          :name vl-netdecllist-p-of-vl-stmtlist-hid-elim)
    :hints(("Goal"
            :induct (vl-flag-stmt-hid-elim flag x mods modalist warnings netdecls)
            :expand ((vl-stmt-hid-elim x mods modalist warnings netdecls)
                     (vl-stmtlist-hid-elim x mods modalist warnings netdecls)))))

  (verify-guards vl-stmt-hid-elim))


(def-vl-hid-elim vl-always-hid-elim
  :type vl-always-p
  :body (b* (((mv warnings stmt-prime netdecls)
              (vl-stmt-hid-elim (vl-always->stmt x) mods modalist warnings netdecls))
             (x-prime (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-alwayslist-hid-elim
  :type vl-alwayslist-p
  :element vl-always-hid-elim)

(def-vl-hid-elim vl-initial-hid-elim
  :type vl-initial-p
  :body (b* (((mv warnings stmt-prime netdecls)
              (vl-stmt-hid-elim (vl-initial->stmt x) mods modalist warnings netdecls))
             (x-prime (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-initiallist-hid-elim
  :type vl-initiallist-p
  :element vl-initial-hid-elim)


(defsection vl-module-hid-elim

  (defund vl-module-hid-elim (x mods modalist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (b* (((when (vl-module->hands-offp x))
          x)

         (warnings (vl-module->warnings x))

         (new-netdecls nil)
         ((mv warnings assigns new-netdecls)
          (vl-assignlist-hid-elim (vl-module->assigns x) mods modalist warnings new-netdecls))
         ((mv warnings modinsts new-netdecls)
          (vl-modinstlist-hid-elim (vl-module->modinsts x) mods modalist warnings new-netdecls))
         ((mv warnings gateinsts new-netdecls)
          (vl-gateinstlist-hid-elim (vl-module->gateinsts x) mods modalist warnings new-netdecls))
         ((mv warnings alwayses new-netdecls)
          (vl-alwayslist-hid-elim (vl-module->alwayses x) mods modalist warnings new-netdecls))
         ((mv warnings initials new-netdecls)
          (vl-initiallist-hid-elim (vl-module->initials x) mods modalist warnings new-netdecls))

         ((unless new-netdecls)
          ;; Optimization.  If there aren't any hids, don't need to do anything.
          (change-vl-module x :warnings warnings))

         ;; Now we want to add new-netdecls.  We need to make sure there aren't any
         ;; conflicting names.
         (new-netdecls (mergesort new-netdecls))
         (all-names    (vl-netdecllist->names-exec new-netdecls
                                                   (vl-module->modnamespace x)))
         ((unless (uniquep all-names))
          (let ((warning (make-vl-warning
                          :type :vl-hid-name-conflict
                          :msg "Flattening hierarchical identifiers produced name ~
                                conflicts for ~&0.  New-netdecls are ~x1."
                          :args (list (duplicated-members all-names)
                                      new-netdecls)
                          :fatalp t
                          :fn 'vl-module-hid-elim)))
            (change-vl-module x :warnings (cons warning warnings))))

         (x-prime (change-vl-module x
                                    :assigns assigns
                                    :modinsts modinsts
                                    :netdecls (append new-netdecls (vl-module->netdecls x))
                                    :gateinsts gateinsts
                                    :alwayses alwayses
                                    :initials initials
                                    :warnings warnings)))
      x-prime))

  (local (in-theory (enable vl-module-hid-elim)))

  (defthm vl-module-p-of-vl-module-hid-elim
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p (vl-module-hid-elim x mods modalist))))

  (defthm vl-module->name-of-vl-module-hid-elim
    (equal (vl-module->name (vl-module-hid-elim x mods modalist))
           (vl-module->name x))))

(defprojection vl-modulelist-hid-elim-aux (x mods modalist)
  (vl-module-hid-elim x mods modalist)
  :guard (and (vl-modulelist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-hid-elim-aux
     (equal (vl-modulelist->names (vl-modulelist-hid-elim-aux x mods modalist))
            (vl-modulelist->names x)))))


(defsection vl-modulelist-hid-elim

  (defund vl-modulelist-hid-elim (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (ret      (vl-modulelist-hid-elim-aux x x modalist)))
      (fast-alist-free modalist)
      ret))

  (local (in-theory (enable vl-modulelist-hid-elim)))

  (defthm vl-modulelist-p-of-vl-modulelist-hid-elim
    (implies (vl-modulelist-p x)
             (vl-modulelist-p (vl-modulelist-hid-elim x))))

  (defthm vl-modulelist->names-of-vl-modulelist-hid-elim
    (equal (vl-modulelist->names (vl-modulelist-hid-elim x))
           (vl-modulelist->names x))))

(define vl-design-hid-elim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x
                      :mods (vl-modulelist-hid-elim x.mods))))