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
;;(include-book "xf-reset-elim")
;;(include-book "xf-make-defm-command")
(include-book "../mlib/port-bits")
(include-book "../transforms/xf-resolve-ranges")
(include-book "../mlib/hierarchy")
(include-book "../mlib/find-item")
(include-book "../mlib/expr-tools")
(include-book "../mlib/hid-tools")
(include-book "../wf-ranges-resolved-p")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(local (defthm crock3
         (implies (and (force (stringp name))
                       (force (vl-module-p x)))
                  (symbolp (tag (vl-find-moduleitem name x))))
         :hints(("Goal"
                 :in-theory (disable vl-find-moduleitem-type-when-nothing-else)
                 :use ((:instance vl-find-moduleitem-type-when-nothing-else))))))


(defxdoc hid-elim
  :parents (transforms)

  :short "Box up hierarchical names into \"externals\" modules."

  :long "<p>This transform confines all uses of hierarchical identifiers to new
<i>externals</i> modules, which can be translated into E in a special way.</p>

<p>This transformation has two phases that must occur separately.</p>

<ul>

<li>@(see vl-modulelist-follow-hids) should happen after implicit wire
declarations are added, but before any modules are thrown out.</li>

<li>@(see vl-modulelist-hid-elim) should happen after unparameterization and
range resolution, but before any expression sizing.</li>

</ul>


<h3>Motivation</h3>

<p>Hierarchical identifiers such as <tt>top.foo.bar.baz</tt> seem very
difficult to synthesize.  Why?  Here are some scenarios.  In these diagrams,
names represent modules and lines represent instantiation.</p>

<h5>Scenario A: access unrelated data</h5>
<code>
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
</code>

<h5>Scenario B: access submodule data</h5>
<code>
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
</code>

<h5>Scenario C: access parent data</h5>
<code>
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
</code>

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
require us to actually synthesize them into gate-level modules.  We accomplish
this using special <b>externals</b> modules.</p>

<h3>Externals Modules</h3>

<p>Suppose we want to deal with some module, <tt>Mod</tt>, that reads from the
hierarchical identifiers <tt>h1</tt>, ..., <tt>hn</tt>.  Further assume that we
are not dealing with any writes to hierarchical identifiers, since that's still
crazy.</p>

<p>Let <tt>hi_flat</tt> be a flattened, ordinary identifier that is derived
from <tt>hi</tt>, but which does not conflict with any other wire in
<tt>Mod</tt> or with any other <tt>hj_flat</tt>.</p>

<p>The HID elimination transform begins by introducing a new module,
<tt>Mod$externals</tt>, that \"boxes up\" all of these identifiers.  The
Verilog definition of <tt>Mod$externals</tt> is as follows:</p>

<code>
module Mod$externals (h1_flat, h2_flat, ..., hn_flat) ;

  output [... width of h1 ...] h1_flat;
  output [... width of h2 ...] h2_flat;
  ...
  output [... width of hn ...] hn_flat;

  assign h1_flat = h1;
  assign h2_flat = h2;
  ...
  assign hn_flat = hn;

endmodule
</code>

<p>Given this, it seems sound to rewrite Mod as follows.  First, add an
instance of <tt>Mod$externals</tt> and all of the appropriate wires, i.e.,</p>

<code>
module Mod ( ... ) ;

  wire [... width of h1 ...] h1_flat;
  wire [... width of h2 ...] h2_flat;
  ...
  wire [... width of hn ...] hn_flat;

  Mod$externals externals (h1_flat, h2_flat, ..., hn_flat);

  ... rest of mod ...

endmodule
</code>

<p>Then replace each occurrence of <tt>hi</tt> in <tt>Mod</tt> with
<tt>hi_flat</tt>.  Assuming that we are careful enough not to introduce any
name conflicts, I think this is a legitimate transform that will precisely
preserve the simulation semantics of <tt>Mod</tt>.</p>

<h3>Externals Modules in E</h3>

<p>So, what's the point?  All we have done so far is isolated the uses of
hierarchical identifiers into this externals module.</p>

<p>The idea is that, in our E conversion, we will eliminate all of these
assignments and instead suppose that the externals module is outputting the
value of some registers.  That is, imagine that <tt>Mod$externals</tt> is
just:</p>

<code>
module Mod$externals (h1_flat, h2_flat, ..., hn_flat) ;

  output reg [... width of h1 ...] h1_flat;
  output reg [... width of h2 ...] h2_flat;
  ...
  output reg [... width of hn ...] hn_flat;

endmodule
</code>

<p>In the E world, <tt>Mod$externals</tt> just emits some state bits that need
to be initialized before each call of Emod.  When proving properties about
<tt>Mod</tt>, we imagine that we could either</p>

<ul>

<li>initialize all externals to <tt>X</tt>, which would be conservative,
or</li>

<li>use an extended Emod to actually find the corresponding values out of other
modules and initialize the state bits appropriately.</li>

</ul>


<h3>Introducing the Externals Modules</h3>

<p>In principle this is easy.</p>

<ol>

<li>Collect all of the hierarchical identifiers used in a module</li>

<li>Mangle their names so that they are ordinary identifiers that don't
   collide with any other names.</li>

<li>Figure out their sizes,</li>

<li>Introduce wire declarations and <tt>Mod$externals</tt>.</li>

</ol>

<p>The really tricky part is #3.  First, we need to be able to figure out what
a hierarchical identifier is pointing at.  Then, we need to see how big that
wire is.</p>

<p>Here's the problem.  In order for all of the sizes to be computed, we will
have needed to carry out unparameterization and range resolution.  But by the
time we have gotten that far, we might have thrown some modules away already,
in particular we may have thrown away modules like <tt>top</tt> that are part
of the hierarchical reference!  Ugh!</p>

<h4>Pre-Resolving HIDs</h4>

<p>To work around this, my first plan was the following:</p>

<p>Right after parsing, or at least alongside other annotation passes like
adding wire declarations for implicit wires, we are going to find every
hierarchical reference in the module list and figure out what module it points
at.  That is, given a hierarchical reference like:</p>

<code>
top.foo.bar[3].baz.w;
</code>

<p>We are going to figure out what module is <tt>baz</tt> an instance of.
Suppose it is an instance of <tt>bazmod</tt>.  Then, we will annotate this
hierarchical identifier with the attribute:</p>

<code>
VL_HID_RESOLVED_MODULE_NAME = \"bazmod\"
</code>

<p>Later on, when we go to figure out the size of our new flattened wire for
<tt>top.foo.bar[3].baz.w</tt>, we don't have to traverse the hierarchy again.
Instead, we will just look up the resolved module name, and go find the size of
<tt>w</tt> in that module.</p>

<p>Note that the resolved name is the <b>origname</b> of the module.  After we
unparameterize, the actual module name might have changed.</p>

<h4>Pre-Collecting Sizes</h4>

<p>After implementing this plan, I discovered a problem.  Many times, even the
module named by <tt>VL_HID_RESOLVED_MODULE_NAME</tt> is unreasonable!  For
instance, many references point to things like clocks in <tt>processor</tt>, so
waiting until after unparameterization and range resolution to try to detect
wire sizes seems difficult because these modules are going to be thrown
away.</p>

<p>To address this, I implemented the following tweak: when we do the initial
lookup, if the range we are looking at is already resolved, go ahead and record
additional attributes:</p>

<ul>

<li><tt>VL_HID_RESOLVED_RANGE_P</tt> is added if the width of the wire can
already be determined at name-resolution time.  In particular, we can determine
the range if it is already resolved, or if it is a single wire that has no
range declaration.</li>

</ul>

<p>And, if there is a range:</p>

<ul>

<li><tt>VL_HID_RESOLVED_RANGE_LEFT</tt> is associated with the expression for
the left-hand side of a range, and</li>

<li><tt>VL_HID_RESOLVED_RANGE_RIGHT</tt> is associated with the expression for
the right-hand side of the range.</li>

</ul>

<p>This way, in the second pass, we only need to try to look up the width if we
don't find these attributes already available.  In practice, almost all ranges
in unparameterized modules are already resolved, so this nicely handles
hierarchical references to wires inside of <tt>processor</tt>, etc.</p>")






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


         ((unless (vl-hid-indicies-resolved-p x))
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

         ((unless (and (or localp globalp)
                       (or (not localp) (not globalp))
                       (and (vl-atom-p target-val)
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

         ((unless (or (eq (tag item) :vl-netdecl)
                      (eq (tag item) :vl-regdecl)))
          (mv (cons (make-vl-warning
                     :type :vl-bad-hid
                     :msg "The hierarchical identifier ~a0 refers to ~s1 in module ~
                           ~m2, which is a module item of type ~s3.  But we only ~
                           allow references to regs and nets."
                     :args (list x itemname target-modname (tag item))
                     :fatalp t
                     :fn 'vl-hidexpr-hid-elim)
                    warnings)
              x netdecls))

         ((mv range signedp arrdims)
          (if (eq (tag item) :vl-netdecl)
              (mv (vl-netdecl->range item)
                  (vl-netdecl->signedp item)
                  (vl-netdecl->arrdims item))
            (mv (vl-regdecl->range item)
                (vl-regdecl->signedp item)
                (vl-regdecl->arrdims item))))

         ((unless (vl-maybe-range-resolved-p range))
          (mv (cons (make-vl-warning
                     :type :vl-bad-hid
                     :msg "The hierarchical identifier ~a0 refers to ~s1 in module ~
                           ~m2, which is a net/reg with range ~a3.  Expected ranges ~
                           to be resolved!"
                     :args (list x itemname target-modname range)
                     :fatalp t
                     :fn 'vl-hidexpr-hid-elim)
                    warnings)
              x netdecls))

         (netdecl   (make-vl-netdecl :name flat-name
                                     :type :vl-wire
                                     :range range
                                     :signedp signedp
                                     :arrdims arrdims
                                     :loc *vl-fakeloc*
                                     :atts decl-atts)))

        (mv warnings x-prime (cons netdecl netdecls))))

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
                     :measure (two-nats-measure (acl2-count x) 1)))
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
                     :measure (two-nats-measure (acl2-count x) 0)))
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
         (thm-warn-s (str::cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (str::cat type-s "-OF-" name-s))
         (thm-net-s  (str::cat "VL-NETDECLLIST-P-OF-" name-s))
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
         (thm-warn-s (str::cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (str::cat type-s "-OF-" name-s))
         (thm-true-s (str::cat "TRUE-LISTP-OF-" name-s))
         (thm-net-s  (str::cat "VL-NETDECLLIST-P-OF-" name-s))
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
  :body (b* ((namedp (vl-arguments->namedp x))
             (args   (vl-arguments->args x))
             ((mv warnings args-prime netdecls)
              (if (vl-arguments->namedp x)
                  (vl-namedarglist-hid-elim args mods modalist warnings netdecls)
                (vl-plainarglist-hid-elim args mods modalist warnings netdecls)))
             (x-prime (vl-arguments namedp args-prime)))
            (mv warnings x-prime netdecls)))

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


(def-vl-hid-elim vl-nullstmt-hid-elim
  :type vl-nullstmt-p
  :body (mv warnings x netdecls))

(def-vl-hid-elim vl-assignstmt-hid-elim
  :type vl-assignstmt-p
  :body (b* (((mv warnings lvalue-prime netdecls)
              (vl-expr-hid-elim (vl-assignstmt->lvalue x)
                                mods modalist warnings netdecls))
             ((mv warnings expr-prime netdecls)
              (vl-expr-hid-elim (vl-assignstmt->expr x)
                                mods modalist warnings netdecls))
             ((mv warnings ctrl-prime netdecls)
              (vl-maybe-delayoreventcontrol-hid-elim (vl-assignstmt->ctrl x)
                                                     mods modalist warnings netdecls))
             (x-prime
              (change-vl-assignstmt x
                                    :lvalue lvalue-prime
                                    :expr expr-prime
                                    :ctrl ctrl-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-deassignstmt-hid-elim
  :type vl-deassignstmt-p
  :body (b* (((mv warnings lvalue-prime netdecls)
              (vl-expr-hid-elim (vl-deassignstmt->lvalue x)
                                mods modalist warnings netdecls))
             (x-prime
              (change-vl-deassignstmt x :lvalue lvalue-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-enablestmt-hid-elim
  :type vl-enablestmt-p
  :body (b* (((mv warnings id-prime netdecls)
              (vl-expr-hid-elim (vl-enablestmt->id x)
                                mods modalist warnings netdecls))
             ((mv warnings args-prime netdecls)
              (vl-exprlist-hid-elim (vl-enablestmt->args x)
                                    mods modalist warnings netdecls))
             (x-prime
              (change-vl-enablestmt x
                                    :id id-prime
                                    :args args-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-disablestmt-hid-elim
  :type vl-disablestmt-p
  :body (b* (((mv warnings id-prime netdecls)
              (vl-expr-hid-elim (vl-disablestmt->id x)
                                mods modalist warnings netdecls))
             (x-prime
              (change-vl-disablestmt x :id id-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-eventtriggerstmt-hid-elim
  :type vl-eventtriggerstmt-p
  :body (b* (((mv warnings id-prime netdecls)
              (vl-expr-hid-elim (vl-eventtriggerstmt->id x)
                                mods modalist warnings netdecls))
             (x-prime
              (change-vl-eventtriggerstmt x :id id-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim vl-atomicstmt-hid-elim
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (vl-nullstmt-hid-elim     x mods modalist warnings netdecls))
          (:vl-assignstmt       (vl-assignstmt-hid-elim   x mods modalist warnings netdecls))
          (:vl-deassignstmt     (vl-deassignstmt-hid-elim x mods modalist warnings netdecls))
          (:vl-enablestmt       (vl-enablestmt-hid-elim   x mods modalist warnings netdecls))
          (:vl-disablestmt      (vl-disablestmt-hid-elim  x mods modalist warnings netdecls))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-hid-elim x mods modalist warnings netdecls))
          (otherwise
           (mv (er hard 'vl-atomicstmt-hid-elim
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               x netdecls))))

(defsection vl-stmt-hid-elim

  (mutual-recursion

   (defund vl-stmt-hid-elim (x mods modalist warnings netdecls)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (vl-warninglist-p warnings)
                                 (vl-netdecllist-p netdecls))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-hid-elim x mods modalist warnings netdecls)
       (b* (((mv warnings exprs-prime netdecls)
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
           (mv warnings x-prime netdecls))))

   (defund vl-stmtlist-hid-elim (x mods modalist warnings netdecls)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (vl-warninglist-p warnings)
                                 (vl-netdecllist-p netdecls))
                     :measure (two-nats-measure (acl2-count x) 0)))
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
              (vl-stmt-hid-elim (vl-always->stmt x)
                                mods modalist warnings netdecls))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-alwayslist-hid-elim
  :type vl-alwayslist-p
  :element vl-always-hid-elim)

(def-vl-hid-elim vl-initial-hid-elim
  :type vl-initial-p
  :body (b* (((mv warnings stmt-prime netdecls)
              (vl-stmt-hid-elim (vl-initial->stmt x)
                                mods modalist warnings netdecls))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime netdecls)))

(def-vl-hid-elim-list vl-initiallist-hid-elim
  :type vl-initiallist-p
  :element vl-initial-hid-elim)







; From the netdecl list that we produce, we can construct the entire externals
; module and its instance.  This takes a bit of work but it's all
; straightforward.

(defsection vl-hid-netdecls-to-output-portdecls

  (defund vl-hid-netdecls-to-output-portdecls (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (if (atom x)
        nil
      (cons (make-vl-portdecl :name (vl-netdecl->name (car x))
                              :range (vl-netdecl->range (car x))
                              :signedp (vl-netdecl->signedp (car x))
                              :dir :vl-output
                              :loc (vl-netdecl->loc (car x)))
            (vl-hid-netdecls-to-output-portdecls (cdr x)))))

  (local (in-theory (enable vl-hid-netdecls-to-output-portdecls)))

  (defthm vl-portdecllist-p-of-vl-hid-netdecls-to-output-portdecls
    (implies (force (vl-netdecllist-p x))
             (vl-portdecllist-p (vl-hid-netdecls-to-output-portdecls x)))))



(defsection vl-hid-netdecls-to-ports

  (defund vl-hid-netdecls-to-ports (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (if (atom x)
        nil
      (let* ((name (vl-netdecl->name (car x)))
             (expr (make-vl-atom :guts (make-vl-id :name name))))
        (cons (make-vl-port :name name
                            :expr expr
                            :loc *vl-fakeloc*)
              (vl-hid-netdecls-to-ports (cdr x))))))

  (local (in-theory (enable vl-hid-netdecls-to-ports)))

  (defthm vl-portlist-p-of-vl-hid-netdecls-to-ports
    (implies (force (vl-netdecllist-p x))
             (vl-portlist-p (vl-hid-netdecls-to-ports x)))))



(defsection vl-hid-netdecls-to-plainargs

  (defund vl-hid-netdecls-to-plainargs (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (if (atom x)
        nil
      (let* ((name (vl-netdecl->name (car x)))
             (expr (make-vl-atom :guts (make-vl-id :name name))))
        (cons (make-vl-plainarg :expr expr
                                :portname name
                                :dir :vl-output)
              (vl-hid-netdecls-to-plainargs (cdr x))))))

  (local (in-theory (enable vl-hid-netdecls-to-plainargs)))

  (defthm vl-plainarglist-p-of-vl-hid-netdecls-to-plainargs
    (implies (force (vl-netdecllist-p x))
             (vl-plainarglist-p (vl-hid-netdecls-to-plainargs x)))))


(defsection vl-hid-netdecls-to-assigns

  (defund vl-hid-netdecls-to-assigns (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (if (atom x)
        nil
      (b* ((name   (vl-netdecl->name (car x)))
           (atts   (vl-netdecl->atts (car x)))
           (lvalue (make-vl-atom :guts (make-vl-id :name name)))
           (lookup (cdr (assoc-equal "VL_HID_ORIG" atts)))
           ((when (not lookup))
            ;; This is a converted register instead of an HID.  Don't
            ;; make an assignment for it.
            (vl-hid-netdecls-to-assigns (cdr x)))
           (assign (make-vl-assign :lvalue lvalue
                                   :expr lookup
                                   :loc *vl-fakeloc*)))
          (cons assign
                (vl-hid-netdecls-to-assigns (cdr x))))))

  (local (in-theory (enable vl-hid-netdecls-to-assigns)))

  (defthm vl-assignlist-p-of-vl-hid-netdecls-to-assigns
    (implies (force (vl-netdecllist-p x))
             (vl-assignlist-p (vl-hid-netdecls-to-assigns x)))))



(defsection vl-make-hid-occs

  (defund vl-make-hid-occs (x)
    (declare (xargs :guard (symbol-listp x)))
    (if (atom x)
        nil
      ;; Each name is of an individual wire, w.  We need to generate
      ;; (:u ext-out :op *ff* :i (out) :o out)
      (let ((generator-name (intern-in-package-of-symbol
                             (str::cat "ext-" (symbol-name (car x)))
                             (car x))))
        (cons `(:u ,generator-name :op ACL2::*ff* :i (,(car x)) :o ,(car x))
              (vl-make-hid-occs (cdr x)))))))



(defsection vl-make-externals-module

  (local (defthm symbol-listp-of-append-domains
           (implies (vl-wirealist-p x)
                    (symbol-listp (append-domains x)))))

  (defund vl-make-externals-module (modname netdecls)
    (declare (xargs :guard (and (stringp modname)
                                (vl-netdecllist-p netdecls))))
    (b* ((modname-expr
          (make-vl-atom :guts (make-vl-id :name modname)))

         (atts nil)
         ;; NO, don't use hands-off.  We want these wires to get
         ;; sized and defm now respects the existing defm.
         ;; (atts (acons "VL_HANDS_OFF" nil atts))
         (atts (acons "VL_EXTERNALS" modname-expr atts))

         (ports     (vl-hid-netdecls-to-ports netdecls))
         (portdecls (vl-hid-netdecls-to-output-portdecls netdecls))
         (assigns   (vl-hid-netdecls-to-assigns netdecls))

         (new-modname (str::cat modname "$externals"))
         (mod  (make-vl-module :name new-modname
                               :origname new-modname
                               :netdecls netdecls
                               :ports ports
                               :portdecls portdecls
                               :assigns assigns
                               :minloc *vl-fakeloc*
                               :maxloc *vl-fakeloc*
                               :atts atts))

; We now generate a custom emod module for this.  The basic idea for the defm
; is that every bit should be uniquely assigned by a *ff* module that is driven
; by itself.  These modules will never change state from what the user inputs,
; but can be configured at the beginning of an emod step.  For instance, a one
; bit module could look like this:
;
; (defm *one-bit-external*
;   '(:i ()
;     :o ((out))
;     :occs ((:u ext-out :op *ff* :i (out) :o out))))

         (starname (vl-starname new-modname))

         ((mv successp warnings walist)
          (vl-module-wirealist mod nil))

         ((unless successp)
          (change-vl-module mod :warnings warnings))

         ;; Compute :i and :o fields.

         ((mv successp warnings in out)
          (vl-portdecls-to-i/o portdecls walist))
         ((unless successp)
          (change-vl-module mod :warnings warnings))

         ;; No :c, no :cd.

         (wires (append-domains walist))
         (occs  (vl-make-hid-occs wires))

         (- (fast-alist-free walist))

         (defm `(ACL2::defm ,starname '(:i ,in :o ,out :occs ,occs)))
         (mod  (change-vl-module mod :defm defm)))

        mod))

  (local (in-theory (enable vl-make-externals-module)))

  (defthm vl-module-p-of-vl-make-externals-module
    (implies (and (force (stringp modname))
                  (force (vl-netdecllist-p netdecls)))
             (vl-module-p (vl-make-externals-module modname netdecls)))))





; One final twist.  We also make any Reset Aliases externals.  We previously
; tried to handle this by looking at source types, and did this for any
; registers that were found in //!! or //@@ comments.  But, with the new
; mp_verror handling, makeTop strips those out and we can't see them anymore.
; We therefore revived the reset detection code from xf-reset-elim, and are
; trying to use it now.

;; (defsection vl-regdecls-to-netdecls-for-externals

;;   (defund vl-regdecls-to-netdecls-for-externals (x)
;;     (declare (xargs :guard (vl-regdecllist-p x)
;;                     :guard-debug t))
;;     (if (atom x)
;;         nil
;;       (let* ((reg     (car x))
;;              (atts    (vl-regdecl->atts reg))
;;              (atts    (acons "VL_RESET_ALIAS" nil atts))
;;              (netdecl (make-vl-netdecl :name    (vl-regdecl->name reg)
;;                                        :type    :vl-wire
;;                                        :signedp (vl-regdecl->signedp reg)
;;                                        :range   (vl-regdecl->range reg)
;;                                        :arrdims (vl-regdecl->arrdims reg)
;;                                        :loc     (vl-regdecl->loc reg)
;;                                        :atts    atts)))
;;         (cons netdecl
;;               (vl-regdecls-to-netdecls-for-externals (cdr x))))))

;;   (local (in-theory (enable vl-regdecls-to-netdecls-for-externals)))

;;   (defthm vl-netdecllist-p-of-vl-regdecls-to-netdecls-for-externals
;;     (implies (vl-regdecllist-p x)
;;              (vl-netdecllist-p (vl-regdecls-to-netdecls-for-externals x)))))




;; A transform to rewrite all statements so that writes to converted regdecls
;; are thrown away.

(defsection vl-atomicstmt-kill-regassigns

  (defund vl-atomicstmt-kill-regassigns (x regnames)
    ;; A lot like vl-atomicstmt-eliminate-resets, but doesn't try to replace
    ;; resets with 1 in the rhses.  Just turn any assignments to regnames into
    ;; no-ops.
    (declare (xargs :guard (and (vl-atomicstmt-p x)
                                (string-listp regnames))))
    (case (tag x)
      (:vl-assignstmt
       (let ((lvalue (vl-assignstmt->lvalue x)))
         (if (and (vl-idexpr-p lvalue)
                  (member-equal (vl-idexpr->name lvalue) regnames))
             (make-vl-nullstmt)
           x)))
      (otherwise x)))

  (local (in-theory (enable vl-atomicstmt-kill-regassigns)))

  (defthm vl-stmt-p-of-vl-atomicstmt-kill-regassigns
    (implies (force (vl-atomicstmt-p x))
             (vl-stmt-p (vl-atomicstmt-kill-regassigns x regnames)))))

(defsection vl-stmt-kill-regassigns

  (mutual-recursion

   (defund vl-stmt-kill-regassigns (x regnames)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (string-listp regnames))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))

     (cond ((vl-fast-atomicstmt-p x)
            (vl-atomicstmt-kill-regassigns x regnames))

           ((not (mbt (consp x)))
            x)

           (t
            (let* ((stmts       (vl-compoundstmt->stmts x))
                   (stmts-prime (vl-stmtlist-kill-regassigns stmts regnames)))
              (change-vl-compoundstmt x :stmts stmts-prime)))))

   (defund vl-stmtlist-kill-regassigns (x regnames)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (string-listp regnames))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-stmt-kill-regassigns (car x) regnames)
             (vl-stmtlist-kill-regassigns (cdr x) regnames)))))

  (defthm vl-stmtlist-kill-regassigns-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-kill-regassigns x regnames)
                    nil))
    :hints(("Goal" :in-theory (enable vl-stmtlist-kill-regassigns))))

  (defthm vl-stmtlist-kill-regassigns-of-cons
    (equal (vl-stmtlist-kill-regassigns (cons a x) regnames)
           (cons (vl-stmt-kill-regassigns a regnames)
                 (vl-stmtlist-kill-regassigns x regnames)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-kill-regassigns))))

  (local (in-theory (disable pick-a-point-subsetp-equal-strategy)))
  (defprojection vl-stmtlist-kill-regassigns (x regnames)
    (vl-stmt-kill-regassigns x regnames)
    :already-definedp t)

  (flag::make-flag vl-flag-stmt-kill-regassigns
                   vl-stmt-kill-regassigns
                   :flag-mapping ((vl-stmt-kill-regassigns . stmt)
                                  (vl-stmtlist-kill-regassigns . list)))

  (defthm-vl-flag-stmt-kill-regassigns lemma
    (stmt (implies (force (vl-stmt-p x))
                   (vl-stmt-p (vl-stmt-kill-regassigns x regnames)))
          :name vl-stmt-p-of-vl-stmt-kill-regassigns)
    (list (implies (force (vl-stmtlist-p x))
                   (vl-stmtlist-p (vl-stmtlist-kill-regassigns x regnames)))
          :name vl-stmtlist-p-of-vl-stmtlist-kill-regassigns)
    :hints(("Goal"
            :induct (vl-flag-stmt-kill-regassigns flag x regnames)
            :expand ((vl-stmt-kill-regassigns x regnames)))))

  (verify-guards vl-stmt-kill-regassigns))



(defsection vl-always-kill-regassigns

  (defund vl-always-kill-regassigns (x regnames)
    (declare (xargs :guard (and (vl-always-p x)
                                (string-listp regnames))))
    (b* ((stmt       (vl-always->stmt x))
         (stmt-prime (vl-stmt-kill-regassigns stmt regnames))
         (x-prime    (change-vl-always x :stmt stmt-prime)))
        x-prime))

  (local (in-theory (enable vl-always-kill-regassigns)))

  (defthm vl-always-p-of-vl-always-kill-regassigns
    (implies (force (vl-always-p x))
             (vl-always-p (vl-always-kill-regassigns x regnames)))))


(defsection vl-alwayslist-kill-regassigns

  (local (in-theory (disable pick-a-point-subsetp-equal-strategy)))
  (defprojection vl-alwayslist-kill-regassigns (x regnames)
    (vl-always-kill-regassigns x regnames)
    :guard (and (vl-alwayslist-p x)
                (string-listp regnames)))

  (local (in-theory (enable vl-alwayslist-kill-regassigns)))

  (defthm vl-alwayslist-p-of-vl-alwayslist-kill-regassigns
    (implies (force (vl-alwayslist-p x))
             (vl-alwayslist-p (vl-alwayslist-kill-regassigns x regnames)))))



(defsection vl-initial-kill-regassigns

  (defund vl-initial-kill-regassigns (x regnames)
    (declare (xargs :guard (and (vl-initial-p x)
                                (string-listp regnames))))
    (b* ((stmt       (vl-initial->stmt x))
         (stmt-prime (vl-stmt-kill-regassigns stmt regnames))
         (x-prime    (change-vl-initial x :stmt stmt-prime)))
        x-prime))

  (local (in-theory (enable vl-initial-kill-regassigns)))

  (defthm vl-initial-p-of-vl-initial-kill-regassigns
    (implies (force (vl-initial-p x))
             (vl-initial-p (vl-initial-kill-regassigns x regnames)))))


(defsection vl-initiallist-kill-regassigns
  (local (in-theory (disable pick-a-point-subsetp-equal-strategy)))
  (defprojection vl-initiallist-kill-regassigns (x regnames)
    (vl-initial-kill-regassigns x regnames)
    :guard (and (vl-initiallist-p x)
                (string-listp regnames)))

  (local (in-theory (enable vl-initiallist-kill-regassigns)))

  (defthm vl-initiallist-p-of-vl-initiallist-kill-regassigns
    (implies (force (vl-initiallist-p x))
             (vl-initiallist-p (vl-initiallist-kill-regassigns x regnames)))))



(defsection vl-module-hid-elim

  (defund vl-module-hid-elim (x mods modalist)
    "Returns (MV X-PRIME ADDMODS)"
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (b* (((when (vl-module->hands-offp x))
          (mv x nil))

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
          (mv (change-vl-module x :warnings warnings)
              nil))

         ;; Now we want to add new-netdecls.  We need to make sure there aren't any
         ;; conflicting names.
         (new-netdecls (mergesort new-netdecls))
         (all-names    (vl-netdecllist->names-exec new-netdecls
                                                   (vl-module->modnamespace-exec x)))
         ((unless (uniquep all-names))
          (let ((warning (make-vl-warning
                          :type :vl-hid-name-conflict
                          :msg "Flattening hierarchical identifiers produced name ~
                                conflicts for ~&0.  New-netdecls are ~x1."
                          :args (list (duplicated-members all-names)
                                      new-netdecls)
                          :fatalp t
                          :fn 'vl-module-hid-elim)))
            (mv (change-vl-module x :warnings (cons warning warnings)) nil)))




; No, let's not do this reset alias stuff...
; Instead, just do this:

         (keep-regdecls (vl-module->regdecls x))

; And don't do all of this:
;
;         ;; A Twist.  Also add into netdecls any regdecls that are reset aliases.
;         (regdecls      (vl-module->regdecls x))
;         (all-regnames  (mergesort (vl-regdecllist->names regdecls)))
;
;         (reset-aliases (mergesort (vl-module-find-potential-reset-aliases x)))
;
;         ;; Dumb sanity check.
;         (- (or (subset reset-aliases all-regnames)
;                (er hard? 'vl-module-hid-elim "Reset aliases are not all regnames?")))
;
;         (warnings (if (not reset-aliases)
;                       warnings
;                     (cons (make-vl-warning
;                            :type :vl-reset-aliases
;                            :msg "The following regs are being treated as reset ~
;                                  aliases: ~&0.~%"
;                            :args (list reset-aliases)
;                            :fn 'vl-module-hid-elim)
;                           warnings)))
;
;         (keep-regdecls (vl-delete-regdecls reset-aliases regdecls))
;         (keep-regnames (vl-regdecllist->names keep-regdecls))
;
;         (kill-regdecls (vl-delete-regdecls keep-regnames regdecls))
;
;         (new-netdecls  (append (vl-regdecls-to-netdecls-for-externals kill-regdecls)
;                                new-netdecls))
;
;
;         ;; Clean up always and initial blocks to eliminate writes to the newly
;         ;; external regdecls.
;         (alwayses (vl-alwayslist-kill-regassigns alwayses reset-aliases))
;         (initials (vl-initiallist-kill-regassigns initials reset-aliases))


         ;; No name conflicts.
         (externals-mod (vl-make-externals-module (vl-module->name x) new-netdecls))

         ;; We're going to instantiate externals-mod.  We want the instance name
         ;; to be consistent, so we try to use @vl_ext, which would be really
         ;; hard for a logic designer to come up with unless they use escaped
         ;; names.  Even so, make sure it's not there.
         ((when (member-equal "@vl_ext" all-names))
          (let ((warning (make-vl-warning
                          :type :vl-hid-name-conflict
                          :msg "The name @vl_ext is already in use!"
                          :fatalp t
                          :fn 'vl-module-hid-elim)))
            (mv (change-vl-module x :warnings (cons warning warnings)) nil)))

         (ext-args (vl-arguments nil (vl-hid-netdecls-to-plainargs new-netdecls)))
         (ext-inst (make-vl-modinst :instname "@vl_ext"
                                    :modname (vl-module->name externals-mod)
                                    :range nil
                                    :paramargs (vl-arguments nil nil)
                                    :portargs ext-args
                                    :loc *vl-fakeloc*))

         (x-prime (change-vl-module x
                                    :assigns assigns
                                    :modinsts (cons ext-inst modinsts)
                                    :netdecls (append new-netdecls (vl-module->netdecls x))
                                    :regdecls keep-regdecls
                                    :gateinsts gateinsts
                                    :alwayses alwayses
                                    :initials initials
                                    :warnings warnings)))

        (mv x-prime (list externals-mod))))

  (defmvtypes vl-module-hid-elim (nil true-listp))

  (local (in-theory (enable vl-module-hid-elim)))

  (defthm vl-module-p-of-vl-module-hid-elim
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p (mv-nth 0 (vl-module-hid-elim x mods modalist)))))

  (defthm vl-module->name-of-vl-module-hid-elim
    (equal (vl-module->name (mv-nth 0 (vl-module-hid-elim x mods modalist)))
           (vl-module->name x)))

  (defthm vl-modulelist-p-of-vl-module-hid-elim
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-modulelist-p (mv-nth 1 (vl-module-hid-elim x mods modalist))))))


(defsection vl-modulelist-hid-elim-aux

  (defund vl-modulelist-hid-elim-aux (x mods modalist)
    "Returns (MV X-PRIME ADDMODS)"
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (if (atom x)
        (mv nil nil)
      (b* (((mv car-prime addmods1) (vl-module-hid-elim (car x) mods modalist))
           ((mv cdr-prime addmods2) (vl-modulelist-hid-elim-aux (cdr x) mods modalist))
           (x-prime                 (cons car-prime cdr-prime))
           (addmods                 (append addmods1 addmods2)))
          (mv x-prime addmods))))

  (defmvtypes vl-modulelist-hid-elim-aux (true-listp true-listp))

  (local (in-theory (enable vl-modulelist-hid-elim-aux)))

  (defthm vl-modulelist-p-of-vl-modulelist-hid-elim-aux-0
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-hid-elim-aux x mods modalist)))))

  (defthm vl-modulelist->names-of-vl-modulelist-hid-elim-aux
    (equal (vl-modulelist->names (mv-nth 0 (vl-modulelist-hid-elim-aux x mods modalist)))
           (vl-modulelist->names x)))

  (defthm vl-modulelist-p-of-vl-modulelist-hid-elim-aux-1
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-modulelist-p (mv-nth 1 (vl-modulelist-hid-elim-aux x mods modalist))))))



(defsection vl-modulelist-hid-elim

  (defund vl-modulelist-hid-elim (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist             (vl-modalist x))
         ((mv x-prime addmods) (vl-modulelist-hid-elim-aux x x modalist))
         (-                    (flush-hons-get-hash-table-link modalist))
         (names                (vl-modulelist->names-exec x-prime nil))
         (add-names            (vl-modulelist->names-exec addmods names))
         ((unless (uniquep add-names))
          (prog2$ (er hard? 'vl-modulelist-hid-elim
                      "Name conflict!  Duplicated names are ~&0.~%"
                      (duplicated-members add-names))
                  x-prime)))
        (append addmods x-prime)))

  (local (in-theory (enable vl-modulelist-hid-elim)))

  (defthm vl-modulelist-p-of-vl-modulelist-hid-elim
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-hid-elim x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-hid-elim
    (implies (force (no-duplicatesp-equal (vl-modulelist->names x)))
             (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-hid-elim x))))))

