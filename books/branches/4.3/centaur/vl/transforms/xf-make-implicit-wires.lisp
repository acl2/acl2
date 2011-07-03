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
(include-book "../mlib/allexprs")
(include-book "../mlib/modnamespace")
(include-book "../mlib/find-item")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defxdoc make-implicit-wires
  :parents (transforms)
  :short "Add declarations for implicit wires"

  :long "<p>This transformation adds declarations for any wires which are only
implicitly declared.  Adding declarations for these wires is useful because it
means our programs may assume every wire is declared.</p>

<p><b>BOZO</b>: Note that in the following summary, we ignore certain scoping
issues relating to tasks, functions, named blocks, and generate blocks.  VL
largely does not support these constructs.  If we ever want to add support for
these constructs, we need to revisit this code and understand the issues.</p>

<h3>Implicit Declarations in the Verilog Specification</h3>

<p>From Section 19.2, implicit wires are assumed to be of the \"default net
type,\" which is controlled by the <tt>`default_nettype</tt> compiler
directive, and which by default is <tt>wire</tt>.  But since VL does not
support this directive, our task here is simpler and we just assume all
implicit nets are of type <tt>wire</tt>.</p>

<p>Section 4.5 outlines the conditions under which an implicit net is
inferred.</p>

<h4>Case 1</h4>

<p>If there is a port declaration like <tt>input [3:0] i;</tt>, which has no
corresponding wire declaration, then we are supposed to infer an implicit net
with the vector width of the \"port expression declaration,\" which I think
means the <tt>[3:0]</tt> part.</p>

<p>Note, however, per 12.3.3, that a port declaration like <tt>input wire [3:0]
i;</tt> is treated as an explicit wire declaration in addition to being an
input declaration.</p>

<h4>Case 2</h4>

<p>If there is an undeclared identifier in the terminal list of a primitive or
module instance, or in the left-hand side of a continuous assignment statement,
then we are supposed to infer an implicit, scalar net.</p>

<p>It appears to me that a \"primitive instance\" is meant to refer to either a
gate instance or a user-defined primitive instance.  See for instance Section
7.1.6, which talks about \"primitive instance connection lists\" in reference
to gates, and 11.6.6 where primitive terminals are distinguished from module
ports.</p>

<h3>How Cadence Handles Things</h3>

<p>See <tt>test/test-implicit.v</tt> for some tests of how Verilog-XL handles
these implicit wires.  In short,</p>

<ul>

<li>It allows implicit wires to be inferred even from the arguments of gate
instances, which seems to be the intent of Case 2.</li>

<li>It complains about undeclared wires anywhere within an assignment, even on
the left-hand side, which appears to directly contradict the specification.</li>

</ul>


<h3>Our Approach</h3>

<p>We begin by addressing Case 1.  We add a net declaration for each port
declaration that needs one, and these new declarations take on the range and
signedness from the port declaration.</p>

<ul>

<li>Keeping the range seems correct with regards to the \"vector width of the
port declaration expression,\" described above.</li>

<li>Keeping the sign isn't discussed above, but appears to be the correct thing
to do; see @(see portdecl-sign) for details.</li>

</ul>

<p>Irrelevant to semantics, we also say the new declaration has the same
location as the port declaration, which practically causes our pretty-printer
to put the new net declaration right next to its port declaration.
Furthermore, we mark the net declaration with the <tt>VL_PORT_IMPLICIT</tt>
attribute, but we have no particular use for this.</p>

<p>We now address Case 2.  We add one-bit wire declarations for any undeclared
wires that occur within the port arguments of gate and module instances, and
which occur in the left-hand sides of assignments.</p>

<p>Irrelevant to semantics, we say that each new declaration is located at the
<tt>minloc</tt> for the module; see @(see vl-module-p).  The effect is that our
pretty-printer puts all of the implicit declarations first, before other module
items.  This is not necessarily the right solution, but I can't think of a much
better place for these declarations to go.  We also annotate each of these
wires with the <tt>VL_IMPLICIT</tt> attribute, which is useful in @(see
typo-detection).</p>

<p>As a convenience to the user, we may also add non-fatal @(see warnings) to
the module if we discover that any implicit wires are only found in the lhs of
an assignment.  These wires are fine according to the specification, but are
not acceptable according to Cadence.</p>")



(defsection vl-make-port-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-make-port-implicit-wires) generates the net declarations
for the implicit wires in Case 1."

  :long "<p>We are given <tt>portdecls</tt>, a list of port declarations, and
<tt>declared</tt>, a list of all the names of all nets and regs declared in the
module.  We are also given <tt>declared-fal</tt>, which should be a lookup
alist for <tt>declared</tt>; see @(see make-lookup-alist).</p>

<p>We construct a list of new net declarations, one for each port declaration
without a corresponding module item.</p>"

; BOZO what about scalaredp, vectoredp, cstrength, delay?  I think we don't
; care, but it might be good to look into this again.

  (defund vl-make-port-implicit-wires (portdecls declared fal)
    (declare (xargs :guard (and (vl-portdecllist-p portdecls)
                                (string-listp declared)
                                (equal fal (make-lookup-alist declared)))))
    (b* (((when (atom portdecls))
          nil)
         ((vl-portdecl portdecl) (car portdecls)))

        (if (fast-memberp portdecl.name declared fal)
            (vl-make-port-implicit-wires (cdr portdecls) declared fal)
          (cons (make-vl-netdecl :name portdecl.name
                                 :type :vl-wire
                                 :range portdecl.range
                                 :atts (cons (cons "VL_PORT_IMPLICIT" nil)
                                             portdecl.atts)
                                 :signedp portdecl.signedp
                                 :loc portdecl.loc)
                (vl-make-port-implicit-wires (cdr portdecls) declared fal)))))

  (local (in-theory (enable vl-make-port-implicit-wires)))

  (defthm vl-netdecllist-p-of-vl-make-port-implicit-wires
    (implies (force (vl-portdecllist-p portdecls))
             (vl-netdecllist-p
              (vl-make-port-implicit-wires portdecls declared fal)))))



(defsection vl-make-other-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-make-other-implicit-wires) generates the net declarations
for the implicit wires in Case 2."

  :long "<p>We are given <tt>x</tt>, a string list that should initially
contain the names of all implicit wires that we are supposed to introduce, and
<tt>loc</tt>, a @(see vl-location-p) that should be the <tt>minloc</tt> for the
module.  We produce a list of @(see vl-netdecl-p)s, one for each name in
<tt>x</tt>.</p>"

  (defund vl-make-other-implicit-wires (loc names)
    (declare (xargs :guard (and (vl-location-p loc)
                                (string-listp names))))
    (if (consp names)
        (cons (make-vl-netdecl :name (car names)
                               :type :vl-wire
                               :loc loc
                               :atts (list (cons "VL_IMPLICIT" nil)))
              (vl-make-other-implicit-wires loc (cdr names)))
      nil))

  (local (in-theory (enable vl-make-other-implicit-wires)))

  (defthm vl-netdecllist-p-of-vl-make-other-implicit-wires
    (implies (and (force (vl-location-p loc))
                  (force (string-listp names)))
             (vl-netdecllist-p (vl-make-other-implicit-wires loc names))))

  (defthm vl-netdecllist->names-of-vl-make-other-implicit-wires
    (equal (vl-netdecllist->names (vl-make-other-implicit-wires loc names))
           (list-fix names))))



(defsection vl-modinstlist-exprs-for-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-modinstlist-exprs-for-implicit-wires) gathers up the
expressions used in the ports of a list of module instances."

  (defund vl-modinstlist-exprs-for-implicit-wires (x acc)
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-exprlist-p acc))))
    (if (atom x)
        acc
      (b* ((args1 (vl-modinst->portargs (car x)))
           (acc   (vl-arguments-allexprs-exec args1 acc)))
          (vl-modinstlist-exprs-for-implicit-wires (cdr x) acc))))

  (local (in-theory (enable vl-modinstlist-exprs-for-implicit-wires)))

  (defthm vl-exprlist-p-of-vl-modinstlist-exprs-for-implicit-wires
    (implies (and (force (vl-modinstlist-p x))
                  (force (vl-exprlist-p acc)))
             (vl-exprlist-p (vl-modinstlist-exprs-for-implicit-wires x acc)))))



(defsection vl-gateinstlist-exprs-for-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-gateinstlist-exprs-for-implicit-wires) gathers up the
expressions used in the ports of a list of gate instances."

  (defund vl-gateinstlist-exprs-for-implicit-wires (x acc)
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-exprlist-p acc))))
    (if (atom x)
        acc
      (b* ((args1 (vl-gateinst->args (car x)))
           (acc   (vl-plainarglist-allexprs-exec args1 acc)))
          (vl-gateinstlist-exprs-for-implicit-wires (cdr x) acc))))

  (local (in-theory (enable vl-gateinstlist-exprs-for-implicit-wires)))

  (defthm vl-exprlist-p-of-vl-gateinstlist-exprs-for-implicit-wires
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-exprlist-p acc)))
             (vl-exprlist-p (vl-gateinstlist-exprs-for-implicit-wires x acc)))))




(defsection vl-module-make-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-module-make-implicit-wires) adds implicit wire declarations
to the module <tt>x</tt>."

  (defund vl-module-make-implicit-wires (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         ((when (vl-module->hands-offp x))
          x)

         (declared
          ;; Set of all explicitly declared names in the module.  I considered
          ;; just explicitly getting the reg and net names, but that might
          ;; cause us to think that, e.g., parameter names are undeclared, so
          ;; this seems safest.
          (mergesort (vl-module->modnamespace-exec x)))

         (implicit-1
          ;; The implicit wire declarations for the ports.
          (b* ((fal (make-lookup-alist declared))
               (ret (vl-make-port-implicit-wires x.portdecls declared fal))
               (-   (fast-alist-free fal)))
              ret))

         (declared
          ;; Extend declared to include implicit-1 wire names.
          ;; BOZO we also need paramdecl names
          (union (mergesort (vl-netdecllist->names-exec implicit-1 nil))
                 declared))

         (undeclared-names-from-args
          ;; Any implicitly used names from gate/submodule arguments.
          (b* ((exprs (vl-modinstlist-exprs-for-implicit-wires x.modinsts nil))
               (exprs (vl-gateinstlist-exprs-for-implicit-wires x.gateinsts exprs))
               (names (mergesort (vl-exprlist-names-exec exprs nil))))
              (difference names declared)))

         (undeclared-names-from-lhses
          ;; Any implicitly used names from lhses that ARE NOT also used in any
          ;; port arguments.  These are the ones Cadence doesn't handle right.
          (b* ((exprs (vl-assignlist->lvalues-exec x.assigns nil))
               (names (mergesort (vl-exprlist-names-exec exprs nil))))
              (difference (difference names declared)
                          undeclared-names-from-args)))

         (undeclared-names
          ;; The set of all undeclared names in port arguments and lhses.
          (union undeclared-names-from-args undeclared-names-from-lhses))

         (implicit-2
          ;; Declarations for all undeclared-names
          (vl-make-other-implicit-wires x.minloc undeclared-names))

         (warnings
          (if (not undeclared-names-from-lhses)
              x.warnings
            (cons (make-vl-warning
                   :type :vl-tricky-implicit
                   :msg "In module ~m0, we found ~x1 implicit wire(s) used only ~
                   in the left-hand sides of assignments.  We accept this and it ~
                   is permitted by the Verilog specification.  But Verilog-XL ~
                   does not tolerate this, so you may wish to explicitly declare ~&2."
                   :args (list x.name
                               (cardinality undeclared-names-from-lhses)
                               undeclared-names-from-lhses)
                   :fatalp nil
                   :fn 'vl-module-make-implicit-wires)
                  x.warnings)))

; Now double-check that all identifiers everywhere are declared.  This could
; probably be factored into its own well-formedness check.

         (allexprs (vl-module-allexprs-exec x nil))
         (allnames (mergesort (vl-exprlist-names-exec allexprs nil)))
         (now-declared (union declared undeclared-names))
         (problems (difference allnames now-declared))
         (warnings
          (if (not problems)
              warnings
            (cons (make-vl-warning
                   :type :vl-undefined-names
                   :msg "In module ~m0, identifiers are not declared even after ~
                         introducing implicit wires: ~&1."
                   :args (list x.name problems)
                   :fatalp t
                   :fn 'vl-module-make-implicit-wires)
                  warnings)))

         (x-prime
          (change-vl-module x
                            :warnings warnings
                            :netdecls (append implicit-1
                                              implicit-2
                                              x.netdecls))))

        x-prime))

  (local (in-theory (enable vl-module-make-implicit-wires)))

  (defthm vl-modulep-of-vl-module-make-implicit-wires
    (implies (vl-module-p x)
             (vl-module-p (vl-module-make-implicit-wires x))))

  (defthm vl-module->name-of-vl-module-make-implicit-wires
    (equal (vl-module->name (vl-module-make-implicit-wires x))
           (vl-module->name x))))



(defsection vl-modulelist-make-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-modulelist-make-implicit-wires) adds implicit wire
declarations to every module in the module list <tt>x</tt>."

  (defprojection vl-modulelist-make-implicit-wires (x)
    (vl-module-make-implicit-wires x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-make-implicit-wires)))

  (defthm vl-modulelist->names-of-vl-modulelist-make-implicit-wires
    (equal (vl-modulelist->names (vl-modulelist-make-implicit-wires x))
           (vl-modulelist->names x))))

