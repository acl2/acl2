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
(include-book "../mlib/expr-tools")
(include-book "../mlib/range-tools")
(include-book "../mlib/namefactory")
(local (include-book "../util/arithmetic"))


(defxdoc gatesplit
  :parents (transforms)
  :short "Split up gates with \"extra\" terminals."

  :long "<h3>Gate Splitting</h3>

<p>This transformation is responsible for splitting up multi-input gates into
multiple one-input gates for <tt>buf</tt> and <tt>not</tt>, or two-input gates
for <tt>and</tt>, <tt>or</tt>, etc.</p>

<p><b>Ordering Notes.</b> This transformation must be done after widths have
been computed, and after @(see replicate) has been run to eliminate any arrays.
Replication is necessary for certain well-formedness checks on the widths to
succeed.</p>

<p>Unlike occforming, we lay down gates directly instead of introducing new
modules.  It might be nicer to do it the other way and introduce modules
instead, since then the module instance could keep the same name as the gate.
On the other hand, the code to just introduce gates is simpler, and it would
probably suffice to just use good names or annotations to explain where the
gates come from.</p>")


(defsection vl-make-temporary-wires

;; BOZO move to mlib?

  :parents (gatesplit)

  :short "Generate expressions and declarations for some fresh (one-bit)
wires."

  :long "<p><b>Signature:</b> @(call vl-make-temporary-wires) returns <tt>(mv
exprs netdecls nf-prime)</tt>.</p>

<ul>
<li><tt>prefix</tt> is the prefix to use for name generation,</li>
<li><tt>i</tt> is the number of wires you want to create,</li>
<li><tt>nf</tt> is a @(see vl-namefactory-p) for generating wire names, and</li>
<li><tt>loc</tt> is the location you want to use for the wire declarations.</li>
</ul>

<p>The <tt>exprs</tt> we return are expressions for each of the new one-bit,
unsigned wires, and are already annotated with their widths and signedness.</p>

<p>The <tt>netdecls</tt> are declarations for these wires, each of which is
said to occur at location <tt>loc</tt>.</p>

<p>We also return the updated name factory.</p>"

  (defund vl-make-temporary-wires (prefix i nf loc)
    (declare (xargs :guard (and (stringp prefix)
                                (natp i)
                                (vl-namefactory-p nf)
                                (vl-location-p loc))))
    (b* (((when (zp i))
          (mv nil nil nf))
         ((mv new-name nf)
          (vl-namefactory-indexed-name prefix nf))
         (expr1    (make-vl-atom :guts (make-vl-id :name new-name)
                                 :finalwidth 1
                                 :finaltype :vl-unsigned))
         (decl1    (make-vl-netdecl :name new-name
                                    :type :vl-wire
                                    :range nil
                                    :loc loc))
         ((mv exprs decls nf)
          (vl-make-temporary-wires prefix (- i 1) nf loc)))

        (mv (cons expr1 exprs)
            (cons decl1 decls)
            nf)))

  (defmvtypes vl-make-temporary-wires (true-listp true-listp))

  (local (in-theory (enable vl-make-temporary-wires)))

  (defthm vl-exprlist-p-of-vl-make-temporary-wires
    (vl-exprlist-p (mv-nth 0 (vl-make-temporary-wires prefix i nf loc))))

  (defthm vl-netdecllist-p-of-vl-make-temporary-wires
    (implies (force (vl-location-p loc))
             (vl-netdecllist-p (mv-nth 1 (vl-make-temporary-wires prefix i nf loc)))))

  (defthm vl-namefactory-p-of-vl-make-temporary-wires
    (implies (and (force (stringp prefix))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 2 (vl-make-temporary-wires prefix i nf loc)))))

  (defthm len-of-vl-make-temporary-wires
    (equal (len (mv-nth 0 (vl-make-temporary-wires prefix i nf loc)))
           (nfix i)))

  (defthm vl-make-temporary-wires-0-under-iff
    (iff (mv-nth 0 (vl-make-temporary-wires prefix i nf loc))
         (not (zp i)))))




(defsection vl-make-gates-for-buf/not
  :parents (vl-gatesplit-buf/not)
  :short "Produce a list of <tt>buf</tt> or <tt>not</tt> gates."

  :long "<p><b>Signature:</b> @(call vl-make-gates-for-buf/not) returns
<tt>(mv warnings' new-gateinsts nf')</tt></p>

<ul>
 <li><tt>in</tt> is a @(see vl-plainarg-p), and is the input terminal to a
     multi-output <tt>buf</tt> or <tt>not</tt> gate.</li>
 <li><tt>outs</tt> are a list of plainargs, and are the output terminals for
     the gate.</li>
 <li><tt>x</tt> is the actual gateinst we are splitting, from which <tt>in</tt>
     and <tt>outs</tt> are derived.  (This is used for good error messages, and
     also to identify which kind of gate we are working with, its location,
     etc.)</li>
 <li><tt>nf</tt> is a @(see vl-namefactory-p) for generating fresh names.</li>
 <li><tt>warnings</tt> is an accumulator for any warnings.</li>
</ul>

<p>We produce a list of gateinsts of the appropriate type, one to drive
each output in <tt>outs</tt> with <tt>in</tt>.</p>"

  (defund vl-make-gates-for-buf/not (in outs x nf warnings)
    (declare (xargs :guard (and (vl-plainarg-p in)
                                (vl-plainarglist-p outs)
                                (vl-gateinst-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom outs))
          (mv warnings nil nf))
         (warnings
          ;; The width-checks below only make sense if there is no range.
          ;; Hence, we double-check that there is no range.
          (if (not (vl-gateinst->range x))
              warnings
            (cons (make-vl-warning
                   :type :vl-bad-gate
                   :msg "~a0: expected all instance arrays to have been ~
                         eliminated, but found a range.  Did you forget to ~
                         run the replicate transform?"
                   :args (list x)
                   :fatalp t
                   :fn 'vl-make-gates-for-buf/not)
                  warnings)))

         (warnings
          ;; Cadence does not allow a multi-bit wire to be used as the output
          ;; of a gate.  So, I disallow it as well.
          (let ((expr (vl-plainarg->expr (car outs))))
            (if (and expr (equal (vl-expr->finalwidth expr) 1))
                warnings
              (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: output terminal has width ~x1 but we only ~
                           support 1-bit outputs.  The expression for the bad ~
                           terminal is ~a2."
                     :args (list x (and expr (vl-expr->finalwidth expr)) expr)
                     :fatalp t
                     :fn 'vl-make-gates-for-buf/not)
                    warnings))))

         ;; Now we make the actual gate for this output.  We add an attribute
         ;; saying the name of the gate instance which was being split up.
         (origname-s     (or (vl-gateinst->name x) "unnamed"))
         (origname-atom  (make-vl-atom :guts (vl-string origname-s)))
         (atts           (cons (cons "VL_GATESPLIT" origname-atom)
                               (vl-gateinst->atts x)))

         ;; We also try to base the new name on the original name of the gate,
         ;; to make it relatively predictable.
         ((mv new-name nf) (vl-namefactory-indexed-name origname-s nf))
         (inst1     (make-vl-gateinst :name new-name
                                      :type (vl-gateinst->type x)
                                      :args (cons in (list (car outs)))
                                      :loc (vl-gateinst->loc x)
                                      :atts atts))
         ((mv warnings rest nf)
          (vl-make-gates-for-buf/not in (cdr outs) x nf warnings)))
        (mv warnings (cons inst1 rest) nf)))

  (defmvtypes vl-make-gates-for-buf/not (nil true-listp nil))

  (local (in-theory (enable vl-make-gates-for-buf/not)))

  (defthm vl-warninglist-p-of-vl-make-gates-for-buf/not
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-make-gates-for-buf/not in outs x nf warnings)))))

  (defthm vl-gateinstlist-p-of-vl-make-gates-for-buf/not
    (implies (and (force (vl-plainarg-p in))
                  (force (vl-plainarglist-p outs))
                  (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p
              (mv-nth 1 (vl-make-gates-for-buf/not in outs x nf warnings)))))

  (defthm vl-namefactory-p-of-vl-make-gates-for-buf/not
    (implies (and (force (vl-plainarg-p in))
                  (force (vl-plainarglist-p outs))
                  (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p
              (mv-nth 2 (vl-make-gates-for-buf/not in outs x nf warnings))))))




(defsection vl-gatesplit-buf/not
  :parents (gatesplit)
  :short "Split up a multi-output <tt>buf</tt> or <tt>not</tt> gate, if
necessary."

  :long "<p>From Section 7.3, <tt>buf</tt> and <tt>not</tt> gates have one
input (the last terminal) and one or more outputs (all other terminals).  We
split up multi-output versions of these gates into many single-output versions,
e.g.,</p>

<code>
not(o1, o2, ..., on, i);
  --&gt;
not(o1, i);
not(o2, i);
  ...
not(on, i);
</code>

<p>We verified this with Cadence, in <tt>xf-gatesplit.v</tt>.</p>

<p><b>Signature:</b> @(call vl-gatesplit-buf/not) returns <tt>(mv warnings'
new-gateinsts nf')</tt>.</p>

<ul>
 <li><tt>x</tt> is an instance of a <tt>buf</tt> or <tt>not</tt> gate.</li>
 <li><tt>nf</tt> is a @(see vl-namefactory-p) for generating fresh names.</li>
</ul>

<p>The <tt>new-gateinsts</tt> we return should be used to replace <tt>x</tt>
in the module.</p>"

  (defund vl-gatesplit-buf/not (x nf warnings)
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (member-eq (vl-gateinst->type x) '(:vl-not :vl-buf))
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))

    (b* ((args  (redundant-list-fix (vl-gateinst->args x)))
         (nargs (length args))

         ((when (< nargs 2))
          ;; Basic sanity check.  Buf/not gate needs at least two terminals.
          (mv (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: gate illegally has ~x1 argument(s)."
                     :args (list x nargs)
                     :fatalp t
                     :fn 'vl-gatesplit-buf/not)
                    warnings)
              (list x)
              nf))

         (input   (car (last args)))
         (outputs (butlast args 1))
         (in-expr (vl-plainarg->expr input))

         ((when (not (and in-expr
                          (equal (vl-expr->finalwidth in-expr) 1))))
          ;; Cadence implicitly bitwise-or's the bits of a gate input when it
          ;; is more than a single bit.  We have decided not to handle this, so
          ;; we check to ensure that the input is only one-bit here.
          (mv (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: input terminal has width ~x1, but we only ~
                           support 1-bit inputs.  Hrmn.  Cadence supports ~
                           multi-bit inputs by adding an implicit, reduction ~
                           bitwise-or operation around them.  Do we want to ~
                           implement this?"
                     :args (list x (and in-expr (vl-expr->finalwidth in-expr)))
                     :fatalp t
                     :fn 'vl-gatesplit-buf/not)
                    warnings)
              (list x)
              nf))

         ((when (= nargs 2))
          ;; Already has only two args.  No need to split it.
          (mv warnings (list x) nf)))

        ;; Else, more than 2 args.  Split it up.
        (vl-make-gates-for-buf/not input outputs x nf warnings)))

  (defmvtypes vl-gatesplit-buf/not (nil true-listp nil))

  (local (in-theory (enable vl-gatesplit-buf/not)))

  (defthm vl-warninglist-p-of-vl-gatesplit-buf/not
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gatesplit-buf/not x nf warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gatesplit-buf/not
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-not :vl-buf)))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p (mv-nth 1 (vl-gatesplit-buf/not x nf warnings)))))

  (defthm vl-namefactory-p-of-vl-gatesplit-buf/not
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-not :vl-buf)))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 2 (vl-gatesplit-buf/not x nf warnings))))))



(defsection vl-make-gates-for-and/etc
  :parents (vl-gatesplit-and/etc)
  :short "Produce a list of two-input <tt>and</tt>, <tt>or</tt>,
<tt>xor</tt>, or <tt>xnor</tt> gates to replace a multi-input gate."

  :long "<p><b>Signature:</b> @(call vl-make-gates-for-and/etc) returns
<tt>(mv warnings' new-gateinsts nf')</tt></p>

<p>This function generates the replacement gates for a multi-input <tt>and</tt>,
<tt>or</tt>, <tt>xor</tt>, or <tt>xnor</tt> gate.  The main inputs are
@(see vl-plainarglist-p)s which have equal lengths:</p>

<code>
 OUTS:  (temp1  temp2  ...     tempN-2  Out)
 LHSES: (i1     temp1  temp2   ...      tempN-2)
 RHSES: (i2     i3     ....    iN-1     iN)
</code>

<p>The other inputs are as follows.</p>

<ul>
<li><tt>TYPE</tt>, the type of the gates being introduced (i.e., AND, OR, XOR, XNOR),</li>
<li><tt>NAME</tt>, the original name of this gate (or \"&lt;unnamed gate&gt;\"),</li>
<li><tt>LOC</tt>, the location for the original gate,</li>
<li><tt>ATTS</tt>, the attributes for the original gate, which have already been
updated with a <tt>VL_GATESPLIT</tt> annotation,</li>
<li><tt>NF</tt>, the @(see vl-namefactory-p) for generating names,</li>
<li><tt>WARNINGS</tt>, an accumulator for warnings.</li>
</ul>

<p>We march down the three main input-lists, zipping them together into new
gate instances.  The new gateinsts we return are intended to replace the
original gate.</p>"

  (defund vl-make-gates-for-and/etc (outs lhses rhses type name loc atts nf warnings)
    (declare (xargs :guard (and (vl-plainarglist-p outs)
                                (vl-plainarglist-p lhses)
                                (vl-plainarglist-p rhses)
                                (same-lengthp outs lhses)
                                (same-lengthp outs rhses)
                                (member-eq type '(:vl-and :vl-or :vl-xor :vl-xnor))
                                (stringp name)
                                (vl-location-p loc)
                                (vl-atts-p atts)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))

    (b* (((when (atom outs))
          (mv warnings nil nf))

         ;; Sanity checks: is everything a single bit wide?
         (warnings
          (let ((expr (vl-plainarg->expr (car outs))))
            (if (and expr (equal (vl-expr->finalwidth expr) 1))
                warnings
              (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: output terminal expression has width ~x1, but ~
                           should have width 1.  The expression is ~a2."
                     :args (list loc
                                 (and expr (vl-expr->finalwidth expr))
                                 expr)
                     :fatalp t
                     :fn 'vl-make-gates-for-and/etc)
                    warnings))))

         (warnings
          (let ((expr (vl-plainarg->expr (car lhses))))
            (if (and expr (equal (vl-expr->finalwidth expr) 1))
                warnings
              (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: input terminal exprsesion has width ~x1, but ~
                           should have width 1.  The expression is ~a2."
                     :args (list loc
                                 (and expr (vl-expr->finalwidth expr))
                                 expr)
                     :fatalp t
                     :fn 'vl-make-gates-for-and/etc)
                    warnings))))

         (warnings
          (let ((expr (vl-plainarg->expr (car rhses))))
            (if (and expr (equal (vl-expr->finalwidth expr) 1))
                warnings
              (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: input terminal expression has width ~x1 but ~
                           should have width 1.  The expression is ~a2."
                     :args (list loc
                                 (and expr (vl-expr->finalwidth expr))
                                 expr)
                     :fatalp t
                     :fn 'vl-make-gates-for-and/etc)
                    warnings))))

         ((mv new-name nf) (vl-namefactory-indexed-name name nf))
         (gate1 (make-vl-gateinst :name new-name
                                  :type type
                                  :args (list (car outs)
                                              (car lhses)
                                              (car rhses))
                                  :range nil
                                  :atts atts
                                  :loc loc))
         ((mv warnings rest nf)
          (vl-make-gates-for-and/etc (cdr outs) (cdr lhses) (cdr rhses)
                                     type name loc atts nf warnings)))

        (mv warnings (cons gate1 rest) nf)))

  (defmvtypes vl-make-gates-for-and/etc (nil true-listp nil))

  (local (in-theory (enable vl-make-gates-for-and/etc)))

  (defthm vl-warninglist-p-of-vl-make-gates-for-and/etc
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-make-gates-for-and/etc outs lhses rhses type name
                                                   loc atts nf warnings)))))

  (defthm vl-gateinstlist-p-of-vl-make-gates-for-and/etc
    (implies (and (force (vl-plainarglist-p outs))
                  (force (vl-plainarglist-p lhses))
                  (force (vl-plainarglist-p rhses))
                  (force (same-lengthp outs lhses))
                  (force (same-lengthp outs rhses))
                  (force (member-eq type '(:vl-and :vl-or :vl-xor :vl-xnor)))
                  (force (stringp name))
                  (force (vl-location-p loc))
                  (force (vl-atts-p atts))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p
              (mv-nth 1 (vl-make-gates-for-and/etc outs lhses rhses type name
                                                   loc atts nf warnings)))))

  (defthm vl-namefactory-p-of-vl-make-gates-for-and/etc
    (implies (and (force (vl-plainarglist-p outs))
                  (force (vl-plainarglist-p lhses))
                  (force (vl-plainarglist-p rhses))
                  (force (same-lengthp outs lhses))
                  (force (same-lengthp outs rhses))
                  (force (member-eq type '(:vl-and :vl-or :vl-xor :vl-xnor)))
                  (force (stringp name))
                  (force (vl-location-p loc))
                  (force (vl-atts-p atts))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p
              (mv-nth 2 (vl-make-gates-for-and/etc outs lhses rhses type name
                                                   loc atts nf warnings))))))



(defsection vl-gatesplit-and/etc
  :parents (gatesplit)
  :short "Split up a multi-input <tt>and</tt>, <tt>or</tt>, <tt>xor</tt>, or
<tt>xnor</tt> gate, if necessary."

  :long "<p>From Section 7.2, <tt>and</tt>, <tt>or</tt>, <tt>xor</tt>, and
<tt>xnor</tt> gates have one output and many inputs.  The behavior for more
than 2 inputs is described as the \"natural extension\".  We have used Cadence
to verify (<tt>xf-gatesplit.v</tt>) that, at least for <tt>n = 4</tt>, they
behave as follows:</p>

<code>
gate(out, i1, i2, ..., iN);
  --&gt;
gate(temp1, i1,      i2);
gate(temp2, temp1,   i3);
 ...
gate(out,   tempN-2, iN);
</code>

<p><b>Signature:</b> @(call vl-gatesplit-and/etc) returns <tt>(mv warnings'
new-decls new-insts nf')</tt>.</p>

<p>We decide if <tt>x</tt>, which should be an <tt>and</tt>, <tt>or</tt>,
<tt>xor</tt>, or <tt>xnor</tt> gate, needs to be split up.  If so, we go ahead
and carry out the split.  <tt>nf</tt> is a @(see vl-namefactory-p) for
generating fresh wire names and <tt>warnings</tt> is an accumulator for
warnings.</p>

<p>The <tt>new-decls</tt> we produce are a list of new net declarations that
should be added to the module.  These declarations are for the temporary wires
as suggested above.  The <tt>new-insts</tt> are new gate instances which should
replace <tt>x</tt>.</p>"

  (local (in-theory (enable len)))

  (defund vl-gatesplit-and/etc (x nf warnings)
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (member-eq (vl-gateinst->type x)
                                           '(:vl-and :vl-or :vl-xor :vl-xnor))
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))
                    :guard-debug t))

    (b* ((type     (vl-gateinst->type x))
         (args     (redundant-list-fix (vl-gateinst->args x)))
         (nargs    (length args))
         (range    (vl-gateinst->range x))
         (loc      (vl-gateinst->loc x))
         (origname (or (vl-gateinst->name x) "unnamed"))

         ((when range)
          ;; Sanity check.  For our wire-width checks to make sense, we need to
          ;; have already gotten rid of any instance arrays.
          (mv (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: expected no instance arrays; did you forget to ~
                           run the replicate transform?"
                     :args (list x)
                     :fatalp t
                     :fn 'vl-gatesplit-and/etc)
                    warnings)
              nil
              (list x)
              nf))

         ((when (< nargs 3))
          ;; Sanity check.  Gate needs at least 3 args.
          (mv (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: expected at least 3 arguments, but found ~x1."
                     :args (list x nargs)
                     :fatalp t
                     :fn 'vl-gatesplit-and/etc)
                    warnings)
              nil
              (list x)
              nf))

         ((when (= nargs 3))
          ;; If the gate has exactly 3 arguments, we don't need to split it.
          (mv warnings nil (list x) nf))

         ;; Otherwise, we have more than 3 args.  Okay, split it up.
         ;; Note that the args are out, in1...inN, so we need N-2 temps,
         ;; and N-2 is the same as nargs-3.
         ((mv temp-exprs temp-decls nf)
          (vl-make-temporary-wires origname (- nargs 3) nf loc))

         (atts     (cons (cons "VL_GATESPLIT" (make-vl-atom :guts (vl-string origname)))
                         (vl-gateinst->atts x)))

         (temp-args-out (vl-exprlist-to-plainarglist temp-exprs :dir :vl-output))
         (temp-args-in  (vl-exprlist-to-plainarglist temp-exprs :dir :vl-input))

         (o    (car args))
         (i1   (cadr args))
         (i2-n (cddr args))

         ;; OUTS are (temp1, temp2, ..., tempN-2, O)
         (outs  (append temp-args-out (list o)))
         ;; LHSES are (i1,    temp1, temp2,  ...,  tempN-2)
         (lhses (cons i1 temp-args-in))
         ;; RHSES are (i2, ..., iN)
         (rhses i2-n)

         ((mv warnings gateinsts nf)
          (vl-make-gates-for-and/etc outs lhses rhses type origname
                                     loc atts nf warnings)))
      (mv warnings temp-decls gateinsts nf)))

  (defmvtypes vl-gatesplit-and/etc (nil true-listp true-listp nil))

  (local (in-theory (enable vl-gatesplit-and/etc)))

  (defthm vl-warninglist-p-of-vl-gatesplit-and/etc
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gatesplit-and/etc x nf warnings)))))

  (defthm vl-netdecllist-p-of-vl-gatesplit-and/etc
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-and :vl-or :vl-xor :vl-xnor)))
                  (force (vl-namefactory-p nf)))
             (vl-netdecllist-p (mv-nth 1 (vl-gatesplit-and/etc x nf warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gatesplit-and/etc
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-and :vl-or :vl-xor :vl-xnor)))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p (mv-nth 2 (vl-gatesplit-and/etc x nf warnings))))
    :hints(("Goal" :in-theory (enable vl-gatesplit-and/etc))))

  (defthm vl-namefactory-p-of-vl-gatesplit-and/etc
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-and :vl-or :vl-xor :vl-xnor)))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 3 (vl-gatesplit-and/etc x nf warnings))))))




(defsection vl-gatesplit-nand/nor
  :parents (gatesplit)
  :short "Split up a multi-input <tt>nand</tt> or <tt>nor</tt> gate, if
necessary."
  :long "<p>From Section 7.2, <tt>nand</tt> and <tt>nor</tt> gates have one
output and many inputs.  The behavior for more than 2 inputs is described as
the \"natural extension\".  We have used Cadence (see <tt>xf-gatesplit.v</tt>)
to verify that they behave as follows for <tt>n = 4</tt>.</p>

<code>
nand(o, i1, i2, ..., iN)
 --&gt;
and(temp, i1, i2, ..., iN)
not(o, temp);
</code>

<code>
nor(o, i1, i2, ..., iN)
 --&gt;
or(temp, i1, i2, ..., iN)
not(o, temp);
</code>

<p><b>Signature:</b> @(call vl-gatesplit-nand/nor) returns <tt>(mv warnings'
new-decls new-insts nf')</tt>.</p>

<p>This function decides if a nand/nor needs to be split up, and if so goes
ahead and performs the split.  We are given:</p>

<ul>
<li><tt>x</tt>, an instance of an <tt>nand</tt> or <tt>nor</tt> gate,</li>
<li><tt>nf</tt>, a @(see vl-namefactory-p) for generating new wires,</li>
<li><tt>warnings</tt>, an accumulator for warnings.</li>
</ul>

<p>The <tt>new-decls</tt> we produce are a list of net declarations that
need to be added to the module, and <tt>new-insts</tt> are gate instances
that are to replace <tt>x</tt>.  We also return the updated warnings and
name factory.</p>

<p>This is basically similar to @(see vl-gatesplit-and/etc), except that
we need to add a \"not\" gate at the end.</p>"

  (local (in-theory (enable len)))

  (defund vl-gatesplit-nand/nor (x nf warnings)
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (member-eq (vl-gateinst->type x) '(:vl-nand :vl-nor))
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))

    (b* ((args     (redundant-list-fix (vl-gateinst->args x)))
         (nargs    (length args))
         (range    (vl-gateinst->range x))
         (loc      (vl-gateinst->loc x))
         (origname (or (vl-gateinst->name x) "unnamed"))

         ((when range)
          ;; Sanity check.  For our wire-width checks to make sense, we need to
          ;; have already gotten rid of instance arrays.
          (mv (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: expected all instance arrays to have been ~
                           eliminated; did you forget to run the argresolve ~
                           transform?"
                     :args (list x)
                     :fatalp t
                     :fn 'vl-gatesplit-nand/nor)
                    warnings)
              nil
              (list x)
              nf))

         ((when (< nargs 3))
          ;; Sanity check: gate is malformed unless it has at least 3 args.
          (mv (cons (make-vl-warning
                     :type :vl-bad-gate
                     :msg "~a0: expected at least 3 arguments, but found ~x1."
                     :args (list x nargs)
                     :fatalp t
                     :fn 'vl-gatesplit-nand/nor)
                    warnings)
              nil
              (list x)
              nf))

         ((when (= nargs 3))
          ;; Already has 3 arguments, no need to split.
          (mv warnings nil (list x) nf))

         ;; Otherwise, more than 3 args.  Split it up.  We're going to call the
         ;; same function as used in and/or to create the main signal, then
         ;; negate it.  We create one extra temporary wire, to hold the result of
         ;; this and/or computation.
         (atts (cons (cons "VL_GATESPLIT" (make-vl-atom :guts (vl-string origname)))
                     (vl-gateinst->atts x)))

         ((mv temp-exprs temp-decls nf)
          (vl-make-temporary-wires origname (- nargs 2) nf loc))

         (all-args-out (vl-exprlist-to-plainarglist temp-exprs :dir :vl-output))
         (all-args-in (vl-exprlist-to-plainarglist temp-exprs :dir :vl-input))

         ;; We call the last temporary "main", and the others are as before.
         (temp-args-out (butlast all-args-out 1))
         (temp-args-in  (butlast all-args-in 1))
         (main-arg-out  (car (last all-args-out)))
         (main-arg-in   (car (last all-args-in)))

         ;; The output and inputs for the nand/nor gate.
         (o    (car args))
         (i1   (cadr args))
         (i2-n (cddr args))

         ;; This is close to before.  But instead of outputting directly to o,
         ;; the inner and/or portion outputs to main.
         (outs  (append temp-args-out (list main-arg-out)))
         (lhses (cons i1 temp-args-in))
         (rhses i2-n)

         ;; Now, we generate the main mess of gates.
         ((mv warnings gateinsts nf)
          (vl-make-gates-for-and/etc outs lhses rhses
                                     (case (vl-gateinst->type x)
                                       (:vl-nand :vl-and)
                                       (:vl-nor  :vl-or))
                                     origname loc atts nf warnings))

         ;; Finally, we just need to hook up the "main" wire to
         ;; our output, o.
         ((mv final-name nf) (vl-namefactory-indexed-name origname nf))
         (final-gate (make-vl-gateinst :type :vl-not
                                       :name final-name
                                       :range nil
                                       :atts atts
                                       :args (list o main-arg-in)
                                       :loc loc)))
      (mv warnings
          temp-decls
          (append gateinsts (list final-gate))
          nf)))

  (defmvtypes vl-gatesplit-nand/nor (nil true-listp true-listp nil))

  (local (in-theory (enable vl-gatesplit-nand/nor)))

  (defthm vl-warninglist-p-of-vl-gatesplit-nand/nor
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gatesplit-nand/nor x nf warnings)))))

  (defthm vl-netdecllist-p-of-vl-gatesplit-nand/nor
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-nand :vl-nor)))
                  (force (vl-namefactory-p nf)))
             (vl-netdecllist-p (mv-nth 1 (vl-gatesplit-nand/nor x nf warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gatesplit-nand/nor
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-nand :vl-nor)))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p (mv-nth 2 (vl-gatesplit-nand/nor x nf warnings)))))

  (defthm vl-namefactory-p-of-vl-gatesplit-nand/nor
    (implies (and (force (vl-gateinst-p x))
                  (force (member-eq (vl-gateinst->type x) '(:vl-nand :vl-nor)))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 3 (vl-gatesplit-nand/nor x nf warnings))))))



(defsection vl-gateinst-gatesplit
  :parents (gatesplit)
  :short "Main routine for splitting high-arity gate instances."
  :long "<p><b>Signature:</b> @(call vl-gateinst-gatesplit) returns <tt>(mv
warnings' new-decls new-gateinsts nf')</tt>.</p>

<p>The inputs:</p>
<ul>
<li><tt>x</tt> is a gateinst that occurs somewhere within mod,</li>
<li><tt>nf</tt> is a @(see vl-namefactory-p) for generating fresh names,</li>
<li><tt>warnings</tt> is an accumulator for warnings</li>
</ul>

<p>The outputs:</p>
<ul>
<li><tt>new-decls</tt> are a list of wire declarations that need to be
added to the module, for any temporary wires we need to use.</li>
<li><tt>new-gateinsts</tt> are a list of gate instances that should
replace <tt>x</tt> in the module.</li>
<li><tt>warnings'</tt> and <tt>nf'</tt> are the updated warnings and
name factory.</li>
</ul>"

  (defund vl-gateinst-gatesplit (x nf warnings)
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))

    (case (vl-gateinst->type x)
      ((:VL-NOT :VL-BUF)
       (b* (((mv warnings new-gateinsts nf)
             (vl-gatesplit-buf/not x nf warnings)))
           (mv warnings nil new-gateinsts nf)))

      ((:VL-AND :VL-OR :VL-XOR :VL-XNOR)
       (vl-gatesplit-and/etc x nf warnings))

      ((:VL-NAND :VL-NOR)
       (vl-gatesplit-nand/nor x nf warnings))

      (otherwise
       (mv (cons (make-vl-warning
                  :type :vl-bad-gate
                  :msg "~a0: unsupported gate type ~x1."
                  :args (list x (vl-gateinst->type x))
                  :fn 'vl-gateinst-gatesplit)
                 warnings)
           nil
           (list x)
           nf))))

  (defmvtypes vl-gateinst-gatesplit (nil true-listp true-listp nil))

  (local (in-theory (enable vl-gateinst-gatesplit)))

  (defthm vl-warninglist-p-of-vl-gateinst-gatesplit
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinst-gatesplit x nf warnings)))))

  (defthm vl-netdecllist-p-of-vl-gateinst-gatesplit
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-netdecllist-p (mv-nth 1 (vl-gateinst-gatesplit x nf warnings)))))

  (defthm vl-gateinstist-p-of-vl-gateinst-gatesplit
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p (mv-nth 2 (vl-gateinst-gatesplit x nf warnings)))))

  (defthm vl-namefactory-p-of-vl-gateinst-gatesplit
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 3 (vl-gateinst-gatesplit x nf warnings))))))




(defsection vl-gateinstlist-gatesplit

  (defund vl-gateinstlist-gatesplit (x nf warnings)
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nf))
         ((mv warnings decls1 gates1 nf)
          (vl-gateinst-gatesplit (car x) nf warnings))
         ((mv warnings declsN gatesN nf)
          (vl-gateinstlist-gatesplit (cdr x) nf warnings)))
        (mv warnings
            (append decls1 declsN)
            (append gates1 gatesN)
            nf)))

  (defmvtypes vl-gateinstlist-gatesplit (nil true-listp true-listp nil))

  (local (in-theory (enable vl-gateinstlist-gatesplit)))

  (defthm vl-warninglist-p-of-vl-gateinstlist-gatesplit
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinstlist-gatesplit x nf warnings)))))

  (defthm vl-netdecllist-p-of-vl-gateinstlist-gatesplit
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-netdecllist-p (mv-nth 1 (vl-gateinstlist-gatesplit x nf warnings)))))

  (defthm vl-gateinstist-p-of-vl-gateinstlist-gatesplit
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p (mv-nth 2 (vl-gateinstlist-gatesplit x nf warnings)))))

  (defthm vl-namefactory-p-of-vl-gateinstlist-gatesplit
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 3 (vl-gateinstlist-gatesplit x nf warnings))))))



(defsection vl-module-gatesplit

  (defund vl-module-gatesplit (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         (gateinsts (vl-module->gateinsts x))
         (warnings  (vl-module->warnings x))
         (netdecls  (vl-module->netdecls x))
         (nf        (vl-starting-namefactory x))
         ((mv warnings new-decls gates nf)
          (vl-gateinstlist-gatesplit gateinsts nf warnings))
         (-         (vl-free-namefactory nf)))
        (change-vl-module x
                          :netdecls (append new-decls netdecls)
                          :gateinsts gates
                          :warnings warnings)))

  (local (in-theory (enable vl-module-gatesplit)))

  (defthm vl-module-p-of-vl-module-gatesplit
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-gatesplit x))))

  (defthm vl-module->name-of-vl-module-gatesplit
    (equal (vl-module->name (vl-module-gatesplit x))
           (vl-module->name x))))



(defsection vl-modulelist-gatesplit

  (defprojection vl-modulelist-gatesplit (x)
    (vl-module-gatesplit x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-gatesplit)))

  (defthm vl-modulelist->names-of-vl-modulelist-gatesplit
    (equal (vl-modulelist->names (vl-modulelist-gatesplit x))
           (vl-modulelist->names x))))

