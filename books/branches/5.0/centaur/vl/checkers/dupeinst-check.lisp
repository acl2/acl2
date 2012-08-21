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
(include-book "duplicate-detect")
(local (include-book "../util/arithmetic"))

(defxdoc dupeinst-check
  :parents (checkers)
  :short "Check for module instances that are driving wires in identical ways."

  :long "<p>This is a trivially simple check for cases like:</p>

<code>
   mymod m1 (o1, a, b);
   mymod m2 (o2, a, b);
</code>

<p>That is, instances of the same module with the same inputs but perhaps with
different outputs.  The @(see duperhs-check) is similar but looks for
assignments whose right-hand sides are the same.</p>

<p>Sometimes this sort of thing is necessary and expected, e.g., you might have
a particular signal that needs to be distributed widely and hence is being
given to multiple inverters.</p>

<p>But in other cases this kind of redundancy can be some legacy stuff that you
want to identify and eliminate.  For instance, it's especially useful to
eliminate redundant registers, to improve power usage.</p>")

(defaggregate vl-dupeinst-key
  (modname inputs)
  :tag :vl-dupeinst-key
  :require ((vl-exprlist-p-of-vl-dupeinst-key->inputs
             (vl-exprlist-p inputs))
            (stringp-of-vl-dupeinst-key->modname
             (stringp modname)
             :rule-classes :type-prescription))
  :parents (dupeinst-check)
  :short "Keys used to determine if module instances have the same inputs."

  :long "<p>We generate a key from each modinst.  Modinsts with the same keys
are regarded as having the same inputs.  That is, the whole point of the
dupeinst check is to find modinsts with the same key.</p>

<p>The keys we use have to know the modname so we don't get confused by things
like</p>

<code>
  mymod1 m1 (o1, a, b);
  mymod2 m2 (o2, a, b);
</code>

<p>Which presumably have the same inputs but are very different things.</p>

<p>They also include the expressions for the inputs.  We expect instances to be
argresolved so that these are already in some canonical order.  We just keep
the expressions because we don't care about port names, directions, etc.  We
also expect all of these expressions to be fixed so that attributes are
ignored.</p>

<p>Our keys should arguably include the params.  But if the inputs are the
same, then the params should probably be the same or, at any rate, seem
basically compatible?  Well, whatever.  It's questionable, but probably doesn't
matter much at all in practice.</p>

<p>We always hons keys because we're going to use them as fast alist keys.</p>"

  :hons t)

(defalist vl-dupeinst-alistp (x)
  :key (vl-dupeinst-key-p x)
  :val (vl-modinstlist-p x)
  :keyp-of-nil nil
  :valp-of-nil t
  :parents (dupeinst-check)
  :long "<p>The basic idea is to bind keys to the lists of modinsts that have
that key, which lets us immediately see which modinsts have the same key.</p>
@(def vl-dupeinst-alistp)")


(defsection vl-make-dupeinst-alist
  :parents (dupeinst-check)
  :short "Builds the @(see vl-dupeinst-alistp) for a list of assignments."

  (defund vl-make-dupeinst-alist-aux (x alist)
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-dupeinst-alistp alist))))
    (b* (((when (atom x))
          alist)
         (x1 (car x))
         ((vl-modinst x1) x1)

         ((when (vl-arguments->namedp x1.portargs))
          ;; Args not resolved, skip it
          (vl-make-dupeinst-alist-aux (cdr x) alist))

         ((mv inputs ?outputs inouts unknowns)
          (vl-partition-plainargs (vl-arguments->args x1.portargs) nil nil nil nil))

         ((unless (and (atom inouts)
                       (atom unknowns)))
          ;; Too hard, skip it
          (vl-make-dupeinst-alist-aux (cdr x) alist))

         (ins    (vl-plainarglist->exprs inputs))
         ((when (member nil ins))
          ;; Blanks?  screw it, skip it.
          (vl-make-dupeinst-alist-aux (cdr x) alist))
         (ins    (vl-exprlist-fix ins))
         (key    (make-vl-dupeinst-key :modname x1.modname :inputs ins))
         (look   (hons-get key alist))
         (alist  (hons-acons key (cons x1 (cdr look)) alist)))
      (vl-make-dupeinst-alist-aux (cdr x) alist)))

  (local (in-theory (enable vl-make-dupeinst-alist-aux)))

  (defthm vl-dupeinst-alistp-of-vl-make-dupeinst-alist-aux
    (implies (and (vl-modinstlist-p x)
                  (vl-dupeinst-alistp alist))
             (vl-dupeinst-alistp (vl-make-dupeinst-alist-aux x alist))))

  (defund vl-make-dupeinst-alist (x)
    "Returns a slow alist."
    (declare (xargs :guard (vl-modinstlist-p x)))
    (b* ((alist (len x))
         (alist (vl-make-dupeinst-alist-aux x alist))
         (ans   (hons-shrink-alist alist nil)))
      (fast-alist-free alist)
      (fast-alist-free ans)
      ans))

  (local (in-theory (enable vl-make-dupeinst-alist)))

  (defthm vl-dupeinst-alistp-of-vl-make-dupeinst-alist
    (implies (force (vl-modinstlist-p x))
             (vl-dupeinst-alistp (vl-make-dupeinst-alist x)))))



(defsection vl-maybe-warn-dupeinst
  :parents (dupeinst-check)
  :short "Possibly add warnings about a group of module instances."
  :long "<p><b>Signature:</b> @(call vl-maybe-warn-dupeinst) returns
<tt>warnings'</tt>.</p>

<ul>
<li><tt>key</tt> is the shared @(see vl-dupeinst-key-p) for a group of modinsts.</li>
<li><tt>modinsts</tt> are the modinsts that share this key.</li>
<li><tt>warnings</tt> is the @(see warnings) accumulator to extend.</li>
</ul>

<p>Modinsts might not have multiple entries, in which case there is nothing to
do and we just return <tt>warnings</tt> unchanged.  Otherwise, we issue a
warning about the modules.</p>

<p>By default, all duplicated modules are considered worth warning about.  But
you can configure which modules are considered trivial/okay to duplicate by
attaching a function to <tt>vl-dupeinst-trivial-p</tt>.  These will be filtered
out into minor warnings.</p>"

  (encapsulate
    (((vl-dupeinst-trivial-p *) => *
      :formals (modname)
      :guard (stringp modname)))

    (local (defun vl-dupeinst-trivial-p (modname)
             (declare (xargs :guard (stringp modname))
                      (ignore modname))
             nil)))

  (defund vl-dupeinst-trivial-p-default (modname)
    (declare (xargs :guard (stringp modname))
             (ignore modname))
    nil)

  (defattach vl-dupeinst-trivial-p vl-dupeinst-trivial-p-default)

  (defun vl-modinstlist-fixed-up-outs (x)
    (declare (xargs :guard (vl-modinstlist-p x)))
    (b* (((when (atom x))
          nil)
         ((vl-modinst x1) (car x))
         ((when (vl-arguments->namedp x1.portargs))
          (er hard? 'vl-modinstlist-fixed-up-outs "expected resolved args"))
         ((mv ?inputs outputs ?inouts ?unknowns)
          (vl-partition-plainargs (vl-arguments->args x1.portargs) nil nil nil nil))
         (outexprs (vl-plainarglist->exprs outputs))
         ((when (member nil outexprs))
          (er hard? 'vl-modinstlist-fixed-up-outs "expected no blanks")))
      (cons (vl-exprlist-fix outexprs)
            (vl-modinstlist-fixed-up-outs (cdr x)))))

  (defund vl-maybe-warn-dupeinst (key modinsts warnings)
    "Returns WARNINGS'"
    (declare (xargs :guard (and (vl-dupeinst-key-p key)
                                (vl-modinstlist-p modinsts)
                                (vl-warninglist-p warnings)))
             (ignorable key))
    (b* (((when (or (atom modinsts)
                    (atom (cdr modinsts))))
          ;; Nothing to do -- there isn't more than one assignment for this RHS.
          warnings)

         ;; BOZO maybe filter some of this stuff?

         (fixed-up-outs (vl-modinstlist-fixed-up-outs modinsts))
         (dupes         (duplicated-members fixed-up-outs))

         (modname (vl-dupeinst-key->modname key))
         (minor-p (vl-dupeinst-trivial-p modname))

         (w (make-vl-warning
             :type (if (consp dupes)
                       (if minor-p :vl-warn-same-ports-minor :vl-warn-same-ports)
                     (if minor-p :vl-warn-same-inputs-minor :vl-warn-same-inputs))
             :msg "Found instances of the same module with ~s0:~%~%~s1"
             :args (list (if (consp dupes)
                             "the same arguments"
                           "the same inputs (but different outputs)")
                         (str::prefix-lines (with-local-ps
                                             ;; may help avoid unnecessary line wrapping
                                             (vl-ps-update-autowrap-col 200)
                                             (vl-pp-modinstlist modinsts nil nil))
                                            "     ")
                         ;; These aren't printed, but we include them in the
                         ;; warning so our suppression mechanism can be
                         ;; applied.
                         modinsts)
             :fatalp nil
             :fn 'vl-maybe-warn-dupeinst)))
      (cons w warnings)))

  (local (in-theory (enable vl-maybe-warn-dupeinst)))

  (defthm vl-warninglist-p-of-vl-maybe-warn-dupeinst
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (vl-maybe-warn-dupeinst rhs modinsts warnings)))))


(defsection vl-warnings-for-dupeinst-alist
  :parents (dupeinst-check)

  (defund vl-warnings-for-dupeinst-alist (alist warnings)
    (declare (xargs :guard (and (vl-dupeinst-alistp alist)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom alist))
          warnings)
         (rhs      (caar alist))
         (assigns  (cdar alist))
         (warnings (vl-maybe-warn-dupeinst rhs assigns warnings)))
      (vl-warnings-for-dupeinst-alist (cdr alist) warnings)))

  (local (in-theory (enable vl-warnings-for-dupeinst-alist)))

  (defthm vl-warninglist-p-of-vl-warnings-for-dupeinst-alist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (vl-warnings-for-dupeinst-alist alist warnings)))))


(defsection vl-module-dupeinst-check
  :parents (dupeinst-check)

  (defund vl-module-dupeinst-check (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         (alist    (vl-make-dupeinst-alist x.modinsts))
         (warnings (vl-warnings-for-dupeinst-alist alist x.warnings)))
      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-dupeinst-check)))

  (defthm vl-module-p-of-vl-module-dupeinst-check
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-dupeinst-check x))))

  (defthm vl-module->name-of-vl-module-dupeinst-check
    (equal (vl-module->name (vl-module-dupeinst-check x))
           (vl-module->name x))))


(defsection vl-modulelist-dupeinst-check
  :parents (dupeinst-check)

  (defprojection vl-modulelist-dupeinst-check (x)
    (vl-module-dupeinst-check x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p
    :parents (dupeinst-check))

  (defthm vl-modulelist->names-of-vl-modulelist-dupeinst-check
    (equal (vl-modulelist->names (vl-modulelist-dupeinst-check x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))

