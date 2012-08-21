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
(include-book "../mlib/ctxexprs")
(include-book "../mlib/range-tools")
(local (include-book "../util/arithmetic"))


(defxdoc selfassigns
  :parents (checkers)
  :short "Simple check for self-assignments."

  :long "<p>This is just a heuristic check that adds warnings if it sees
assignments where some bit is on both the left- and right-hand sides.  For
instance, it would warn about something like this:</p>

<code>
 assign foo = a ? b : foo;
</code>

<p>Such assignments might be combinational loops.  Of course, most
combinational loops are not so simple, and this is just an extremely stupid
check that will only catch the most obvious problems.</p>

<p>I started by just seeing how bad it would be if I just gathered names on
both side of the expression using vl-expr-names to gather up the names.  But
that produced too much noise about assignments like <code>foo[1] =
foo[0]</code>.</p>

<p>So I now essentially collect up the bits of expressions, fudging for
bit/part selects that aren't resolved.  If this is done only after ranges are
resolved, it is still pretty good.  But it needs to be done before expressions
are split, etc.</p>

<p>This found only two things at Centaur, one of which was an assignment of an
otherwise-unused wire to itself, and one which was not actually a problem because
essentially it had the form:</p>

<code>
assign {foo, bar} = {baz, foo};
</code>")


(defsection vl-expr-approx-bits
  :parents (selfassigns)
  :short "Collect strings representing (approximately) the individual bits of
wires involved in an expression."

  :long "<p><b>Signature:</b> @(call vl-expr-approx-bits) returns a string
list.</p>

<ul>
 <li><tt>x</tt> is the @(see vl-expr-p) to gather bits from</li>
 <li><tt>mod</tt> is the module that <tt>x</tt> occurs in (for wire lookups)</li>
 <li><tt>ialist</tt> is the @(see vl-moditem-alist) for <tt>mod</tt> (for fast lookups)</li>
</ul>

<p>We try to return a list of strings like <tt>\"foo[3]\"</tt> that are
approximately the bits indicated by the expression.  This routine is at the
core of our @(see selfassigns) check, which is just an informal heuristic and
doesn't need to be particularly correct or accurate.</p>

<p>This is mostly similar to the @(see vl-wirealist-p) facilities, but we trade
some accuracy to be especially forgiving.  We don't really try to avoid name
clashes that could be caused by using escaped identifiers.  We also correct for
other errors in some questionable ways:</p>

<ul>

<li>If we encounter an unresolved bit- or part-select from <tt>w</tt>, or if we
 encounter a plain <tt>w</tt> that is not defined, we just return
 <tt>\"w[0]\"</tt>.</li>

<li>We don't do any index checking, so if we see an out-of-bounds bit- or
 part-select we just return strings that refer to non-existent bits.</li>

<li>If we encounter a plain, undefined wire <tt>w</tt>, we just return
 <tt>\"w[0]\"</tt>.</li>

</ul>

<p>It is somewhat <i>wrong</i> to fudge like this, but these cases won't be hit
in well-formed modules, and they allow us to handle expressions even in
malformed modules in a mostly correct way without having to consider how to
handle problems with collecting bits.</p>"

  (defund vl-selfassign-bit (name index)
    (declare (xargs :guard (and (stringp name)
                                (natp index))))
    (cat name "[" (natstr index) "]"))

  (defund vl-selfassign-bits (name low high)
    (declare (xargs :guard (and (stringp name)
                                (natp low)
                                (natp high)
                                (<= low high))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (if (mbe :logic (zp (- (nfix high) (nfix low)))
             :exec (= high low))
        (list (vl-selfassign-bit name low))
      (cons (vl-selfassign-bit name low)
            (vl-selfassign-bits name (+ (lnfix low) 1) high))))

  (mutual-recursion

   (defund vl-expr-approx-bits (x mod ialist)
     ;; Approximate all bits used in the expression X.  We may return X[0] if
     ;; we can't determine the range of X.
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (two-nats-measure (acl2-count x) 1)
                     :hints(("Goal" :in-theory (disable (force))))))
     (b* (((when (vl-fast-atom-p x))
           (if (vl-idexpr-p x)
               (b* ((name (vl-idexpr->name x))
                    ;; If there's some problem looking up the range, we'll just
                    ;; return name[0].
                    ((mv ?foundp range) (vl-find-net/reg-range name mod ialist))
                    (range-okp (and range (vl-range-resolved-p range)))
                    (left  (if range-okp
                               (vl-resolved->val (vl-range->msb range))
                             0))
                    (right (if range-okp
                               (vl-resolved->val (vl-range->lsb range))
                             0))
                    (high (max left right))
                    (low  (min left right)))
                 (vl-selfassign-bits name low high))
             nil))

          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((when (and (eq op :vl-bitselect)))
           (b* (((unless (vl-idexpr-p (first args)))
                 nil)
                (name (vl-idexpr->name (first args)))
                (idx  (second args))
                (idx-val (if (vl-expr-resolved-p idx)
                             (vl-resolved->val idx)
                           0)))
             (list (vl-selfassign-bit name idx-val))))

          ((when (eq op :vl-partselect-colon))
           (b* (((unless (vl-idexpr-p (first args)))
                 nil)
                (name  (vl-idexpr->name (first args)))
                (left  (second args))
                (right (third args))
                (left-val (if (vl-expr-resolved-p left)
                              (vl-resolved->val left)
                            0))
                (right-val (if (vl-expr-resolved-p right)
                               (vl-resolved->val right)
                             0))
                (high (max left-val right-val))
                (low  (min left-val right-val)))
             (vl-selfassign-bits name low high))))

       (vl-exprlist-approx-bits args mod ialist)))

   (defund vl-exprlist-approx-bits (x mod ialist)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (append (vl-expr-approx-bits (car x) mod ialist)
               (vl-exprlist-approx-bits (cdr x) mod ialist))))))


(defsection vl-assign-check-selfassigns
  :parents (selfassigns)
  :short "@(call vl-assign-check-selfassigns) checks an assignment for
bits that occur on the lhs and rhs."

  (defund vl-assign-check-selfassigns (x mod ialist)
    (declare (xargs :guard (and (vl-assign-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))))
    (b* (((vl-assign x) x)
         (lhs-bits (mergesort (vl-expr-approx-bits x.lvalue mod ialist)))
         (rhs-bits (mergesort (vl-expr-approx-bits x.expr mod ialist)))
         (oops     (intersect lhs-bits rhs-bits)))
      (if oops
          (list (make-vl-warning
                 :type :vl-warn-selfassign
                 :msg "~a0: lhs bits occur on rhs: ~&1."
                 :args (list x oops)
                 :fatalp nil
                 :fn 'vl-assign-check-selfassigns))
        nil)))

  (defthm vl-warninglist-p-of-vl-assign-check-selfassigns
    (vl-warninglist-p (vl-assign-check-selfassigns x mod ialist))
    :hints(("Goal" :in-theory (enable vl-assign-check-selfassigns)))))


(defmapappend vl-assignlist-check-selfassigns (x mod ialist)
  (vl-assign-check-selfassigns x mod ialist)
  :guard (and (vl-assignlist-p x)
              (vl-module-p mod)
              (equal ialist (vl-moditem-alist mod)))
  :transform-true-list-p t
  :parents (selfassigns))

(defthm vl-warninglist-p-of-vl-assignlist-check-selfassigns
  (vl-warninglist-p (vl-assignlist-check-selfassigns x mod ialist))
  :hints(("Goal" :in-theory (enable vl-assignlist-check-selfassigns))))



(defsection vl-module-check-selfassigns
  :parents (selfassigns)
  :short "Check the assignments of a module for self-assignments to bits."
  :long "<p>@(call vl-module-check-selfassigns) checks all of the
assignments in the module <tt>x</tt> for @(see selfassigns), and adds any
warnings to the module.</p>"

  (defund vl-module-check-selfassigns (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* ((assigns (vl-module->assigns x))
         ((unless assigns)
          x)
         (ialist (vl-moditem-alist x))
         (warnings (vl-assignlist-check-selfassigns assigns x ialist))
         (- (fast-alist-free ialist))
         ((unless warnings)
          x))
      (change-vl-module x :warnings (append warnings (vl-module->warnings x)))))

  (local (in-theory (enable vl-module-check-selfassigns)))

  (defthm vl-module-p-of-vl-module-check-selfassigns
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-check-selfassigns x))))

  (defthm vl-module->name-of-vl-module-check-selfassigns
    (equal (vl-module->name (vl-module-check-selfassigns x))
           (vl-module->name x))))


(defprojection vl-modulelist-check-selfassigns (x)
  (vl-module-check-selfassigns x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (selfassigns))

(defthm vl-modulelist->names-of-vl-modulelist-check-selfassigns
  (equal (vl-modulelist->names (vl-modulelist-check-selfassigns x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))

