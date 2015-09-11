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
(include-book "../mlib/ctxexprs")
(include-book "../mlib/range-tools-legacy")
(local (include-book "../util/arithmetic"))

(defxdoc selfassigns
  :parents (lint)
  :short "Simple check for self-assignments."

  :long "<p>This is just a heuristic check that adds warnings if it sees
assignments where some bit is on both the left- and right-hand sides.  For
instance, it would warn about something like this:</p>

@({
 assign foo = a ? b : foo;
})

<p>Such assignments might be combinational loops.  Of course, most
combinational loops are not so simple, and this is just an extremely stupid
check that will only catch the most obvious problems.</p>

<p>I started by just seeing how bad it would be if I just gathered names on
both side of the expression using vl-expr-names to gather up the names.  But
that produced too much noise about assignments like @({foo[1] =
foo[0]}).</p>

<p>So I now essentially collect up the bits of expressions, fudging for
bit/part selects that aren't resolved.  If this is done only after ranges are
resolved, it is still pretty good.  But it needs to be done before expressions
are split, etc.</p>

<p>This found only two things at Centaur, one of which was an assignment of an
otherwise-unused wire to itself, and one which was not actually a problem because
essentially it had the form:</p>

@({
assign {foo, bar} = {baz, foo};
})")

(local (xdoc::set-default-parents selfassigns))

(define vl-selfassign-bit ((name stringp)
                           (index natp))
  :returns (bit stringp :rule-classes :type-prescription)
  (cat name "[" (natstr index) "]"))

(define vl-selfassign-bits ((name stringp)
                            (low  natp)
                            (high natp))
  :guard (<= low high)
  :measure (nfix (- (nfix high) (nfix low)))
  :returns (bits string-listp)
  (if (mbe :logic (zp (- (nfix high) (nfix low)))
           :exec (eql high low))
      (list (vl-selfassign-bit name low))
    (cons (vl-selfassign-bit name low)
          (vl-selfassign-bits name (+ (lnfix low) 1) high))))

(defines vl-expr-approx-bits
  :short "Collect strings representing (approximately) the individual bits of
wires involved in an expression."

  :long "<p>We try to return a list of strings like @('\"foo[3]\"') that are
approximately the bits indicated by the expression.  This routine is at the
core of our @(see selfassigns) check, which is just an informal heuristic and
doesn't need to be particularly correct or accurate.</p>

<p>This is mostly similar to the @(see vl-wirealist-p) facilities, but we trade
some accuracy to be especially forgiving.  We don't really try to avoid name
clashes that could be caused by using escaped identifiers.  We also correct for
other errors in some questionable ways:</p>

<ul>

<li>If we encounter an unresolved bit- or part-select from @('w'), or if we
encounter a plain @('w') that is not defined, we just return
@('\"w[0]\"').</li>

<li>We don't do any index checking, so if we see an out-of-bounds bit- or
part-select we just return strings that refer to non-existent bits.</li>

<li>If we encounter a plain, undefined wire @('w'), we just return
@('\"w[0]\"').</li>

</ul>

<p>It is somewhat <i>wrong</i> to fudge like this, but these cases won't be hit
in well-formed modules, and they allow us to handle expressions even in
malformed modules in a mostly correct way without having to consider how to
handle problems with collecting bits.</p>"

  (define vl-expr-approx-bits ((x      vl-expr-p)
                               (mod    vl-module-p)
                               (ialist (equal ialist (vl-make-moditem-alist mod))))
    :returns (approx-bits string-listp)
    :measure (vl-expr-count x)
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

  (define vl-exprlist-approx-bits
    ((x      vl-exprlist-p)
     (mod    vl-module-p)
     (ialist (equal ialist (vl-make-moditem-alist mod))))
    :measure (vl-exprlist-count x)
    :returns (bits string-listp)
    (if (atom x)
        nil
      (append (vl-expr-approx-bits (car x) mod ialist)
              (vl-exprlist-approx-bits (cdr x) mod ialist)))))

(define vl-assign-check-selfassigns
  :short "@(call vl-assign-check-selfassigns) checks an assignment for
bits that occur on the lhs and rhs."
  ((x      vl-assign-p)
   (mod    vl-module-p)
   (ialist (equal ialist (vl-make-moditem-alist mod))))
  :returns (warnings vl-warninglist-p)
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
               :fn __function__))
      nil)))

(defmapappend vl-assignlist-check-selfassigns (x mod ialist)
  (vl-assign-check-selfassigns x mod ialist)
  :guard (and (vl-assignlist-p x)
              (vl-module-p mod)
              (equal ialist (vl-make-moditem-alist mod)))
  :transform-true-list-p t)

(defthm vl-warninglist-p-of-vl-assignlist-check-selfassigns
  (vl-warninglist-p (vl-assignlist-check-selfassigns x mod ialist))
  :hints(("Goal" :induct (len x))))

(define vl-module-check-selfassigns
  :short "Check the assignments of a module for self-assignments to bits."
  ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :long "<p>@(call vl-module-check-selfassigns) checks all of the assignments
in the module @('x') for @(see selfassigns), and adds any warnings to the
module.</p>"

  (b* ((assigns (vl-module->assigns x))
       ((unless assigns)
        x)
       (ialist (vl-make-moditem-alist x))
       (warnings (vl-assignlist-check-selfassigns assigns x ialist))
       (- (fast-alist-free ialist))
       ((unless warnings)
        x))
    (change-vl-module x
                      :warnings (append warnings (vl-module->warnings x)))))

(defprojection vl-modulelist-check-selfassigns (x)
  (vl-module-check-selfassigns x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-check-selfassigns ((x vl-design-p))
  :returns (new-design vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-check-selfassigns x.mods))))

