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
(include-book "../mlib/expr-tools")
(include-book "lucid")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc selfassigns
  :parents (vl-lint)
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
                           (index integerp))
  :returns (bit stringp :rule-classes :type-prescription)
  (b* ((index (lifix index)))
    (cat name "[" (if (< index 0) "-" "") (natstr (abs index)) "]")))

(define vl-selfassign-bits-from-indices ((name stringp)
                                         (bits integer-listp))
  :returns (bits string-listp)
  (if (atom bits)
      nil
    (cons (vl-selfassign-bit name (car bits))
          (vl-selfassign-bits-from-indices name (cdr bits)))))

(local (in-theory (disable nfix)))
(local (include-book "std/basic/arith-equivs" :dir :system))

(define vl-selfassign-bits ((name stringp)
                            (low  integerp)
                            (high integerp))
  :guard (<= low high)
  :measure (nfix (- (ifix high) (ifix low)))
  :returns (bits string-listp)
  (if (mbe :logic (zp (- (ifix high) (ifix low)))
           :exec (eql high low))
      (list (vl-selfassign-bit name low))
    (cons (vl-selfassign-bit name low)
          (vl-selfassign-bits name (+ (lifix low) 1) high))))

(defines vl-expr-approx-bits
  :short "Collect strings representing (approximately) the individual bits of
wires involved in an expression."

  :long "<p>We try to return a list of strings like @('\"foo[3]\"') that are
approximately the bits indicated by the expression.  This routine is at the
core of our @(see selfassigns) check, which is just an informal heuristic and
doesn't need to be particularly correct or accurate.</p>"

  (define vl-expr-approx-bits ((x      vl-expr-p)
                               (ss     vl-scopestack-p))
    :returns (approx-bits string-listp)
    :measure (vl-expr-count x)
    (append
     (vl-expr-case x
       :vl-index (b* ((varname (vl-scopeexpr-case x.scope
                                 :end (vl-hidexpr-case x.scope.hid
                                        :end x.scope.hid.name
                                        :otherwise nil)
                                 :otherwise nil))
                      ((unless varname) nil)
                      (no-indices (atom x.indices))
                      (one-index  (tuplep 1 x.indices))
                      (no-partselect (vl-partselect-case x.part :none))
                      ((when (and no-indices no-partselect))
                       ;; Lone occurrence of "foo" -- try to figure out what the
                       ;; valid bits of foo are from its declaration.
                       (b* (((mv err trace ?context ?tail)
                             (vl-follow-scopeexpr x.scope ss))
                            ((when err) nil)
                            ((vl-hidstep step) (car trace))
                            ((unless (eq (tag step.item) :vl-vardecl))
                             nil)
                            ((mv simplep valid-bits)
                             (vl-lucid-valid-bits-for-decl step.item step.ss))
                            ((unless simplep)
                             nil))
                         (vl-selfassign-bits-from-indices varname valid-bits)))
                      ((when (and one-index no-partselect))
                       (if (vl-expr-resolved-p (first x.indices))
                           (list (vl-selfassign-bit varname
                                                    (vl-resolved->val (first x.indices))))
                         nil))
                      ((when (and no-indices
                                  (vl-partselect-case x.part :range)))
                       (b* (((vl-range x.part) (vl-partselect->range x.part))
                            ((unless (and (vl-expr-resolved-p x.part.msb)
                                          (vl-expr-resolved-p x.part.lsb)))
                             nil)
                            (high (max (vl-resolved->val x.part.msb)
                                       (vl-resolved->val x.part.lsb)))
                            (low  (min (vl-resolved->val x.part.msb)
                                       (vl-resolved->val x.part.lsb))))
                         (vl-selfassign-bits varname low high))))
                   ;; Else, too complicated, well whatever.
                   nil)
       :otherwise nil)
     (vl-exprlist-approx-bits (vl-expr->subexprs x) ss)))

  (define vl-exprlist-approx-bits ((x  vl-exprlist-p)
                                   (ss vl-scopestack-p))
    :measure (vl-exprlist-count x)
    :returns (bits string-listp)
    (if (atom x)
        nil
      (append (vl-expr-approx-bits (car x) ss)
              (vl-exprlist-approx-bits (cdr x) ss))))
  ///
  (deffixequiv-mutual vl-expr-approx-bits))

(define vl-assign-check-selfassigns
  :short "@(call vl-assign-check-selfassigns) checks an assignment for
bits that occur on the lhs and rhs."
  ((x      vl-assign-p)
   (ss     vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-assign x) (vl-assign-fix x))
       (lhs-bits (mergesort (vl-expr-approx-bits x.lvalue ss)))
       (rhs-bits (mergesort (vl-expr-approx-bits x.expr ss)))
       (oops     (intersect lhs-bits rhs-bits)))
    (if oops
        (list (make-vl-warning
               :type :vl-warn-selfassign
               :msg "~a0: lhs bits occur on rhs: ~&1."
               :args (list x oops)
               :fatalp nil
               :fn __function__))
      nil)))

(defmapappend vl-assignlist-check-selfassigns (x ss)
  (vl-assign-check-selfassigns x ss)
  :guard (and (vl-assignlist-p x)
              (vl-scopestack-p ss))
  :transform-true-list-p t)

(defthm vl-warninglist-p-of-vl-assignlist-check-selfassigns
  (vl-warninglist-p (vl-assignlist-check-selfassigns x ss))
  :hints(("Goal" :induct (len x))))

(define vl-module-check-selfassigns
  :short "Check the assignments of a module for self-assignments to bits."
  ((x  vl-module-p)
   (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  :long "<p>@(call vl-module-check-selfassigns) checks all of the assignments
in the module @('x') for @(see selfassigns), and adds any warnings to the
module.</p>"

    ;; BOZO doesn't do generates correctly
  (b* (((vl-module x) (vl-module-fix x))
       ((unless x.assigns)
        x)
       (ss       (vl-scopestack-push x ss))
       (warnings (vl-assignlist-check-selfassigns x.assigns ss))
       ((unless warnings)
        x))
    (change-vl-module x
                      :warnings (append warnings x.warnings))))

(defprojection vl-modulelist-check-selfassigns ((x vl-modulelist-p)
                                                (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-check-selfassigns x ss))

(define vl-design-check-selfassigns ((x vl-design-p))
  :returns (new-design vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x)))
    (change-vl-design x
                      :mods (vl-modulelist-check-selfassigns x.mods ss))))

