; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "centaur/vl/mlib/scopestack" :dir :system)
(include-book "centaur/vl/mlib/hid-tools" :dir :system)
(include-book "centaur/vl/mlib/selfsize" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (:e tau-system))))
(local (in-theory (enable tag-reasoning)))

(defxdoc truncation-warnings
  :parents (vl-lint)
  :short "Warnings about implicit truncation and extensions in assignments,
casts, and so forth."

  :long "<p>Truncation warnings are really, really good to have, and have found
many bugs.  However, if we just issue a truncation warning about everything, we
find that there are way too many nitpicky warnings and it's hard to go through
them all.  So, we want to be clever and not warn in certain cases that we have
seen where the truncation really doesn't matter.  Efficiency is of no concern
because this is called so infrequently.</p>

<p>Probably the biggest source of spurious truncation warnings is from the use
of unsized numbers like 0 and 1.  It's a pretty good bet that any truncation
from 32-bits to some other number of bits is no big deal and is just being
caused by a unsized number.</p>

<p>At any rate, we now have a notion of expression that are okay to truncate.
We basically don't want to complain about things like</p>

@({
    assign foo[3:0] = 0;              // 32 bits, but who cares, it fits

    assign foo[3:0] = 5'd7;           // 5 bits, but who cares, it still fits

    assign foo[3:0] = x0 ? 5'h0 :     // each are 5 bits, but who cares, they
                      x1 ? 5'h1 :     // still fit.
                      x2 ? 5'h2 :
                      ...
                      x14 ? 5'h14 :
                      5'h15;
})")

(local (xdoc::set-default-parents truncation-warnings))

(local (defthm alistp-of-vl-expr->atts
         ;; BOZO probably move to vl/expr.lisp
         (alistp (vl-expr->atts x))
         :hints(("Goal" :in-theory (enable (:e tau-system))))))

(define vl-unsized-parameter-index-p
  :short "Identify occurrences of basic, unsized parameters."
  ((x  vl-expr-p)
   (ss vl-scopestack-p))
  :long "<p>We often run into cases like</p>

@({
    parameter foo = 5;
    ...
    assign w[3:0] = foo;
})

<p>It was annoying to get truncation warnings about this sort of thing.  So,
here, as a heuristic, we are looking for expression like @('foo') which are
references to untyped parameters.</p>"
  (vl-expr-case x
    :vl-index
    (b* (((when (or x.indices
                    (not (vl-partselect-case x.part :none))))
          ;; something like foo[3] or foo[3:0] is not a plain parameter
          nil)
         ((mv err trace ?context tail) (vl-follow-scopeexpr x.scope ss))
         ((when err)
          ;; don't know what it is, don't assume it's a plain parameter
          nil)
         ((when (vl-hidexpr-case tail :dot))
          ;; reference into a structure or something, not a plain parameter
          nil)
         (item (vl-hidstep->item (car trace)))
         ((unless (mbe :logic (vl-paramdecl-p item)
                       :exec (eq (tag item) :vl-paramdecl)))
          nil)
         ((vl-paramdecl item)))
      (vl-paramtype-case item.type
        :vl-implicitvalueparam t
        :vl-typeparam nil
        :vl-explicitvalueparam
        (and (vl-datatype-resolved-p item.type.type)
             (b* (((mv err size) (vl-datatype-size item.type.type)))
               (and (not err)
                    (equal size 32))))))
    :otherwise nil))

(define vl-okay-to-truncate-expr ((width natp "Width being truncated to.")
                                  (x vl-expr-p "Expression being truncated.")
                                  (ss vl-scopestack-p))
  :short "Heuristic for deciding whether to issue truncation warnings."
  :measure (vl-expr-count x)
  (let* ((width (nfix width))
         (x (vl-expr-fix x))
         (ss (vl-scopestack-fix ss)))
    (vl-expr-case x
      :vl-literal
      ;; Recognize:
      ;;
      ;; (1) ordinary constant integer numbers like 5, but which are not
      ;;     "negative" numbers (i.e., bit 31 should not be set), and whose value
      ;;     is small enough to fit into WIDTH many bits.
      ;;
      ;; (2) sized but unsigned constant integers that can be chopped down to
      ;;     width-many bits without changing their value.
      ;;
      ;; (3) parameters that were constant integers and fit into the desired
      ;;     width.
      (vl-value-case x.val
        (:vl-constint (or ;; Case 1:
                       (and x.val.wasunsized
                            (= x.val.origwidth 32)
                            (not (logbitp 31 x.val.value))
                            (< x.val.value (ash 1 width)))
                       ;; Case 2:
                       (and (vl-exprsign-equiv x.val.origsign :vl-unsigned)
                            (< x.val.value (ash 1 width)))
                       ;; Case 3:
                       (and (assoc-equal "VL_PARAMNAME" x.atts)
                            (< x.val.value (ash 1 width)))))
        (:otherwise
         nil))
      :vl-index
      ;; BOZO probably we should be doing something more clever here to
      ;; actually check the bounds of the parameter.
      (vl-unsized-parameter-index-p x ss)
      :vl-qmark
      ;; Recognize as okay nests of (A ? B : C) where all of the final branches
      ;; are okay to truncate.
      (and (vl-okay-to-truncate-expr width x.then ss)
           (vl-okay-to-truncate-expr width x.else ss))
      :otherwise nil))
  ///
  (local (assert!
          ;; Basic test to make sure it seems to be working right.
          (flet ((test (value)
                       (make-vl-literal :val
                                        (make-vl-constint :value value
                                                          :origwidth 32
                                                          :origsign :vl-signed
                                                          :wasunsized t))))
            (and (vl-okay-to-truncate-expr 8 (test 0) nil)
                 (vl-okay-to-truncate-expr 8 (test 255) nil)
                 (not (vl-okay-to-truncate-expr 8 (test 256) nil)))))))

(define vl-unsized-atom-p ((x  vl-expr-p)
                           (ss vl-scopestack-p))
  :prepwork ((local (in-theory (enable tag-reasoning
                                       (:e tau-system)))))
  (vl-expr-case x
    :vl-literal
    (vl-value-case x.val
      (:vl-constint (or x.val.wasunsized
                        (assoc-equal "VL_PARAMNAME" x.atts)))
      (:vl-weirdint x.val.wasunsized)
      (:otherwise nil))
    :vl-index
    (vl-unsized-parameter-index-p x ss)
    :otherwise nil))

(define vl-some-unsized-atom-p ((x  vl-exprlist-p)
                                (ss vl-scopestack-p))
  (if (atom x)
      nil
    (or (vl-unsized-atom-p (car x) ss)
        (vl-some-unsized-atom-p (cdr x) ss))))

(define vl-toobig-constant-atom-p ((width natp)
                                   (x     vl-expr-p))
  ;; Recognize any constant integers that don't fit into the given width and
  ;; are therefore going to be truncated.
  (and (vl-expr-resolved-p x)
       (not (< (vl-resolved->val x) (ash 1 (lnfix width))))))

(define vl-collect-toobig-constant-atoms ((width natp)
                                          (x     vl-exprlist-p))
  :returns (toobig vl-exprlist-p)
  (cond ((atom x) nil)
        ((vl-toobig-constant-atom-p width (car x))
         (cons (vl-expr-fix (car x))
               (vl-collect-toobig-constant-atoms width (cdr x))))
        (t
         (vl-collect-toobig-constant-atoms width (cdr x)))))

(define vl-maybe-warn-about-implicit-truncation
  ((lvalue   vl-maybe-expr-p
             "LHS expression, if applicable.  There might not be a left-hand
              side expression in case of things like @('foo_t'(bar)').")
   (lw       natp      "LHS size, or size of the type being cast to, etc.")
   (expr     vl-expr-p "RHS expression.")
   (ew       natp      "RHS expression width.")
   (ss       vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* ((lw     (lnfix lw))
       (ew     (lnfix ew))
       ((unless (< lw ew))
        ;; It isn't being truncated.
        nil)

       (lvalue (vl-maybe-expr-fix lvalue))
       (expr   (vl-expr-fix expr))

       ((when (vl-okay-to-truncate-expr lw expr ss))
        ;; Just ignore it, this is nothing to be worried about
        nil)

       (atoms
        ;; This tries to smartly collect atoms, for instance, it avoids collecting
        ;; the `3` in `foo[3] + bar`, but does collect the 4 in `a + 4`.
        (vl-expr-interesting-size-atoms expr))

       (toobig (vl-collect-toobig-constant-atoms lw atoms))

       (probably-minor-p
        ;; We could probably improve this somewhat... if the RHS is 32 bits
        ;; and it at least has some atom that was originally unsized in it,
        ;; it's probably just a truncation because there's a plain number on
        ;; the rhs, and it probably isn't a real problem, so we'll call such
        ;; things minor.  This is something we couldn't check very well when
        ;; we were trying to handle truncation warnings as part of
        ;; assign-trunc, because by then the expressions had already been
        ;; split and the temp wires could hide unsized atoms.
        (and (equal ew 32)
             (not toobig)
             (vl-some-unsized-atom-p atoms ss)))

       (warning (make-vl-warning
                 :type (if probably-minor-p
                           :vl-warn-truncation-minor
                         :vl-warn-truncation)
                 :msg "implicit truncation from ~x0-bit expression ~
                       to ~x1-bit lvalue/type.~%     ~
                         lhs: ~a2~%     ~
                         rhs: ~a3~%~%"
                 :args (list ew lw (or lvalue 'n/a) expr)
                 :fatalp nil
                 :fn __function__)))
    (list warning))
  ///
  (defret true-listp-of-vl-maybe-warn-about-implicit-truncation
    (true-listp warnings)
    :rule-classes :type-prescription))


(defsection vl-classify-extension-warning-hook
  :short "Configurable hook for classifying extension warnings."

  :long "<p>Extension warnings are very good to have and have helped us to find
many bugs.  However, we need to be pretty clever to avoid getting too many
trivial, nitpicky complaints about assignments that aren't really bugs.</p>

<p>This hook can be used with @(see defattach) to customize exactly how
extension warnings are filtered out and easily experiment with new heuristics.
See @(see vl-classify-extension-warning-default) for the arguments.  The task
of your function is to classify the type of warning to issue.  Typically the
type should be one of the following:</p>

<ul>
<li>@('nil') - do not issue any warnings about this extension,</li>
<li>@(':vl-warn-extension') - issue a default warning, or</li>
<li>@(':vl-warn-extension-minor') - issue a minor warning.</li>
</ul>

<p>However in principle you can return any warning type you like.</p>

<p>Note that your function will only be called when there is an extension
taking place, so it is generally fine to use a function that is relatively
expensive or inefficient here.</p>

@(def vl-classify-extension-warning-hook)"
  :autodoc nil

  (encapsulate
    (((vl-classify-extension-warning-hook * * * *) => *
      :formals (lhs-size x-selfsize x ss)
      :guard (and (natp lhs-size)
                  (natp x-selfsize)
                  (> lhs-size x-selfsize)
                  (vl-expr-p x)
                  (vl-scopestack-p ss))))

    (local (defun vl-classify-extension-warning-hook (lhs-size x-selfsize x ss)
             (declare (ignorable lhs-size x-selfsize x ss))
             nil))

    (defthm keywordp-of-vl-classify-extension-warning-hook
      (implies (vl-classify-extension-warning-hook lhs-size x-selfsize x ss)
               (keywordp (vl-classify-extension-warning-hook lhs-size x-selfsize x ss))))))

(local (defthm symbolp-of-vl-classify-extension-warning-hook
         (symbolp (vl-classify-extension-warning-hook lhs-size x-selfsize x ss))
         :rule-classes :type-prescription
         :hints(("Goal"
                 :in-theory (disable keywordp-of-vl-classify-extension-warning-hook)
                 :use ((:instance keywordp-of-vl-classify-extension-warning-hook))))))



(define vl-classify-extension-warning-default
  :parents (vl-classify-extension-warning-hook)
  :short "Default heuristic for filtering extension warnings."

  :long "<p>We found that extension warnings were frequently triggered by
things like @('assign {carry,sum} = a + b') where the designer seems to
explicitly intend to get the carry bit.  We therefore only cause a minor
warning if the right-hand side is composed only of additions.  Later it turned
out we need to permit selects, too.  And later we decided to also add
subtraction as a permitted operation.</p>

<p>Another kind of extension warning that is stupidly minor is when we just
have assignments like @('assign foo[127:0] = 0;').  We now do not even create a
minor warning for assignments where the rhs is a constant.</p>"

  ((lhs-size   natp)
   (x-selfsize natp)
   (x          vl-expr-p)
   (ss         vl-scopestack-p))
  :guard (> lhs-size x-selfsize)
  (declare (ignorable lhs-size x-selfsize ss))
  (vl-expr-case x
    :vl-literal
    (vl-value-case x.val
      ;; Extension integers like '0 are meant to be extended, so don't give
      ;; any warning here.
      :vl-extint nil
      ;; Plain integers like 0 or 5 probably shouldn't cause any extension
      ;; warnings.  BOZO might also not want to warn about other special
      ;; cases like 0?
      :vl-constint (if x.val.wasunsized
                       nil
                     :vl-warn-extension)
      ;; For any other literals go ahead and warn?
      :otherwise :vl-warn-extension)
    :otherwise
    (b* ((ops    (vl-expr-ops x))
         (minorp (and (or (member-equal :vl-binary-plus ops)
                          (member-equal :vl-binary-minus ops))
                      (subsetp-equal ops '(:vl-binary-plus
                                           :vl-binary-minus
                                           :vl-partselect-colon
                                           :vl-bitselect)))))
      (if minorp
          :vl-warn-extension-minor
        :vl-warn-extension)))
  ///
  (defattach vl-classify-extension-warning-hook
    vl-classify-extension-warning-default))


(define vl-maybe-warn-about-implicit-extension
  :short "Lint-like warnings about right hand sides being extended."
  ((lhs-size   natp)
   (x-selfsize natp)
   (x          vl-expr-p)
   (ss         vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* ((lhs-size   (lnfix lhs-size))
       (x-selfsize (lnfix x-selfsize))
       ((unless (> lhs-size x-selfsize))
        nil)
       (x          (vl-expr-fix x))
       (ss         (vl-scopestack-fix ss))
       (type       (vl-classify-extension-warning-hook lhs-size x-selfsize x ss))
       ((unless type)
        nil))
    (list
     (make-vl-warning :type type
                      :msg "implicit extension from ~x0-bit expression to ~x1 bits: ~a2"
                      :args (list x-selfsize lhs-size x)
                      :fn __function__)))
  ///
  (defret true-listp-of-vl-maybe-warn-about-implicit-extension
    (true-listp warnings)
    :rule-classes :type-prescription))
