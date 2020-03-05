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
(include-book "centaur/vl/mlib/strip" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "../../vl/util/arithmetic"))
(local (include-book "std/testing/assert" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (:e tau-system))))
(local (in-theory (enable tag-reasoning)))

; Matt K.: Avoid ACL2(p) error (the job died after vl-maybe-type-error-p).
(set-waterfall-parallelism nil)

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

(defenum vl-typecompat-p (:cast :assign :equiv))
  ;; (:cast ((expr vl-expr-p)))
  ;; (:assign ((lhs vl-expr-p)
  ;;           (rhs vl-expr-p)))
  ;; (:port   ((portname stringp)
  ;;           (expr vl-expr-p)))
  ;; (:gateport ((portname stringp)
  ;;             (expr vl-expr-p))))

(define vl-expr-is-{n{0}}-p ((x vl-expr-p))
  (vl-expr-case x
    :vl-multiconcat
    (and (equal (len x.parts) 1)
         (let ((first (car x.parts)))
           (vl-expr-case first
             :vl-literal
             (vl-value-case first.val
               :vl-constint (equal first.val.value 0)
               :vl-extint   (vl-bit-equiv first.val.value :vl-0val)
               :otherwise   nil)
             :otherwise nil)))
    :otherwise nil))

(define vl-okay-to-truncate-expr ((width natp       "Width being truncated to.")
                                  (x     vl-expr-p  "Expression being truncated.")
                                  (ss    vl-scopestack-p))
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
      (vl-unsized-index-p x ss)
      :vl-binary
      ;; Recognize expressions like A % K, and don't warn if the width we are
      ;; assigning to allows us to represent numbers through K-1.  This isn't
      ;; necessarily sensible for signed numbers, but should probably be a
      ;; pretty good heuristic in general.
      (and (vl-binaryop-equiv x.op :vl-binary-rem)
           (b* ((k   (and (vl-expr-resolved-p x.right)
                          (vl-resolved->val x.right)))
                (max (ash 1 width)))
             ;;(cw "Dealing with ~s0: k is ~x1 and max value for this width is ~x2~%"
             ;;    (vl-pps-expr x) k max)
             (and k (<= k max))))
      :vl-qmark
      ;; Recognize as okay nests of (A ? B : C) where all of the final branches
      ;; are okay to truncate.
      (and (vl-okay-to-truncate-expr width x.then ss)
           (vl-okay-to-truncate-expr width x.else ss))
      :vl-call
      (vl-is-integer-valued-syscall x)
      :vl-multiconcat
      ;; If someone is replicating a zero, it's all just zero, so that seems OK
      ;; to truncate even if they've replicated it some incorrect number of times.
      (vl-expr-is-{n{0}}-p x)
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
    :vl-index (vl-unsized-index-p x ss)
    :vl-call  (vl-is-integer-valued-syscall x)
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



(define vl-expr-is-|{'0, ...}|-p ((x vl-expr-p))
  (vl-expr-case x
    :vl-concat
    (and (consp x.parts)
         (let ((first (car x.parts)))
           (vl-expr-case first
             :vl-literal
             (vl-value-case first.val
               :vl-extint (vl-bit-equiv first.val.value :vl-0val)
               :otherwise nil)
             :otherwise nil)))
    :otherwise nil))

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
      :vl-constint (cond (x.val.wasunsized
                          ;; Plain integers like 0 or 5 probably shouldn't
                          ;; cause any extension warnings.
                          nil)
                         ((eql x.val.value 0)
                          ;; Zero seems like a good special case, because
                          ;; it's horribly nitpicky to complain about things
                          ;; like wire [1:0] = 1'b0, or wire [3:0] = 2'b0,
                          ;; because the designer pretty clearly just wants
                          ;; a zero here and the zero-extension isn't going
                          ;; to change that.
                          nil)
                         (t
                          ;; Otherwise go ahead and warn since it isn't the
                          ;; right size?
                          :vl-warn-extension))
      ;; For any other literals go ahead and warn?
      :otherwise :vl-warn-extension)
    :vl-concat
    ;; If someone is trying to concatenate an extension 0 onto something, it
    ;; seems like they want it to be zero extended, and they will get their
    ;; wish.
    (if (vl-expr-is-|{'0, ...}|-p x)
        nil
      :vl-warn-extension)
    :vl-multiconcat
    ;; If someone is replicating a zero, it's all just zero, so that seems OK
    ;; to extend.
    (if (vl-expr-is-{n{0}}-p x)
        nil
      :vl-warn-extension)
    :otherwise
    (b* ((ops    (vl-expr-ops x))
         (minorp (and (or (member-equal :vl-binary-plus ops)
                          (member-equal :vl-binary-minus ops)
                          (member-equal :vl-binary-times ops))
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

(deftypes vl-type-error
  (deftagsum vl-type-error
    (:incompat ((actual-type vl-datatype-p)
                (detail vl-msg-p)))
    (:trunc/extend ((lhs-size natp :rule-classes :type-prescription)
                    (rhs-selfsize natp :rule-classes :type-prescription)))
    (:qmark-subexpr ((alist vl-type-error-alist))))
  (fty::defalist vl-type-error-alist :key-type vl-expr :val-type vl-type-error))

(defoption vl-maybe-type-error vl-type-error-p)

(defprod vl-subexpr-type-error
  ((expr vl-expr-p)
   (type vl-datatype-p)
   (type-err vl-type-error-p)))

(fty::deflist vl-subexpr-type-error-list :elt-type vl-subexpr-type-error)

(defines vl-type-error-basic-warn
  (define vl-type-error-basic-warn ((x vl-expr-p "outer expression")
                                    (subexpr vl-maybe-expr-p "current subexpression")
                                    (err vl-maybe-type-error-p)
                                    (lhs vl-maybe-expr-p)
                                    (type vl-datatype-p)
                                    (ss vl-scopestack-p))
    :returns (warnings vl-warninglist-p)
    :measure (if err (vl-type-error-count err) 0)
    (b* (((unless err) nil)
         (warnings nil))
      (vl-type-error-case err
        :incompat (fatal :type :vl-types-incompatible
                         :msg "~@0 has type ~a1, incompatible with required type ~a2~@3: ~@4"
                         :args (list (if subexpr
                                         (vmsg "In ~a0, subexpression ~a1" (vl-expr-fix x) (vl-expr-fix subexpr))
                                       (vmsg "~a0" (vl-expr-fix x)))
                                     err.actual-type (vl-datatype-fix type)
                                     (if lhs (vmsg "for ~a0" (vl-expr-fix lhs)) "")
                                     err.detail))
        :trunc/extend (if (< err.lhs-size err.rhs-selfsize)
                          (vl-maybe-warn-about-implicit-truncation
                           lhs err.lhs-size (or subexpr x) err.rhs-selfsize ss)
                        (vl-maybe-warn-about-implicit-extension
                         err.lhs-size err.rhs-selfsize (or subexpr x) ss))
        :qmark-subexpr (vl-type-error-alist-basic-warn err.alist x lhs type ss))))
  (define vl-type-error-alist-basic-warn ((alist vl-type-error-alist-p)
                                          (x vl-expr-p)
                                          (lhs vl-maybe-expr-p)
                                          (type vl-datatype-p)
                                          (ss vl-scopestack-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-type-error-alist-count alist)
    (b* ((alist (vl-type-error-alist-fix alist))
         ((unless (consp alist)) nil)
         (warnings (vl-type-error-alist-basic-warn (cdr alist) x lhs type ss))
         ((wmv warnings) (vl-type-error-basic-warn
                          x (caar alist) (cdar alist) lhs type ss)))
      warnings))
  ///
  (fty::deffixequiv-mutual vl-type-error-basic-warn))






(define vl-typecast-type-error-warn ((type-error vl-maybe-type-error-p)
                                     (x vl-expr-p)
                                     (ss vl-scopestack-p))
  :guard (vl-expr-case x
           :vl-cast (vl-casttype-case x.to :type)
           :otherwise nil)
  :returns (warnings vl-warninglist-p)
  (b* (((vl-cast x))
       ((vl-casttype-type x.to))
       ((unless (and type-error (vl-type-error-case type-error :incompat)))
        ;; Don't warn about truncation/extensions.
        nil))
    (vl-type-error-basic-warn x.expr nil type-error nil x.to.type ss)))

(define vl-assignpat-cast-type-error-warn ((type-err vl-maybe-type-error-p)
                                           (x vl-expr-p)
                                           (ss vl-scopestack-p))
  :guard (vl-expr-case x
           :vl-pattern x.pattype
           :otherwise nil)
  :returns (warnings vl-warninglist-p)
  (b* (((unless type-err) nil)
       ((vl-pattern x)))
    (vl-type-error-basic-warn
     (change-vl-pattern x :pattype nil)
     nil type-err nil x.pattype ss)))




;; Datatype compatibility:

;; The SV manual says (in 6.22) that it defines five levels of type
;; compatibility: matching, equivalent, assignment compatible, cast compatible,
;; and nonequivalent.  We think only two of these are important: equivalence
;; and assignment compatibility.  Explanation:

;;   - Matching is a very strict check and the only thing we could ascertain
;;     that it is used for is comparison of type operators, e.g.
;;        generate
;;          case type(foo)
;;            type(bar) : initial $display("foo and bar have matching types"); end
;;            default   : initial $display("foo and bar have non-matching types"); end
;;          endcase
;;       endgenerate
;;     However, this isn't even supported by VCS/NCV yet.
;;   - Basically all the types we support are cast compatible.

;; Equivalence of types is essentially:
;;   - non-enum packed types of the same size and (top-level) signedness are
;;     equivalent
;;   - equal types are equivalent
;;   - fixed-size unpacked array types are equivalent if they have equal size
;;     and equivalent element types.

;; We deviate from the standard in one respect which makes our conception of
;; type equivalence more lenient: In the manual, an unpacked struct/union is
;; only equivalent to another if they are really from the same declaration; we
;; don't track this, so we view such types as equivalent if they are equal.
;; Note: it is not enough for them to be isomorphic, i.e. they are not
;; equivalent if they have different member names (of the same types) or if
;; members have equivalent but not equal types.  If we wanted to fix this, we
;; could assign a unique number to each structs/union encountered at parse
;; time, or perhaps the source location.  Past parse time, we lose the ability
;; to distinguish between
;;   struct { integer a; } a1, a2;
;; and
;;   struct { integer a; } a1;
;;   struct { integer a; } a2;

;; Assignment compatibility is essentially:
;;    - equivalent types are assignment compatible
;;    - packed non-enum types are all assignment compatible with each other
;;    - an enum is assignment compatible with an integral type, but not vice
;;      versa (because it requires a cast to assign an integral object to an
;;      enum variable, but not vice versa).


;; A typecompat object is a signifier of a kind of type compatibility.  For us,
;; cast means no compatibility is required.  Assign means we check for
;; assignment compatibility, equiv means check for equivalence.

(define vl-dimension-compare-sizes ((a vl-dimension-p)
                                    (b vl-dimension-p))
  (vl-dimension-case a
    :unsized (vl-dimension-case b :unsized)
    :range   (vl-dimension-case b
               :range (and (vl-range-resolved-p a.range)
                           (vl-range-resolved-p b.range)
                           (equal (vl-range-size a.range) (vl-range-size b.range)))
               :otherwise nil)
    ;; BOZO for now, don't regard any of these as type compatible.
    ;; They don't have fixed sizes anyway.  If this is the right behavior,
    ;; is it not also the right behavior for unsized dimensions?  If it
    ;; is not the right behavior, then the right behavior might be
    ;; something like the commented out code below.
    :datatype nil
    :star nil
    :queue nil

    ;; Possibly instead we should do something like...
    ;; :datatype nil ;; bozo??
    ;; :star     (vl-dimension-case b :star)
    ;; :queue    (vl-dimension-case b
    ;;             :queue (or (and (not a.maxsize)
    ;;                             (not b.maxsize))
    ;;                        (and a.maxsize
    ;;                             b.maxsize
    ;;                             (vl-expr-resolved-p a.maxsize)
    ;;                             (vl-expr-resolved-p b.maxsize)
    ;;                             (equal (vl-resolved->val a.maxsize)
    ;;                                    (vl-resolved->val b.maxsize))))
    ;;             :otherwise nil)
    ))

(define vl-dimensionlist-compare-sizes ((a vl-dimensionlist-p)
                                        (b vl-dimensionlist-p))
  (if (atom a)
      (atom b)
    (and (consp b)
         (vl-dimension-compare-sizes (car a) (car b))
         (vl-dimensionlist-compare-sizes (cdr a) (cdr b)))))


(define vl-check-datatype-equivalence ((a vl-datatype-p)
                                       (b vl-datatype-p))
  :short "Returns NIL if the datatypes are equivalent, or an explanatory message if not."
  :guard (and (vl-datatype-resolved-p a)
              (vl-datatype-resolved-p b))
  :prepwork ((local (defthm symbolp-when-vl-maybe-exprsign-p
                      (implies (vl-maybe-exprsign-p x)
                               (symbolp x))
                      :hints(("Goal" :in-theory (enable vl-maybe-exprsign-p
                                                        vl-exprsign-p))))))
  :returns (msg (iff (vl-msg-p msg) msg))
  (b* ((udims-compatible (vl-dimensionlist-compare-sizes (vl-datatype->udims a)
                                                         (vl-datatype->udims b)))
       ((unless udims-compatible)
        (vmsg "Unpacked dimensions mismatch"))
       (a-core (vl-maybe-usertype-resolve (vl-datatype-update-udims nil a)))
       (b-core (vl-maybe-usertype-resolve (vl-datatype-update-udims nil b)))
       ((when (vl-datatype-equiv (vl-datatype-strip a-core)
                                 (vl-datatype-strip b-core)))
        nil)
       ((unless (and (vl-datatype-packedp a-core)
                     (vl-datatype-packedp b-core)))
        (vmsg "Unpacked base datatypes are unequal"))
       ((when (or (and (vl-datatype-case a-core :vl-enum)
                       (atom (vl-datatype->pdims a-core)))
                  (and (vl-datatype-case b-core :vl-enum)
                       (atom (vl-datatype->pdims b-core)))))
        ;; Implementation disagreement: NCV views a packed array of enums as a
        ;; non-enum, packed type, and therefore views it as equivalent to any
        ;; other packed type of the same size and signedness.  VCS says it's an
        ;; enum so it's only equivalent to another enum.  We go with the NCV
        ;; behavior because it's more permissive, but not in a way that's
        ;; problematic for us.
        (if (and (vl-datatype-case a-core :vl-enum)
                 (vl-datatype-case b-core :vl-enum))
            "Different enums"
          "One is an enum and the other isn't"))
       ((mv erra asize) (vl-datatype-size a-core))
       ((mv errb bsize) (vl-datatype-size b-core))
       ((when (or erra errb))
        (vmsg "Sizing failed: ~@0" (or erra errb)))
       ((when (or (not asize) (not bsize)))
        (vmsg "~s0 unsized" (cond (asize "b")
                                  (bsize "a")
                                  (t "a and b"))))
       ((unless (eql asize bsize))
        (vmsg "Packed core datatypes differ in size: ~x0 versus ~x1"  asize bsize))
       ;; ((mv ?caveata aclass) (vl-datatype-arithclass a-core))
       ;; ((mv ?caveatb bclass) (vl-datatype-arithclass b-core))
       ;; ((unless (eq aclass bclass))
       ;;  ;; Note: since both of them are packed, there shouldn't be any
       ;;  ;; chance of having arithmetic classes other than integers.
       ;;  (vmsg "Packed core datatypes differ in arithmetic class: ~x0 versus ~x1"  aclass bclass))
       )
    nil))

(define vl-check-datatype-assignment-compatibility ((a vl-datatype-p)
                                                    (b vl-datatype-p))
  :short "Returns NIL if the datatypes are assignment compatible (an object of
          type B can be assigned to a variable of type A) or an explanatory message
          if not."
  :guard (and (vl-datatype-resolved-p a)
              (vl-datatype-resolved-p b))
  :returns (msg (iff (vl-msg-p msg) msg))
  (b* (((when (or (consp (vl-datatype->udims a))
                  (consp (vl-datatype->udims b))))
        ;; Note about implementations: NCV agrees with us (and the spec,
        ;; sec. 7.6) that unpacked arrays are assignment compatible only if the
        ;; element types are equivalent.  VCS allows assignments between
        ;; compatible-sized unpacked arrays of assignment-compatible elements.
        ;; This would be a pain for us to implement because we'd need to extend
        ;; or truncate the individual elements of the RHS to match the LHS
        ;; element size.
        (vl-check-datatype-equivalence a b))
       (a-core (vl-maybe-usertype-resolve a))
       (b-core (vl-maybe-usertype-resolve b))
       ((when (vl-datatype-equiv (vl-datatype-strip a-core)
                                 (vl-datatype-strip b-core)))
        nil)
       ((unless (and (vl-datatype-packedp a-core)
                     (vl-datatype-packedp b-core)))
        (vmsg "Unpacked base datatypes are unequal"))
       ((when (and (vl-datatype-case a-core :vl-enum)
                   (atom (vl-datatype->pdims a-core))))
        ;; Implementation disagreement: NCV views a packed array of enums as a
        ;; non-enum, packed type, and therefore views it as equivalent to any
        ;; other packed type of the same size and signedness.  VCS says it's an
        ;; enum so it can only be assigned an array of the same enum type.  We
        ;; go with the NCV behavior because it's more permissive, but not in a
        ;; way that's problematic for us.
        "LHS may not be an enum unless RHS is the same enum"))
    ;; Other than enums, any two packed datatypes are assignment compatible.
    nil))

(define vl-check-datatype-compatibility ((a vl-datatype-p)
                                         (b vl-datatype-p)
                                         (compattype vl-typecompat-p))
  :guard (and (vl-datatype-resolved-p a)
              (vl-datatype-resolved-p b))
  :returns (msg "nil if the comparison passed" (iff (vl-msg-p msg) msg))
  :short "Checks two datatypes for compatibility.  The compattype argument determines
          which kind of compatibility -- equivalence, assignment compatibility,
          or cast compatibility.  For assignment and cast compatibility, B is the
          source type and A the destination type."
  :long "<p>At the moment, cast compatibility doesn't check anything.</p>"
  (b* ((a (vl-datatype-fix a))
       (b (vl-datatype-fix b))
       (compattype (vl-typecompat-fix compattype))
       (errmsg
        (case compattype
          (:assign (vl-check-datatype-assignment-compatibility a b))
          (:cast nil)
          (t (vl-check-datatype-equivalence a b)))))
    (and errmsg
         (vmsg "Datatype ~a0 is not ~s1 to ~a2:  ~@3"
               (if (vl-datatype->pdims b)
                   (make-vl-structmember :type b :name "b")
                 b)
               (case compattype
                 (:equiv "equivalent")
                 (:assign "assignment compatible")
                 (otherwise "cast compatible"))
               (if (vl-datatype->udims a)
                   (make-vl-structmember :type a :name "a")
                 a)
               errmsg))))

(define vl-datatype-compatibility-type-error ((req-type vl-datatype-p)
                                              (actual-type vl-datatype-p)
                                              (compattype vl-typecompat-p))
  :returns (type-err vl-maybe-type-error-p)
  :guard (and (vl-datatype-resolved-p req-type)
              (vl-datatype-resolved-p actual-type))
  (b* ((msg (vl-check-datatype-compatibility req-type actual-type compattype)))
    (and msg
         (make-vl-type-error-incompat :actual-type actual-type
                                      :detail msg))))




(define vl-type-error-qmark-combine ((x vl-expr-p)
                                     (type-err1 vl-maybe-type-error-p)
                                     (type-err2 vl-maybe-type-error-p))
  ;; Combines type errors from the two branches of a qmark expression.  For
  ;; each branch, if the error of that branch a qmark-subexpr type error, which
  ;; contains an alist mapping subexpressions to errors, then preserve that
  ;; alist; otherwise, it's an error directly from the immediate subexpression,
  ;; so make a new singleton alist.  Append the alists of the two branches.
  :guard (vl-expr-case x :vl-qmark)
  :returns (type-err vl-maybe-type-error-p)
  :prepwork ((local (in-theory (enable VL-MAYBE-TYPE-ERROR-FIX))))
  (b* (((when (and (not type-err1) (not type-err2))) nil)
       ((when (and (not type-err1) (vl-type-error-case type-err2 :qmark-subexpr)))
        (vl-type-error-fix type-err2))
       ((when (and (not type-err2) (vl-type-error-case type-err1 :qmark-subexpr)))
        (vl-type-error-fix type-err1))
       ((vl-qmark x))
       (alist1 (and type-err1
                    (vl-type-error-case type-err1
                      :qmark-subexpr type-err1.alist
                      :otherwise (list (cons x.then type-err1)))))
       (alist2 (and type-err2
                    (vl-type-error-case type-err2
                      :qmark-subexpr type-err2.alist
                      :otherwise (list (cons x.else type-err2))))))
    (make-vl-type-error-qmark-subexpr :alist (append-without-guard alist1 alist2))))


(define vl-subexpr-type-error-list-combine ((x vl-expr-p)
                                            (type vl-datatype-p)
                                            (err vl-maybe-type-error-p)
                                            (rest vl-subexpr-type-error-list-p))
  :returns (errs vl-subexpr-type-error-list-p)
  (if err
      (cons (make-vl-subexpr-type-error :expr x :type type :type-err err)
            (vl-subexpr-type-error-list-fix rest))
    (vl-subexpr-type-error-list-fix rest)))


(define vl-subexpr-type-error-list-warn ((x vl-expr-p)
                                         (type-errs vl-subexpr-type-error-list-p)
                                         (ss vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom type-errs)) nil)
       (warnings (vl-subexpr-type-error-list-warn x (cdr type-errs) ss))
       ((vl-subexpr-type-error err1) (car type-errs))
       ((wmv warnings) (vl-type-error-basic-warn x err1.expr err1.type-err nil err1.type ss)))
    warnings))


(define vl-struct-assignpat-keyval-type-err-warn ((x vl-expr-p)
                                                  (structmem vl-structmember-p)
                                                  (subexpr vl-expr-p)
                                                  (type-err vl-maybe-type-error-p)
                                                  (ss vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* (((unless type-err) nil)
       ((vl-structmember structmem)))
    (vl-type-error-basic-warn x (vl-expr-fix subexpr) type-err (vl-idexpr structmem.name) structmem.type ss)))
