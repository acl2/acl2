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
(include-book "expr-tools")
(include-book "range-tools")
(include-book "scopestack")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defxdoc expr-cleaning
  :parents (mlib)
  :short "Functions for cleaning up ugly expressions.")

(local (xdoc::set-default-parents expr-cleaning))

(defthm vl-exprlist-count-of-append-upper-bound
  (<= (vl-exprlist-count (append x y))
      (+ 1 (vl-exprlist-count x) (vl-exprlist-count y)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :induct (len x)
          :in-theory (enable vl-exprlist-count))))

(define vl-elim-nested-concats-pass ((x vl-exprlist-p))
  :parents (vl-elim-nested-concats)
  :returns (mv (progressp booleanp :rule-classes :type-prescription)
               (new-x vl-exprlist-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv cdr-progressp cdr-prime)
        (vl-elim-nested-concats-pass (cdr x)))
       (expr1 (vl-expr-fix (car x)))
       ((unless (and (not (vl-fast-atom-p expr1))
                     (eq (vl-nonatom->op expr1) :vl-concat)))
        (mv cdr-progressp (cons expr1 cdr-prime)))

       ;; Else, we found a concat.  Eliminate it.
       (args (vl-nonatom->args expr1)))
    (mv t (append-without-guard args cdr-prime)))
  ///
  (defmvtypes vl-elim-nested-concats-pass (nil true-listp))

  (defthm vl-exprlist-count-of-vl-elim-nested-concats-pass-weak
    (<= (vl-exprlist-count (mv-nth 1 (vl-elim-nested-concats-pass x)))
        (vl-exprlist-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable vl-expr-count vl-exprlist-count))))

  (defthm vl-exprlist-count-of-vl-elim-nested-concats-pass-strong
    (implies (mv-nth 0 (vl-elim-nested-concats-pass x))
             (< (vl-exprlist-count (mv-nth 1 (vl-elim-nested-concats-pass x)))
                (vl-exprlist-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable vl-exprlist-count)))))

(define vl-elim-nested-concats
  :short "Flatten out nested concatenations like @('{a, b, {c, d}, { { e, f }
  }}') into @('{a, b, c, d, e, f}')."

  ((x vl-exprlist-p "The arguments to a concatenation."))
  :returns (new-x vl-exprlist-p "Possibly somewhat flattened.")

  :long "<p>We flatten out any top-level concatenations within @('x'), and
return the possibly simplified list of expressions.</p>

<p>This may help @(see vl-maybe-merge-selects) to be more effective.  For
instance, with the help of flattening, it can merge selects such as:</p>

@({{foo[3], {foo[2], foo[1]}, foo[0]}})"

  :measure (vl-exprlist-count x)
  (b* (((mv progressp x-prime)
        (vl-elim-nested-concats-pass x)))
    (if progressp
        (vl-elim-nested-concats x-prime)
      x-prime))
  ///
  (defthm true-listp-of-vl-elim-nested-concats
    (true-listp (vl-elim-nested-concats x))
    :rule-classes :type-prescription))


(define vl-maybe-merge-selects-aux
  :short "Identify a sequence of decreasing bit- and part-selects."
  ((x    vl-exprlist-p "Expressions we're looking through.")
   (from vl-expr-p     "Wire we're trying to match bitselects from.")
   (n    natp          "Last index we matched."))
  :returns (mv (min  natp :rule-classes :type-prescription)
               (rest vl-exprlist-p))
  :long "<p>We look for a sequence of decreasing bit- and part- selects that
count downward from @('from[n]').</p>

<p>We return the index of the final bit select that matches this criteria as
@('min'), and the remainder of @('x') as @('rest').</p>

<p>Here are some examples.</p>

<p>Suppose FROM is the idexpr \"foo\", and N is 6.</p>

<p>Then, given a sequence x = (foo[5] foo[4] foo[3] bar baz), we return</p>
@({
   MIN = 3
   REST = (bar baz)
})

<p>But if x = (bar baz), we just immediately return</p>
@({
   MIN = 6
   REST = (bar baz)
})

<p>We also handle part selects, e.g., if X is (foo[5:3], foo[2], bar, baz),
we return</p>
@({
   MIN = 2
   REST = (bar baz)
})"

  (b* ((from (vl-expr-fix from))
       (n    (lnfix n))

       ((when (atom x))
        (mv n (vl-exprlist-fix x)))

       (expr1 (car x))
       ((unless (and (not (vl-fast-atom-p expr1))
                     (or (eq (vl-nonatom->op expr1) :vl-bitselect)
                         (eq (vl-nonatom->op expr1) :vl-partselect-colon))))
        (mv n (vl-exprlist-fix x)))

       ;; We'll treat everything like a part select.
       (expr1-args (vl-nonatom->args expr1))
       (expr1-from (first expr1-args))
       (expr1-high (second expr1-args))
       (expr1-low  (if (eq (vl-nonatom->op expr1) :vl-bitselect)
                       expr1-high
                     (third expr1-args)))
       ((unless (and (equal expr1-from from)
                     (vl-expr-resolved-p expr1-high)
                     (vl-expr-resolved-p expr1-low)))
        (mv n (vl-exprlist-fix x)))

       (high-val (vl-resolved->val expr1-high))
       (low-val  (vl-resolved->val expr1-low))
       ((unless (and (natp high-val)
                     (natp low-val)
                     (= high-val (- n 1))
                     (<= low-val high-val)))
        (mv n (vl-exprlist-fix x))))

    ;; If we get this far, expr1 is from[n-1] or from[n-1:low].  Let's
    ;; keep looking for more to merge after low-val.
    (vl-maybe-merge-selects-aux (cdr x) from low-val))
  ///
  (defthm vl-exprlist-count-of-vl-maybe-merge-selects-aux-weak
    (<= (vl-exprlist-count (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))
        (vl-exprlist-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-exprlist-count-of-vl-maybe-merge-selects-aux-strong
    (implies (not (equal (nfix n) (mv-nth 0 (vl-maybe-merge-selects-aux x from n))))
             (< (vl-exprlist-count (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))
                (vl-exprlist-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm upper-bound-of-vl-maybe-merge-selects-aux
    (<= (mv-nth 0 (vl-maybe-merge-selects-aux x from n))
        (nfix n))
    :rule-classes :linear))

(define vl-maybe-merge-selects
  :short "Merge together concatenations like @('{foo[3], foo[2], foo[1]}') into
prettier expressions like @('foo[3:1]')."

  ((x      vl-exprlist-p)
   (ss     vl-scopestack-p))
  :returns (new-x vl-exprlist-p
                  :hints(("Goal" :in-theory (disable (:d vl-maybe-merge-selects))
                          :induct (vl-maybe-merge-selects x ss)
                          :expand ((vl-maybe-merge-selects x ss)))))
  :hooks ((:fix :hints(("Goal" :in-theory (disable (:d vl-maybe-merge-selects))
                          :induct (vl-maybe-merge-selects x ss)
                          :expand ((:free (ss) (vl-maybe-merge-selects x ss))
                                   (:free (ss) (vl-maybe-merge-selects (vl-exprlist-fix x) ss)))))))
  :guard-hints (("goal" :in-theory (disable vl-maybe-merge-selects
                                            (tau-system))))
  :prepwork ((local (in-theory (disable vl-expr-resolved-p-of-car-when-vl-exprlist-resolved-p
                                        vl-idexpr-p-of-car-when-vl-idexprlist-p
                                        default-car default-cdr))))
  :long "<p>Here, @('x') is a list of expressions which we assume is found
within either a concatenation or a multiple concatenation.  The @('mod') and
@('ialist') are the module and its @(see vl-make-moditem-alist) so we can look up
wires in @('x') to see their ranges.</p>

<p>Note: to make this function more effective, @('x') can be preprocessed with
@(see vl-elim-nested-concats).</p>

<p>We walk over @('x'), looking for sequences of selects that can be merged
together.  For instance, @('foo[3:1], foo[0]') could generally be merged into
@('foo[3:0]').</p>"

  :measure (vl-exprlist-count x)

  (b* (((when (atom x))
        nil)

       (expr1 (vl-expr-fix (car x)))
       ((when (vl-fast-atom-p expr1))
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       (expr1-op (vl-nonatom->op expr1))
       ((unless (or (eq expr1-op :vl-bitselect)
                    (eq expr1-op :vl-partselect-colon)))
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       ;; Else, expr is a bit or part select from some wire.  Let's see if it
       ;; is the start of a descending range.
       (expr1-args (vl-nonatom->args expr1))
       (expr1-from (first expr1-args))
       (expr1-high (second expr1-args))
       (expr1-low  (if (eq (vl-nonatom->op expr1) :vl-bitselect)
                       expr1-high
                     (third expr1-args)))

       ((unless (and (vl-idexpr-p expr1-from)
                     (vl-expr-resolved-p expr1-high)
                     (vl-expr-resolved-p expr1-low)))
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       (high-val (vl-resolved->val expr1-high))
       (low-val  (vl-resolved->val expr1-low))
       ((unless (<= low-val high-val))
        ;; We could extend this to tolerate [low:high] ranges, but for now
        ;; we'll not bother.  It's always safe to do nothing.
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       ;; Looking good: we have a bit or part select with good indicies.  Lets
       ;; see if there's anything to merge it with.
       ((mv min rest)
        (vl-maybe-merge-selects-aux (cdr x) expr1-from low-val))

       ((when (= min low-val))
        ;; There wasn't anything to merge with.
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       ;; If we get this far, we found something to merge.  But, to make sure
       ;; that merging is safe, we need to look at the net declaration for
       ;; this wire and make sure it really is a [high:low] range wire.  It
       ;; would not be legitimate, for instance, to try to merge {foo[3],
       ;; foo[2]} if foo is declared as: wire [0:5] foo.  (Verilog simulators
       ;; would complain at the syntax foo[3:2] in such a case).
       ((mv okp range)
        (vl-ss-find-range (vl-idexpr->name expr1-from) ss))
       ((unless okp)
        ;; Something is fubar.  Chicken out and don't change anything.
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       ((unless (and range
                     (vl-range-resolved-p range)
                     (>= (vl-resolved->val (vl-range->msb range))
                         (vl-resolved->val (vl-range->lsb range)))
                     (>= (vl-resolved->val (vl-range->msb range))
                         high-val)
                     (>= low-val
                         (vl-resolved->val (vl-range->lsb range)))))
        ;; Hrmn.  Maybe the wire has a "backwards" range like [0:5], or
        ;; maybe something is just totally screwed up with the input
        ;; expression.  Let's not change anything.
        (cons expr1 (vl-maybe-merge-selects (cdr x) ss)))

       ;; Else, everything seems okay.  We know it's a foo[3:0] style wire
       ;; and we've found entries from high down to min, so we'll just
       ;; collapse these exprs into a part select of foo[high:min].

       ;; Sizing this seems reasonable as long as these really are
       ;; expressions that occur within a concatenation or multiple
       ;; concatenation.  Why?  Well, if we've gotten this far, all of the
       ;; expressions we are collapsing are bit/part selects and hence they
       ;; are unsigned.  And, if we are in a concat/multiconcat, then there
       ;; is no external context to propagate into the expressions as far as
       ;; sizing goes, so we know that every bit select really will have size
       ;; 1 and every part select will have size high-low+1.
       (min-expr  (vl-make-index min))
       (new-expr1 (make-vl-nonatom :op :vl-partselect-colon
                                   :args (list expr1-from expr1-high min-expr)
                                   :finalwidth (+ 1 (- high-val low-val))
                                   :finaltype :vl-unsigned
                                   :atts nil)))
    (cons new-expr1 (vl-maybe-merge-selects rest ss))))



(defines vl-merge-consts
  :short "Consolidate concatenations of constants."

  :long "<p>@(call vl-merge-consts-aux) returns @('(mv startwidth startval
weirdval rest)').</p>

<p>Startwidth is the width of the initial sequence of constants.  If this
initial sequence involves any bits which are Z or X, then weirdval is a
vl-bitlist-p whose value is the same as the bits of this initial sequence, and
startval is nil.  Otherwise, weirdval is nil and startval is the value of the
initial sequence.  Rest is the remaining expressions, with constants
consolidated.</p>

<p>Example: Suppose we have @('{ 2'h3, 4'ha, foo[4:3], 6'h3a, 8'h10 }').
Running vl-merge-consts-aux on this yields</p>

@({
  STARTWIDTH = 6      ;; sum of widths of initial constants
  STARTVAL = 53       ;; hex 3a, value of concatenated initial constants
  WEIRDVAL = nil
  REST = { foo[4:3], 14'ha10 }
                      ;; remaining exprs, constants consolidated
})

<p>If we have @('{ 2'b1x, 4'ha, foo[4:3], 6'h3a, 8'h10 }').  Running
vl-merge-consts-aux on this yields</p>

@({
  STARTWIDTH = 6      ;; sum of widths of initial constants
  STARTVAL = nil
  WEIRDVAL = bits 1x1010
  REST = { foo[4:3], 14'ha10 }
                      ;; remaining exprs, constants consolidated
})"

  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (in-theory (disable cons-equal))))
  (define vl-merge-consts ((x vl-exprlist-p))
    :returns (new-x vl-exprlist-p)
    :measure (two-nats-measure (vl-exprlist-count x) 1)
    :verify-guards nil
    :flag :main
    (b* (((mv rest-w rest-val rest-weird rest-exprs)
          (vl-merge-consts-aux x))
         ((when (zp rest-w))
          rest-exprs)
         ((when rest-val)
          ;; constint case
          (cons (make-vl-atom :guts (make-vl-constint
                                     :origwidth rest-w
                                     :origtype :vl-unsigned
                                     :value rest-val
                                     :wasunsized nil)
                              :finalwidth rest-w
                              :finaltype :vl-unsigned)
                rest-exprs)))
      ;; weirdint case
      (cons (make-vl-atom :guts (make-vl-weirdint
                                 :origwidth rest-w
                                 :origtype :vl-unsigned
                                 :bits rest-weird
                                 :wasunsized nil)
                          :finalwidth rest-w
                          :finaltype :vl-unsigned)
            rest-exprs)))

  (define vl-merge-consts-aux ((x vl-exprlist-p))
    :returns (mv (startwidth natp :rule-classes :type-prescription)
                 (startval   maybe-natp :rule-classes :type-prescription)
                 (weirdval   vl-bitlist-p)
                 (rest       vl-exprlist-p))
    :measure (two-nats-measure (vl-exprlist-count x) 0)
    :flag :aux
    (b* (((when (atom x))
          (mv 0 0 nil nil))

         (expr1 (vl-expr-fix (car x)))
         ((unless (and (vl-fast-atom-p expr1)
                       (let ((guts (vl-atom->guts expr1)))
                         (or (vl-fast-constint-p guts)
                             (vl-fast-weirdint-p guts)))))
          ;; the first expression is not a constant, so get the rest as exprs
          ;; and cons on expr1
          (mv 0 0 nil (cons expr1 (vl-merge-consts (cdr x)))))

         ;; process the rest
         ((mv rest-w rest-val rest-weird rest-exprs)
          (vl-merge-consts-aux (cdr x)))

         (guts (vl-atom->guts expr1))
         ((when (vl-fast-constint-p guts))
          (b* (((vl-constint guts) guts)
               ((when rest-val)
                ;; concatenate (with ash/+) the values, add the widths
                (mv (+ guts.origwidth rest-w)
                    (+ (ash guts.value rest-w) rest-val)
                    nil rest-exprs))
               ;; the rest starts with a weirdint, so we need to transform
               ;; this value into bits and append them on
               (bits (vl-bitlist-from-nat guts.value guts.origwidth))
               (all-bits (append bits rest-weird)))
            (mv (+ guts.origwidth rest-w)
                nil all-bits rest-exprs)))

         ;; otherwise expr1 is a weirdint.  append its bits to those from the
         ;; initial expr.
         ((vl-weirdint guts) guts)
         ((when (zp rest-w))
          ;; optimization; don't bother appending stuff
          (mv guts.origwidth nil guts.bits rest-exprs))
         ((when rest-val)
          (b* ((rest-bits (vl-bitlist-from-nat rest-val rest-w)))
            (mv (+ rest-w guts.origwidth)
                nil
                (append-without-guard guts.bits rest-bits)
                rest-exprs))))
      (mv (+ rest-w guts.origwidth)
          nil
          (append-without-guard guts.bits rest-weird)
          rest-exprs)))
  ///
  (local (in-theory (disable vl-merge-consts-aux
                             vl-merge-consts)))
  (defthm-vl-merge-consts-flag
    (defthm true-listp-of-vl-merge-consts-aux->exprs
      (true-listp (mv-nth 3 (vl-merge-consts-aux x)))
      :rule-classes :type-prescription
      :hints ('(:expand ((vl-merge-consts-aux x))))
      :flag :aux)
    (defthm true-listp-of-vl-merge-consts->exprs
      (true-listp (vl-merge-consts x))
      :hints ('(:expand ((vl-merge-consts x))))
      :rule-classes :type-prescription
      :flag :main))

  (local (defthm arith-lemma
           (implies (and (natp v)
                         (natp v-cap)
                         (natp w)
                         (natp w-cap)
                         (< v v-cap)
                         (< w w-cap))
                    (< (+ w (* v w-cap))
                       (* v-cap w-cap)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))


  (defthm-vl-merge-consts-flag
    (defthm vl-merge-consts-aux-invar
      (b* (((mv width val bits ?exprs) (vl-merge-consts-aux x)))
        (and (implies val (not bits))
             (implies (not val)
                      (equal (len bits) width))
             (implies val
                      (< val (expt 2 width)))))
      :hints ('(:expand ((vl-merge-consts-aux x)))
              (and stable-under-simplificationp
                   '(:in-theory (enable ash floor))))
      :flag :aux)
    :skip-others t)

  (verify-guards vl-merge-consts)

  (deffixequiv-mutual vl-merge-consts
    :hints ((and stable-under-simplificationp
                 '( :expand ((vl-merge-consts-aux x)
                             (vl-merge-consts-aux (vl-exprlist-fix x))
                             (vl-merge-consts x)
                             (vl-merge-consts (vl-exprlist-fix x))))))))


(define vl-spurious-concatenation-p
  :parents (vl-expr-clean-concats)
  :short "Determine if a concatenation such as @('{foo}') can be safely
rewritten to just @('foo')."
  ((arg vl-expr-p "The argument to the concatenation.")
   (ss  vl-scopestack-p "the scope stack we're in"))
  :returns (spurious-p booleanp :rule-classes :type-prescription)

  :long "<p>In early implementations of @(see vl-expr-clean-concats), we
looked for singleton concatenations like @('{foo}') and replaced them with
@('foo').</p>

<p>Unfortunately, it's tricky to safely do this before sizing has been done.
For instance, if we replace @('{a+b}') with just @('a+b'), then we've lost the
fact that @('a+b') should be self-determined.  In general this wouldn't be safe
and could screw things up.</p>

<p>However, we found that we still wanted to carry out this reduction in places
where it <i>is</i> safe.  For instance, it seems okay to do this in the special
cases of bit- and part-selects: these expressions are always unsigned and,
e.g., there is no difference between extending @('{foo[3]}') and @('foo[3]'),
since a zero-extension is necessary in either case.</p>

<p>As an additional tweak, which we wanted for a particular VL-Mangle project,
we now also permit @('arg') to be an unsigned constint, weirdint, or identifier
atom (if it is the name of an unsigned net or register.)</p>"

  (if (vl-fast-atom-p arg)
      (b* ((guts (vl-atom->guts arg))
           ((when (vl-fast-constint-p guts))
            (equal (vl-constint->origtype guts) :vl-unsigned))
           ((when (vl-fast-weirdint-p guts))
            (equal (vl-weirdint->origtype guts) :vl-unsigned))
           ((unless (vl-fast-id-p guts))
            ;; Other things might be okay too, but for now we don't care.
            nil)
           (look (vl-scopestack-find-item (vl-id->name guts) ss))
           ((unless (and look
                         (eq (tag look) :vl-vardecl)
                         (vl-simplevar-p look)))
            nil))
        (not (vl-simplevar->signedp look)))
    (or (eq (vl-nonatom->op arg) :vl-bitselect)
        (eq (vl-nonatom->op arg) :vl-partselect-colon)
        ;; It would probably be fine to extend this with other operators
        ;; as long as they are unsigned and self-determined.
        )))


(defines vl-expr-clean-concats

  (define vl-expr-clean-concats
    :short "Flatten concatenations and try to merge adjacent, compatible wires
within them into larger part-selects."

    ((x   vl-expr-p   "Any expression that occurs in the module @('mod')")
     (ss  vl-scopestack-p "Containing scope stack."))
    :returns (new-x vl-expr-p "Perhaps simplified version of X.")

    :long "<p>We try to simplify the concatenations within @('x'), by
flattening out nested concatenations and merging concatenations like
@('{foo[3:1], foo[0]}') into selects like @('foo[3:0]').</p>"

    :measure (vl-expr-count x)
    :verify-guards nil
    (b* (((when (vl-fast-atom-p x))
          (vl-expr-fix x))
         (op         (vl-nonatom->op x))
         (args       (vl-nonatom->args x))

         ((unless (eq op :vl-concat))
          ;; Not a concat, just recursively clean its args.
          (change-vl-nonatom x :args (vl-exprlist-clean-concats args ss)))

         ;; Else, it is a concat.
         (args (vl-exprlist-clean-concats args ss)) ;; do this first for easy termination argument
         (args (vl-elim-nested-concats args))
         (args (vl-maybe-merge-selects args ss))
         (args (vl-merge-consts args))

         ((when (and (eql (length args) 1)
                     (vl-spurious-concatenation-p (car args) ss)))
          ;; Safe to rewrite this singleton concatenation from {arg} --> arg
          (car args)))
      (change-vl-nonatom x :args args)))

  (define vl-exprlist-clean-concats ((x      vl-exprlist-p)
                                     (ss     vl-scopestack-p))
    :measure (vl-exprlist-count x)
    :returns (new-x (and (vl-exprlist-p new-x)
                         (equal (len new-x) (len x))))
     (if (atom x)
         nil
       (cons (vl-expr-clean-concats (car x) ss)
             (vl-exprlist-clean-concats (cdr x) ss))))
  ///
  (defprojection vl-exprlist-clean-concats (x ss)
    (vl-expr-clean-concats x ss)
    :already-definedp t)

  (verify-guards vl-expr-clean-concats)
  (deffixequiv-mutual vl-expr-clean-concats))


(with-output :off (prove)
  (defines vl-expr-clean-selects1
    :short "Core routine behind @(see vl-expr-clean-selects)."
    :prepwork ((local (in-theory (disable default-car default-cdr not))))
    (define vl-expr-clean-selects1 ((x      vl-expr-p)
                                    (ss     vl-scopestack-p))
      :returns (new-x vl-expr-p)
      :measure (vl-expr-count x)
      :verify-guards nil
      :flag :expr
      (b* (((when (vl-fast-atom-p x))
            (vl-expr-fix x))

           ((vl-nonatom x) x)
           (args (vl-exprlist-clean-selects1 x.args ss))

           ;; To handle bit- and part-selects in the same way, we now treat
           ;; bit-selects like foo[3] as foo[3:3] and extract the name (as a
           ;; string), and the msb/lsb (as naturals).

           ((mv name sel-msb sel-lsb)
            (cond ((eq x.op :vl-bitselect)
                   (b* (((list from bit) args))
                     (if (and (vl-idexpr-p from)
                              (vl-expr-resolved-p bit))
                         (mv (vl-idexpr->name from)
                             (vl-resolved->val bit)
                             (vl-resolved->val bit))
                       (mv nil nil nil))))
                  ((eq x.op :vl-partselect-colon)
                   (b* (((list from msb lsb) args))
                     (if (and (vl-idexpr-p from)
                              (vl-expr-resolved-p msb)
                              (vl-expr-resolved-p lsb))
                         (mv (vl-idexpr->name from)
                             (vl-resolved->val msb)
                             (vl-resolved->val lsb))
                       (mv nil nil nil))))
                  (t
                   (mv nil nil nil))))

           ((unless name)
            ;; Not something we can simplify further, just update the args.
            (change-vl-nonatom x :args args))

           ;; It's important that the declaration is of an unsigned wire.  Note
           ;; that in Verilog, foo[3:0] is always unsigned.  So it's not
           ;; generally sound to replace foo[3:0] with foo when we have "wire
           ;; signed [3:0] foo", because the replacement expression "foo" would
           ;; now be signed, whereas the original was unsigned.
           (decl (vl-scopestack-find-item name ss))
           ((mv decl-okp range)
            (if (and decl
                     (eq (tag decl) :vl-vardecl)
                     (vl-simplevar-p decl)
                     (not (vl-simplevar->signedp decl)))
                (mv t (vl-simplevar->range decl))
              (mv nil nil)))

           ((unless (and decl-okp (vl-maybe-range-resolved-p range)))
            ;; The declaration is too complex for us to really try to simplify any
            ;; selects to it, so don't try to simplify, just update the args.
            (change-vl-nonatom x :args args))

           (range-msb (if range (vl-resolved->val (vl-range->msb range)) 0))
           (range-lsb (if range (vl-resolved->val (vl-range->lsb range)) 0))
           ((when (and (eql sel-msb range-msb)
                       (eql sel-lsb range-lsb)))
            ;; Success: we have just found foo[msb:lsb] where the wire's declaration is
            ;; of foo[msb:lsb].  Drop the select.
            (first args)))

        ;; Else, we found some other kind of select, e.g., maybe we found foo[3:0] but
        ;; the declaration is foo[5:0].  Don't simplify anything.
        (change-vl-nonatom x :args args)))

    (define vl-exprlist-clean-selects1 ((x      vl-exprlist-p)
                                        (ss     vl-scopestack-p))
      :returns (new-x (and (vl-exprlist-p new-x)
                           (equal (len new-x) (len x))))
      :measure (vl-exprlist-count x)
      :flag :list
      (if (atom x)
          nil
        (cons (vl-expr-clean-selects1 (car x) ss)
              (vl-exprlist-clean-selects1 (cdr x) ss))))
    ///

    (defprojection vl-exprlist-clean-selects1 (x ss)
      (vl-expr-clean-selects1 x ss)
      :already-definedp t)

    ;; BOZO I don't really understand why these cause problems for the guard proof.
    (local (in-theory (disable vl-expr-clean-selects1
                               vl-exprlist-clean-selects1)))

    (deffixequiv-mutual vl-expr-clean-selects1
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (ss) (vl-expr-clean-selects1 x ss))
                              (:free (ss) (vl-expr-clean-selects1 (vl-expr-fix x) ss))
                              (:free (ss) (vl-exprlist-clean-selects1 x ss))
                              (:free (ss) (vl-exprlist-clean-selects1 (vl-exprlist-fix x) ss)))))))

    (verify-guards vl-exprlist-clean-selects1)))


(define vl-expr-clean-selects
  :short "Simplify concatenations and selects in an expression."

  ((x      vl-expr-p        "An expression that occurs somewhere in @('mod').")
   (ss     vl-scopestack-p  "Containing scope stack."))
  :returns
  (new-x vl-expr-p "Simplified version of @('x').")

  :long "<p>We try to simplify @('x') in a fairly advanced way, and return the
simplified expression @('x'').  There are two phases to the simplification:</p>

<ul>

<li>We clean up the concatenations using @(see vl-expr-clean-concats), in order
to eliminate nested concatenations and merge together expressions like
@('{foo[3:1], foo[0]}') info @('foo[3:0]').</li>

<li>We walk over the reduced expression, trying to notice any unnecessary
selects, e.g., if we have @('wire [3:0] w'), then we will replace occurrences
of @('w[3:0]') with just @('w').</li>

</ul>"

  (vl-expr-clean-selects1 (vl-expr-clean-concats x ss)
                          ss))

(defprojection vl-exprlist-clean-selects ((x      vl-exprlist-p)
                                          (ss     vl-scopestack-p))
  :returns (new-x (and (vl-exprlist-p new-x)
                       (equal (len new-x) (len x))))
  (vl-expr-clean-selects x ss))


#||

Testing the constant consolidation....


(include-book
 "../loader/lexer")
(include-book
 "../loader/parse-expressions")
(include-book
 "fmt")

(defun cleaned-version (str)
  (b* (((mv erp val tokens ?warnings)
        (vl-parse-expression (make-test-tokens str) nil))
       ((when erp) "parse error")
       ((when tokens) "extra tokens")
       (empty-mod (make-vl-module :name "fake"
                                  :minloc *vl-fakeloc*
                                  :maxloc *vl-fakeloc*
                                  :origname "fake"))
       (clean (vl-expr-clean-concats val empty-mod (vl-make-moditem-alist empty-mod))))
    (with-local-ps
      (vl-cw "Orig:  ~a0~%Clean: ~a1~%" val clean))))

(cleaned-version "{ 2'h3, 4'ha, foo[4:3], 6'h3a, 8'h10 }")
(cleaned-version "{ 2'b1x, 4'ha, foo[4:3], 1'bz, 6'h3a, 8'h10 }")

||#
