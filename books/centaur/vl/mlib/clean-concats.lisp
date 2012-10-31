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
(include-book "expr-tools")
(include-book "range-tools")
(local (include-book "../util/arithmetic"))


(defxdoc expr-cleaning
  :parents (mlib)
  :short "Functions for cleaning up ugly expressions.")


(defsection vl-elim-nested-concats
  :parents (expr-cleaning)
  :short "Flatten out nested concatenations like @('{a, b, {c, d}, { { e, f }
  }}') into @('{a, b, c, d, e, f}')."

  :long "<p>@(call vl-elim-nested-concats) is given @('x'), a list of
expressions which we assume are the arguments to a concatenation.  We flatten
out any top-level nested concatenations in @('x'), and return the possibly
simplified list of expressions.</p>

<p>This may help @(see vl-maybe-merge-selects) to be more effective.  For
instance, with the help of flattening, it can merge selects such as:</p>

@({{foo[3], {foo[2], foo[1]}, foo[0]}})"

  (defund vl-elim-nested-concats-pass (x)
    "Returns (MV PROGRESSP X-PRIME)"
    (declare (xargs :guard (vl-exprlist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv cdr-progressp cdr-prime)
          (vl-elim-nested-concats-pass (cdr x)))
         (expr1 (car x))
         ((unless (and (not (vl-fast-atom-p expr1))
                       (eq (vl-nonatom->op expr1) :vl-concat)))
          (mv cdr-progressp (cons expr1 cdr-prime)))

         ;; Else, we found a concat.  Eliminate it.
         (args (vl-nonatom->args expr1)))
        (mv t (append-without-guard args cdr-prime))))

  (defmvtypes vl-elim-nested-concats-pass (booleanp true-listp))

  (local (in-theory (enable vl-elim-nested-concats-pass)))

  (defthm vl-exprlist-p-of-vl-elim-nested-concats-pass
    (implies (vl-exprlist-p x)
             (vl-exprlist-p (mv-nth 1 (vl-elim-nested-concats-pass x)))))

  (defthm acl2-count-of-vl-elim-nested-concats-pass-weak
    (<= (acl2-count (mv-nth 1 (vl-elim-nested-concats-pass x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :in-theory (enable acl2-count))))

  (defthm acl2-count-of-vl-elim-nested-concats-pass-strong
    (implies (mv-nth 0 (vl-elim-nested-concats-pass x))
             (< (acl2-count (mv-nth 1 (vl-elim-nested-concats-pass x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :in-theory (enable acl2-count))))

  (local (in-theory (disable vl-elim-nested-concats-pass)))


  (defund vl-elim-nested-concats (x)
    (declare (xargs :guard (vl-exprlist-p x)))


    (b* (((mv progressp x-prime)
          (vl-elim-nested-concats-pass x)))
        (if progressp
            (vl-elim-nested-concats x-prime)
          x-prime)))

  (local (in-theory (enable vl-elim-nested-concats)))

  (defthm true-listp-of-vl-elim-nested-concats
    (true-listp (vl-elim-nested-concats x))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-elim-nested-concats
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-elim-nested-concats x)))))



(defsection vl-maybe-merge-selects-aux
  :parents (expr-cleaning)
  :short "Identify a sequence of decreasing bit- and part-selects."

  :long "<p>@(call vl-maybe-merge-selects-aux) returns @('(mv min rest)').</p>

<p>We look for a sequence of decreasing bit- and part- selects that count
downward from @('from[n]').</p>

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

  (defund vl-maybe-merge-selects-aux (x from n)
    "Returns (MIN REST)"
    (declare (xargs :guard (and (vl-exprlist-p x)
                                (vl-expr-p from)
                                (natp n))))
    (b* (((when (atom x))
          (mv n x))

         (expr1 (car x))
         ((unless (and (not (vl-fast-atom-p expr1))
                       (or (eq (vl-nonatom->op expr1) :vl-bitselect)
                           (eq (vl-nonatom->op expr1) :vl-partselect-colon))))
          (mv n x))

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
          (mv n x))

         (high-val (vl-resolved->val expr1-high))
         (low-val  (vl-resolved->val expr1-low))
         ((unless (and (natp high-val)
                       (natp low-val)
                       (= high-val (- n 1))
                       (<= low-val high-val)))
          (mv n x)))

      ;; If we get this far, expr1 is from[n-1] or from[n-1:low].  Let's
      ;; keep looking for more to merge after low-val.
      (vl-maybe-merge-selects-aux (cdr x) from low-val)))

  (local (in-theory (enable vl-maybe-merge-selects-aux)))

  (defthm natp-of-vl-maybe-merge-selects-aux
    (implies (force (natp n))
             (natp (mv-nth 0 (vl-maybe-merge-selects-aux x from n))))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-maybe-merge-selects-aux
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))))

  (defthm acl2-count-of-vl-maybe-merge-selects-aux-weak
    (<= (acl2-count (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-maybe-merge-selects-aux-strong
    (implies (not (equal n (mv-nth 0 (vl-maybe-merge-selects-aux x from n))))
             (< (acl2-count (mv-nth 1 (vl-maybe-merge-selects-aux x from n)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm upper-bound-of-vl-maybe-merge-selects-aux
    (implies (force (natp n))
             (<= (mv-nth 0 (vl-maybe-merge-selects-aux x from n))
                 n))
    :rule-classes :linear))



(defsection vl-maybe-merge-selects
  :parents (expr-cleaning)
  :short "Merge together concatenations like @('{foo[3], foo[2], foo[1]}') into
prettier expressions like @('foo[3:1]')."

  :long "<p><b>Signature:</b> @(call vl-maybe-merge-selects) returns
@('x'').</p>

<p>Here, @('x') is a list of expressions which we assume is found within either
a concatenation or a multiple concatenation.  The @('mod') and @('ialist') are
the module and its @(see vl-moditem-alist) so we can look up wires in @('x') to
see their ranges.</p>

<p>Note: to make this function more effective, @('x') can be preprocessed with
@(see vl-elim-nested-concats).</p>

<p>We walk over @('x'), looking for sequences of selects that can be merged
together.  For instance, @('foo[3:1], foo[0]') could generally be merged into
@('foo[3:0]').</p>"

  (local (in-theory (enable vl-maybe-natp)))

  (defund vl-maybe-merge-selects (x mod ialist)
    (declare (xargs :guard (and (vl-exprlist-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))))
    (b* (((when (atom x))
          nil)

         (expr1 (car x))
         ((when (vl-fast-atom-p expr1))
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

         (expr1-op (vl-nonatom->op expr1))
         ((unless (or (eq expr1-op :vl-bitselect)
                      (eq expr1-op :vl-partselect-colon)))
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

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
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

         (high-val (vl-resolved->val expr1-high))
         (low-val  (vl-resolved->val expr1-low))
         ((unless (<= low-val high-val))
          ;; We could extend this to tolerate [low:high] ranges, but for now
          ;; we'll not bother.  It's always safe to do nothing.
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

         ;; Looking good: we have a bit or part select with good indicies.  Lets
         ;; see if there's anything to merge it with.
         ((mv min rest)
          (vl-maybe-merge-selects-aux (cdr x) expr1-from low-val))

         ((when (= min low-val))
          ;; There wasn't anything to merge with.
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

         ;; If we get this far, we found something to merge.  But, to make sure
         ;; that merging is safe, we need to look at the net declaration for
         ;; this wire and make sure it really is a [high:low] range wire.  It
         ;; would not be legitimate, for instance, to try to merge {foo[3],
         ;; foo[2]} if foo is declared as: wire [0:5] foo.  (Verilog simulators
         ;; would complain at the syntax foo[3:2] in such a case).
         ((mv okp range)
          (vl-find-net/reg-range (vl-idexpr->name expr1-from) mod ialist))
         ((unless okp)
          ;; Something is fubar.  Chicken out and don't change anything.
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

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
          (cons expr1 (vl-maybe-merge-selects (cdr x) mod ialist)))

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
      (cons new-expr1 (vl-maybe-merge-selects rest mod ialist))))

  (local (in-theory (enable vl-maybe-merge-selects)))

  (defthm vl-exprlist-p-of-vl-maybe-merge-selects
    (implies (force (vl-exprlist-p x))
             (vl-exprlist-p (vl-maybe-merge-selects x mod ialist)))))



(defsection vl-expr-clean-concats
  :parents (expr-cleaning)
  :short "Flatten concatenations and try to merge adjacent, compatible wires
within them into larger part-selects."

  :long "<p><b>Signature:</b> @(call vl-expr-clean-concats) returns
@('x'').</p>

<p>Here, @('x') is any expression that occurs in the module @('mod'), and
@('ialist') is the @(see vl-moditem-alist) for @('mod') so that we can quickly
look up wires to ensure that our simplifications are sound.</p>

<p>We try to simplify the concatenations within @('x'), by flattening out
nested concatenations and merging concatenations like @('{foo[3:1], foo[0]}')
into selects like @('foo[3:0]').</p>

<p>We return a new expression, @('x''), which is semantically equal to @('x')
but may be aesthetically better.</p>"

  (mutual-recursion

   (defund vl-expr-clean-concats (x mod ialist)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (b* (((when (vl-fast-atom-p x))
           x)
          (op         (vl-nonatom->op x))
          (args       (vl-nonatom->args x))

          ((unless (eq op :vl-concat))
           ;; Not a concat, just recursively clean its args.
           (change-vl-nonatom x :args (vl-exprlist-clean-concats args mod ialist)))

          ;; Else, it is a concat.
          (args (vl-exprlist-clean-concats args mod ialist)) ;; do this first for easy termination argument
          (args (vl-elim-nested-concats args))
          (args (vl-maybe-merge-selects args mod ialist))

          ;; Historically we looked for singleton concatenations like {a} here,
          ;; and replaced them with just a.  It's tricky to safely do this
          ;; before sizing has been done, because for instance if we replace
          ;; {a+b} with just a+b then we've lost the fact that a+b should be
          ;; self-determined.  But it seems okay to do this in the special
          ;; cases of bit- and part-selects, since they must be unsigned and
          ;; there is no difference between extending {foo[3]} and foo[3] -- a
          ;; zero-extension is necessary in either case.
          ((when (and (= (length args) 1)
                      (vl-nonatom-p (car args))
                      (or (eq (vl-nonatom->op (car args)) :vl-bitselect)
                          (eq (vl-nonatom->op (car args)) :vl-partselect-colon))))
           (car args)))
       (change-vl-nonatom x :args args)))

   (defund vl-exprlist-clean-concats (x mod ialist)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-expr-clean-concats (car x) mod ialist)
             (vl-exprlist-clean-concats (cdr x) mod ialist)))))

  (defthm vl-exprlist-clean-concats-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-clean-concats x mod ialist)
                    nil))
    :hints(("Goal" :in-theory (enable vl-exprlist-clean-concats))))

  (defthm vl-exprlist-clean-concats-of-cons
    (equal (vl-exprlist-clean-concats (cons a x) mod ialist)
           (cons (vl-expr-clean-concats a mod ialist)
                 (vl-exprlist-clean-concats x mod ialist)))
    :hints(("Goal" :in-theory (enable vl-exprlist-clean-concats))))

  (defprojection vl-exprlist-clean-concats (x mod ialist)
    (vl-expr-clean-concats x mod ialist)
    :already-definedp t)

  (flag::make-flag vl-flag-expr-clean-concats
                   vl-expr-clean-concats
                   :flag-mapping ((vl-expr-clean-concats . expr)
                                  (vl-exprlist-clean-concats . list)))

  (defthm-vl-flag-expr-clean-concats lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (vl-expr-clean-concats x mod ialist)))
          :name vl-expr-p-of-vl-expr-clean-concats)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (vl-exprlist-clean-concats x mod ialist)))
          :name vl-exprlist-p-of-vl-exprlist-clean-concats)
    :hints(("Goal"
            :induct (vl-flag-expr-clean-concats flag x mod ialist)
            :in-theory (enable vl-expr-clean-concats))))

  (verify-guards vl-expr-clean-concats))



(defsection vl-expr-clean-selects1
  :parents (expr-cleaning)
  :short "Core routine behind @(see vl-expr-clean-selects)."

  (mutual-recursion

   (defund vl-expr-clean-selects1 (x mod ialist)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (vl-expr-count x)
                     :verify-guards nil))
     (b* (((when (vl-fast-atom-p x))
           x)

          ((vl-nonatom x) x)
          (args (vl-exprlist-clean-selects1 x.args mod ialist))

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
          (decl (vl-fast-find-moduleitem name mod ialist))
          ((mv decl-okp range)
           (case (tag decl)
             (:vl-netdecl (mv (not (vl-netdecl->signedp decl)) (vl-netdecl->range decl)))
             (:vl-regdecl (mv (not (vl-regdecl->signedp decl)) (vl-regdecl->range decl)))
             (otherwise (mv nil nil))))

          ((unless (and decl-okp (vl-maybe-range-resolved-p range)))
           ;; The declaration is too complex for us to really try to simplify any
           ;; selects to it, so don't try to simplify, just update the args.
           (change-vl-nonatom x :args args))

          (range-msb (if range (vl-resolved->val (vl-range->msb range)) 0))
          (range-lsb (if range (vl-resolved->val (vl-range->lsb range)) 0))
          ((when (and (= sel-msb range-msb)
                      (= sel-lsb range-lsb)))
           ;; Success: we have just found foo[msb:lsb] where the wire's declaration is
           ;; of foo[msb:lsb].  Drop the select.
           (first args)))

       ;; Else, we found some other kind of select, e.g., maybe we found foo[3:0] but
       ;; the declaration is foo[5:0].  Don't simplify anything.
       (change-vl-nonatom x :args args)))

   (defund vl-exprlist-clean-selects1 (x mod ialist)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (equal ialist (vl-moditem-alist mod)))
                     :measure (vl-exprlist-count x)))
     (if (atom x)
         nil
       (cons (vl-expr-clean-selects1 (car x) mod ialist)
             (vl-exprlist-clean-selects1 (cdr x) mod ialist)))))

  (defthm true-listp-of-vl-exprlist-clean-selects1
    (true-listp (vl-exprlist-clean-selects1 x mod ialist))
    :rule-classes :type-prescription
    :hints(("Goal"
            :induct (len x)
            :expand (vl-exprlist-clean-selects1 x mod ialist))))

  (defthm len-of-vl-exprlist-clean-selects1
    (equal (len (vl-exprlist-clean-selects1 x mod ialist))
           (len x))
    :hints(("Goal" :induct (len x)
            :expand (vl-exprlist-clean-selects1 x mod ialist))))

  (defthm vl-exprlist-clean-selects1-under-iff
    (iff (vl-exprlist-clean-selects1 x mod ialist)
         (consp x))
    :hints(("Goal" :induct (len x)
            :expand (vl-exprlist-clean-selects1 x mod ialist))))

  (flag::make-flag vl-flag-expr-clean-selects
                   vl-expr-clean-selects1
                   :flag-mapping ((vl-expr-clean-selects1 . expr)
                                  (vl-exprlist-clean-selects1 . list)))

  (defthm-vl-flag-expr-clean-selects
    (defthm vl-expr-p-of-vl-expr-clean-selects1
      (implies (and (force (vl-expr-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-expr-p (vl-expr-clean-selects1 x mod ialist)))
      :flag expr)

    (defthm vl-exprlist-p-of-vl-exprlist-clean-selects1
      (implies (and (force (vl-exprlist-p x))
                    (force (vl-module-p mod))
                    (force (equal ialist (vl-moditem-alist mod))))
               (vl-exprlist-p (vl-exprlist-clean-selects1 x mod ialist)))
      :flag list)

    :hints(("Goal"
            :expand ((vl-expr-clean-selects1 x mod ialist)
                     (vl-exprlist-clean-selects1 x mod ialist)))))


; BOZO gross horribly yucky rules.  These solve the problem but are really slow
; and terrible looking.  We need a better way to deal with this kind of arity
; reasoning.  I'd like to only need to prove the
; len-of-vl-exprlist-clean-selects1 rule, and have it be able to figure out the
; rest.

  (local (defthm cdr-by-len-under-iff
           (implies (<= 2 (len x))
                    (cdr x))
           :hints(("Goal" :expand ((len x))))))

  (local (defthm cddr-by-len-under-iff
           (implies (<= 3 (len x))
                    (cddr x))
           :hints(("Goal"
                   :expand ((len x)
                            (len (cdr x)))))))

  (local (defthm car-by-len-when-vl-exprlist-p
           (implies (and (<= 1 (len x))
                         (vl-exprlist-p x))
                    (first x))))

  (local (defthm second-by-len-when-vl-exprlist-p
           (implies (and (<= 2 (len x))
                         (vl-exprlist-p x))
                    (second x))))

  (local (defthm third-by-len-when-vl-exprlist-p
           (implies (and (<= 3 (len x))
                         (vl-exprlist-p x))
                    (third x))))

  (verify-guards vl-exprlist-clean-selects1))



(defsection vl-expr-clean-selects
  :parents (expr-cleaning)
  :short "Simplify concatenations and selects in an expression."

  :long "<p><b>Signature:</b> @(call vl-expr-clean-selects) returns
@('x'').</p>

<p>We are given @('x'), an expression that occurs within the module @('mod'),
and @('ialist'), the @(see vl-moditem-alist) for @('mod').</p>

<p>We try to simplify @('x') in a fairly advanced way, and return the
simplified expression @('x'').  There are two phases to the simplification:</p>

<ul>

<li>We clean up the concatenations using @(see vl-expr-clean-concats), in order
to eliminate nested concatenations and merge together expressions like
@('{foo[3:1], foo[0]}') info @('foo[3:0]').</li>

<li>We walk over the reduced expression, trying to notice any unnecessary
selects, e.g., if we have @('wire [3:0] w'), then we will replace occurrences
of @('w[3:0]') with just @('w').</li>

</ul>"

  (defund vl-expr-clean-selects (x mod ialist)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-module-p mod)
                                (equal ialist (vl-moditem-alist mod)))))
    (vl-expr-clean-selects1 (vl-expr-clean-concats x mod ialist)
                            mod ialist))

  (local (in-theory (enable vl-expr-clean-selects)))

  (defthm vl-expr-p-of-vl-expr-clean-selects
    (implies (and (force (vl-expr-p x))
                  (force (vl-module-p mod))
                  (force (equal ialist (vl-moditem-alist mod))))
             (vl-expr-p (vl-expr-clean-selects x mod ialist)))))


(defprojection vl-exprlist-clean-selects (x mod ialist)
  (vl-expr-clean-selects x mod ialist)
  :guard (and (vl-exprlist-p x)
              (vl-module-p mod)
              (equal ialist (vl-moditem-alist mod)))
  :result-type vl-exprlist-p
  :parents (expr-cleaning))

