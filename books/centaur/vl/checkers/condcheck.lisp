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
(include-book "duplicate-detect")
(local (include-book "../util/arithmetic"))


(defxdoc condcheck
  :parents (checkers)
  :short "Check for <tt>?:</tt>-expressions with strange conditions."

  :long "<p>This is a heuristic for generating warnings.  We look for things
like the following, except that we target the <tt>?:</tt> operator instead of
<tt>if</tt> statements.</p>

<code>
    if A { ... }
    else if B { ... }
    else if A { ... }   // already checked A above, so this is unreachable
    else if C { ... }
    else ...
</code>

<p>And also things like:</p>

<code>
    if A { ... }
    else if B { ... }
    else if !A { ... }   // already checked A above, so this is just true
    else if C { ... }
    else ...
</code>

<p>And for <tt>if(constant) {...}</tt>.</p>

<p>All of this could be adapted to <tt>if</tt> statements too, but we target
the <tt>?:</tt> operator because we care a lot less about procedural code (like
test benches) than we do about the actual hardware modules.  Note that the
@(see qmarksize-check) can also be used for some additional checking on
<tt>?:</tt> operators, but it tries to identify a different class of
problems.</p>

<p>Since this is just a heuristic and it is completely unrelated to soundness,
we feel justified in doing a couple of seemingly unsound things.  In
particular, we basically ignore widths of test expressions and treat <tt>!</tt>
and <tt>~</tt> as equivalent.  We also treat <tt>^</tt> as <tt>!=</tt> and
<tt>~^</tt> as <tt>==</tt>.  This is completely wrong in general, but it makes
sense if you assume that the tests are all going to be one-bit wide.</p>

<p>This check has no prerequisites and can in principle be run at any time.
But it is probably best to run it very early before throwing things out, and it
should probably be run before @(see oprewrite), which screws around with
conditional expressions, and also before things like expression splitting which
would get rid of the nested branches.</p>")


(defsection vl-condcheck-fix
  :parents (condcheck)
  :short "Canonicalize an test expression for condcheck."

  :long "<p>We fix X (in the normal sense of @(see vl-expr-fix), to throw away
widths, attributes, etc., to facilitate equality checking), and then do certain
kinds of not-necessarily-sound rewriting to try to further canonicalize things.
These rewrites might possibly help us recognize a broader class of errors, but
probably aren't super important.</p>

<code>
    !A     --&gt; ~A               unsound, but sort of valid for one-bit ops

    A != B --&gt; ~(A == B)        and we sort the args
    A ~^ B --&gt; A == B           unsound, but sort of valid for one-bit ops
    A ^ B  --&gt; ~(A == B)        unsound, but sort of valid for one-bit ops

    A &lt; B  --&gt; ~(A &gt;= B)
    A &gt; B  --&gt; ~(B &gt;= A)
    A &lt;= B --&gt; B &gt;= A
</code>

<p>We also put arguments of commutative operators into @(see <<) order.  Note
that we only apply these rewrites at the top-level and not in any deep way,
which also sort of makes sense since we only want to assume that the top-level
expression is one-bit wide.</p>"

  (defund vl-condcheck-fix (x)
    (declare (xargs :guard (vl-expr-p x)))
    (b* ((x (vl-expr-fix x))

         ((when (vl-fast-atom-p x))
          x)

         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))

         ;; !A --> ~A
         ((when (eq op :vl-unary-lognot))
          (change-vl-nonatom x :op :vl-unary-bitnot))

         ;; A != B --> ~(A == B)
         ((when (eq op :vl-binary-neq))
          (make-vl-nonatom :op :vl-unary-bitnot
                           :args (list (change-vl-nonatom x
                                                          :op :vl-binary-eq
                                                          :args (if (<< (first args) (second args))
                                                                    args
                                                                  (rev args))))))

         ;; A ~^ B --> A == B
         ((when (eq op :vl-binary-xnor))
          (change-vl-nonatom x
                             :op :vl-binary-eq
                             :args (if (<< (first args) (second args))
                                       args
                                     (rev args))))

         ;; A ^ B --> ~(A == B)
         ((when (eq op :vl-binary-xor))
          (make-vl-nonatom :op :vl-unary-bitnot
                           :args (list (change-vl-nonatom x
                                                          :op :vl-binary-eq
                                                          :args (if (<< (first args) (second args))
                                                                    args
                                                                  (rev args))))))

         ;; A < B  --> ~(A >= B)
         ((when (eq op :vl-binary-lt))
          (make-vl-nonatom :op :vl-unary-bitnot
                           :args (list (change-vl-nonatom x :op :vl-binary-gte))))

         ;; A > B  --> ~(B >= A)
         ((when (eq op :vl-binary-gt))
          (make-vl-nonatom :op :vl-unary-bitnot
                           :args (list (change-vl-nonatom x
                                                          :op :vl-binary-gte
                                                          :args (rev args)))))

         ;; A <= B --> B >= A
         ((when (eq op :vl-binary-lte))
          (change-vl-nonatom x
                             :op :vl-binary-gte
                             :args (rev args)))

         ((when (member op '(:vl-binary-plus :vl-binary-times
                                             :vl-binary-ceq :vl-binary-cne
                                             :vl-binary-logand :vl-binary-logor
                                             :vl-binary-bitand :vl-binary-bitor)))
          (change-vl-nonatom x :args (if (<< (first args) (second args))
                                         args
                                       (rev args)))))

      x))

  (defthm vl-expr-p-of-vl-condcheck-fix
    (implies (force (vl-expr-p x))
             (vl-expr-p (vl-condcheck-fix x)))
    :hints(("Goal" :in-theory (enable vl-condcheck-fix)))))



(defsection vl-condcheck-negate
  :parents (condcheck)
  :short "Smartly negate a canonicalized expression."
  :long "<p>We assume <tt>X</tt> is already canonicalized in the sense of @(see
  vl-condcheck-fix).  We \"smartly\" negate it so that, e.g., <tt>A</tt>
  becomes <tt>~A</tt>, but <tt>~A</tt> becomes <tt>A</tt> instead of
  <tt>~~A</tt>.</p>"

  (defund vl-condcheck-negate (x)
    (declare (xargs :guard (vl-expr-p x)))
    (if (and (not (vl-fast-atom-p x))
             (eq (vl-nonatom->op x) :vl-unary-bitnot))
        (first (vl-nonatom->args x))
      (make-vl-nonatom :op :vl-unary-bitnot
                       :args (list x))))

  (defthm vl-expr-p-of-vl-condcheck-negate
    (implies (force (vl-expr-p x))
             (vl-expr-p (vl-condcheck-negate x)))
    :hints(("Goal" :in-theory (enable vl-condcheck-negate)))))




(defsection vl-expr-condcheck
  :parents (condcheck)
  :short "Look for strange conditions throughout an expression."
  :long "<p>@(call vl-expr-condcheck) returns a list of warnings.</p>

<p>We recursively look throughout <tt>x</tt> for problematic tests.</p>

<p>The <tt>tests-above</tt> are all the tests we have seen as we have descended
through expressions of the form</p>

<code>
    test ? then : else
</code>

<p>Except:</p>
<ul>
 <li>all of the <tt>tests-above</tt> have been fixed with @(see vl-condcheck-fix), and</li>
 <li>when we descend into the else branch, we add <tt>~test</tt> to <tt>tests-above</tt>;
     more precisely, we use @(see vl-condcheck-negate) to form this term.</li>
</ul>

<p>The basic idea is that <tt>tests-above</tt> acts as a list of things we can
assume must be true as we are seeing <tt>X</tt>.</p>

<p><tt>ctx</tt> is a @(see vl-context-p) that should explain where this expression
occurs, and is used in any warning messages we produce.</p>"

  (mutual-recursion

   (defund vl-expr-condcheck (x tests-above ctx)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-exprlist-p tests-above)
                                 (true-listp tests-above)
                                 (vl-context-p ctx))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)
                     :hints(("Goal" :in-theory (disable (force))))))
     (b* (((when (vl-fast-atom-p x))
           nil)
          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((unless (eq op :vl-qmark))
           (vl-exprlist-condcheck args tests-above ctx))

          (test      (first args))
          (test-fix  (vl-condcheck-fix test))
          (~test-fix (vl-condcheck-negate test-fix))

          (warnings
           (cond ((and (vl-fast-atom-p test)
                       (or (vl-fast-constint-p (vl-atom->guts test))
                           (vl-fast-weirdint-p (vl-atom->guts test))))
                  (list (make-vl-warning
                         :type :vl-warn-qmark-const
                         :msg "~a0: found a ?: operator with constant ~
                             expression ~a1 as its test: ~a2.~%"
                         :args (list ctx test x)
                         :fatalp nil
                         :fn 'vl-expr-condcheck)))

                 ((member-equal test-fix tests-above)
                  (list (make-vl-warning
                         :type :vl-warn-qmark-always-true
                         :msg "~a0: found a ?: operator that is considering ~
                             whether ~a1 holds, but an equivalent case was ~
                             considered above, so this will always be true. ~
                             The sub-expression is ~a2."
                         :args (list ctx test x)
                         :fatalp nil
                         :fn 'vl-expr-condcheck)))

                 ((member-equal ~test-fix tests-above)
                  (list (make-vl-warning
                         :type :vl-warn-qmark-always-false
                         :msg "~a0: found a ?: operator that is considering ~
                             whether ~a1 holds, but an equivalent case was ~
                             considered above, so this will always be false. ~
                             The sub-expression is ~a2."
                         :args (list ctx test x)
                         :fatalp nil
                         :fn 'vl-expr-condcheck)))

                 (t
                  nil))))

       (append warnings
               (vl-expr-condcheck (second args)
                                  (cons test-fix tests-above)
                                  ctx)
               (vl-expr-condcheck (third args)
                                  (cons ~test-fix tests-above)
                                  ctx))))

   (defund vl-exprlist-condcheck (x tests-above ctx)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-exprlist-p tests-above)
                                 (true-listp tests-above)
                                 (vl-context-p ctx))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (append (vl-expr-condcheck (car x) tests-above ctx)
               (vl-exprlist-condcheck (cdr x) tests-above ctx)))))


  (flag::make-flag vl-flag-expr-condcheck
                   vl-expr-condcheck
                   :flag-mapping ((vl-expr-condcheck . expr)
                                  (vl-exprlist-condcheck . list)))

  (defthm-vl-flag-expr-condcheck
    (defthm vl-warninglist-p-of-vl-expr-condcheck
      (vl-warninglist-p (vl-expr-condcheck x tests-above ctx))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-condcheck
      (vl-warninglist-p (vl-exprlist-condcheck x tests-above ctx))
      :flag list)
    :hints(("Goal" :expand ((vl-expr-condcheck x tests-above ctx)
                            (vl-exprlist-condcheck x tests-above ctx)))))

  (verify-guards vl-expr-condcheck
    :hints(("Goal" :in-theory (enable vl-expr-condcheck)))))



(defsection vl-exprctxalist-condcheck
  :parents (condcheck)
  :short "@(call vl-exprctxalist-condcheck-check) extends @(see
vl-expr-condcheck-check) across an @(see vl-exprctxalist-p)."

  (defund vl-exprctxalist-condcheck (x)
    (declare (xargs :guard (vl-exprctxalist-p x)))
    (if (atom x)
        nil
      (append (vl-expr-condcheck (caar x) nil (cdar x))
              (vl-exprctxalist-condcheck (cdr x)))))

  (defthm vl-warninglist-p-of-vl-exprctxalist-condcheck
    (vl-warninglist-p (vl-exprctxalist-condcheck x))
    :hints(("Goal" :in-theory (enable vl-exprctxalist-condcheck)))))



(defsection vl-module-condcheck
  :parents (condcheck)
  :short "@(call vl-module-condcheck) carries our our @(see condcheck) on all
the expressions in a module, and adds any resulting warnings to the module."

  (defund vl-module-condcheck (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* ((ctxexprs     (vl-module-ctxexprs x))
         (new-warnings (vl-exprctxalist-condcheck ctxexprs)))
      (change-vl-module x
                        :warnings (append new-warnings (vl-module->warnings x)))))

  (local (in-theory (enable vl-module-condcheck)))

  (defthm vl-module-p-of-vl-module-condcheck
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-condcheck x))))

  (defthm vl-module->name-of-vl-module-condcheck
    (equal (vl-module->name (vl-module-condcheck x))
           (vl-module->name x))))


(defprojection vl-modulelist-condcheck (x)
  (vl-module-condcheck x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (condcheck))

(defthm vl-modulelist->names-of-vl-modulelist-condcheck
  (equal (vl-modulelist->names (vl-modulelist-condcheck x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))


