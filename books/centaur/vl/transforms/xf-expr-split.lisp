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
(include-book "../mlib/namefactory")
(include-book "../wf-ranges-resolved-p")
(include-book "../wf-widthsfixed-p")
(local (include-book "../util/arithmetic"))


(deflist vl-atomlist-p (x)
  (vl-atom-p x)
  :guard t
  :elementp-of-nil nil)



(defxdoc split
  :parents (transforms)
  :short "Split up expressions by generating new wires."
  :long "<p>In this transformation, our goal is to split up expressions so
that every assignment has at most one operation, and so that the arguments
to every gate and module instance are operation-free.</p>

<p>The basic idea is to introduce temporary variables, e.g., an assignment
such as</p>

<code>
     assign w = a + b * c + d;
</code>

<p>would be transformed into a series of simpler assignments, e.g.,</p>

<code>
    assign t1 = b * c;
    assign t2 = a + t1;
    assign w = t2 + d;
</code>

<p>This involves creating new wire declarations and assignments to those wires,
and requires us to be very careful to avoid name collisions.</p>

<p>Efficiency note.  Split needs to be relatively efficient.  In one module,
splitting results in about 80,000 wires being introduced.  So we need to be
able to create these declarations and assignments relatively quickly.  We use a
@(see vl-namefactory-p) to generate fresh names like <tt>temp_12</tt> and
<tt>temp_46</tt>.</p>")



(defsection vl-expr-split
  :parents (split)
  :short "Split up complex subexpressions throughout an expression."
  :long "<p><b>Signature:</b> @(call vl-expr-split) returns <tt>(mv
warnings-prime x-prime decls-prime assigns-prime nf-prime)</tt>.</p>

<p>Inputs.</p>

<ul>

<li><tt>x</tt> is an expression to split, which occurs at within the parse tree
construct located at <tt>loc</tt>,</li>

<li><tt>mod</tt> is the module we are descending through.  We need the module
in order to ensure that the new names we are generating are unique.  Our
original approach was to pre-compute the namespace, but in our new approach we
only need the namespace at most once, so we can construct it on demand and, in
so doing, often avoid needing to construct it at all.</li>

<li><tt>decls</tt> and <tt>assigns</tt> are accumulators for our answers.  Each
time we split up an expression, we are going to introduce a new wire that will
hold the intermediate answer.  This new wire will need a declaration which we
accumulate into decls, and an assignment which we accumulate into assigns.</li>

<li><tt>nf</tt> is a @(see vl-namefactory-p) for generating fresh wires.</li>

<li><tt>warnings</tt> is an accumulator for warnings, which we may extend.</li>

</ul>

<p>Outputs.</p>

<ul>

<li><tt>warnings-prime</tt> includes any updated warnings,</li>

<li><tt>x-prime</tt> is an atomic expression which serves as a \"replacement\"
for <tt>x</tt>.  If <tt>x</tt> is already an atomic expression, then
<tt>x-prime</tt> will just be <tt>x</tt>; otherwise <tt>x-prime</tt> will be
an identifier atom, which simply contains the name of a new wire that has been
generated to store the result of <tt>x</tt>,</li>

<li><tt>decls-prime</tt> and <tt>assigns-prime</tt> are updated accumulators
for declarations and assignments for the newly generated wires, and</li>

<li><tt>nf-prime</tt> is the updated name factory.</li>

</ul>

<p>A fundamental claim is that if we add the <tt>new-decls</tt> and
<tt>new-assigns</tt> to mod, then <tt>new-x</tt> and <tt>x</tt> should be
equivalent in the Verilog semantics.</p>

<p>This function is mutually recursive with @(call vl-exprlist-split).</p>"

  (mutual-recursion

   (defund vl-expr-split (x mod decls assigns nf loc warnings)
     ;; BOZO loc should probably become a vl-modelement-p
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (vl-netdecllist-p decls)
                                 (vl-assignlist-p assigns)
                                 (vl-namefactory-p nf)
                                 (vl-location-p loc)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))

     (b* ((width (vl-expr->finalwidth x))
          (type  (vl-expr->finaltype x))

          ((unless (and (posp width) type))
           ;; Basic sanity check.  Widths should be computed and positive, or
           ;; what are we even doing??
           (mv (cons (make-vl-warning
                      :type :vl-programming-error
                      :msg "~l0: expected widths/types to be determined, but ~
                            expression ~a1 has width ~x2 and type ~x3."
                      :args (list loc x width type)
                      :fatalp t
                      :fn 'vl-expr-split)
                     warnings)
               x decls assigns nf))

          ((when (vl-fast-atom-p x))
           ;; X is already atomic, so there is nothing to do.  We just return
           ;; it and our accumulators, unchanged.
           (mv warnings x decls assigns nf))

          ;; To begin with, we recursively split the arguments.  Note that each
          ;; of the new-args will be an atom!
          ((mv warnings new-args decls assigns nf)
           (vl-exprlist-split (vl-nonatom->args x) mod decls assigns nf loc warnings))

          ;; Now, our operation applied to the simplified args is a simple
          ;; expression.  We create a new, temporary wire of the appropriate
          ;; width, and assign the expression to this new wire.
          (new-expr         (change-vl-nonatom x :args new-args))
          ((mv new-name nf) (vl-namefactory-indexed-name "temp" nf))
          (new-name-expr    (vl-idexpr new-name width type))
          (new-decl         (make-vl-netdecl :loc loc
                                             :name new-name
                                             :type :vl-wire
                                             :signedp (eq type :vl-signed)
                                             :range (vl-make-n-bit-range width)))
          (new-assign       (make-vl-assign :loc loc
                                            :lvalue new-name-expr
                                            :expr new-expr)))

         ;; And that's it.
         (mv warnings
             new-name-expr
             (cons new-decl decls)
             (cons new-assign assigns)
             nf)))

   (defund vl-exprlist-split (x mod decls assigns nf loc warnings)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (vl-netdecllist-p decls)
                                 (vl-assignlist-p assigns)
                                 (vl-namefactory-p nf)
                                 (vl-location-p loc)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil decls assigns nf))
          ((mv warnings car-prime decls assigns nf)
           (vl-expr-split (car x) mod decls assigns nf loc warnings))
          ((mv warnings cdr-prime decls assigns nf)
           (vl-exprlist-split (cdr x) mod decls assigns nf loc warnings)))
         (mv warnings (cons car-prime cdr-prime) decls assigns nf))))

  (FLAG::make-flag flag-vl-expr-split
                   vl-expr-split
                   :flag-mapping ((vl-expr-split . expr)
                                  (vl-exprlist-split . list)))

  (local
   (defthm-flag-vl-expr-split lemma
     (expr t
           :rule-classes nil)
     (list (equal (len (mv-nth 1 (vl-exprlist-split x mod decls assigns nf loc warnings)))
                  (len x))
           :name len-of-vl-exprlist-split-2)
     :hints(("Goal"
             :induct (flag-vl-expr-split flag x mod decls assigns nf loc warnings)
             :expand ((vl-expr-split x mod decls assigns nf loc warnings)
                      (vl-exprlist-split x mod decls assigns nf loc warnings))))))

  (defthm len-of-vl-exprlist-split-2
    (equal (len (mv-nth 1 (vl-exprlist-split x mod decls assigns nf loc warnings)))
           (len x)))

  (defthm-flag-vl-expr-split flag-vl-expr-split-basics
    (expr (implies (and (force (vl-expr-p x))
                        (force (vl-module-p mod))
                        (force (vl-netdecllist-p decls))
                        (force (vl-assignlist-p assigns))
                        (force (vl-namefactory-p nf))
                        (force (vl-location-p loc))
                        (force (vl-warninglist-p warnings)))
                   (let ((ret (vl-expr-split x mod decls assigns nf loc warnings)))
                     (and (vl-warninglist-p (mv-nth 0 ret))
                          (vl-expr-p        (mv-nth 1 ret))
                          (vl-netdecllist-p (mv-nth 2 ret))
                          (vl-assignlist-p  (mv-nth 3 ret))
                          (vl-namefactory-p (mv-nth 4 ret))))))

    (list (implies (and (force (vl-exprlist-p x))
                        (force (vl-module-p mod))
                        (force (vl-netdecllist-p decls))
                        (force (vl-assignlist-p assigns))
                        (force (vl-namefactory-p nf))
                        (force (vl-location-p loc))
                        (force (vl-warninglist-p warnings)))
                   (let ((ret (vl-exprlist-split x mod decls assigns nf loc warnings)))
                     (and (vl-warninglist-p (mv-nth 0 ret))
                          (vl-exprlist-p    (mv-nth 1 ret))
                          (vl-netdecllist-p (mv-nth 2 ret))
                          (vl-assignlist-p  (mv-nth 3 ret))
                          (vl-namefactory-p (mv-nth 4 ret))))))

    :hints(("Goal"
            :induct (flag-vl-expr-split flag x mod decls assigns nf loc warnings)
            :expand ((vl-expr-split x mod decls assigns nf loc warnings)
                     (vl-exprlist-split x mod decls assigns nf loc warnings))
            :do-not '(generalize fertilize)
            :do-not-induct t
            )))

  (verify-guards vl-expr-split)

  (local (defthm-flag-vl-expr-split lemma
           (expr t :rule-classes nil)
           (list (true-listp (mv-nth 1 (vl-exprlist-split x mod decls assigns nf loc warnings)))
                 :rule-classes :type-prescription
                 :name true-listp-of-vl-exprlist-split-1)
           :hints(("Goal"
                   :induct (flag-vl-expr-split flag x mod decls assigns nf loc warnings)
                   :expand ((vl-expr-split x mod decls assigns nf loc warnings)
                            (vl-exprlist-split x mod decls assigns nf loc warnings))))))

  (defthm true-listp-of-vl-exprlist-split-1
    (true-listp (mv-nth 1 (vl-exprlist-split x mod decls assigns nf loc warnings)))
    :rule-classes :type-prescription)

  (defthm-flag-vl-expr-split lemma
    (expr (equal (true-listp (mv-nth 2 (vl-expr-split x mod decls assigns nf loc warnings)))
                 (true-listp decls))
          :name true-listp-of-vl-expr-split-2)
    (list (equal (true-listp (mv-nth 2 (vl-exprlist-split x mod decls assigns nf loc warnings)))
                 (true-listp decls))
          :name true-listp-of-vl-exprlist-split-2)
    :hints(("Goal"
            :induct (flag-vl-expr-split flag x mod decls assigns nf loc warnings)
            :expand ((vl-expr-split x mod decls assigns nf loc warnings)
                     (vl-exprlist-split x mod decls assigns nf loc warnings)))))

  (defthm-flag-vl-expr-split lemma
    (expr (equal (true-listp (mv-nth 3 (vl-expr-split x mod decls assigns nf loc warnings)))
                 (true-listp assigns))
          :name true-listp-of-vl-expr-split-3)
    (list (equal (true-listp (mv-nth 3 (vl-exprlist-split x mod decls assigns nf loc warnings)))
                 (true-listp assigns))
          :name true-listp-of-vl-exprlist-split-3)
    :hints(("Goal"
            :induct (flag-vl-expr-split flag x mod decls assigns nf loc warnings)
            :expand ((vl-expr-split x mod decls assigns nf loc warnings)
                     (vl-exprlist-split x mod decls assigns nf loc warnings)))))

  )



(defsection vl-assign-split
  :parents (split)
  :short "Split up an assignment if the right-hand side is complicated."
  :long "<p><b>Signature:</b> @(call vl-assign-split) returns <tt>(mv
warnings-prime x-prime decls-prime assigns-prime nf-prime)</tt>.</p>

<p><tt>x</tt> is a @(see vl-assign-p), and the other arguments are as in @(see
vl-expr-split).</p>

<p>Contract: we may replace the assignment <tt>x</tt> with <tt>x-prime</tt>, so
long as <tt>decls-prime</tt> and <tt>assigns-prime</tt> are also added to the
module.</p>

<p>This is a little more interesting than usual.  We want to split up the
right-hand side of an assignment only if it is a compound expression that
involves more than just atoms.  That is, it's fine if we have an assignment
like <tt>foo = bar</tt>, or <tt>foo = bar + 1</tt>.  But we do want to split
once we arrive at <tt>foo = bar + (baz + 1)</tt>, because at that point
<tt>(baz + 1)</tt> is a compound expression instead of an atom.</p>"

  (defund vl-assign-split (x mod decls assigns nf warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-assign-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* ((expr    (vl-assign->expr x))
         (loc     (vl-assign->loc x))
         ((when (vl-fast-atom-p expr))
          (mv warnings x decls assigns nf))
         ((when (vl-atomlist-p (vl-nonatom->args expr)))
          (mv warnings x decls assigns nf))
         ;; Even at this point, we don't want to eliminate the whole
         ;; expression.  Just recursively simplify the args until they are
         ;; constants, and build a new expr out of them.
         ((mv warnings new-args decls assigns nf)
          (vl-exprlist-split (vl-nonatom->args expr) mod decls assigns nf loc warnings))
         (new-expr   (change-vl-nonatom expr :args new-args))
         (new-assign (change-vl-assign x :expr new-expr)))
        (mv warnings new-assign decls assigns nf)))

  (local (in-theory (enable vl-assign-split)))

  (defthm vl-assign-split-basics
    (implies (and (force (vl-assign-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-assign-split x mod decls assigns nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-assign-p      (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-assign-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-assign-split x mod decls assigns nf warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-assign-split x mod decls assigns nf warnings)))
                (true-listp assigns)))))



(defsection vl-assignlist-split

  (defund vl-assignlist-split (x mod decls assigns nf warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil decls assigns nf))
         ((mv warnings car-prime decls assigns nf)
          (vl-assign-split (car x) mod decls assigns nf warnings))
         ((mv warnings cdr-prime decls assigns nf)
          (vl-assignlist-split (cdr x) mod decls assigns nf warnings))
         (x-prime (cons car-prime cdr-prime)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-assignlist-split)))

  (defthm vl-assignlist-split-basics
    (implies (and (force (vl-assignlist-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-assignlist-split x mod decls assigns nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-assignlist-p  (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-assignlist-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-assignlist-split x mod decls assigns nf warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-assignlist-split x mod decls assigns nf warnings)))
                (true-listp assigns)))))



(defsection vl-plainarg-split

  (defund vl-plainarg-split (x mod decls assigns nf loc warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-plainarg-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-location-p loc)
                                (vl-warninglist-p warnings))))

    (b* (((unless (eq (vl-plainarg->dir x) :vl-input))
          ;; IMPORTANT.  We do not want to apply unless this is an input.  When
          ;; we have outputs, we want to hook up to the actual wires being
          ;; outputted, not to internal wires that we've just created.  I don't
          ;; know what we want to do for inouts, but for now I'm not trying to
          ;; split them at all.
          (mv warnings x decls assigns nf))

         ((unless (vl-plainarg->expr x))
          ;; Found a blank port.  Nothing to do.
          (mv warnings x decls assigns nf))

         ;; Okay, we have a legitimate input expression.  We want to do the
         ;; splitting.  Unlike assignments, we want to just go ahead and fully
         ;; split and get ourselves a single wire.
         ((mv warnings new-expr decls assigns nf)
          (vl-expr-split (vl-plainarg->expr x) mod decls assigns nf loc warnings))
         (x-prime (change-vl-plainarg x :expr new-expr)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-plainarg-split)))

  (defthm vl-plainarg-split-basics
    (implies (and (force (vl-plainarg-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-location-p loc))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-plainarg-split x mod decls assigns nf loc warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-plainarg-p    (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-plainarg-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-plainarg-split x mod decls assigns nf loc warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-plainarg-split x mod decls assigns nf loc warnings)))
                (true-listp assigns)))))



(defsection vl-plainarglist-split

  (defund vl-plainarglist-split (x mod decls assigns nf loc warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-plainarglist-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-location-p loc)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil decls assigns nf))
         ((mv warnings car-prime decls assigns nf)
          (vl-plainarg-split (car x) mod decls assigns nf loc warnings))
         ((mv warnings cdr-prime decls assigns nf)
          (vl-plainarglist-split (cdr x) mod decls assigns nf loc warnings)))
        (mv warnings (cons car-prime cdr-prime) decls assigns nf)))

  (local (in-theory (enable vl-plainarglist-split)))

  (defthm vl-plainarglist-split-basics
    (implies (and (force (vl-plainarglist-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-location-p loc))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-plainarglist-split x mod decls assigns nf loc warnings)))
               (and (vl-warninglist-p  (mv-nth 0 ret))
                    (vl-plainarglist-p (mv-nth 1 ret))
                    (vl-netdecllist-p  (mv-nth 2 ret))
                    (vl-assignlist-p   (mv-nth 3 ret))
                    (vl-namefactory-p  (mv-nth 4 ret))))))

  (defthm vl-plainarglist-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-plainarglist-split x mod decls assigns nf loc warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-plainarglist-split x mod decls assigns nf loc warnings)))
                (true-listp assigns)))))



(defsection vl-arguments-split

  (defund vl-arguments-split (x mod decls assigns nf loc warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-arguments-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-location-p loc)
                                (vl-warninglist-p warnings))))
    (b* (((when (vl-arguments->namedp x))
          (mv (cons (make-vl-warning
                     :type :vl-bad-arguments
                     :msg "~l0: expected to only encounter plain arguments, ~
                           but found a named argument list.  Not actually ~
                           splitting anything."
                     :args (list loc)
                     :fatalp t
                     :fn 'vl-arguments-split)
                    warnings)
              x decls assigns nf))
         ((mv warnings new-args decls assigns nf)
          (vl-plainarglist-split (vl-arguments->args x) mod decls assigns nf loc warnings))
         (x-prime (vl-arguments nil new-args)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-arguments-split)))

  (defthm vl-arguments-split-basics
    (implies (and (force (vl-arguments-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-location-p loc))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-arguments-split x mod decls assigns nf loc warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-arguments-p   (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-arguments-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-arguments-split x mod decls assigns nf loc warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-arguments-split x mod decls assigns nf loc warnings)))
                (true-listp assigns)))))



(defsection vl-modinst-split

  (defund vl-modinst-split (x mod decls assigns nf warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* ((portargs (vl-modinst->portargs x))
         (loc      (vl-modinst->loc x))
         ((mv warnings new-args decls assigns nf)
          (vl-arguments-split portargs mod decls assigns nf loc warnings))
         (x-prime (change-vl-modinst x :portargs new-args)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-modinst-split)))

  (defthm vl-modinst-split-basics
    (implies (and (force (vl-modinst-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-modinst-split x mod decls assigns nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-modinst-p     (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-modinst-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-modinst-split x mod decls assigns nf warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-modinst-split x mod decls assigns nf warnings)))
                (true-listp assigns)))))


(defsection vl-modinstlist-split

  (defund vl-modinstlist-split (x mod decls assigns nf warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil decls assigns nf))
         ((mv warnings car-prime decls assigns nf)
          (vl-modinst-split (car x) mod decls assigns nf warnings))
         ((mv warnings cdr-prime decls assigns nf)
          (vl-modinstlist-split (cdr x) mod decls assigns nf warnings))
         (x-prime (cons car-prime cdr-prime)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-modinstlist-split)))

  (defthm vl-modinstlist-split-basics
    (implies (and (force (vl-modinstlist-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-modinstlist-split x mod decls assigns nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-modinstlist-p (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-modinstlist-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-modinstlist-split x mod decls assigns n warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-modinstlist-split x mod decls assigns n warnings)))
                (true-listp assigns)))))



(defsection vl-gateinst-split

  (defund vl-gateinst-split (x mod decls assigns nf warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* ((args (vl-gateinst->args x))
         (loc  (vl-gateinst->loc x))
         ((mv warnings new-args decls assigns nf)
          (vl-plainarglist-split args mod decls assigns nf loc warnings))
         (x-prime (change-vl-gateinst x :args new-args)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-gateinst-split)))

  (defthm vl-gateinst-split-basics
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-gateinst-split x mod decls assigns nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-gateinst-p    (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-assignlist-p  (mv-nth 3 ret))
                    (vl-namefactory-p (mv-nth 4 ret))))))

  (defthm vl-gateinst-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-gateinst-split x mod decls assigns nf warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-gateinst-split x mod decls assigns nf warnings)))
                (true-listp assigns)))))



(defsection vl-gateinstlist-split

  (defund vl-gateinstlist-split (x mod decls assigns nf warnings)
    "Returns (MV WARNINGS' X' DECLS' ASSIGNS' NF')"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-module-p mod)
                                (vl-netdecllist-p decls)
                                (vl-assignlist-p assigns)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil decls assigns nf))
         ((mv warnings car-prime decls assigns nf)
          (vl-gateinst-split (car x) mod decls assigns nf warnings))
         ((mv warnings cdr-prime decls assigns nf)
          (vl-gateinstlist-split (cdr x) mod decls assigns nf warnings))
         (x-prime (cons car-prime cdr-prime)))
        (mv warnings x-prime decls assigns nf)))

  (local (in-theory (enable vl-gateinstlist-split)))

  (defthm vl-gateinstlist-split-basics
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-module-p mod))
                  (force (vl-netdecllist-p decls))
                  (force (vl-assignlist-p assigns))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-gateinstlist-split x mod decls assigns nf warnings)))
               (and (vl-warninglist-p  (mv-nth 0 ret))
                    (vl-gateinstlist-p (mv-nth 1 ret))
                    (vl-netdecllist-p  (mv-nth 2 ret))
                    (vl-assignlist-p   (mv-nth 3 ret))
                    (vl-namefactory-p  (mv-nth 4 ret))))))

  (defthm vl-gateinstlist-split-true-list
    (and (equal (true-listp (mv-nth 2 (vl-gateinstlist-split x mod decls assigns nf warnings)))
                (true-listp decls))
         (equal (true-listp (mv-nth 3 (vl-gateinstlist-split x mod decls assigns nf warnings)))
                (true-listp assigns)))))



(defsection vl-module-split

  (defund vl-module-split (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         (warnings  (vl-module->warnings x))
         (netdecls  (vl-module->netdecls x))
         (decls     nil)
         (assigns   nil)
         (nf        (vl-starting-namefactory x))

         ((mv warnings new-assigns decls assigns nf)
          (vl-assignlist-split (vl-module->assigns x) x decls assigns nf warnings))

         ((mv warnings new-modinsts decls assigns nf)
          (vl-modinstlist-split (vl-module->modinsts x) x decls assigns nf warnings))

         ((mv warnings new-gateinsts decls assigns nf)
          (vl-gateinstlist-split (vl-module->gateinsts x) x decls assigns nf warnings))

         (-         (vl-free-namefactory nf))

         ;; For idempotency, we want to keep the new-assigns and original
         ;; netdecls in the same order.  We put the assignments for the
         ;; temporaries first.
         (full-new-assigns (revappend assigns new-assigns))
         (full-new-decls   (revappend decls netdecls)))

        (change-vl-module x
                          :assigns full-new-assigns
                          :netdecls full-new-decls
                          :modinsts new-modinsts
                          :gateinsts new-gateinsts
                          :warnings warnings)))

  (local (in-theory (enable vl-module-split)))

  (defthm vl-module-p-of-vl-module-split
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-split x))))

  (defthm vl-module->name-of-vl-module-split
    (equal (vl-module->name (vl-module-split x))
           (vl-module->name x))))



(defsection vl-modulelist-split

  (defprojection vl-modulelist-split (x)
    (vl-module-split x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-split)))

  (defthm vl-modulelist->names-of-vl-modulelist-split
    (equal (vl-modulelist->names (vl-modulelist-split x))
           (vl-modulelist->names x))))




