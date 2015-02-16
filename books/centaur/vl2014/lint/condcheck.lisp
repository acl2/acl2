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
(include-book "../mlib/strip")
(local (include-book "../util/arithmetic"))

(defxdoc condcheck
  :parents (lint)
  :short "Check for @('?:')-expressions with strange conditions."

  :long "<p>This is a heuristic for generating warnings.  We look for things
like the following, except that we target the @('?:') operator instead of
@('if') statements.</p>

@({
    if A { ... }
    else if B { ... }
    else if A { ... }   // already checked A above, so this is unreachable
    else if C { ... }
    else ...
})

<p>And also things like:</p>

@({
    if A { ... }
    else if B { ... }
    else if !A { ... }   // already checked A above, so this is just true
    else if C { ... }
    else ...
})

<p>And for @('if (constant) {...}').</p>

<p>All of this could be adapted to @('if') statements too, but we target the
@('?:') operator because we care a lot less about procedural code (like test
benches) than we do about the actual hardware modules.  Note that the @(see
qmarksize-check) can also be used for some additional checking on @('?:')
operators, but it tries to identify a different class of problems.</p>

<p>Since this is just a heuristic and it is completely unrelated to soundness,
we feel justified in doing a couple of seemingly unsound things.  In
particular, we basically ignore widths of test expressions and treat @('!')
and @('~') as equivalent.  We also treat @('^') as @('!=') and @('~^') as
@('==').  This is completely wrong in general, but it makes sense if you assume
that the tests are all going to be one-bit wide.</p>

<p>This check has no prerequisites and can in principle be run at any time.
But it is probably best to run it very early before throwing things out, and it
should probably be run before @(see oprewrite), which screws around with
conditional expressions, and also before things like expression splitting which
would get rid of the nested branches.</p>")

(local (xdoc::set-default-parents condcheck))

(define vl-condcheck-fix ((x vl-expr-p))
  :returns (new-x vl-expr-p :hyp :fguard)
  :short "Canonicalize an test expression for condcheck."

  :long "<p>We fix X (in the normal sense of @(see vl-expr-strip), to throw away
widths, attributes, etc., to facilitate equality checking), and then do certain
kinds of not-necessarily-sound rewriting to try to further canonicalize things.
These rewrites might possibly help us recognize a broader class of errors, but
probably aren't super important.</p>

@({
    !A     --> ~A               unsound, but sort of valid for one-bit ops

    A != B --> ~(A == B)        and we sort the args
    A ~^ B --> A == B           unsound, but sort of valid for one-bit ops
    A ^ B  --> ~(A == B)        unsound, but sort of valid for one-bit ops

    A < B  --> ~(A >= B)
    A > B  --> ~(B >= A)
    A <= B --> B >= A
})

<p>We also put arguments of commutative operators into @(see <<) order.  Note
that we only apply these rewrites at the top-level and not in any deep way,
which also sort of makes sense since we only want to assume that the top-level
expression is one-bit wide.</p>"

  (b* ((x (vl-expr-strip x))

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


(define vl-condcheck-negate ((x vl-expr-p))
  :returns (new-x vl-expr-p :hyp :fguard)
  :short "Smartly negate a canonicalized expression."

  :long "<p>We assume @('X') is already canonicalized in the sense of @(see
vl-condcheck-fix).  We \"smartly\" negate it so that, e.g., @('A') becomes
@('~A'), but @('~A') becomes @('A') instead of @('~~A').</p>"

    (declare (xargs :guard (vl-expr-p x)))
    (if (and (not (vl-fast-atom-p x))
             (eq (vl-nonatom->op x) :vl-unary-bitnot))
        (first (vl-nonatom->args x))
      (make-vl-nonatom :op :vl-unary-bitnot
                       :args (list x))))


(defines vl-expr-condcheck
  :short "Look for strange conditions throughout an expression."

  :long "<p>We recursively look throughout @('x') for problematic tests.</p>

<p>The @('tests-above') are all the tests we have seen as we have descended
through expressions of the form</p>

@({
    test ? then : else
})

<p>Except:</p>

<ul>

<li>all of the @('tests-above') have been fixed with @(see vl-condcheck-fix),
and</li>

<li>when we descend into the else branch, we add @('~test') to
@('tests-above'); more precisely, we use @(see vl-condcheck-negate) to form
this term.</li>

</ul>

<p>The basic idea is that @('tests-above') acts as a list of things we can
assume must be true as we are seeing @('X').</p>

<p>@('ctx') is a @(see vl-context-p) that should explain where this expression
occurs, and is used in any warning messages we produce.</p>"

  (define vl-expr-condcheck
    ((x           vl-expr-p)
     (tests-above (and (vl-exprlist-p tests-above)
                       (true-listp tests-above)))
     (ctx         vl-context-p))
    :returns (warnings vl-warninglist-p)
    :verify-guards nil
    :measure (vl-expr-count x)
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

  (define vl-exprlist-condcheck
    ((x vl-exprlist-p)
     (tests-above (and (vl-exprlist-p tests-above)
                       (true-listp tests-above)))
     (ctx vl-context-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-expr-condcheck (car x) tests-above ctx)
              (vl-exprlist-condcheck (cdr x) tests-above ctx))))
  ///
  (verify-guards vl-expr-condcheck
    :guard-debug t))

(define vl-exprctxalist-condcheck ((x vl-exprctxalist-p))
  :returns (warnings vl-warninglist-p)
  :short "@(call vl-exprctxalist-condcheck) extends @(see vl-expr-condcheck)
across an @(see vl-exprctxalist-p)."
  (if (atom x)
      nil
    (append (vl-expr-condcheck (caar x) nil (cdar x))
            (vl-exprctxalist-condcheck (cdr x)))))


(define vl-module-condcheck ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :short "@(call vl-module-condcheck) carries our our @(see condcheck) on all
the expressions in a module, and adds any resulting warnings to the module."

  (b* ((ctxexprs     (vl-module-ctxexprs x))
       (new-warnings (vl-exprctxalist-condcheck ctxexprs)))
    (change-vl-module x
                      :warnings (append new-warnings (vl-module->warnings x)))))

(defprojection vl-modulelist-condcheck (x)
  (vl-module-condcheck x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-condcheck ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (new-mods (vl-modulelist-condcheck x.mods)))
    (clear-memoize-table 'vl-expr-strip)
    (change-vl-design x :mods new-mods)))



