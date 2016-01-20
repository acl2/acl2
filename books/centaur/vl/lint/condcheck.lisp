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
(include-book "../mlib/ctxexprs")
(include-book "../mlib/strip")
(include-book "../mlib/expr-tools")
(local (include-book "../util/arithmetic"))

(local (std::add-default-post-define-hook :fix))

(defxdoc condcheck
  :parents (vl-lint)
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
should probably be run before any transform that might alter
expressions.  (Historically it was important to run it before, e.g., @(see
vl2014::oprewrite), but now we generally are not rewriting expressions like
that so it may be that we don't need to care much about this anymore.)</p>")

(local (xdoc::set-default-parents condcheck))

(define vl-condcheck-fix ((x vl-expr-p))
  :returns (new-x vl-expr-p)
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

  (b* ((x (vl-expr-strip x)))
    (vl-expr-case x
      :vl-unary
      (if (vl-unaryop-equiv x.op :vl-unary-lognot)
          ;; !A --> ~A
          (change-vl-unary x :op :vl-unary-bitnot)
        x)

      :vl-binary
      (b* (((mv min max)
            (if (<< x.left x.right)
                (mv x.left x.right)
              (mv x.right x.left)))

           ((when (vl-binaryop-equiv x.op :vl-binary-neq))
            ;; A != B --> ~(A == B)
            (make-vl-unary :op :vl-unary-bitnot
                           :arg (change-vl-binary x
                                                  :op :vl-binary-eq
                                                  :left min :right max)))

           ((when (vl-binaryop-equiv x.op :vl-binary-xnor))
            ;; A ~^ B --> A == B
            (change-vl-binary x
                              :op :vl-binary-eq
                              :left min :right max))

           ((when (vl-binaryop-equiv x.op :vl-binary-xor))
            ;; A ^ B --> ~(A == B)
            (make-vl-unary :op :vl-unary-bitnot
                           :arg (change-vl-binary x
                                                  :op :vl-binary-eq
                                                  :left min :right max)))

           ((when (vl-binaryop-equiv x.op :vl-binary-lt))
            ;; A < B  --> ~(A >= B)
            (make-vl-unary :op :vl-unary-bitnot
                           :arg (change-vl-binary x :op :vl-binary-gte)))

           ((when (vl-binaryop-equiv x.op :vl-binary-gt))
            ;; A > B  --> ~(B >= A)
            (make-vl-unary :op :vl-unary-bitnot
                           :arg (change-vl-binary x
                                                  :op :vl-binary-gte
                                                  :left x.right :right x.left)))

           ((when (vl-binaryop-equiv x.op :vl-binary-lte))
            ;; A <= B --> B >= A
            (change-vl-binary x
                              :op :vl-binary-gte
                              :left x.right :right x.left))

           ((when (member x.op '(:vl-binary-plus :vl-binary-times
                                 :vl-binary-ceq :vl-binary-cne
                                 :vl-binary-logand :vl-binary-logor
                                 :vl-binary-bitand :vl-binary-bitor)))
            (change-vl-binary x :left min :right max)))
        x)

      :otherwise x)))


(define vl-condcheck-negate ((x vl-expr-p))
  :returns (new-x vl-expr-p)
  :short "Smartly negate a canonicalized expression."

  :long "<p>We assume @('X') is already canonicalized in the sense of @(see
vl-condcheck-fix).  We \"smartly\" negate it so that, e.g., @('A') becomes
@('~A'), but @('~A') becomes @('A') instead of @('~~A').</p>"

  (let ((dumb (make-vl-unary :op :vl-unary-bitnot :arg x)))
    (vl-expr-case x
      :vl-unary (if (vl-unaryop-equiv x.op :vl-unary-bitnot)
                    x.arg
                  dumb)
      :otherwise dumb)))


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

  (define vl-expr-condcheck ((x           vl-expr-p)
                             (tests-above vl-exprlist-p)
                             (ctx         vl-context-p))
    :returns (warnings vl-warninglist-p)
    :verify-guards nil
    :measure (vl-expr-count x)
    (b* ((x           (vl-expr-fix x))
         (tests-above (vl-exprlist-fix tests-above))
         (ctx         (vl-context-fix ctx)))
      (vl-expr-case x
        :vl-qmark
        (b* ((test-fix  (vl-condcheck-fix x.test))
             (~test-fix (vl-condcheck-negate test-fix))
             (warnings
              (cond ((vl-expr-case x.test :vl-literal)
                     (list (make-vl-warning
                            :type :vl-warn-qmark-const
                            :msg "~a0: found a ?: operator with constant ~
                                expression ~a1 as its test: ~a2.~%"
                            :args (list ctx x.test x)
                            :fatalp nil
                            :fn __function__)))
                    ((member-equal test-fix tests-above)
                     (list (make-vl-warning
                            :type :vl-warn-qmark-always-true
                            :msg "~a0: found a ?: operator that is considering ~
                                whether ~a1 holds, but an equivalent case was ~
                                considered above, so this will always be ~
                                true. The sub-expression is ~a2."
                            :args (list ctx x.test x)
                            :fatalp nil
                            :fn __function__)))
                    ((member-equal ~test-fix tests-above)
                     (list (make-vl-warning
                            :type :vl-warn-qmark-always-false
                            :msg "~a0: found a ?: operator that is considering ~
                                whether ~a1 holds, but an equivalent case was ~
                                considered above, so this will always be ~
                                false. The sub-expression is ~a2."
                            :args (list ctx x.test x)
                            :fatalp nil
                            :fn __function__)))
                    (t
                     nil))))
          (append warnings
                  (vl-expr-condcheck x.test tests-above ctx)
                  (vl-expr-condcheck x.then
                                     (cons test-fix tests-above)
                                     ctx)
                  (vl-expr-condcheck x.else
                                     (cons ~test-fix tests-above)
                                     ctx)))
        :otherwise
        (vl-exprlist-condcheck (vl-expr->subexprs x) tests-above ctx))))

  (define vl-exprlist-condcheck
    ((x vl-exprlist-p)
     (tests-above vl-exprlist-p)
     (ctx vl-context-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-expr-condcheck (car x) tests-above ctx)
              (vl-exprlist-condcheck (cdr x) tests-above ctx))))
  ///
  (verify-guards vl-expr-condcheck
    :guard-debug t)
  (deffixequiv-mutual vl-expr-condcheck))

(def-expr-check condcheck :formals (x.expr nil x.ctx))
