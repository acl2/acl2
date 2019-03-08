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
(include-book "../util/warningtree")
(local (include-book "../util/arithmetic"))
(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))

(defxdoc condcheck
  :parents (vl-lint)
  :short "Check for @('?:')-expressions with strange conditions."

  :long "<p>This is a heuristic for generating warnings.  We look for things
like the following,targeting the @('?:') operator as well as
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

(define vl-iftest-condcheck ((x vl-expr-p "The test of the IF statement or ?: operator.")
                             (tests-above vl-exprlist-p)
                             (ctx)
                             (ifstmtp))
  :returns (warnings vl-warninglist-p)
  (b* ((x (vl-expr-fix x))
       (tests-above (vl-exprlist-fix tests-above))
       (test-fix  (vl-condcheck-fix x))
       (~test-fix (vl-condcheck-negate test-fix))
       (warning-descrip (if ifstmtp "an IF statement" "a ?: operator")))
    (cond ((vl-expr-case x :vl-literal)
           (list (make-vl-warning
                  :type (if ifstmtp :vl-warn-ifstmt-const :vl-warn-qmark-const)
                  :msg "found ~s3 with constant ~
                                expression ~a1 as its test: ~a2.~%"
                  :args (list ctx x x warning-descrip)
                  :fatalp nil
                  :fn __function__)))
          ((member-equal test-fix tests-above)
           (list (make-vl-warning
                  :type (if ifstmtp :vl-warn-ifstmt-always-true :vl-warn-qmark-always-true)
                  :msg "found ~s3 that is considering ~
                                whether ~a1 holds, but an equivalent case was ~
                                considered above, so this will always be ~
                                true. The sub-expression is ~a2."
                  :args (list ctx x x warning-descrip)
                  :fatalp nil
                  :fn __function__)))
          ((member-equal ~test-fix tests-above)
           (list (make-vl-warning
                  :type (if ifstmtp :vl-warn-ifstmt-always-false :vl-warn-qmark-always-false)
                  :msg "found ~s3 that is considering ~
                                whether ~a1 holds, but an equivalent case was ~
                                considered above, so this will always be ~
                                false. The sub-expression is ~a2."
                  :args (list ctx x x warning-descrip)
                  :fatalp nil
                  :fn __function__)))
          (t
           nil))))


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
                             (tests-above vl-exprlist-p))
    :returns (warnings vl-warningtree-p)
    :verify-guards nil
    :measure (vl-expr-count x)
    (b* ((x           (vl-expr-fix x))
         (tests-above (vl-exprlist-fix tests-above)))
      (vl-expr-case x
        :vl-qmark
        (b* ((test-fix  (vl-condcheck-fix x.test))
             (~test-fix (vl-condcheck-negate test-fix)))
          (vl-warningtree-cons
           (vl-warningtree-cons (vl-iftest-condcheck x.test tests-above nil nil)
                                (vl-expr-condcheck x.test tests-above))
           (vl-warningtree-cons (vl-expr-condcheck x.then
                                                   (cons test-fix tests-above))
                                (vl-expr-condcheck x.else
                                                   (cons ~test-fix tests-above)))))
        :otherwise
        (vl-exprlist-condcheck (vl-expr->subexprs x) tests-above))))

  (define vl-exprlist-condcheck
    ((x vl-exprlist-p)
     (tests-above vl-exprlist-p))
    :returns (warnings vl-warningtree-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (vl-warningtree-cons (vl-expr-condcheck (car x) tests-above)
                           (vl-exprlist-condcheck (cdr x) tests-above))))
  ///
  (verify-guards vl-expr-condcheck
    :guard-debug t)
  (deffixequiv-mutual vl-expr-condcheck))

;; (def-expr-check condcheck :formals (x.expr nil x.ctx))

(fty::defvisitor-template stmt-condcheck ((x :object)
                                          (tests-above vl-exprlist-p))
  :returns (warnings (:join (vl-warningtree-cons warnings1 warnings)
                      :tmp-var warnings1
                      :initial nil)
                     vl-warningtree-p)
  :renames ((vl-stmt vl-stmt-condcheck-aux))
    
    :type-fns ((vl-stmt vl-stmt-condcheck)
               (vl-expr vl-expr-condcheck)
               (vl-exprlist vl-exprlist-condcheck))
    :fnname-template <type>-condcheck)

(local (in-theory (disable vl-context-p-when-vl-ctxelement-p
                           double-containment not
                           (:t acl2::true-listp-append))))

(set-bogus-mutual-recursion-ok t)
(set-bogus-measure-ok t)

(fty::defvisitors vl-stmt-condcheck-deps
  :template stmt-condcheck
  :dep-types (vl-stmt))


(fty::defvisitor vl-stmt-condcheck
  :template stmt-condcheck
  :type statements
  :measure (two-nats-measure :count 0)

  (define vl-stmt-condcheck ((x vl-stmt-p)
                             (tests-above vl-exprlist-p))
    :returns (warnings vl-warningtree-p)
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (vl-stmt-case x
      :vl-ifstmt
      (b* ((test-fix  (vl-condcheck-fix x.condition))
           (~test-fix (vl-condcheck-negate test-fix)))
        (vl-warningtree-cons
         (vl-warningtree-cons (vl-iftest-condcheck x.condition tests-above (vl-stmt-fix x) t)
                              (vl-expr-condcheck x.condition tests-above))
          (vl-warningtree-cons (vl-stmt-condcheck x.truebranch (cons test-fix tests-above))
                               (vl-stmt-condcheck x.falsebranch (cons ~test-fix tests-above)))))
      :otherwise (vl-stmt-condcheck-aux x tests-above))))



(local (defconst *condcheck-ctx-types*
         '(vl-assign
           vl-alias
           vl-vardecl
           vl-paramdecl
           vl-fundecl
           vl-taskdecl
           vl-modinst
           vl-gateinst
           vl-always
           vl-initial
           vl-final
           vl-typedef)))

(local (define condcheck-ctx-to-aux-fns (x)
         :mode :program :hooks nil
         (if (atom x)
             nil
           (cons `(,(car x) ,(intern$ (cat (symbol-name (car x)) "-CONDCHECK!-AUX") "VL"))
                 (condcheck-ctx-to-aux-fns (cdr x))))))

(local (define condcheck-ctx-to-condcheck!-fns (x)
         :mode :program :hooks nil
         (if (atom x)
             nil
           (cons `(,(car x) ,(intern$ (cat (symbol-name (car x)) "-CONDCHECK!") "VL"))
                 (condcheck-ctx-to-condcheck!-fns (cdr x))))))

(local (define condcheck-existing-type-fns (x)
         :mode :program :hooks nil
         (if (atom x)
             nil
           (cons (list (caar x) `(lambda (x) (,(cdar x) x nil)))
                 (condcheck-existing-type-fns (cdr x))))))

(make-event
 `(fty::defvisitor-template condcheck ((x :object))
    :returns (warnings (:join (vl-warningtree-cons warnings1 warnings)
                        :tmp-var warnings1
                        :initial nil)
                       vl-warningtree-p)
    :renames ,(condcheck-ctx-to-aux-fns *condcheck-ctx-types*)
    :type-fns ((vl-module :skip)
               (vl-interface :skip)
               ,@(condcheck-existing-type-fns
                  (fty::visitorspec->type-fns
                   (cdr (assoc 'stmt-condcheck
                               (table-alist 'fty::visitor-templates (w state))))))
                 . ,(condcheck-ctx-to-condcheck!-fns *condcheck-ctx-types*))
    :fnname-template <type>-condcheck!))




(local (define def-condcheck-ctx-fn (x)
         :mode :program :hooks nil
         `((fty::defvisitors ,(intern$ (cat (symbol-name x) "-CONDCHECK-DEPS") "VL")
             :types (,x)
             :template condcheck)
           (define ,(intern$ (cat (symbol-name x) "-CONDCHECK!") "VL")
             ((x ,(intern$ (cat (symbol-name x) "-P") "VL")))
             :returns (warnings vl-warningtree-p)
             (vl-warningtree-context
              (,(intern$ (cat (symbol-name x) "-FIX") "VL") x)
              (,(intern$ (cat (symbol-name x) "-CONDCHECK!-AUX") "VL")
               x))))))

(local (define def-condcheck-contexts-fn (x)
         :mode :program :hooks nil
         (if (atom x)
             nil
           (append (def-condcheck-ctx-fn (car x))
                   (def-condcheck-contexts-fn (cdr x))))))



(make-event
 (cons 'progn (def-condcheck-contexts-fn *condcheck-ctx-types*)))

(fty::defvisitors module/interface/design-condcheck
  :template condcheck
  :types (vl-design vl-module vl-interface))

(define vl-module-condcheck ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((warnings (vl-module-condcheck! x)))
    (change-vl-module x :warnings (vl-warningtree-flatten-aux warnings nil (vl-module->warnings x)))))

(define vl-interface-condcheck ((x vl-interface-p))
  :returns (new-x vl-interface-p)
  (b* ((warnings (vl-interface-condcheck! x)))
    (change-vl-interface x :warnings (vl-warningtree-flatten-aux warnings nil (vl-interface->warnings x)))))

(defprojection vl-modulelist-condcheck ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-condcheck x))

(defprojection vl-interfacelist-condcheck ((x vl-interfacelist-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-condcheck x))

(define vl-design-condcheck ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (warnings (vl-warningtree-flatten-aux (vl-design-condcheck! x) nil x.warnings))
       (mods (vl-modulelist-condcheck x.mods))
       (interfaces (vl-interfacelist-condcheck x.interfaces)))
    (change-vl-design x :warnings warnings :mods mods :interfaces interfaces)))




       
  
