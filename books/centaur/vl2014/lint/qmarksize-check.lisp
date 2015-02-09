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
(local (include-book "../util/arithmetic"))

(defsection qmarksize-check
  :parents (lint)
  :short "Check the sizes of conditional expression tests."

  :long "<p>This is a heuristic for generating warnings.</p>

<p>We think it would be strange to see an expression like @('A ? B : C') where
@('A') is not one bit wide.  It found a few minor things that we were able to
clean up, but nothing that was really a bug.</p>

<p>Since the @('?:') operator has the lowest precedence, expressions like @('A
& B ? C : D') are parsed as @('(A & B) ? C : D'), which might not be what is
intended.  In some cases, an actual precedence problem might be revealed by
seeing that the size of the test expression isn't 1.</p>")

(local (xdoc::set-default-parents qmarksize-check))


(define vl-qmark-test-size
  :short "Determine the \"original size\" of the test expression for a @('?:')
operator."
  ((x vl-expr-p))
  :long "<p>This is an ugly hack.  @(call vl-qmark-test-size) is given an
exprsesion @('x') which should be the @('test') expression from a conditional
expression like:</p>

@({
    test ? then : else
})

<p>Also, @('x') should have already been sized.</p>

<p>Since @(see oprewrite) is applied before sizing, @('x') has been transformed
and either looks like @('|A') or @('~(|A)'), where @('A') is the original
version of @('x').</p>

<p>We want to return the width of @('A'), rather than the width of
@('x') (which is always just 1), so that we can detect cases where the test
expression that was given was wider than 1 bit.</p>

<p>To support this, @(see oprewrite) is set up so that it annotates the @('|')
and @('~') expressions it introduces with the @('VL_CONDITIONAL_FIX')
attribute.  We check for this attribute in order to know where to find
@('A').</p>"

  (b* (((when (vl-fast-atom-p x))
        (vl-expr->finalwidth x))
       (op   (vl-nonatom->op x))
       (args (vl-nonatom->args x))

       ((unless (and (or (eq op :vl-unary-bitnot)
                         (eq op :vl-unary-bitor))
                     (assoc-equal "VL_CONDITIONAL_FIX" (vl-nonatom->atts x))))
        (vl-expr->finalwidth x))

       (arg1 (first args))
       ((when (eq op :vl-unary-bitor))
        (vl-expr->finalwidth arg1))

       ((unless (and (not (vl-fast-atom-p arg1))
                     (eq (vl-nonatom->op arg1) :vl-unary-bitor)
                     (assoc-equal "VL_CONDITIONAL_FIX" (vl-nonatom->atts arg1))))
        (raise "Malformed oprewrite conditional fix?  ~x0.~%" x)))

    (vl-expr->finalwidth (first (vl-nonatom->args arg1)))))

(defines vl-expr-qmarksize-check
  :short "Look throughout an expression for any @('?:') expressions that have
wide tests."

  :long "<p>We look through the expression @('x') for any @('?:')
sub-expressions with wide tests, and produce a warning whenever we find one.
The @('ctx') is a @(see vl-context-p) that says where @('x') occurs, and is
just used to generate more meaningful error messages.</p>"

  (define vl-expr-qmarksize-check ((x   vl-expr-p)
                                   (ctx vl-context-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-expr-count x)
    (b* (((when (vl-fast-atom-p x))
          nil)
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))

         ((unless (eq op :vl-qmark))
          (vl-exprlist-qmarksize-check args ctx))

         (test-expr (first args))
         (test-size (vl-qmark-test-size test-expr))
         ((unless (or (equal test-size 1)
                      ;; Historically we didn't have this extra exclusion for
                      ;; nil test sizes.  I later discovered that, e.g., due
                      ;; to using arrays or other things that VL doesn't
                      ;; support, we could run into a case like:
                      ;;
                      ;;    wire [2:0] foo;
                      ;;    wire bar;
                      ;;
                      ;;    assign foo = bar ? bad-expression : 3'b0;
                      ;;
                      ;; Here BAR is a perfectly good expression, but due to
                      ;; the bad-expression, our sizing code will fail to
                      ;; assign any size to BAR.
                      ;;
                      ;; In this case, the warning we produced was very
                      ;; confusing because the condition is obviously just a
                      ;; single bit.  I think it just doesn't make sense to
                      ;; try to create a warning in this case, so now we will
                      ;; suppress these.
                      (not test-size)))
          (cons (make-vl-warning
                 :type :vl-warn-qmark-width
                 :msg "~a0: ~x1-bit wide \"test\" expression for ?: operator, ~a2."
                 :args (list ctx test-size test-expr)
                 :fatalp nil
                 :fn __function__)
                (vl-exprlist-qmarksize-check args ctx))))
      (vl-exprlist-qmarksize-check args ctx)))

  (define vl-exprlist-qmarksize-check ((x   vl-exprlist-p)
                                       (ctx vl-context-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-expr-qmarksize-check (car x) ctx)
              (vl-exprlist-qmarksize-check (cdr x) ctx)))))


(define vl-exprctxalist-qmarksize-check
  :short "@(call vl-exprctxalist-qmarksize-check) extends @(see
vl-expr-qmarksize-check) across an @(see vl-exprctxalist-p)."
  ((x vl-exprctxalist-p))
  :returns (warnings vl-warninglist-p)
  (if (atom x)
      nil
    (append (vl-expr-qmarksize-check (caar x) (cdar x))
            (vl-exprctxalist-qmarksize-check (cdr x)))))


(define vl-module-qmarksize-check
  :short "@(call vl-module-qmarksize-check) carries our our @(see
qmarksize-check) on all the expressions in a module, and adds any resulting
warnings to the module."
  ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((when (vl-module->hands-offp x))
        ;; don't check things like vl_1_bit_latch if they're already defined somehow
        x)
       (ctxexprs     (vl-module-ctxexprs x))
       (new-warnings (vl-exprctxalist-qmarksize-check ctxexprs)))
    (change-vl-module x
                      :warnings (append new-warnings (vl-module->warnings x)))))

(defprojection vl-modulelist-qmarksize-check (x)
  (vl-module-qmarksize-check x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-qmarksize-check ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-qmarksize-check x.mods))))
