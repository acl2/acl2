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
(local (include-book "../util/arithmetic"))


(defsection qmarksize-check
  :parents (checkers)
  :short "Check the sizes of conditional expression tests."

  :long "<p>This is a heuristic for generating warnings.</p>

<p>We think it would be strange to see an expression like <tt>A ? B : C</tt>
where <tt>A</tt> is not one bit wide.  It found a few minor things that we
were able to clean up, but nothing that was really a bug.</p>

<p>Since the <tt>?:</tt> operator has the lowest precedence, expressions like
<tt>A & B ? C : D</tt> are parsed as <tt>(A & B) ? C : D</tt>, which might not
be what is intended.  In some cases, an actual precedence problem might be
revealed by seeing that the size of the test expression isn't 1.</p>")


(defsection vl-qmark-test-size
  :parents (qmarksize-check)
  :short "Determine the \"original size\" of the test expression for a
<tt>?:</tt> operator."

  :long "<p>This is an ugly hack.  @(call vl-qmark-test-size) is given an
exprsesion <tt>x</tt> which should be the <tt>test</tt> expression from a
conditional expression like:</p>

<code>
    test ? then : else
</code>

<p>Also, <tt>x</tt> should have already been sized.</p>

<p>Since @(see oprewrite) is applied before sizing, <tt>x</tt> has been
transformed and either looks like <tt>|A</tt> or <tt>~(|A)</tt>, where
<tt>A</tt> is the original version of <tt>x</tt>.</p>

<p>We want to return the width of <tt>A</tt>, rather than the width of
<tt>x</tt> (which is always just 1), so that we can detect cases where the test
expression that was given was wider than 1 bit.</p>

<p>To support this, @(see oprewrite) is set up so that it annotates the
<tt>|</tt> and <tt>~</tt> expressions it introduces with the
<tt>VL_CONDITIONAL_FIX</tt> attribute.  We check for this attribute in
order to know where to find <tt>A</tt>.</p>"

  (defund vl-qmark-test-size (x)
    (declare (xargs :guard (vl-expr-p x)))
    (b* (((when (vl-fast-atom-p x))
          (er hard? 'vl-qmark-test-size
              "Conditional test is not |A or ~|A.  ~x0.~%" x))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))

         ((unless (and (or (eq op :vl-unary-bitnot)
                           (eq op :vl-unary-bitor))
                       (assoc-equal "VL_CONDITIONAL_FIX" (vl-nonatom->atts x))))
          (er hard? 'vl-qmark-test-size
              "Conditional test is not |A or ~|A.  ~x0.~%" x))

         (arg1 (first args))
         ((when (eq op :vl-unary-bitor))
          (vl-expr->finalwidth arg1))

         ((unless (and (not (vl-fast-atom-p arg1))
                       (eq (vl-nonatom->op arg1) :vl-unary-bitor)
                       (assoc-equal "VL_CONDITIONAL_FIX" (vl-nonatom->atts arg1))))
          (er hard? 'vl-qmark-test-size
              "Conditional test is not |A or ~|A.  ~x0.~%" x)))

      (vl-expr->finalwidth (first (vl-nonatom->args arg1))))))


(defsection vl-expr-qmarksize-check
  :parents (qmarksize-check)
  :short "Look throughout an expression for any <tt>?:</tt> expressions that
have wide tests."

  :long "<p><b>Signature:</b> @(call vl-expr-qmarksize-check) returns a
@(see vl-warninglist-p).</p>

<p>We look through the expression <tt>x</tt> for any <tt>?:</tt>
sub-expressions with wide tests, and produce a warning whenever we find one.
The <tt>ctx</tt> is a @(see vl-context-p) that says where <tt>x</tt> occurs,
and is just used to generate more meaningful error messages.</p>"

  (mutual-recursion

   (defund vl-expr-qmarksize-check (x ctx)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-context-p ctx))
                     :measure (two-nats-measure (acl2-count x) 1)
                     :hints(("Goal" :in-theory (disable (force))))))
     (b* (((when (vl-fast-atom-p x))
           nil)
          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ((unless (eq op :vl-qmark))
           (vl-exprlist-qmarksize-check args ctx))

          (test-expr (first args))
          (test-size (vl-qmark-test-size test-expr))
          ((unless (equal test-size 1))
           (cons (make-vl-warning :type :vl-warn-qmark-width
                                  :msg "~a0: ~x1-bit wide \"test\" expression for ?: operator, ~a2."
                                  :args (list ctx test-size test-expr)
                                  :fatalp nil
                                  :fn 'vl-expr-qmarksize-check)
                 (vl-exprlist-qmarksize-check args ctx))))
       (vl-exprlist-qmarksize-check args ctx)))

   (defund vl-exprlist-qmarksize-check (x ctx)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-context-p ctx))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (append (vl-expr-qmarksize-check (car x) ctx)
               (vl-exprlist-qmarksize-check (cdr x) ctx)))))

  (flag::make-flag vl-flag-expr-qmarksize-check
                   vl-expr-qmarksize-check
                   :flag-mapping ((vl-expr-qmarksize-check . expr)
                                  (vl-exprlist-qmarksize-check . list)))

  (defthm-vl-flag-expr-qmarksize-check
    (defthm vl-warninglist-p-of-vl-expr-qmarksize-check
      (vl-warninglist-p (vl-expr-qmarksize-check x ctx))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-qmarksize-check
      (vl-warninglist-p (vl-exprlist-qmarksize-check x ctx))
      :flag list)
    :hints(("Goal" :expand ((vl-expr-qmarksize-check x ctx)
                            (vl-exprlist-qmarksize-check x ctx))))))



(defsection vl-exprctxalist-qmarksize-check
  :parents (qmarksize-check)
  :short "@(call vl-exprctxalist-qmarksize-check) extends @(see
vl-expr-qmarksize-check) across an @(see vl-exprctxalist-p)."

  (defund vl-exprctxalist-qmarksize-check (x)
    (declare (xargs :guard (vl-exprctxalist-p x)))
    (if (atom x)
        nil
      (append (vl-expr-qmarksize-check (caar x) (cdar x))
              (vl-exprctxalist-qmarksize-check (cdr x)))))

  (defthm vl-warninglist-p-of-vl-exprctxalist-qmarksize-check
    (vl-warninglist-p (vl-exprctxalist-qmarksize-check x))
    :hints(("Goal" :in-theory (enable vl-exprctxalist-qmarksize-check)))))



(defsection vl-module-qmarksize-check
  :parents (qmarksize-check)
  :short "@(call vl-module-qmarksize-check) carries our our @(see
qmarksize-check) on all the expressions in a module, and adds any resulting
warnings to the module."

  (defund vl-module-qmarksize-check (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* ((ctxexprs     (vl-module-ctxexprs x))
         (new-warnings (vl-exprctxalist-qmarksize-check ctxexprs)))
      (change-vl-module x
                        :warnings (append new-warnings (vl-module->warnings x)))))

  (local (in-theory (enable vl-module-qmarksize-check)))

  (defthm vl-module-p-of-vl-module-qmarksize-check
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-qmarksize-check x))))

  (defthm vl-module->name-of-vl-module-qmarksize-check
    (equal (vl-module->name (vl-module-qmarksize-check x))
           (vl-module->name x))))


(defprojection vl-modulelist-qmarksize-check (x)
  (vl-module-qmarksize-check x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (qmarksize-check))

(defthm vl-modulelist->names-of-vl-modulelist-qmarksize-check
  (equal (vl-modulelist->names (vl-modulelist-qmarksize-check x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))


