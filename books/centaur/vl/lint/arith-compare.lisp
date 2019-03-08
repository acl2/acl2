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
(include-book "../../sv/vl/expr")
(local (include-book "../util/arithmetic"))

(defsection arith-compare-check
  :parents (vl-lint)
  :short "Warn about comparisons involving arithmetic operators."

  :long "<p>This is a heuristic for generating warnings.</p>

<p>Often an expression like @('a + b >= c') conceals a bug where the size of
@('a + b') isn't big enough to represent all its possible values.  Instead of
doing something smarter, we just warn about all occurrences of comparisons
where one side is a plus, minus, multiply, or divide expression.</p>")

(local (xdoc::set-default-parents arith-compare-check))

(define vl-expr-is-arith ((x vl-expr-p))
  :measure (vl-expr-count x)
  (b* ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-unary
      (and (member x.op '(:vl-unary-plus :vl-unary-minus))
           (vl-expr-is-arith x.arg))
      :vl-binary
      (member x.op '(:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div))
      :otherwise nil)))

(define vl-arith-range-from-size/type ((ctxsize natp)
                                       (type vl-exprsign-p))
  :returns (mv (ok)
               (min integerp :rule-classes :type-prescription)
               (max integerp :rule-classes :type-prescription))
  (case (vl-exprsign-fix type)
    (:vl-unsigned (mv t 0 (1- (ash 1 (lnfix ctxsize)))) )
    (t            (mv t
                      (-  (ash 1 (max 0 (1- (lnfix ctxsize)))))
                      (1- (ash 1 (max 0 (1- (lnfix ctxsize)))))))))


(define vl-expr-arith-range-from-size/type ((x vl-expr-p)
                                            (ss vl-scopestack-p)
                                            (scopes vl-elabscopes-p))
  :returns (mv (ok)
               (min integerp :rule-classes :type-prescription)
               (max integerp :rule-classes :type-prescription))
  (b* (((mv ?warn size) (vl-expr-selfsize x ss scopes))
       ((mv ?warn class) (vl-expr-typedecide x ss scopes))
       ((unless (and size (vl-integer-arithclass-p class)))
        (mv nil 0 0)))
    (vl-arith-range-from-size/type size (vl-integer-arithclass->exprsign class))))


(define my-trunc ((x integerp) (y integerp))
  (mbe :logic (truncate x y)
       :exec (if (eql y 0) 0 (truncate x y))))



(local (in-theory (disable (tau-system) min max not)))

(local (defthm posp-max
         (implies (and (integerp x) (posp y))
                  (posp (max x y)))
         :hints(("Goal" :in-theory (enable max)))
         :rule-classes :type-prescription))

(define vl-arith-expr-range ((x vl-expr-p)
                             (ctxsize natp)
                             (type vl-exprsign-p)
                             (ss vl-scopestack-p)
                             (scopes vl-elabscopes-p))
  :returns (mv ok
               (min integerp :rule-classes :type-prescription)
               (max integerp :rule-classes :type-prescription))
  :verify-guards nil
  :measure (vl-expr-count x)
  ;; :prepwork ((local (defthm integerp-*
  ;;                     (implies (and (integerp x) (integerp y))
  ;;                              (integerp (* x y)))
  ;;                     :rule-classes (:rewrite :type-prescription))))
  (b* ((type (vl-exprsign-fix type)))
    (vl-expr-case x
      :vl-literal (vl-value-case x.val
                    :vl-constint (case type
                                   (:vl-unsigned
                                    (b* ((val (acl2::loghead ctxsize x.val.value)))
                                      (mv t val val)))
                                   (t
                                    (b* ((val (acl2::logext (max (lnfix ctxsize) 1) x.val.value)))
                                      (mv t val val))))
                    :vl-extint (prog2$ (and (eq type :vl-signed)
                                            (raise "Expected extints to always be in an unsigned context"))
                                       (case x.val.value
                                         (:vl-0val (mv t 0 0))
                                         (:vl-1val
                                          (b* ((val (acl2::loghead ctxsize -1)))
                                            (mv t val val)))
                                         (t (mv nil 0 0))))
                    :otherwise (mv nil 0 0))
      :vl-index (b* (((mv ?vttree svex ?indtype) (vl-index-expr-to-svex x ss scopes))
                     ((unless (sv::svex-case svex :quote (sv::2vec-p svex.val) :otherwise nil))
                      (vl-expr-arith-range-from-size/type x ss scopes))
                     (val (sv::2vec->val (sv::svex-quote->val svex))))
                  (mv t val val))
      :vl-unary (b* (((when (eq x.op :vl-unary-plus))
                      (vl-arith-expr-range x.arg ctxsize type ss scopes))
                     ((unless (eq x.op :vl-unary-minus))
                      (vl-expr-arith-range-from-size/type x ss scopes))
                     ((mv arg-ok arg-min arg-max) (vl-arith-expr-range x.arg ctxsize type ss scopes))
                     ((unless arg-ok) (mv nil 0 0)))
                  (mv t (- (lifix arg-max)) (- (lifix arg-min))))
      :vl-binary (b* (((unless (member x.op '(:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div)))
                       (vl-expr-arith-range-from-size/type x ss scopes))
                      ((mv left-ok left-min left-max) (vl-arith-expr-range x.left ctxsize type ss scopes))
                      ((mv right-ok right-min right-max) (vl-arith-expr-range x.right ctxsize type ss scopes))
                      ((unless (and left-ok right-ok)) (mv nil 0 0))
                      (left-min (lifix left-min))
                      (right-min (lifix right-min))
                      (left-max (lifix left-max))
                      (right-max (lifix right-max))
                      (min (case x.op
                             (:vl-binary-plus (+ left-min right-min))
                             (:vl-binary-minus (- left-min right-max))
                             ;; kind of silly way to do it
                             (:vl-binary-times (min (min (* left-min right-min)
                                                         (* left-min right-max))
                                                    (min (* left-max right-min)
                                                         (* left-max right-max))))
                             (t (min (min (my-trunc left-min right-min)
                                          (my-trunc left-min right-max))
                                     (min (my-trunc left-max right-min)
                                          (my-trunc left-max right-max))))))
                      (max (case x.op
                             (:vl-binary-plus (+ left-max right-max))
                             (:vl-binary-minus (- left-max right-min))
                             ;; kind of silly way to do it
                             (:vl-binary-times (max (max (* left-min right-min)
                                                         (* left-min right-max))
                                                    (max (* left-max right-min)
                                                         (* left-max right-max))))
                             (t (max (max (my-trunc left-min right-min)
                                          (my-trunc left-min right-max))
                                     (max (my-trunc left-max right-min)
                                          (my-trunc left-max right-max)))))))
                   (mv t min max))
      :otherwise (vl-expr-arith-range-from-size/type x ss scopes)))
  ///
  (verify-guards vl-arith-expr-range))
    

(define vl-expr-arith-compare-warn ((x vl-expr-p)
                                    (ss vl-scopestack-p))
  ;; (declare (ignore ss))
  :returns (warnings vl::vl-warninglist-p)
  (b* ((x (vl-expr-fix x))
       (warnings nil))
    (vl-expr-case x
      :vl-binary
      (and (member x.op '(:vl-binary-eq :vl-binary-neq :vl-binary-lt :vl-binary-lte :vl-binary-gt :vl-binary-gte
                          ;; maybe?
                          :vl-binary-ceq :vl-binary-cne :vl-binary-wildeq :vl-binary-wildneq
                          ))
           (or (vl-expr-is-arith x.left)
               (vl-expr-is-arith x.right))
           ;; (warn :type :vl-warn-arithmetic-comparison
           ;;       :msg "The comparison ~a0 involves an arithmetic expression ~
           ;;             on ~s1.  Such expressions are often not sized ~
           ;;             according to reasonable expectations."
           ;;       :args (list x (if (vl-expr-is-arith x.left)
           ;;                         (if (vl-expr-is-arith x.right)
           ;;                             "both sides"
           ;;                           "the left-hand side")
           ;;                       "the right-hand side")))
           (b* ((scopes (vl-elabscopes-init-ss ss))
                ((mv ?warns left-size) (vl-expr-selfsize x.left ss scopes))
                ((mv ?warns right-size) (vl-expr-selfsize x.right ss scopes))
                ((mv ?warns left-class) (vl-expr-typedecide x.left ss scopes))
                ((mv ?warns right-class) (vl-expr-typedecide x.right ss scopes))
                ((unless (and left-size right-size
                              (vl-integer-arithclass-p left-class)
                              (vl-integer-arithclass-p right-class)))
                 nil)
                (size (max left-size right-size))
                (type (vl-integer-arithclass->exprsign (vl-arithclass-max left-class right-class)))
                ((mv left-ok left-min left-max) (vl-arith-expr-range x.left size type ss scopes))
                ((mv right-ok right-min right-max) (vl-arith-expr-range x.right size type ss scopes))
                ((mv ?ok size-min size-max) (vl-arith-range-from-size/type size type))
                ((unless (and left-ok right-ok)) nil)
                ((mv left-warning left-severity)
                 (if (vl-expr-is-arith x.left)
                     (cond ((> left-max size-max)
                            (mv t t))
                           ((< left-min size-min)
                            (mv t nil))
                           (t (mv nil nil)))
                   (mv nil nil)))
                ((mv right-warning right-severity)
                 (if (vl-expr-is-arith x.right)
                     (cond ((> right-max size-max)
                            (mv t t))
                           ((< right-min size-min)
                            (mv t nil))
                           (t (mv nil nil)))
                   (mv nil nil)))
                ((unless (or left-warning right-warning)) nil)
                (severity (or (and left-warning left-severity)
                              (and right-warning right-severity)))
                (left-msg (and left-warning
                               (vmsg "the value range of the left-hand-side may ~
                                     ~s0~s1 that."
                                     (if (> left-max size-max) "overflow" "underflow")
                                     (if (and (> left-max size-max) (< left-min size-min))
                                         " or underflow" ""))))
                (right-msg (and right-warning
                                (vmsg "the value range of the right-hand-side may ~
                                     ~s0~s1 that."
                                     (if (> right-max size-max) "overflow" "underflow")
                                     (if (and (> right-max size-max) (< right-min size-min))
                                         " or underflow" ""))))
                (first-msg (or left-msg right-msg))
                (second-msg (if (and left-msg right-msg)
                                (vmsg "  Additionally, ~@0" right-msg)
                              "")))
             (warn :type (if severity
                             :vl-warn-arithmetic-comparison
                           :vl-warn-arithmetic-comparison-minor)
                   :msg "The comparison ~a0 involves an arithmetic expression ~
                         on ~s1.  Such expressions are often not sized ~
                         according to reasonable expectations.  The final ~
                         size of both sides is ~x2 (~s3), but ~@4~@5"
                   :args (list x (if left-warning
                                     (if right-warning
                                         "both sides"
                                       "the left-hand side")
                                   "the right-hand side")
                               size
                               (if (eq (vl-exprsign-fix type) :vl-unsigned) "unsigned" "signed")
                               first-msg second-msg))))
      :otherwise nil)))

(defines vl-expr-arith-compare-check
  :short "Look throughout an expression for any @('?:') expressions that have
wide tests."

  :long "<p>We look through the expression @('x') for any @('?:')
sub-expressions with wide tests, and produce a warning whenever we find one.
The @('ctx') is a @(see vl-context-p) that says where @('x') occurs, and is
just used to generate more meaningful error messages.</p>"

  (define vl-expr-arith-compare-check ((x   vl-expr-p)
                                       (ss vl-scopestack-p))
    :returns (warnings (and (vl-warninglist-p warnings)
                            (true-listp warnings)))
    :measure (vl-expr-count x)
    :verify-guards nil
    (append-without-guard
     (vl-expr-arith-compare-warn x ss)
     (vl-exprlist-arith-compare-check (vl-expr->subexprs x) ss)))

  (define vl-exprlist-arith-compare-check ((x vl-exprlist-p)
                                           (ss vl-scopestack-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append
       (vl-expr-arith-compare-check (car x) ss)
       (vl-exprlist-arith-compare-check (cdr x) ss))))
  ///
  (verify-guards vl-expr-arith-compare-check))

(def-expr-check arith-compare-check)

