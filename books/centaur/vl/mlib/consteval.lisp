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
(include-book "../transforms/xf-expr-size")
(include-book "centaur/bitops/fast-logext" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (xdoc::set-default-parents vl-consteval))

(local (defthm integerp-of-rem
         (implies (and (integerp a)
                       (integerp b))
                  (integerp (rem a b)))
         :rule-classes :type-prescription
         :hints(("Goal" :in-theory (enable rem truncate)))))

(local (in-theory (enable vl-expr-welltyped-p)))

(local (defthm vl-nonatom->finalwidth-removal
         (implies (force (equal (vl-expr-kind x) :nonatom))
                  (equal (vl-nonatom->finalwidth x)
                         (vl-expr->finalwidth x)))
         :hints(("Goal" :in-theory (enable vl-expr->finalwidth)))))

(local (defthm vl-nonatom->finaltype-removal
         (implies (force (equal (vl-expr-kind x) :nonatom))
                  (equal (vl-nonatom->finaltype x)
                         (vl-expr->finaltype x)))
         :hints(("Goal" :in-theory (enable vl-expr->finaltype)))))


(defval *vl-fake-module-for-vl-consteval*
  (make-vl-module :name "VL_FAKE_MODULE_FOR_VL_CONSTEVAL"
                  :origname "VL_FAKE_MODULE_FOR_VL_CONSTEVAL"
                  :minloc *vl-fakeloc*
                  :maxloc *vl-fakeloc*))

(defval *vl-fake-ialist-for-vl-consteval*
  nil)

(defval *vl-fake-elem-for-vl-consteval*
  (make-vl-vardecl :name "VL_FAKE_ELEM_FOR_VL_CONSTEVAL"
                   :type *vl-plain-old-wire-type*
                   :loc *vl-fakeloc*))

(local (assert! (equal (vl-moditem-alist *vl-fake-module-for-vl-consteval*)
                       *vl-fake-ialist-for-vl-consteval*)))

(define vl-consteval-ans (&key (value natp)
                               (width posp)
                               (type  vl-exprtype-p))
  :returns (ans vl-expr-p)
  :guard (< value (expt 2 width))
  (b* ((width (lposfix width))
       (type  (vl-exprtype-fix type))
       (guts  (make-vl-constint :value value
                                :origwidth width
                                :origtype type))
       (ans   (make-vl-atom :guts guts
                            :finalwidth width
                            :finaltype type)))
    ans)
  ///
  (defthm vl-expr-resolved-p-of-vl-consteval-ans
    (vl-expr-resolved-p (vl-consteval-ans :value value
                                          :width width
                                          :type type))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p))))

  (defthm vl-expr-welltyped-p-of-vl-consteval-ans
    (vl-expr-welltyped-p (vl-consteval-ans :value value
                                           :width width
                                           :type type))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-atom-welltyped-p))))

  (defthm vl-expr->finalwidth-of-vl-consteval-ans
    (equal (vl-expr->finalwidth (vl-consteval-ans :value value
                                                  :width width
                                                  :type type))
           (pos-fix width)))

  (defthm vl-expr->finaltype-of-vl-consteval-ans
    (equal (vl-expr->finaltype (vl-consteval-ans :value value
                                                 :width width
                                                 :type type))
           (vl-exprtype-fix type))))


(local (in-theory (disable acl2::unsigned-byte-p
                           acl2::loghead-identity
                           vl-expr-p-when-vl-maybe-expr-p
                           MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                           acl2::subsetp-member
                           default-car
                           default-cdr
                           truncate
                           rem
                           double-containment
                           abs
                           VL-NONATOM->OP-WHEN-HIDINDEX-RESOLVED-P
                           VL-HIDINDEX-RESOLVED-P-WHEN-VL-HIDEXPR-RESOLVED-P
                           VL-EXPR-RESOLVED-P-OF-CAR-WHEN-VL-EXPRLIST-RESOLVED-P
                           VL-ATOM-P-OF-CAR-WHEN-VL-ATOMLIST-P
                           ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP

                           ACL2::NATP-POSP
                           ACL2::POSP-REDEFINITION
                           NATP-WHEN-POSP
                           INTEGERP-WHEN-NATP
                           ACL2::ZP-OPEN
                           ACL2::ZP-WHEN-INTEGERP
                           ACL2::ZP-WHEN-GT-0
                           ACL2::POSP-RW
                           SUM-NATS-WHEN-ALL-EQUALP-1
                           acl2::MEMBER-EQUAL-WHEN-ALL-EQUALP
                           VL-HIDINDEX-P-WHEN-VL-HIDEXPR-P
                           all-equalp
                           CONSP-OF-VL-EXPRLIST->FINALWIDTHS
                           LEN-OF-VL-NONATOM->ARGS-WHEN-VL-HIDINDEX-P
                           VL-HIDEXPR-P-WHEN-VL-HIDINDEX-P
                           (:TYPE-PRESCRIPTION VL-HIDINDEX-P)
                           LEN-OF-VL-NONATOM->ARGS-WHEN-VL-HIDEXPR-P
                           (:TYPE-PRESCRIPTION VL-NONATOM->OP$INLINE)
                           VL-EXPR-KIND-WHEN-VL-$RANDOM-EXPR-P
                           VL-NONATOM->OP-WHEN-VL-HIDINDEX-P
                           acl2::CAR-WHEN-ALL-EQUALP

                           ACL2::CANCEL_TIMES-EQUAL-CORRECT
                           ACL2::CANCEL_PLUS-EQUAL-CORRECT
                           ACL2::TRUE-LISTP-MEMBER-EQUAL

                           VL-NONATOM->OP$INLINE-OF-VL-EXPR-FIX-X-NORMALIZE-CONST
                           )))

;; Stupid little functions to avoid lots of case splitting.

(define vl-consteval-binop
  ((op (member op '(:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
                    :vl-binary-rem :vl-binary-bitand :vl-binary-bitor :vl-binary-xor
                    :vl-binary-xnor)))
   (aval natp)
   (bval natp))
  :guard (implies (member op '(:vl-binary-div :vl-binary-rem))
                  (posp bval))
  :returns (ans integerp :rule-classes :type-prescription)
  (b* ((aval (lnfix aval))
       (bval (lnfix bval)))
    (case op
      (:vl-binary-plus   (+ aval bval))
      (:vl-binary-minus  (- aval bval))
      (:vl-binary-times  (* aval bval))
      (:vl-binary-div    (truncate aval bval))
      (:vl-binary-rem    (rem aval bval))
      (:vl-binary-bitand (logand aval bval))
      (:vl-binary-bitor  (logior aval bval))
      (:vl-binary-xor    (logxor aval bval))
      (:vl-binary-xnor   (lognot (logxor aval bval)))
      (otherwise         (progn$ (impossible) 0)))))

(define vl-consteval-wideunary
  ((op (member op '(:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)))
   (aval natp))
  :returns (ans integerp :rule-classes :type-prescription)
  (b* ((aval (lnfix aval)))
    (case op
      (:vl-unary-plus   aval)
      (:vl-unary-minus  (- aval))
      (:vl-unary-bitnot (lognot aval))
      (otherwise        (progn$ (impossible) 0)))))

(define vl-consteval-cmpop
  ((op (member op '(:vl-binary-ceq :vl-binary-cne :vl-binary-eq :vl-binary-neq
                    :vl-binary-gt :vl-binary-gte :vl-binary-lt :vl-binary-lte)))
   (aval natp)
   (bval natp))
  :returns (ans acl2::bitp)
  (b* ((aval (lnfix aval))
       (bval (lnfix bval)))
    (case op
      ;; Since we're only dealing with constant integers, there's no difference
      ;; between case and ordinary equality
      ((:vl-binary-ceq :vl-binary-eq)  (if (equal aval bval) 1 0))
      ((:vl-binary-cne :vl-binary-neq) (if (equal aval bval) 0 1))
      (:vl-binary-gt                   (if (>  aval bval) 1 0))
      (:vl-binary-gte                  (if (>= aval bval) 1 0))
      (:vl-binary-lt                   (if (<  aval bval) 1 0))
      (:vl-binary-lte                  (if (<= aval bval) 1 0))
      (otherwise                       (progn$ (impossible) 0)))))

(define vl-consteval-binlogic
  ((op (member op '(:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)))
   (aval natp)
   (bval natp))
  :returns (ans acl2::bitp)
  (b* ((aval (lnfix aval))
       (bval (lnfix bval)))
    (case op
      (:vl-binary-logand  (if (and (posp aval) (posp bval))     1 0))
      (:vl-binary-logor   (if (or  (posp aval) (posp bval))     1 0))
      (:vl-implies        (if (implies (posp aval) (posp bval)) 1 0))
      (:vl-equiv          (if (equal (posp aval) (posp bval))   1 0))
      (otherwise          (progn$ (impossible) 0)))))

(define vl-consteval-unary-reduxop
  ((op (member op '(:vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
                    :vl-unary-xor :vl-unary-xnor :vl-unary-lognot)))
   (aval natp)
   (width posp))
  :returns (ans acl2::bitp)
  (b* ((aval (lnfix aval)))
    (case op
      (:vl-unary-bitand (if (equal (acl2::loghead width aval) (1- (expt 2 width))) 1 0))
      (:vl-unary-nand   (if (equal (acl2::loghead width aval) (1- (expt 2 width))) 0 1))
      (:vl-unary-bitor  (if (posp aval) 1 0))
      (:vl-unary-nor    (if (posp aval) 0 1))
      (:vl-unary-xor    (if (oddp aval) 1 0))
      (:vl-unary-xnor   (if (oddp aval) 0 1))
      (:vl-unary-lognot (if (posp aval) 0 1))
      (otherwise        (progn$ (impossible) 0)))))

(define vl-consteval-shiftop
  ((op     (member op '(:vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl :vl-binary-power)))
   (aval   natp)
   (bval   natp)
   (awidth posp)
   (atype  vl-exprtype-p))
  :returns (ans integerp)
  (b* ((aval    (lnfix aval))
       (bval    (lnfix bval))
       (awidth  (lposfix awidth))
       (ainterp (if (eq atype :vl-signed)
                    (acl2::fast-logext awidth aval)
                  aval)))
    (case op
      (:vl-binary-shr   (ash aval (- bval)))
      (:vl-binary-shl   (ash aval bval))
      (:vl-binary-ashr  (ash ainterp (- bval)))
      (:vl-binary-ashl  (ash ainterp bval))
      (:vl-binary-power (expt ainterp bval))
      (otherwise        (progn$ (impossible) 0)))))

(define vl-consteval-main ((x vl-expr-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (ans      vl-expr-p))
  :guard (vl-expr-welltyped-p x)
  :measure (vl-expr-count x)
  :verify-guards nil
  (b* ((x (vl-expr-fix x))
       ((when (vl-expr-resolved-p x))
        (mv t x))
       ((unless (eq (vl-expr-kind x) :nonatom))
        (mv nil x))
       ((vl-nonatom x) x))
    (case x.op
      ((:vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
        :vl-binary-rem :vl-binary-bitand :vl-binary-bitor :vl-binary-xor
        :vl-binary-xnor)
       ;; See vl-expr-welltyped-p.  We know that the argument widths and types
       ;; agree with the width/type of x.
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((mv bok b) (vl-consteval-main (second x.args)))
            ((unless (and aok bok))
             (mv nil x))
            (aval   (vl-resolved->val a))
            (bval   (vl-resolved->val b))
            ((when (and (member x.op '(:vl-binary-div :vl-binary-rem))
                        (zp bval)))
             ;; Whoops, trying to divide by zero.
             (mv nil x))
            (ans    (vl-consteval-ans
                     :value (acl2::loghead x.finalwidth (vl-consteval-binop x.op aval bval))
                     :width x.finalwidth
                     :type  x.finaltype)))
         (mv t ans)))

      ((:vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
       ;; See vl-expr-welltyped-p.  We know that the argument's size and type
       ;; agrees with the width/type of X.
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((unless aok)
             (mv nil x))
            (aval (vl-resolved->val a))
            (ans  (vl-consteval-ans
                   :value (acl2::loghead x.finalwidth (vl-consteval-wideunary x.op aval))
                   :width x.finalwidth
                   :type x.finaltype)))
         (mv t ans)))

      ((:vl-binary-ceq :vl-binary-cne :vl-binary-eq :vl-binary-neq
        :vl-binary-gt :vl-binary-gte :vl-binary-lt :vl-binary-lte)
       ;; See vl-expr-welltyped-p.  We know that the result is a 1-bit unsigned
       ;; number.  We know that the two operands agree on their sizes and
       ;; types.
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((mv bok b) (vl-consteval-main (second x.args)))
            ((unless (and aok bok))
             (mv nil x))
            (aval (vl-resolved->val a))
            (bval (vl-resolved->val b))
            (ans  (vl-consteval-ans :value (vl-consteval-cmpop x.op aval bval)
                                    :width 1
                                    :type :vl-unsigned)))
         (mv t ans)))

      ((:vl-binary-logand :vl-binary-logor :vl-implies :vl-equiv)
       ;; See vl-expr-welltyped-p.  We know the result is a 1-bit unsigned.
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((mv bok b) (vl-consteval-main (second x.args)))
            ((unless (and aok bok))
             (mv nil x))
            (aval (vl-resolved->val a))
            (bval (vl-resolved->val b))
            (ans  (vl-consteval-ans :value (vl-consteval-binlogic x.op aval bval)
                                    :width 1
                                    :type :vl-unsigned)))
         (mv t ans)))


      ((:vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
        :vl-unary-xor :vl-unary-xnor :vl-unary-lognot)
       ;; See vl-expr-welltyped-p.  We know the result is a 1-bit unsigned.
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((unless aok)
             (mv nil x))
            (aval   (vl-resolved->val a))
            (awidth (vl-expr->finalwidth a))
            (ans    (vl-consteval-ans :value (vl-consteval-unary-reduxop x.op aval awidth)
                                      :width 1
                                      :type :vl-unsigned)))
         (mv t ans)))

      ((:vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl
        :vl-binary-power)
       ;; See vl-expr-welltyped-p.  See sizing minutia.  The exponent or shift
       ;; amount part has a type that doesn't matter, it is always treated as
       ;; an unsigned/positive number.  The size/type of A always agree with X.
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((mv bok b) (vl-consteval-main (second x.args)))
            ((unless (and aok bok))
             (mv nil x))
            (aval (vl-resolved->val a))
            (bval (vl-resolved->val b))
            (ans  (vl-consteval-ans :value (acl2::loghead x.finalwidth
                                                          (vl-consteval-shiftop x.op aval bval
                                                                                x.finalwidth x.finaltype))
                                    :width x.finalwidth
                                    :type  x.finaltype)))
         (mv t ans)))

      ((:vl-qmark)
       (b* (((mv aok a) (vl-consteval-main (first x.args)))
            ((mv bok b) (vl-consteval-main (second x.args)))
            ((mv cok c) (vl-consteval-main (third x.args)))
            ((unless (and aok bok cok))
             (mv nil x))
            (ans (if (posp (vl-resolved->val a)) b c)))
         (mv t ans)))

      ;; BOZO could eventually add support for other operators like
      ;; concatenation, bitselect, etc.  But the above is probably pretty
      ;; good and should be good enough for most cases.
      (otherwise
       (mv nil x))))


  :prepwork
  (
   ;; Baseline (after accumulated-persistence hacking above, before adding
   ;; welltyped-p theorem.  Accumulated-persistence enabled.)
   ;; Time:  176.51 seconds (prove: 176.35, print: 0.14, other: 0.03)

   ;; Deferred enabling of vl-expr-welltyped-p:
   ;; Time:  157.17 seconds (prove: 156.96, print: 0.19, other: 0.03)
   (local (in-theory (disable vl-expr-welltyped-p)))

   ;; Fancy trick to try to resolve these membership things faster:
   (local (defthm fancy-solve-member-consts
            (implies (and (syntaxp (quotep x))
                          (member a free)
                          (syntaxp (quotep free))
                          (not (intersectp-equal x free)))
                     (equal (member a x)
                            nil))
            :hints((set-reasoning))))

   (local (defthm member-of-singleton
            (iff (member a (cons x nil))
                 (equal a x))))

   (local (in-theory (disable acl2::member-of-cons acl2::member-when-atom)))

   ;; This is pretty good:
   ;; (add-default-hints
   ;;  '((and stable-under-simplificationp
   ;;         '(:expand (vl-expr-welltyped-p x)
   ;;           :in-theory (enable acl2::member-of-cons)))))

   ;; This seems a bit better, still pretty slow, ~60s for all the proofs.
   (add-default-hints
    '((and stable-under-simplificationp
           '(:expand (vl-expr-welltyped-p x)))
      (and stable-under-simplificationp
           '(:in-theory (enable acl2::member-of-cons
                                acl2::member-when-atom))))))

  ///

  (more-returns
   (ans (vl-expr-welltyped-p ans)
        :hyp (vl-expr-welltyped-p x)
        :name vl-expr-welltyped-p-of-vl-consteval-main)

   (ans (equal (vl-expr->finalwidth ans) (vl-expr->finalwidth x))
        :hyp (vl-expr-welltyped-p x)
        :name vl-expr->finalwidth-of-vl-consteval-main)

   (ans (equal (vl-expr->finaltype ans) (vl-expr->finaltype x))
        :hyp (vl-expr-welltyped-p x)
        :name vl-expr->finaltype-of-vl-consteval-main)

   (ans (implies successp (vl-expr-resolved-p ans))
        :hyp (vl-expr-welltyped-p x)
        :name vl-expr-resolved-p-of-vl-consteval-main))

  (verify-guards vl-consteval-main))



(define vl-consteval
  :parents (mlib)
  :short "An evaluator for a small set of \"constant expressions\" in Verilog."
  ((x vl-expr-p "Expression to try to evaluate."))
  :returns (mv (successp booleanp :rule-classes :type-prescription
                         "Indicates whether we successfully sized and evaluated
                         @('x') to a constant.")
               (ans      vl-expr-p
                         "On success, a resolved, constant expression with the
                          appropriate width and size."))

  :long "<p>This is a careful, limited evaluator for a small subset of Verilog
expressions.  It is intended to be safe for use in contexts such as:</p>

<ul>
 <li>Wire ranges, e.g., @('wire [width-1:0] foo')</li>
 <li>Selects from wires, e.g., @('foo[width-1:0]')</li>
 <li>Parameter values arguments, e.g., @('mymod #(.size(width*2)) ...')</li>
</ul>

<p>Where there is no explicit left-hand side.  This evaluator does <b>not</b>
know how to look up identifiers like @('width').  Instead, it is generally
meant to be useful after @('`define')d constants and parameters have already
been expanded.</p>

<p>Note that in general it is <b>not safe</b> to call this function on
arbitrary Verilog expressions to do constant folding.  That is, this function
does not know about any surrounding expression or left-hand side, which could
alter the widths (and hence the values) produced by certain operations.</p>

<p>However, we think this function is safe to use on top-level indexes into
arrays, range expressions, parameter values, etc., where there is no left-hand
side context.</p>

<p>This function can fail for a number of reasons.  For it to succeed, the
expression can contain only resolved constant values.  That is, things like
\"weird\" integers with X/Z bits aren't allowed.  Neither are any identifiers,
function calls, and so forth.  The operators in the expression must be
supported by @(see vl-consteval-main), and the evaluation must proceed without
\"run-time errors\" such as division by zero.</p>"

  (b* ((x (vl-expr-fix x))
       ((mv successp ?warnings sized-x)
        (vl-expr-size nil ;; we assume there's no left-hand side context
                      x
                      *vl-fake-module-for-vl-consteval*
                      *vl-fake-ialist-for-vl-consteval*
                      *vl-fake-elem-for-vl-consteval*
                      nil ;; don't care about warnings
                      ))
       ((unless (and successp
                     (posp (vl-expr->finalwidth sized-x))
                     (vl-expr->finaltype sized-x)))
        (mv nil x))
       ((mv okp ans) (vl-consteval-main sized-x))
       ((unless okp)
        (mv nil x)))
    (mv t ans))

  ///
  (more-returns

   (ans (implies successp (vl-expr-resolved-p ans))
        :name vl-expr-resolved-p-of-vl-consteval)

   (ans (implies successp (vl-expr-welltyped-p ans))
        :name vl-expr-welltyped-p-of-vl-consteval)

   (ans (implies successp
                 (posp (vl-expr->finalwidth ans)))
        :rule-classes :type-prescription
        :name vl-expr->finalwidth-of-vl-consteval)

   (ans (implies successp
                 (vl-exprtype-p (vl-expr->finaltype ans)))
        :name vl-expr->finaltype-of-vl-consteval)))


