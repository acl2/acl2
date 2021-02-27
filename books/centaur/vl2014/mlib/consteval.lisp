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
(include-book "../transforms/expr-size")
(include-book "centaur/bitops/fast-logext" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (xdoc::set-default-parents vl-consteval))
(local (std::add-default-post-define-hook :fix))

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





(defval *vl-fake-elem-for-vl-consteval*
  (make-vl-vardecl :name "VL_FAKE_ELEM_FOR_VL_CONSTEVAL"
                   :type *vl-plain-old-wire-type*
                   :loc *vl-fakeloc*))

(define vl-consteval-ans (&key (value natp)
                               (width posp)
                               (type  vl-exprtype-p))
  :returns (ans vl-expr-p)
  :guard (unsigned-byte-p width value)
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
                           ;; VL-NONATOM->OP-WHEN-HIDINDEX-RESOLVED-P
                           ;; VL-NONATOM->OP-WHEN-VL-HIDINDEX-P
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
                           all-equalp
                           CONSP-OF-VL-EXPRLIST->FINALWIDTHS
                           LEN-OF-VL-NONATOM->ARGS-WHEN-VL-HIDINDEX-P
                           (:TYPE-PRESCRIPTION VL-HIDINDEX-P)
                           LEN-OF-VL-NONATOM->ARGS-WHEN-VL-HIDEXPR-P
                           (:TYPE-PRESCRIPTION VL-NONATOM->OP$INLINE)
                           VL-EXPR-KIND-WHEN-VL-$RANDOM-EXPR-P

                           acl2::CAR-WHEN-ALL-EQUALP

                           ACL2::CANCEL_TIMES-EQUAL-CORRECT
                           ACL2::CANCEL_PLUS-EQUAL-CORRECT
                           ACL2::TRUE-LISTP-MEMBER-EQUAL)))

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
  (b* ((aval (lnfix aval))
       (width (lposfix width)))
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
       (ainterp (if (eq (vl-exprtype-fix atype) :vl-signed)
                    (acl2::fast-logext awidth aval)
                  aval)))
    (case op
      (:vl-binary-shr   (ash aval (- bval)))
      (:vl-binary-shl   (ash aval bval))
      (:vl-binary-ashr  (ash ainterp (- bval)))
      (:vl-binary-ashl  (ash ainterp bval))
      (:vl-binary-power (expt ainterp bval))
      (otherwise        (progn$ (impossible) 0)))))


(define vl-consteval-usertype-bits ((typename stringp) (ss vl-scopestack-p))
  :returns (mv (ok booleanp :rule-classes :type-prescription)
               (res (implies ok (posp res)) :rule-classes :type-prescription))
  (b* ((usertype (make-vl-usertype :kind (vl-idexpr typename nil nil)))
       ((mv warning type) (vl-datatype-usertype-elim usertype ss 100))
       ((when warning) (mv nil nil))
       ((mv warning size) (vl-datatype-size type))
       ((when warning) (mv nil nil)))
    (mv t size)))

(define vl-consteval-basictype-bits ((type vl-basictype-p))
  :returns (mv (ok booleanp :rule-classes :type-prescription)
               (res (implies ok (posp res)) :rule-classes :type-prescription))
  (b* (((vl-basictype type)))
    (case type.kind
      (:vl-byte     (mv t 8))
      (:vl-shortint (mv t 16))
      (:vl-longint  (mv t 64))
      (:vl-integer  (mv t 32))
      (:vl-time     (mv t 64))
      (:vl-bit      (mv t 1))
      (:vl-logic    (mv t 1))
      (:vl-reg      (mv t 1))
      (otherwise    (mv nil nil)))))

(define vl-consteval-$bits ((x vl-expr-p "the expression inside the $bits call")
                            (orig vl-expr-p "the $bits call itself")
                            (ss vl-scopestack-p))
  :prepwork ((local (in-theory (disable not))))
  :guard (vl-unary-syscall-p "$bits" orig)
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (ans vl-expr-p))
  (b* ((orig            (vl-expr-fix orig))
       (orig.finalwidth (vl-expr->finalwidth orig))
       (orig.finaltype  (vl-expr->finaltype orig))
       ((unless (and (posp orig.finalwidth)
                     orig.finaltype))
        (mv nil orig))
       ((unless (and (vl-atom-p x)
                     (member (tag (vl-atom->guts x)) '(:vl-basictype :vl-typename))))
        (b* (((mv & arg-width) (vl-expr-selfsize x ss
                                                 *vl-fake-elem-for-vl-consteval*
                                                 nil)))
          (if arg-width
              (mv t (vl-consteval-ans :value (acl2::loghead orig.finalwidth arg-width)
                                      :width orig.finalwidth
                                      :type orig.finaltype))
            (mv nil orig))))
       (typeguts (vl-atom->guts x))
       ((mv ok res) (if (eq (tag typeguts) :vl-typename)
                        (vl-consteval-usertype-bits (vl-typename->name typeguts) ss)
                      (vl-consteval-basictype-bits typeguts))))
    (if ok
        (mv ok (vl-consteval-ans :value (acl2::loghead orig.finalwidth res)
                                 :width orig.finalwidth :type orig.finaltype))
      (mv nil orig)))
  ///

  (local (in-theory (disable (force))))

  (more-returns
   (ans (vl-expr-welltyped-p ans)
        :hyp (vl-expr-welltyped-p orig)
        :name vl-expr-welltyped-p-of-vl-consteval-$bits)

   (ans (equal (vl-expr->finalwidth ans) (vl-expr->finalwidth orig))
        :name vl-expr->finalwidth-of-vl-consteval-$bits)

   (ans (equal (vl-expr->finaltype ans) (vl-expr->finaltype orig))
        :name vl-expr->finaltype-of-vl-consteval-$bits)

   (ans (implies successp (vl-expr-resolved-p ans))
        :name vl-expr-resolved-p-of-vl-consteval-$bits)))

(define vl-consteval-concat ((x vl-exprlist-p)
                             (val-acc natp)
                             (width-acc natp))
  :guard (and (vl-exprlist-resolved-p x)
              (consp x)
              (unsigned-byte-p width-acc val-acc))
  :guard-hints (("goal" :in-theory (enable bitops::expt-2-is-ash
                                           vl-exprlist-resolved-p
                                           vl-expr-resolved-p)))
  :returns (ans vl-expr-p)
  (b* (((vl-constint x1) (vl-atom->guts (car x)))
       (val-acc (acl2::logapp x1.origwidth x1.value (lnfix val-acc)))
       (width-acc (+ x1.origwidth (lnfix width-acc)))
       ((when (atom (cdr x)))
        (vl-consteval-ans :value val-acc :width width-acc :type :vl-unsigned)))
    (vl-consteval-concat (cdr x) val-acc width-acc))
  ///
  (local (in-theory (enable vl-exprlist->finalwidths
                            vl-exprlist-resolved-p
                            vl-exprlist-welltyped-p)))

  (local (defthm origwidth-when-welltyped/resolved
           (implies (and (vl-expr-welltyped-p x)
                         (vl-expr-resolved-p x))
                    (equal (vl-constint->origwidth (vl-atom->guts x))
                           (vl-expr->finalwidth x)))
           :hints(("Goal" :in-theory (enable vl-expr-resolved-p
                                             vl-expr-welltyped-p
                                             vl-atom-welltyped-p
                                             vl-expr->finalwidth)))))

  (local (defthm finalwidth-type-when-welltyped/resolved
           (implies (and (vl-expr-welltyped-p x)
                         (vl-expr-resolved-p x))
                    (posp (vl-expr->finalwidth x)))
           :hints(("Goal" :in-theory (enable vl-expr-resolved-p
                                             vl-expr-welltyped-p
                                             vl-atom-welltyped-p
                                             vl-expr->finalwidth)))
           :rule-classes :type-prescription))

  (more-returns
   (ans (vl-expr-welltyped-p ans)
        :name vl-expr-welltyped-p-of-vl-consteval-concat)

   (ans (implies (and (vl-exprlist-welltyped-p x)
                      (vl-exprlist-resolved-p x)
                      (consp x))
                 (equal (vl-expr->finalwidth ans)
                        (+ (nfix width-acc) (sum-nats (vl-exprlist->finalwidths x)))))
        :name vl-expr->finalwidth-of-vl-consteval-concat)

   (ans (equal (vl-expr->finaltype ans) :vl-unsigned)
        :name vl-expr->finaltype-of-vl-consteval-concat)

   (ans (vl-expr-resolved-p ans)
        :name vl-expr-resolved-p-of-vl-consteval-concat)))


(define vl-clog2 ((n natp))
  :returns (ans natp :rule-classes :type-prescription)
  :short "Implementation of the @('$clog2') system function."
  :long "<p>The SystemVerilog spec (20.8.1, page 567) says that @('$clog2(0)')
is 0 and that otherwise @('$clog2') should return the ceiling of the log base 2
of the argument, i.e., the log rounded up to an integer value.</p>

<p>This <b>almost</b> lines up with @(see integer-length) but not quite, so to
avoid problems at the border cases we just need to subtract one from @('n').
For instance:</p>

@({
         n      (integer-length n)     (integer-length (- n 1))    $clog2
    -----------------------------------------------------------------------
         0               0                       0                   0
         1               1                       0                   0
         2               2                       1                   1
         3               2                       2                   2
         4               3                       2                   2
         5               3                       3                   3
         6               3                       3                   3
         7               3                       3                   3
         8               4                       3                   3
         9               4                       4                   4
         10              4                       4                   4
    -----------------------------------------------------------------------
})"
  (integer-length (- (lnfix n) 1)))

(defines vl-consteval-main
  (define vl-consteval-main ((x vl-expr-p)
                             (ss vl-scopestack-p))
    :short "Recursive helper for @(see vl-consteval)"
    :inline nil
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
              ((mv bok b) (vl-consteval-main (second x.args) ss))
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
              ((mv bok b) (vl-consteval-main (second x.args) ss))
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
              ((mv bok b) (vl-consteval-main (second x.args) ss))
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
              ((mv bok b) (vl-consteval-main (second x.args) ss))
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
         (b* (((mv aok a) (vl-consteval-main (first x.args) ss))
              ((mv bok b) (vl-consteval-main (second x.args) ss))
              ((mv cok c) (vl-consteval-main (third x.args) ss))
              ((unless (and aok bok cok))
               (mv nil x))
              (ans (if (posp (vl-resolved->val a)) b c)))
           (mv t ans)))

        ((:vl-syscall)
         (cond ((vl-unary-syscall-p "$bits" x)
                (b* ((obj (vl-unary-syscall->arg x))
                     ;; Do we need to do something like this?
                     ;; ;; If obj is a constant we should evaluate it first, but
                     ;; ;; don't fail if it doesn't work.
                     ;; ((mv ok ev-obj) (vl-consteval-main obj ss))
                     ;; (obj (if ok ev-obj obj))
                     )
                  (vl-consteval-$bits obj x ss)))

               ((vl-unary-syscall-p "$clog2" x)
                (b* ((arg (vl-unary-syscall->arg x))
                     ((unless (vl-expr-welltyped-p arg))
                      ;; BOZO.  It would perhaps be nice to know this as part
                      ;; of vl-expr-welltyped-p.  But this could get tricky --
                      ;; sometimes (e.g., $clog2) we want the arguments to be
                      ;; welltyped, but other times (e.g., $bits) we don't.
                      ;; For now I'll just explicitly check it.
                      (mv nil x))
                     ((mv aok a) (vl-consteval-main arg ss))
                     ((unless aok)
                      (mv nil x))
                     (val (vl-clog2 (vl-resolved->val a)))
                     ((unless (< val (expt 2 31)))
                      ;; Out of range for $clog2.
                      (mv nil x))
                     (ans (vl-consteval-ans :value val
                                            :width x.finalwidth
                                            :type x.finaltype)))
                  (mv t ans)))

               (t
                (mv nil x))))

        (:vl-concat
         (b* (((mv argsok args) (vl-consteval-exprlist-main x.args ss))
              ((unless (and argsok (consp args))) (mv nil x)))
           (mv t (vl-consteval-concat args 0 0))))



        ;; BOZO could eventually add support for other operators like
        ;; concatenation, bitselect, etc.  But the above is probably pretty
        ;; good and should be good enough for most cases.
        (otherwise
         (mv nil x)))))


  (define vl-consteval-exprlist-main ((x vl-exprlist-p)
                                      (ss vl-scopestack-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (ans      vl-exprlist-p))
    :guard (vl-exprlist-welltyped-p x)
    :measure (vl-exprlist-count x)
    (b* (((when (atom x)) (mv t nil))
         ((mv ok1 ans1) (vl-consteval-main (car x) ss))
         ((mv ok2 ans2) (vl-consteval-exprlist-main (cdr x) ss)))
      (mv (and ok1 ok2) (cons ans1 ans2))))


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
     ;; (add-default-hints
     ;;  '((and stable-under-simplificationp
     ;;         '(:expand (vl-expr-welltyped-p x)))
     ;;    (and stable-under-simplificationp
     ;;         '(:in-theory (enable acl2::member-of-cons
     ;;                              acl2::member-when-atom)))))
     (local (in-theory (disable acl2::consp-of-car-when-alistp
                                acl2::alistp-when-keyval-alist-p-rewrite
                                vl-exprlist-p-when-not-consp
                                acl2::alistp-of-cdr
                                alistp-when-vl-atts-p-rewrite
                                natp-of-car-when-nat-listp
                                acl2::natp-of-car-when-nat-listp
                                acl2::natp-rw
                                acl2::natp-when-maybe-natp
                                acl2::maybe-natp-when-natp
                                maybe-natp-of-car-when-vl-maybe-nat-listp
                                acl2::consp-when-member-equal-of-atom-listp
                                (tau-system))))
     )

    ///
    (local (set-default-hints
            '((acl2::just-expand-mrec-default-hint 'vl-consteval-main id nil world)
              (and stable-under-simplificationp
                   '(:expand ((vl-expr-welltyped-p x)
                              (vl-hidexpr-p x)
                              (vl-hidindex-p x)))))))
    (defthm-vl-consteval-main-flag
      (defthm vl-expr-welltyped-p-of-vl-consteval-main
        (b* (((mv ?ok ?ans) (vl-consteval-main x ss)))
          (implies (vl-expr-welltyped-p x)
                   (vl-expr-welltyped-p ans)))
        :flag vl-consteval-main)
      (defthm vl-exprlist-welltyped-p-of-vl-consteval-exprlist-main
        (b* (((mv ?ok ?ans) (vl-consteval-exprlist-main x ss)))
          (implies (vl-exprlist-welltyped-p x)
                   (vl-exprlist-welltyped-p ans)))
        :flag vl-consteval-exprlist-main))

    (local (defthm clog2-has-return-info
             (implies (vl-unary-syscall-p "$clog2" x)
                      (vl-syscall->returninfo x))
             :rule-classes :forward-chaining
             :hints(("Goal" :in-theory (enable vl-syscall->returninfo)))))

    (local (defthm clog2-helpers
             (implies (and (vl-unary-syscall-p "$clog2" x)
                           (vl-expr-welltyped-p x))
                      (and (equal (vl-expr->finalwidth x) 32)
                           (vl-expr->finaltype x)))
             :hints(("Goal" :in-theory (enable vl-syscall->returninfo)))))

    (defthm-vl-consteval-main-flag
      (defthm vl-expr-resolved-p-of-vl-consteval-main
        (b* (((mv ?ok ?ans) (vl-consteval-main x ss)))
          (implies (and (vl-expr-welltyped-p x)
                        ok)
                   (vl-expr-resolved-p ans)))
        :flag vl-consteval-main)
      (defthm vl-exprlist-resolved-p-of-vl-consteval-exprlist-main
        (b* (((mv ?ok ?ans) (vl-consteval-exprlist-main x ss)))
          (implies (and (vl-exprlist-welltyped-p x)
                        ok)
                   (vl-exprlist-resolved-p ans)))
        :flag vl-consteval-exprlist-main))

    (defthm-vl-consteval-main-flag
      (defthm vl-expr->finalwidth-of-vl-consteval-main
        (b* (((mv ?ok ?ans) (vl-consteval-main x ss)))
          (implies (vl-expr-welltyped-p x)
                   (equal (vl-expr->finalwidth ans)
                          (vl-expr->finalwidth x))))
        :flag vl-consteval-main)
      (defthm vl-exprlist->finalwidth-of-vl-consteval-exprlist-main
        (b* (((mv ?ok ?ans) (vl-consteval-exprlist-main x ss)))
          (implies (vl-exprlist-welltyped-p x)
                   (equal (vl-exprlist->finalwidths ans)
                          (vl-exprlist->finalwidths x))))
        :flag vl-consteval-exprlist-main))

    (defthm-vl-consteval-main-flag
      (defthm vl-expr->finaltype-of-vl-consteval-main
        (b* (((mv ?ok ?ans) (vl-consteval-main x ss)))
          (implies (vl-expr-welltyped-p x)
                   (equal (vl-expr->finaltype ans)
                          (vl-expr->finaltype x))))
        :flag vl-consteval-main)
      (defthm vl-exprlist->finaltype-of-vl-consteval-exprlist-main
        (b* (((mv ?ok ?ans) (vl-consteval-exprlist-main x ss)))
          (implies (vl-exprlist-welltyped-p x)
                   (equal (vl-exprlist->finaltypes ans)
                          (vl-exprlist->finaltypes x))))
        :flag vl-consteval-exprlist-main))

    (local (set-default-hints nil))
    (local (defthm <-2-when-bitp
             (implies (acl2::bitp x)
                      (< x 2))))
    (local (in-theory (enable unsigned-byte-p)))

    (deffixequiv-mutual vl-consteval-main)

    (local
     ;; Blah, after a lot of trying to get this rule not to blow up expt, I
     ;; fail.  It would be nice to come up with a way to prevent these kinds
     ;; of problems.
     (in-theory (disable upper-bound-of-vl-sign-extend-constint)))
    (verify-guards vl-consteval-main$notinline
      :hints (("goal" :do-not-induct t
               :expand ((vl-expr-welltyped-p x)))
              (and stable-under-simplificationp
                   '(:in-theory (enable acl2::member-of-cons)))
              )))


(define vl-consteval
  :parents (mlib)
  :short "An evaluator for a small set of \"constant expressions\" in Verilog."
  ((x vl-expr-p "Expression to try to evaluate.")
   (ss vl-scopestack-p))
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
                      ss
                      *vl-fake-elem-for-vl-consteval*
                      nil ;; don't care about warnings
                      ))
       ((unless (and successp
                     (posp (vl-expr->finalwidth sized-x))
                     (vl-expr->finaltype sized-x)))
        (mv nil x))
       ((mv okp ans) (vl-consteval-main sized-x ss))
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
