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
(include-book "expr-tools")
(include-book "range-tools")
(include-book "hid-tools")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))

(defsection vl-atom-welltyped-p
  :parents (vl-expr-welltyped-p)
  :short "@(call vl-atom-welltyped-p) determines if a @(see vl-atom-p) is
well-typed."

  :long "<p>For every integer <see topic=\"@(url
vl-atom-p)\">atom</see> (whether constant or weird), the finalwidth and
finaltype must agree with the origwidth and origtype of the guts.</p>

<p>For every identifier atom, the finalwidth and finaltype <b>may differ</b>
from the identifier's declaration.  These differences allow us to implicitly
represent the sign-extension or zero-extension of a wire, register, or
variable.  Informally, we also generally expect that the finalwidth should
never be less than the declaration's width, and that the finaltype should be
signed only if the declaration is signed.  But to allow @(see
vl-expr-welltyped-p) not to take a module as an argument, we actually do not
check that these expectations hold.</p>

<p>For string atoms, per Section 3.6 we say that the finalwidth must be 8 times
the string's length (which, interestingly, may be zero).  We also say that the
finaltype is unsigned.</p>

<p>For all other atoms, we insist that the finaltype and finalwidth are
@('nil'), which we intend to mean \"not applicable\".  These atoms are reals,
function names and system function names, and the individual pieces of
hierarchical identifiers.</p>"

  (defund vl-atom-welltyped-p (x)
    (declare (xargs :guard (vl-atom-p x)))
    (b* (((vl-atom x) x)

         ((when (vl-fast-constint-p x.guts))
          (b* (((vl-constint x.guts) x.guts))
            (and (eq x.finaltype x.guts.origtype)
                 (eql x.finalwidth x.guts.origwidth))))

         ((when (vl-fast-weirdint-p x.guts))
          (b* (((vl-weirdint x.guts) x.guts))
            (and (eq x.finaltype x.guts.origtype)
                 (eql x.finalwidth x.guts.origwidth))))

         ((when (vl-fast-id-p x.guts))
          (and x.finaltype
               (posp x.finalwidth)))

         ((when (vl-fast-string-p x.guts))
          (b* (((vl-string x.guts) x.guts))
            (and (eq x.finaltype :vl-unsigned)
                 (eql x.finalwidth (* 8 (length x.guts.value)))))))

      ;; Otherwise -- reals, function names, hierarchical identifier pieces;
      ;; these atoms do not get a finalwidth or finaltype.
      (and (not x.finalwidth)
           (not x.finaltype))))

  (defthm booleanp-of-vl-atom-welltyped-p
    (or (equal (vl-atom-welltyped-p x) nil)
        (equal (vl-atom-welltyped-p x) t))
    :rule-classes :type-prescription))









(define vl-hidexpr-welltyped-p ((x (and (vl-expr-p x)
                                        (vl-nonatom-p x))))
  (b* (((vl-nonatom x) x)
       (width (vl-hid-width x)))
    (and (eq x.finaltype :vl-unsigned)
         width
         (eql x.finalwidth width))))


(defsection vl-expr-welltyped-p
  :parents (vl-expr-p expression-sizing)
  :short "@(call vl-expr-welltyped-p) determines if an @(see vl-expr-p) is
well-typed."

  :long "<p>We say expressions are well-typed when their signs and widths have
been computed, and when certain consistency requirements are met.  This is a
rather elaborate consistency check we use as a basic correctness property of
our @(see expression-sizing) transformation.  It may also be useful in later
transformations to insist that the you are working with reasonably sane
expressions.</p>

<p>Every atom in the expression must satisfy @(see vl-atom-welltyped-p).</p>

<p>Every nonatom has certain consistency checks that depend upon which operator
is being applied.  For instance, in an expression like @('a + b'), we require
that the final width/type of the expression agrees exactly with the final
widths/types of @('a') and @('b').  As another example, we insist that the
finalwidth/type of @('&foo') is one-bit unsigned, but otherwise we only require
that the width of @('foo') itself is non-zero.</p>"

  (mutual-recursion

   (defund vl-expr-welltyped-p (x)
     (declare (xargs :guard (vl-expr-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (vl-atom-welltyped-p x))
          ((when (not (mbt (consp x))))
           (er hard 'vl-expr-welltyped-p "Termination hack."))
          ((vl-nonatom x) x)
          ((when (vl-hidexpr-p x))
           ;; These are special because we don't require the args to be sized.
           ;; Signedness of hierarchical identifiers is very tricky; we require
           ;; that they be unsigned to avoid a lot of potential problems.
           (vl-hidexpr-welltyped-p x)))
       (and
        (vl-exprlist-welltyped-p x.args)
        (case x.op
          (( ;; Table 5-22, Line 3.
            :vl-binary-plus :vl-binary-minus :vl-binary-times :vl-binary-div
            :vl-binary-rem :vl-binary-bitand :vl-binary-bitor :vl-binary-xor
            :vl-binary-xnor)
           (b* ((a (first x.args))
                (b (second x.args)))
             (and x.finaltype
                  (posp x.finalwidth)
                  ;; context-determined operands; must have x's size/type
                  (eq x.finaltype (vl-expr->finaltype a))
                  (eq x.finaltype (vl-expr->finaltype b))
                  (eql x.finalwidth (vl-expr->finalwidth a))
                  (eql x.finalwidth (vl-expr->finalwidth b)))))

          (( ;; Table 5-22, Line 4.
            :vl-unary-plus :vl-unary-minus :vl-unary-bitnot)
           (b* ((a (first x.args)))
             (and x.finaltype
                  (posp x.finalwidth)
                  ;; context-determined operand; must have x's size/type
                  (eq x.finaltype (vl-expr->finaltype a))
                  (eql x.finalwidth (vl-expr->finalwidth a)))))

          (( ;; Table 5-22, Line 5.
            :vl-binary-ceq :vl-binary-cne :vl-binary-eq :vl-binary-neq
            :vl-binary-gt :vl-binary-gte :vl-binary-lt :vl-binary-lte
            ;; SystemVerilog extensions:
            :vl-binary-wildeq :vl-binary-wildneq)
           (b* ((a (first x.args))
                (b (second x.args)))
             (and ;; result must be unsigned (5.5.1) and one-bit (Table 5-22)
                  (eq x.finaltype :vl-unsigned)
                  (eql x.finalwidth 1)
                  ;; the operands are unrelated to x but must at least have a
                  ;; non-zero size and a type.
                  (vl-expr->finaltype a)
                  (posp (vl-expr->finalwidth a))
                  (eql (vl-expr->finalwidth a) (vl-expr->finalwidth b))
                  (eq (vl-expr->finaltype a) (vl-expr->finaltype b)))))

          (( ;; Table 5-22, Line 6.
            :vl-binary-logand
            :vl-binary-logor
            ;; SystemVerilog Extensions
            :vl-implies :vl-equiv)
           (b* ((a (first x.args))
                (b (second x.args)))
             (and ;; result must be unsigned (see "minutia") and one-bit (Table 5-22)
                  (eql x.finalwidth 1)
                  (eq x.finaltype :vl-unsigned)
                  ;; self-determined operands; unrelated to the size/type of X,
                  ;; but must at least have a non-zero size and a type.
                  (vl-expr->finaltype a)
                  (vl-expr->finaltype b)
                  (posp (vl-expr->finalwidth a))
                  (posp (vl-expr->finalwidth b)))))

          (( ;; Table 5-22, Line 7.
            :vl-unary-bitand :vl-unary-nand :vl-unary-bitor :vl-unary-nor
            :vl-unary-xor :vl-unary-xnor :vl-unary-lognot)
           (b* ((a (first x.args)))
             (and ;; result must be unsigned (see "minutia") and one-bit (Table 5-22)
                  (eq x.finaltype :vl-unsigned)
                  (eql x.finalwidth 1)
                  ;; self-determined operand; unrelated to the size/type of X,
                  ;; but must at least have a non-zero size and a type.
                  (vl-expr->finaltype a)
                  (posp (vl-expr->finalwidth a)))))

          (( ;; Table 5-22, Line 8
            :vl-binary-shr :vl-binary-shl :vl-binary-ashr :vl-binary-ashl
                           :vl-binary-power)
           (b* ((a (first x.args))
                (b (second x.args)))
             (and x.finaltype
                  (posp x.finalwidth)
                  ;; A is context-determined and must agree with x's size/type
                  (eql x.finalwidth (vl-expr->finalwidth a))
                  (eq x.finaltype (vl-expr->finaltype a))
                  ;; B is self-determined and must have a size/type.  Type of B
                  ;; is unrelated to type of X and must be ignored by
                  ;; transforms; see minutia.
                  (vl-expr->finaltype b)
                  (posp (vl-expr->finalwidth b)))))

          (( ;; Table 5-22, Line 9 -- we ignore the type of A; see minutia
            :vl-qmark)
           (b* ((a (first x.args))
                (b (second x.args))
                (c (third x.args)))
             (and x.finaltype
                  (posp x.finalwidth)
                  ;; A is self-determined and unrelated to size/type of X (see
                  ;; "minutia").  We insist it is at least non-zero sized and
                  ;; has a type.
                  (posp (vl-expr->finalwidth a))
                  (vl-expr->finaltype a)
                  ;; B and C are context-determined, must agree with X
                  (eql x.finalwidth (vl-expr->finalwidth b))
                  (eql x.finalwidth (vl-expr->finalwidth c))
                  (eq x.finaltype (vl-expr->finaltype b))
                  (eq x.finaltype (vl-expr->finaltype c)))))

          (( ;; Table 5-22, Line 10
            :vl-concat)
           (b* ((arg-widths (vl-exprlist->finalwidths x.args)))
             (and ;; result is unsigned (5.5.1) and its width is the sum of
                  ;; its arg widths (Table 5-22)
                  (eq x.finaltype :vl-unsigned)
                  (posp x.finalwidth)
                  ;; we choose not to allow any unsized args.  this does NOT
                  ;; prohibit zero-sized multiconcats or zero-sized strings.
                  ;; But it does prohibit reals, function names, etc.
                  (not (member nil arg-widths))
                  (equal x.finalwidth (sum-nats arg-widths)))))

          (( ;; Table 5-22, Line 11.
            :vl-multiconcat)
           (b* ((a (first x.args))
                (b (second x.args)))
             (and ;; result is unsigned (5.5.1) -- well, assuming that a multiple
                  ;; concatenation is also a "concatenation", at least, which seems
                  ;; reasonable.  its width is multiplicity * width(arg)
                  (eq x.finaltype :vl-unsigned)
                  (vl-expr-resolved-p a)
                  ;; It's actually valid to require the concatenation part to have
                  ;; a positive width.  We could also probably require it to be a
                  ;; concatenation with unsigned type, but I haven't done that.
                  (posp (vl-expr->finalwidth b))
                  ;; The finalwidth can be zero if the multiplicity is zero.
                  (eql x.finalwidth (* (vl-resolved->val a) (vl-expr->finalwidth b))))))

          ((:vl-bitselect)
           ;; Always unsigned per 5.5.1.  Always one bit since it's a bit select.
           (and (eql x.finalwidth 1)
                (eq x.finaltype :vl-unsigned)))

          ((:vl-partselect-colon)
           ;; Always unsigned per 5.5.1.  Width is typical (max-min)+1
           (b* ((b (second x.args))
                (c (third x.args))
                ((unless (and (vl-expr-resolved-p b)
                              (vl-expr-resolved-p c)))
                 nil)
                (b-val (vl-resolved->val b))
                (c-val (vl-resolved->val c)))
             (and

; Historically we insisted on foo[5:0] order rather than foo[0:5], since to do
; otherwise seems crazy, but now we support both orders so we had to drop that
; restriction.
                  (eql x.finalwidth (+ 1 (abs (- b-val c-val))))
                  (eq x.finaltype :vl-unsigned))))

          ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
           ;; Always unsigned per 5.5.1.  Width is given by the width-expr.
           (b* ((c (third x.args)))
             (and (vl-expr-resolved-p c)
                  (eql x.finalwidth (vl-resolved->val c))
                  (eq x.finaltype :vl-unsigned))))

          ((:vl-array-index :vl-index)
           ;; BOZO eventually require there to be a type and positive width.
           t)

          ((:vl-funcall)
           ;; BOZO do we want to constrain these in any way?
           t)

          ((:vl-syscall)
           ;; BOZO do we want to constrain these in any way?
           t)

          ((:vl-mintypmax)
           ;; These are crazy.  I insist that they must have non-applicable
           ;; type.  This means things like (3:4:5) + 1 are not well-typed.
           ;; I think of this more as a feature than as a limitation.
           (and (not x.finalwidth)
                (not x.finaltype)))))))

   (defund vl-exprlist-welltyped-p (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (or (atom x)
         (and (vl-expr-welltyped-p (car x))
              (vl-exprlist-welltyped-p (cdr x))))))

  (defthm booleanp-of-vl-expr-welltyped-p
    (or (equal (vl-expr-welltyped-p x) t)
        (equal (vl-expr-welltyped-p x) nil))
    :rule-classes :type-prescription)

  (defthm booleanp-of-vl-exprlist-welltyped-p
    (or (equal (vl-exprlist-welltyped-p x) t)
        (equal (vl-exprlist-welltyped-p x) nil))
    :rule-classes :type-prescription)

  (verify-guards vl-expr-welltyped-p
    :hints((and stable-under-simplificationp
                '(:in-theory (enable vl-op-arity vl-op-p)))))

  (defthm vl-exprlist-welltyped-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-welltyped-p x)
                    t))
    :hints(("Goal" :expand ((vl-exprlist-welltyped-p x)))))

  (defthm vl-exprlist-welltyped-p-of-cons
    (equal (vl-exprlist-welltyped-p (cons a x))
           (and (vl-expr-welltyped-p a)
                (vl-exprlist-welltyped-p x)))
    :hints(("Goal" :expand ((vl-exprlist-welltyped-p (cons a x))))))

  (deflist vl-exprlist-welltyped-p (x)
    (vl-expr-welltyped-p x)
    :guard (vl-exprlist-p x)
    :parents (expression-sizing)
    :already-definedp t))
