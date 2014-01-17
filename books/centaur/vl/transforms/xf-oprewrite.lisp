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
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/fix")
(local (include-book "../util/arithmetic"))

(defxdoc oprewrite
  :parents (transforms)
  :short "Rewrite expressions to eliminate various operators."

  :long "<p>We transform expressions by applying the following rewrite rules.
Note that we do not expect any widths to have been computed at the time this
operation is performed, and so we do not try to preserve any widths.</p>

<p>For our translation to be correct, each of these rules needs to be sound.
That is, choose any Verilog bit vectors for a, b, and c.  Then, it needs to be
the case that each left-hand side, above, evaluates to the same thing as its
corresponding right-hand side.</p>

<p>After reading the Verilog spec, we think this is true.  In addition, we have
constructed a Verilog test harness (see xf-oprewrite.v) which checks that this
is the case for all Verilog bit vectors of length 4 (i.e., vectors whose bits
are 0, 1, x, or z), and we have established that there are no 4-bit violations
on Cadence.</p>

<h4>Operator Elimination Rules</h4>

<p>The following rules are useful in that the operators on the left are
completely erased from the parse tree.  Hence, we do not need to consider
how to synthesize them or handle them at all!</p>

<ul>
<li>@('+a')     --&gt; @('a + 1'sb0')</li>
<li>@('-a')     --&gt; @('1'sb0 - a')</li>

<li>@('a && b') --&gt; @('(|a) & (|b)')</li>
<li>@('a || b') --&gt; @('(|a) | (|b)')</li>
<li>@('!a')     --&gt; @('{~(|a)}')</li>

<li>@('~& (a)') --&gt; @('{~( &a )}')</li>
<li>@('~| (a)') --&gt; @('{~( |a )}')</li>
<li>@('~^ (a)') --&gt; @('{~( ^a )}')</li>

<li>@('a < b')  --&gt; @('{~(a >= b)}')</li>
<li>@('a > b')  --&gt; @('{~(b >= a)}')</li>
<li>@('a <= b') --&gt; @('b >= a')</li>

<li>@('a == b') --&gt; @('&(a ~^ b)')</li>
<li>@('a != b') --&gt; @('|(a ^ b)')</li>

<li>@('a !== b') --&gt; @('{~(a === b)}')</li>
</ul>

<h4>Additional Rules</h4>

<p>We also have a couple of rules that help to standardize conditional
expressions.  In particular, the first rule here ensures that when we go to
synthesize a conditional operation, we can assume that the \"test\" argument
has a width of 1.  The second rule ensures that if we encounter a (<b>BOZO</b>
is that the right name for this kind of thing?) then then Z is always in the
false branch.</p>

<ul>
<li>@('a ? b : c') --&gt; @('(|a) ? b : c')</li>
<li>@('a ? z : c') --&gt; @('~(|a) ? c : z')</li>
</ul>

<p>We also consolidate multiple-concatenations of constint and weirdint values
into a single values.  This is important for properly recognizing zatoms in
occform, since designers sometimes write things like</p>

@({
    assign foo = a ? b : width{ 1'bz }
})

<p>Here, if we don't consolidate @('width{1'bz}'), we're not going to recognize
it as a zatom and occform it correctly.</p>")


(defsection vl-replicate-constint-value
  :parents (oprewrite)

  (defund vl-replicate-constint-value (n width x)
    (declare (xargs :guard (and (natp n)
                                (posp width)
                                (natp x))))
    ;; Suppose x is a value that fits into width bits.  We generate n copies of
    ;; x, side by side.
    (if (zp n)
        0
      (+ (ash x (* width (1- n)))
         (vl-replicate-constint-value (- n 1) width x))))

  (defthm natp-of-vl-replicate-constint-value
    (implies (natp x)
             (natp (vl-replicate-constint-value n width x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-replicate-constint-value))))

  (local
   (progn
     (assert! (equal (vl-replicate-constint-value 5 1 1) #b11111))
     (assert! (equal (vl-replicate-constint-value 5 2 1) #b0101010101))
     (assert! (equal (vl-replicate-constint-value 5 3 1) #b001001001001001))
     (assert! (equal (vl-replicate-constint-value 3 5 1) #b000010000100001))
     (assert! (equal (vl-replicate-constint-value 3 5 7) #b001110011100111))
     (assert! (equal (vl-replicate-constint-value 1 5 7) #b00111)))))



(defsection vl-replicate-weirdint-bits
  :parents (oprewrite)

  (defund vl-replicate-weirdint-bits (n x)
    (declare (xargs :guard (and (natp n)
                                (vl-bitlist-p x))))
    (if (zp n)
        nil
      (append-without-guard x (vl-replicate-weirdint-bits (- n 1) x))))

  (defthm len-of-vl-replicate-weirdint-bits
    (equal (len (vl-replicate-weirdint-bits n x))
           (* (nfix n) (len x)))
    :hints(("Goal" :in-theory (enable vl-replicate-weirdint-bits))))

  (defthm vl-bitlist-p-of-vl-replicate-weirdint-bits
    (implies (force (vl-bitlist-p x))
             (vl-bitlist-p (vl-replicate-weirdint-bits n x)))
    :hints(("Goal" :in-theory (enable vl-replicate-weirdint-bits)))))




(defsection vl-maybe-consolidate-multiconcat
  :parents (oprewrite)

  (defund vl-maybe-consolidate-multiconcat (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (not (vl-atom-p x))
                                (equal (vl-nonatom->op x) :vl-multiconcat))))
    (b* (((list arg1 arg2) (vl-nonatom->args x))
         ((unless (and
                   ;; The first argument must be a constant, positive integer.
                   (vl-fast-atom-p arg1)
                   (vl-fast-constint-p (vl-atom->guts arg1))
                   (posp (vl-constint->value (vl-atom->guts arg1)))
                   ;; The second argument must be a concatenation with a single, atomic
                   ;; argument.
                   (not (vl-fast-atom-p arg2))
                   (equal (vl-nonatom->op arg2) :vl-concat)
                   (= 1 (len (vl-nonatom->args arg2)))
                   (vl-fast-atom-p (first (vl-nonatom->args arg2)))))
          x)

         (num-copies (vl-constint->value (vl-atom->guts arg1)))
         (original   (vl-atom->guts (first (vl-nonatom->args arg2))))

         ((when (and (vl-constint-p original)
                     (posp (vl-constint->origwidth original))
                     (natp (vl-constint->value original))))
          (let* ((width     (vl-constint->origwidth original))
                 (value     (vl-constint->value original))
                 (new-width (* num-copies width))
                 (new-val   (vl-replicate-constint-value num-copies width value)))
            (if (< new-val (expt 2 new-width))
                (make-vl-atom
                 :guts (make-vl-constint :origwidth new-width
                                         ;; multiconcat always produces unsigned results
                                         :origtype :vl-unsigned
                                         :value new-val))
              (prog2$ (er hard? 'vl-maybe-consolidate-multiconcat "Out of range??")
                      x))))

         ((when (and (vl-weirdint-p original)
                     (posp (vl-weirdint->origwidth original))))
          (let ((width (vl-weirdint->origwidth original))
                (bits  (vl-weirdint->bits original)))
            (make-vl-atom
             :guts (make-vl-weirdint
                    :origwidth (* num-copies width)
                    :origtype :vl-unsigned ;; multiconcat always produced unsigned results
                    :bits (vl-replicate-weirdint-bits num-copies bits))))))

      x))

  (local (in-theory (enable vl-maybe-consolidate-multiconcat)))

  (defthm vl-expr-p-of-vl-maybe-consolidate-multiconcat
    (implies (and (force (vl-expr-p x))
                  (force (not (vl-atom-p x)))
                  (force (equal (vl-nonatom->op x) :vl-multiconcat)))
             (vl-expr-p (vl-maybe-consolidate-multiconcat x)))))




(defsection vl-op-oprewrite
  :parents (oprewrite)
  :short "Main operator rewriting function."

  :long "<p><b>Signature:</b> @(call vl-op-oprewrite) returns @('(mv
warnings-prime expr-prime)').</p>

<p>We are given @('op'), an operator which is being applied to @('args'), which
are some already-rewritten arguments.  @('atts') are the current attributes for
this operator, and @('warnings') is an accumulator for warnings which we may
extend.</p>

<p>We produce a new expression, either by applying @('op') to @('args')
verbatim, or by applying one of the rewrites described in @(see oprewrite).
Keeping this function separate from @(see vl-expr-oprewrite) helps to keep the
mutual recursion as simple as possible.</p>"

  (defund vl-op-oprewrite (op args atts warnings)
    "Returns (MV WARNINGS-PRIME EXPR-PRIME)"
    (declare (xargs :guard (and (vl-op-p op)
                                (vl-exprlist-p args)
                                (vl-atts-p atts)
                                (or (not (vl-op-arity op))
                                    (equal (len args) (vl-op-arity op)))
                                (vl-warninglist-p warnings))
                    :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity)))))
    (case op
      (:vl-qmark
       (b* (((list a b c) args)
            (or-a (make-vl-nonatom :op :vl-unary-bitor
                                   :args (list a)
                                   :atts (acons "VL_CONDITIONAL_FIX" nil nil))))

           (if (vl-zatom-p b)
               ;; a ? z : c -->  ~(|a) ? c : z
               (let ((nor-a (make-vl-nonatom :op :vl-unary-bitnot
                                             :args (list or-a)
                                             :atts (acons "VL_CONDITIONAL_FIX" nil nil)
                                             )))
                 (mv warnings (make-vl-nonatom :op :vl-qmark
                                               :atts atts
                                               :args (list nor-a c b))))
             ;; a ? b : c --> (|a) ? b : c
             (mv warnings (make-vl-nonatom :op :vl-qmark
                                           :atts atts
                                           :args (list or-a b c))))))

      (:vl-binary-logand
       ;; a && b --> (|a) & (|b)
       (b* (((list a b) args)
            (or-a   (make-vl-nonatom :op :vl-unary-bitor :args (list a)))
            (or-b   (make-vl-nonatom :op :vl-unary-bitor :args (list b)))
            (result (make-vl-nonatom :op :vl-binary-bitand
                                     :atts atts
                                     :args (list or-a or-b))))
           (mv warnings result)))

      (:vl-binary-logor
       ;; a || b --> (|a) | (|b)
       (b* (((list a b) args)
            (or-a   (make-vl-nonatom :op :vl-unary-bitor :args (list a)))
            (or-b   (make-vl-nonatom :op :vl-unary-bitor :args (list b)))
            (result (make-vl-nonatom :op :vl-binary-bitor
                                     :atts atts
                                     :args (list or-a or-b))))
           (mv warnings result)))


      (:vl-unary-plus
       ;; +a --> a + 1'sb0

; What is the meaning of +a?  In Verilog-XL it seems to be equal to A.  In
; NCVerilog it is equal to (a + 1'sb0).
;
; This difference matters because, e.g., if a is 4'b000X, then in Verilog-XL +a
; is also 4'b000X, whereas in NCVerilog it is 4'bXXXX.  We choose to implement
; NCVerilog's behavior since it is more conservative.
;
; It's important to add a signed zero since otherwise we could inadvertently be
; changing the sign of the expression.  If A is signed we preserve this since
; signed + signed is signed.  If A is unsigned, we also preserve it since
; unsigned + signed is unsigned.
;
; It's important to add a one-bit zero since that way we know that we are not
; increasing the size of the expression.  If A is one bit we won't be changing
; its size.  If A is larger, we'll inherit its size.

       (b* (((list a) args)
            (|1'sb0|  (make-vl-atom
                       :guts (make-vl-constint :value 0
                                               :origwidth 1
                                               :origtype :vl-signed)))
            (result   (make-vl-nonatom :op :vl-binary-plus
                                       :atts atts
                                       :args (list a |1'sb0|))))
         (mv warnings result)))


      (:vl-unary-minus
       ;; -a --> 1'sb0 - a

; Verilog-XL and NCVerilog both agree on this for the meaning of -a.

       (b* (((list a) args)
            (|1'sb0|  (make-vl-atom
                       :guts (make-vl-constint :value 0
                                               :origwidth 1
                                               :origtype :vl-signed)))
            (result   (make-vl-nonatom :op :vl-binary-minus
                                       :atts atts
                                       :args (list |1'sb0| a))))
         (mv warnings result)))



      (:vl-unary-lognot
       ;; !a -->  {~(|a)}

; BUG FOUND ON 2011-09-22.  We used to not put in the concatenation.  This was
; correct for one-bit contexts, but if a !a was being used in a wider context,
; there could be a problem.  For instance, if a was 4'b1011, then something
; like:
;
;    wire [3:0] w = !a;
;
; should yield w = 4'b0000.  But without the concatenation, the ~ gets applied
; to 4'b0001, and yields 4'b1110, which is just totally wrong.
;
; We therefore add the concatenation to force the ~ to be self-determined and
; hence to be carried out in one bit.  This creates an unsigned result, but
; that is okay because (we think) !a should produce a one-bit unsigned result
; anyway.

       (b* (((list a) args)
            (or-a   (make-vl-nonatom :op :vl-unary-bitor  :args (list a)))
            (~or-a  (make-vl-nonatom :op :vl-unary-bitnot :args (list or-a)))
            (result (make-vl-nonatom :op :vl-concat
                                     :atts atts
                                     :args (list ~or-a))))
         (mv warnings result)))


      (:vl-unary-nand
       ;; ~& (a)  -->  {~( &a )}

; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.

       (b* (((list a) args)
            (and-a    (make-vl-nonatom :op :vl-unary-bitand :args (list a)))
            (~and-a   (make-vl-nonatom :op :vl-unary-bitnot :args (list and-a)))
            (result   (make-vl-nonatom :op :vl-concat
                                       :atts atts
                                       :args (list ~and-a))))
           (mv warnings result)))


      (:vl-unary-nor
       ;; ~| (a)  -->  {~( |a )}

; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.

       (b* (((list a) args)
            (or-a     (make-vl-nonatom :op :vl-unary-bitor  :args (list a)))
            (~or-a    (make-vl-nonatom :op :vl-unary-bitnot :args (list or-a)))
            (result   (make-vl-nonatom :op :vl-concat
                                       :atts atts
                                       :args (list ~or-a))))
         (mv warnings result)))


      (:vl-unary-xnor
       ;; ~^ (a)  -->  {~( ^a )}

; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.

       (b* (((list a) args)
            (^a       (make-vl-nonatom :op :vl-unary-xor    :args (list a)))
            (~^a      (make-vl-nonatom :op :vl-unary-bitnot :args (list ^a)))
            (result   (make-vl-nonatom :op :vl-concat
                                       :atts atts
                                       :args (list ~^a))))
         (mv warnings result)))


      ((:vl-binary-eq)
       ;; a == b    -->  &(a ~^ b)

; We once also rewrite a === b and warned that it was a dangerous operator.
; But we now treat === as a primitive instead, and leave it up to warn about it
; and perhaps to explain how it is being handled.

       (b* (((list a b) args)
            (a~^b   (make-vl-nonatom :op :vl-binary-xnor :args (list a b)))
            (result (make-vl-nonatom :op :vl-unary-bitand
                                     :atts atts
                                     :args (list a~^b))))
         (mv warnings result)))


      ((:vl-binary-neq)
       ;; a != b    -->  |(a ^ b)

; We once rewrite a !== b in the same way, but now it is handled separately
; since === is a primitive.

       (b* (((list a b) args)
            (a^b        (make-vl-nonatom :op :vl-binary-xor :args (list a b)))
            (result     (make-vl-nonatom :op :vl-unary-bitor
                                         :atts atts
                                         :args (list a^b))))
         (mv warnings result)))

      (:vl-binary-cne
       ;; a !== b   -->  {~(a === b)}
       (b* (((list a b) args)
            (a===b      (make-vl-nonatom :op :vl-binary-ceq :args (list a b)))
            (~a===b     (make-vl-nonatom :op :vl-unary-bitnot :args (list a===b)))
            (result     (make-vl-nonatom :op :vl-concat
                                         :atts atts
                                         :args (list ~a===b))))
         (mv warnings result)))

      (:vl-binary-lt
       ;; a < b     -->  {~(a >= b)}

; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.

; Note that on Verilog-XL, in a 4-bit context, when there are X bits involved,
; a < b produces 4'bXXXX instead of 4'b000X like NCVerilog produces.  From the
; Verilog-2005 standard, it seems that NCVerilog gets it right: the answer from an
; addition is supposed to be one-bit unsigned.  So, this rewrite doesn't agree
; with the Verilog-XL interpretation in all cases, but that's okay because
; Verilog-XL is wrong.

       (b* (((list a b) args)
            (a>=b       (make-vl-nonatom :op :vl-binary-gte   :args (list a b)))
            (~a>=b      (make-vl-nonatom :op :vl-unary-bitnot :args (list a>=b)))
            (result     (make-vl-nonatom :op :vl-concat
                                         :atts atts
                                         :args (list ~a>=b))))
           (mv warnings result)))

      (:vl-binary-gt
       ;; a > b     -->  {~(b >= a)}

; BUG FOUND ON 2011-09-22.  Same deal as binary-lt.

       (b* (((list a b) args)
            (b>=a       (make-vl-nonatom :op :vl-binary-gte   :args (list b a)))
            (~b>=a      (make-vl-nonatom :op :vl-unary-bitnot :args (list b>=a)))
            (result     (make-vl-nonatom :op :vl-concat
                                         :atts atts
                                         :args (list ~b>=a))))
         (mv warnings result)))


      (:vl-binary-lte
       ;; a <= b    -->  b >= a
       (b* (((list a b) args)
            (result (make-vl-nonatom :op :vl-binary-gte
                                     :atts atts
                                     :args (list b a))))
         (mv warnings result)))

      (:vl-multiconcat
       (let ((result (vl-maybe-consolidate-multiconcat
                      (make-vl-nonatom :op :vl-multiconcat
                                       :args args
                                       :atts atts))))
         (mv warnings result)))

      (otherwise
       (mv warnings (make-vl-nonatom :op op
                                     :args args
                                     :atts atts)))))

  (defthm vl-warninglist-p-of-vl-op-oprewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-op-oprewrite op args atts warnings))))
    :hints(("Goal" :in-theory (enable vl-op-oprewrite))))

  (defthm vl-expr-p-of-vl-op-oprewrite
    (implies (and (force (vl-op-p op))
                  (force (vl-exprlist-p args))
                  (force (vl-atts-p atts))
                  (force (or (not (vl-op-arity op))
                             (equal (len args) (vl-op-arity op)))))
             (vl-expr-p (mv-nth 1 (vl-op-oprewrite op args atts warnings))))
    :hints(("Goal" :in-theory (enable vl-op-oprewrite)))))



; Special outside-in rewrite for strange muxes

(defsection vl-qmark-p
  :parents (oprewrite)

  ;; Recognize a ? b : c and return the components, or return NILs
  ;; if X doens't match.

  (defund vl-qmark-p (x)
    "Returns (MV A B C)"
    (declare (xargs :guard (vl-expr-p x)))
    (b* (((when (vl-fast-atom-p x))
          (mv nil nil nil))
         ((unless (and (eq (vl-nonatom->op x) :vl-qmark)
                       (mbt (equal (len (vl-nonatom->args x)) 3))))
          (mv nil nil nil))
         (args (vl-nonatom->args x)))
      (mv (first args) (second args) (third args))))

  (local (in-theory (enable vl-qmark-p)))

  (defthm vl-qmark-p-basics
    (let ((ret (vl-qmark-p x)))
      (implies (vl-expr-p x)
               (and (equal (vl-expr-p (mv-nth 0 ret))
                           (if (mv-nth 0 ret) t nil))
                    (equal (vl-expr-p (mv-nth 1 ret))
                           (if (mv-nth 0 ret) t nil))
                    (equal (vl-expr-p (mv-nth 2 ret))
                           (if (mv-nth 0 ret) t nil)))))))

(defsection vl-goofymux-p
  :parents (oprewrite)

  ;; Recognize terms of the following forms:
  ;;  1. (i1 === i2) ? i1 : (s ? i1 : i2)
  ;;  2. (i1 === i2) ? i2 : (s ? i1 : i2)
  ;;  3. (i1 === i2) ? i1 : (s ? i2 : i1)
  ;;  4. (i1 === i2) ? i2 : (s ? i2 : i1)
  ;; Return the three components, or NIL if it doesn't match.

  (defund vl-goofymux-p (x)
    "Returns (MV S I1 I2)"
    (declare (xargs :guard (vl-expr-p x)))
    (b* (((mv equiv i1 mux)
          (vl-qmark-p x))
         ((unless equiv)
          (mv nil nil nil))
         ((unless (and (not (vl-fast-atom-p equiv))
                       (eq (vl-nonatom->op equiv) :vl-binary-ceq)))
          (mv nil nil nil))

         (i1-fix    (vl-expr-fix i1))
         (equiv-lhs (vl-expr-fix (first (vl-nonatom->args equiv))))
         (equiv-rhs (vl-expr-fix (second (vl-nonatom->args equiv))))
         ((unless (or (equal equiv-lhs i1-fix)
                      (equal equiv-rhs i1-fix)))
          (mv nil nil nil))

         ((mv sel mi1 mi2) (vl-qmark-p mux))
         ((unless sel)
          (mv nil nil nil))

         (mi1-fix (vl-expr-fix mi1))
         (mi2-fix (vl-expr-fix mi2))

         ((unless (or (and (equal equiv-lhs mi1-fix)
                           (equal equiv-rhs mi2-fix))
                      (and (equal equiv-lhs mi2-fix)
                           (equal equiv-rhs mi1-fix))))
          (mv nil nil nil)))
      (mv sel mi1 mi2)))

  (local (in-theory (enable vl-goofymux-p)))

  (defthm vl-goofymux-p-basics
    (let ((ret (vl-goofymux-p x)))
      (implies (vl-expr-p x)
               (and (equal (vl-expr-p (mv-nth 0 ret))
                           (if (mv-nth 0 ret) t nil))
                    (equal (vl-expr-p (mv-nth 1 ret))
                           (if (mv-nth 0 ret) t nil))
                    (equal (vl-expr-p (mv-nth 2 ret))
                           (if (mv-nth 0 ret) t nil)))))))


(defsection vl-goofymux-rewrite
  :parents (oprewrite)

  (local (defthm crock
           (implies (and (mv-nth 0 (vl-goofymux-p x))
                         (vl-expr-p x))
                    (vl-nonatom-p x))
           :hints(("Goal" :in-theory (enable vl-goofymux-p
                                             vl-qmark-p)))))

  (local (defthm crock2
           (implies (vl-atom-p x)
                    (equal (vl-expr-count x)
                           1))
           :hints(("Goal" :in-theory (enable vl-expr-count)))))

  (local (defthm crock3
           (implies (not (vl-atom-p x))
                    (equal (vl-expr-count x)
                           (+ 1 (vl-exprlist-count (vl-nonatom->args x)))))
           :hints(("Goal" :in-theory (enable vl-expr-count)))))

  (local (defthm crock234
           (implies (mv-nth 0 (vl-qmark-p x))
                    (equal (vl-expr-count x)
                           (+ 2 (vl-expr-count (mv-nth 0 (vl-qmark-p x)))
                              (vl-expr-count (mv-nth 1 (vl-qmark-p x)))
                              (vl-expr-count (mv-nth 2 (vl-qmark-p x))))))
           :hints(("Goal" :in-theory (e/d (vl-qmark-p)
                                          ((force)))
                   :expand ((vl-exprlist-count (vl-nonatom->args x))
                            (vl-exprlist-count (cdr (vl-nonatom->args x)))
                            (vl-exprlist-count (cddr (vl-nonatom->args x))))))))


  (defund vl-goofymux-rewrite (x)
    (declare (xargs :guard (vl-expr-p x)))
    (b* (((mv sel i1 i2) (vl-goofymux-p x))
         ((unless sel)
          x))
      (make-vl-nonatom
       :op :vl-qmark
       :args (list sel i1 i2)
       ;; See vl-mux-occform; this uses a less-conservative version of the mux,
       ;; which is what we want if we're writing this goofy === thing.
       :atts (acons "VL_X_SELECT" nil (vl-nonatom->atts x)))))

  (local (in-theory (enable vl-goofymux-rewrite)))

  (defthm vl-expr-p-of-vl-goofymux-rewrite
    (implies (force (vl-expr-p x))
             (vl-expr-p (vl-goofymux-rewrite x))))

  (defthm vl-expr-count-of-vl-goofymux-rewrite
    (<= (vl-expr-count (vl-goofymux-rewrite x))
        (vl-expr-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable vl-goofymux-p))))

  (defthm vl-nonatom-p-of-vl-goofymux-rewrite
    (implies (vl-expr-p x)
             (equal (vl-nonatom-p (vl-goofymux-rewrite x))
                    (vl-nonatom-p x))))

  (defthm vl-not-atom-p-of-vl-goofymux-rewrite
    (equal (vl-atom-p (vl-goofymux-rewrite x))
           (vl-atom-p x))
    :hints(("Goal" :in-theory (e/d (vl-goofymux-p
                                    vl-qmark-p)
                                   ((force)))))))



(defsection vl-expr-oprewrite
  :parents (oprewrite)
  :short "@(call vl-expr-oprewrite) rewrites operators throughout the @(see
vl-expr-p) @('x') and returns @('(mv warnings-prime x-prime)')."

  (mutual-recursion

   (defund vl-expr-oprewrite (x warnings)
     "Returns (MV WARNINGS-PRIME X-PRIME)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (vl-expr-count x)))
     (b* (((when (vl-fast-atom-p x))
           (mv warnings x))

          ;; Outside-in rewriting of any goofy mux expressions.  We might
          ;; eventually want to expand this to include other kinds of rules
          ;; about === or other operators that we're too conservative for...
          (x (vl-goofymux-rewrite x))
          ((vl-nonatom x) x)

          ((mv warnings args-prime)
           (vl-exprlist-oprewrite x.args warnings)))
       (vl-op-oprewrite x.op args-prime x.atts warnings)))

   (defund vl-exprlist-oprewrite (x warnings)
     "Returns (MV WARNINGS-PRIME X-PRIME)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (vl-exprlist-count x)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-prime) (vl-expr-oprewrite (car x) warnings))
          ((mv warnings cdr-prime) (vl-exprlist-oprewrite (cdr x) warnings)))
       (mv warnings (cons car-prime cdr-prime)))))

  (defthm vl-exprlist-oprewrite-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-oprewrite x warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-oprewrite))))

  (defthm vl-exprlist-oprewrite-when-of-cons
    (equal (vl-exprlist-oprewrite (cons a x) warnings)
           (b* (((mv warnings car-prime) (vl-expr-oprewrite a warnings))
                ((mv warnings cdr-prime) (vl-exprlist-oprewrite x warnings)))
               (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-exprlist-oprewrite))))

  (local (defun my-induction (x warnings)
           (if (atom x)
               (mv warnings nil)
             (b* (((mv warnings &) (vl-expr-oprewrite (car x) warnings)))
                 (my-induction (cdr x) warnings)))))

  (defthm len-of-vl-exprlist-oprewrite
    (equal (len (mv-nth 1 (vl-exprlist-oprewrite x warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x warnings))))

  (defthm true-listp-of-vl-exprlist-oprewrite
    (true-listp (mv-nth 1 (vl-exprlist-oprewrite x warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-induction x warnings))))

  (FLAG::make-flag vl-flag-expr-oprewrite
                   vl-expr-oprewrite
                   :flag-mapping ((vl-expr-oprewrite . expr)
                                  (vl-exprlist-oprewrite . list)))

  (defthm-vl-flag-expr-oprewrite lemma
    (expr (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-expr-oprewrite x warnings))))
          :name vl-warninglist-p-of-vl-expr-oprewrite)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-exprlist-oprewrite x warnings))))
          :name vl-warninglist-p-of-vl-exprlist-oprewrite)
    :hints(("Goal"
            :induct (vl-flag-expr-oprewrite flag x warnings)
            :expand ((vl-expr-oprewrite x warnings)
                     (vl-exprlist-oprewrite x warnings)))))

  (defthm-vl-flag-expr-oprewrite lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (mv-nth 1 (vl-expr-oprewrite x warnings))))
          :name vl-expr-p-of-vl-expr-oprewrite)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (mv-nth 1 (vl-exprlist-oprewrite x warnings))))
          :name vl-exprlist-p-of-vl-exprlist-oprewrite)
    :hints(("Goal"
            :induct (vl-flag-expr-oprewrite flag x warnings)
            :expand ((vl-expr-oprewrite x warnings)
                     (vl-exprlist-oprewrite x warnings)))))

  (verify-guards vl-expr-oprewrite))



(defmacro def-vl-oprewrite (name &key type body)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (short      (cat "Rewrite operators throughout a @(see " type-s ")"))
         (long       (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('(mv warnings-prime x-prime)')</p>")))

  `(defsection ,name
     :parents (oprewrite)
     :short ,short
     :long ,long

    (defund ,name (x warnings)
      (declare (xargs :guard (and (,type x)
                                  (vl-warninglist-p warnings))))
      ,body)

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

    (defthm ,thm-type
      (implies (force (,type x))
               (,type (mv-nth 1 (,name x warnings)))))
    )))


(defmacro def-vl-oprewrite-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name))
         (short      (cat "Rewrite operators throughout a @(see " type-s ")"))
         (long       (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('(mv warnings-prime x-prime)')</p>")))

  `(defsection ,name
     :parents (oprewrite)
     :short ,short
     :long ,long

    (defund ,name (x warnings)
      (declare (xargs :guard (and (,type x)
                                  (vl-warninglist-p warnings))))
      (if (atom x)
          (mv warnings nil)
        (b* (((mv warnings car-prime) (,element (car x) warnings))
             ((mv warnings cdr-prime) (,name (cdr x) warnings)))
            (mv warnings (cons car-prime cdr-prime)))))

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x warnings)))))

    (defthm ,thm-type
      (implies (force (,type x))
               (,type (mv-nth 1 (,name x warnings)))))

    (defthm ,thm-true
      (true-listp (mv-nth 1 (,name x warnings)))
      :rule-classes :type-prescription))))



(def-vl-oprewrite vl-maybe-expr-oprewrite
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv warnings nil)
          (vl-expr-oprewrite x warnings)))

(def-vl-oprewrite vl-assign-oprewrite
  :type vl-assign-p
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-oprewrite x.lvalue warnings))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings
                (change-vl-assign x
                                  :lvalue lvalue-prime
                                  :expr expr-prime))))

(def-vl-oprewrite-list vl-assignlist-oprewrite
  :type vl-assignlist-p
  :element vl-assign-oprewrite)


(def-vl-oprewrite vl-plainarg-oprewrite
  :type vl-plainarg-p
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-oprewrite-list vl-plainarglist-oprewrite
  :type vl-plainarglist-p
  :element vl-plainarg-oprewrite)


(def-vl-oprewrite vl-namedarg-oprewrite
  :type vl-namedarg-p
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-oprewrite-list vl-namedarglist-oprewrite
  :type vl-namedarglist-p
  :element vl-namedarg-oprewrite)

(def-vl-oprewrite vl-arguments-oprewrite
  :type vl-arguments-p
  :body (b* (((vl-arguments x) x)
             ((mv warnings args-prime)
              (if x.namedp
                  (vl-namedarglist-oprewrite x.args warnings)
                (vl-plainarglist-oprewrite x.args warnings))))
            (mv warnings (vl-arguments x.namedp args-prime))))

(def-vl-oprewrite vl-modinst-oprewrite
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x)
             ((mv warnings args-prime)
              (vl-arguments-oprewrite x.portargs warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-oprewrite-list vl-modinstlist-oprewrite
  :type vl-modinstlist-p
  :element vl-modinst-oprewrite)

(def-vl-oprewrite vl-gateinst-oprewrite
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args-prime)
              (vl-plainarglist-oprewrite x.args warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-oprewrite-list vl-gateinstlist-oprewrite
  :type vl-gateinstlist-p
  :element vl-gateinst-oprewrite)

(def-vl-oprewrite vl-delaycontrol-oprewrite
  :type vl-delaycontrol-p
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime)
              (vl-expr-oprewrite x.value warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-oprewrite vl-evatom-oprewrite
  :type vl-evatom-p
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-oprewrite-list vl-evatomlist-oprewrite
  :type vl-evatomlist-p
  :element vl-evatom-oprewrite)

(def-vl-oprewrite vl-eventcontrol-oprewrite
  :type vl-eventcontrol-p
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime)
              (vl-evatomlist-oprewrite x.atoms warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-oprewrite vl-repeateventcontrol-oprewrite
  :type vl-repeateventcontrol-p
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-oprewrite x.ctrl warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-oprewrite vl-delayoreventcontrol-oprewrite
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol (vl-delaycontrol-oprewrite x warnings))
           (:vl-eventcontrol (vl-eventcontrol-oprewrite x warnings))
           (:vl-repeat-eventcontrol (vl-repeateventcontrol-oprewrite x warnings))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-oprewrite
                    "Impossible case.  This is not really an error.  We are just ~
                     using the guard mechanism to prove that all cases have been ~
                     covered.")
                x)))))

(def-vl-oprewrite vl-maybe-delayoreventcontrol-oprewrite
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-oprewrite x warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-oprewrite-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-oprewrite x warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-oprewrite
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-oprewrite))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-oprewrite)))))



(def-vl-oprewrite vl-nullstmt-oprewrite
  :type vl-nullstmt-p
  :body (mv warnings x))

(def-vl-oprewrite vl-assignstmt-oprewrite
  :type vl-assignstmt-p
  :body (b* (((vl-assignstmt x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-oprewrite x.lvalue warnings))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings))
             ((mv warnings ctrl-prime)
              (vl-maybe-delayoreventcontrol-oprewrite x.ctrl warnings))
             (x-prime
              (change-vl-assignstmt x
                                    :lvalue lvalue-prime
                                    :expr expr-prime
                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite vl-deassignstmt-oprewrite
  :type vl-deassignstmt-p
  :body (b* (((vl-deassignstmt x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-oprewrite x.lvalue warnings))
             (x-prime
              (change-vl-deassignstmt x :lvalue lvalue-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite vl-enablestmt-oprewrite
  :type vl-enablestmt-p
  :body (b* (((vl-enablestmt x) x)
             ((mv warnings id-prime)
              (vl-expr-oprewrite x.id warnings))
             ((mv warnings args-prime)
              (vl-exprlist-oprewrite x.args warnings))
             (x-prime
              (change-vl-enablestmt x
                                    :id id-prime
                                    :args args-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite vl-disablestmt-oprewrite
  :type vl-disablestmt-p
  :body (b* (((vl-disablestmt x) x)
             ((mv warnings id-prime)
              (vl-expr-oprewrite x.id warnings))
             (x-prime
              (change-vl-disablestmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite vl-eventtriggerstmt-oprewrite
  :type vl-eventtriggerstmt-p
  :body (b* (((vl-eventtriggerstmt x) x)
             ((mv warnings id-prime)
              (vl-expr-oprewrite x.id warnings))
             (x-prime
              (change-vl-eventtriggerstmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite vl-atomicstmt-oprewrite
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (vl-nullstmt-oprewrite x warnings))
          (:vl-assignstmt       (vl-assignstmt-oprewrite x warnings))
          (:vl-deassignstmt     (vl-deassignstmt-oprewrite x warnings))
          (:vl-enablestmt       (vl-enablestmt-oprewrite x warnings))
          (:vl-disablestmt      (vl-disablestmt-oprewrite x warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-oprewrite x warnings))
          (otherwise
           (mv (er hard 'vl-atomicstmt-oprewrite
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               x))))

(defsection vl-stmt-oprewrite

(mutual-recursion

   (defund vl-stmt-oprewrite (x warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-oprewrite x warnings)
       (b* (((vl-compoundstmt x) x)
            ((mv warnings exprs-prime)
             (vl-exprlist-oprewrite x.exprs warnings))
            ((mv warnings stmts-prime)
             (vl-stmtlist-oprewrite x.stmts warnings))
            ((mv warnings ctrl-prime)
             (vl-maybe-delayoreventcontrol-oprewrite x.ctrl warnings))
            (x-prime
             (change-vl-compoundstmt x
                                     :exprs exprs-prime
                                     :stmts stmts-prime
                                     :ctrl ctrl-prime)))
           (mv warnings x-prime))))

   (defund vl-stmtlist-oprewrite (x warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil)
       (b* (((mv warnings car-prime) (vl-stmt-oprewrite (car x) warnings))
            ((mv warnings cdr-prime) (vl-stmtlist-oprewrite (cdr x) warnings)))
           (mv warnings (cons car-prime cdr-prime))))))

(FLAG::make-flag vl-flag-stmt-oprewrite
                   vl-stmt-oprewrite
                   :flag-mapping ((vl-stmt-oprewrite . stmt)
                                  (vl-stmtlist-oprewrite . list)))

(defthm-vl-flag-stmt-oprewrite lemma
    (stmt (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmt-oprewrite x warnings))))
          :name vl-warninglist-p-of-vl-stmt-oprewrite)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmtlist-oprewrite x warnings))))
          :name vl-warninglist-p-of-vl-stmtlist-oprewrite)
    :hints(("Goal"
            :induct (vl-flag-stmt-oprewrite flag x warnings)
            :expand ((vl-stmt-oprewrite x warnings)
                     (vl-stmtlist-oprewrite x warnings)))))

(defthm vl-stmtlist-oprewrite-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-oprewrite x warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-oprewrite))))

(defthm vl-stmtlist-oprewrite-of-cons
    (equal (vl-stmtlist-oprewrite (cons a x) warnings)
           (b* (((mv warnings car-prime) (vl-stmt-oprewrite a warnings))
                ((mv warnings cdr-prime) (vl-stmtlist-oprewrite x warnings)))
               (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-stmtlist-oprewrite))))

(local (defun my-induction (x warnings)
           (if (atom x)
               (mv warnings x)
             (b* (((mv warnings car-prime) (vl-stmt-oprewrite (car x) warnings))
                  ((mv warnings cdr-prime) (my-induction (cdr x) warnings)))
                 (mv warnings (cons car-prime cdr-prime))))))

(defthm len-of-vl-stmtlist-oprewrite
    (equal (len (mv-nth 1 (vl-stmtlist-oprewrite x warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x warnings))))

(defthm-vl-flag-stmt-oprewrite lemma
    (stmt (implies (force (vl-stmt-p x))
                   (vl-stmt-p (mv-nth 1 (vl-stmt-oprewrite x warnings))))
          :name vl-stmt-p-of-vl-stmt-oprewrite)
    (list (implies (force (vl-stmtlist-p x))
                   (vl-stmtlist-p (mv-nth 1 (vl-stmtlist-oprewrite x warnings))))
          :name vl-stmtlist-p-of-vl-stmtlist-oprewrite)
    :hints(("Goal"
            :induct (vl-flag-stmt-oprewrite flag x warnings)
            :expand ((vl-stmt-oprewrite x warnings)
                     (vl-stmtlist-oprewrite x warnings)))))

  (verify-guards vl-stmt-oprewrite))

(def-vl-oprewrite vl-always-oprewrite
  :type vl-always-p
  :body (b* (((vl-always x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-oprewrite x.stmt warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite-list vl-alwayslist-oprewrite
  :type vl-alwayslist-p
  :element vl-always-oprewrite)

(def-vl-oprewrite vl-initial-oprewrite
  :type vl-initial-p
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-oprewrite x.stmt warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite-list vl-initiallist-oprewrite
  :type vl-initiallist-p
  :element vl-initial-oprewrite)


(defsection vl-module-oprewrite
  :parents (oprewrite)

  (defund vl-module-oprewrite (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         ((when (vl-module->hands-offp x))
          x)
         (warnings                x.warnings)
         ((mv warnings assigns)   (vl-assignlist-oprewrite   x.assigns warnings))
         ((mv warnings modinsts)  (vl-modinstlist-oprewrite  x.modinsts warnings))
         ((mv warnings gateinsts) (vl-gateinstlist-oprewrite x.gateinsts warnings))
         ((mv warnings alwayses)  (vl-alwayslist-oprewrite   x.alwayses warnings))
         ((mv warnings initials)  (vl-initiallist-oprewrite  x.initials warnings)))
      (change-vl-module x
                        :assigns assigns
                        :modinsts modinsts
                        :gateinsts gateinsts
                        :alwayses alwayses
                        :initials initials
                        :warnings warnings)))

  (local (in-theory (enable vl-module-oprewrite)))

  (defthm vl-module-p-of-vl-module-oprewrite
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-oprewrite x))))

  (defthm vl-module->name-of-vl-module-oprewrite
    (equal (vl-module->name (vl-module-oprewrite x))
           (vl-module->name x))))


(defprojection vl-modulelist-oprewrite (x)
  (vl-module-oprewrite x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-oprewrite
     (equal (vl-modulelist->names (vl-modulelist-oprewrite x))
            (vl-modulelist->names x)))))
