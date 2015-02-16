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
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/strip")
(local (include-book "../util/arithmetic"))
(local (in-theory (enable tag-reasoning)))
(local (std::add-default-post-define-hook :fix))

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

(local (xdoc::set-default-parents oprewrite))

(define vl-replicate-constint-value
  :short "Generate @('n') copies of a constant integer."
  ((n     natp "How many copies to generate.")
   (width posp "The bit-width of @('x').")
   (x     natp "The integer to replicate."))
  :returns (replicated natp :rule-classes :type-prescription)
  (let ((width (lposfix width)))
    (if (zp n)
        0
      (+ (ash (lnfix x) (* width (1- n)))
         (vl-replicate-constint-value (- n 1) width x))))
  ///
  (local
   (progn
     (assert! (equal (vl-replicate-constint-value 5 1 1) #b11111))
     (assert! (equal (vl-replicate-constint-value 5 2 1) #b0101010101))
     (assert! (equal (vl-replicate-constint-value 5 3 1) #b001001001001001))
     (assert! (equal (vl-replicate-constint-value 3 5 1) #b000010000100001))
     (assert! (equal (vl-replicate-constint-value 3 5 7) #b001110011100111))
     (assert! (equal (vl-replicate-constint-value 1 5 7) #b00111)))))

(define vl-replicate-weirdint-bits
  :short "Generate @('n') copies of a weird integer."
  ((n natp         "How many copies to generate.")
   (x vl-bitlist-p "The bits of the weirdint."))
  :returns (new-bits vl-bitlist-p)
  (if (zp n)
      nil
    (append-without-guard (vl-bitlist-fix x)
                          (vl-replicate-weirdint-bits (- n 1) x)))
  ///
  (defthm len-of-vl-replicate-weirdint-bits
    (equal (len (vl-replicate-weirdint-bits n x))
           (* (nfix n) (len x)))))

(define vl-maybe-consolidate-multiconcat ((x vl-expr-p))
  :guard (and (not (vl-atom-p x))
              (equal (vl-nonatom->op x) :vl-multiconcat))
  :returns (expr vl-expr-p)
  (b* ((x (vl-expr-fix x))
       ((list arg1 arg2) (vl-nonatom->args x))
       ((unless (and
                 ;; The first argument must be a constant, positive integer.
                 (vl-fast-atom-p arg1)
                 (vl-fast-constint-p (vl-atom->guts arg1))
                 (posp (vl-constint->value (vl-atom->guts arg1)))
                 ;; The second argument must be a concatenation with a single, atomic
                 ;; argument.
                 (not (vl-fast-atom-p arg2))
                 (eq (vl-nonatom->op arg2) :vl-concat)
                 (eql 1 (len (vl-nonatom->args arg2)))
                 (vl-fast-atom-p (first (vl-nonatom->args arg2)))))
        x)

       (num-copies (vl-constint->value (vl-atom->guts arg1)))
       (original   (vl-atom->guts (first (vl-nonatom->args arg2))))

       ((when (and (vl-constint-p original)
                   (posp (vl-constint->origwidth original))
                   (natp (vl-constint->value original))))
        (b* ((width     (vl-constint->origwidth original))
             (value     (vl-constint->value original))
             (new-width (* num-copies width))
             (new-val   (vl-replicate-constint-value num-copies width value))
             ((when (< new-val (expt 2 new-width)))
              (make-vl-atom
               :guts (make-vl-constint :origwidth new-width
                                       ;; multiconcat always produces unsigned results
                                       :origtype :vl-unsigned
                                       :value new-val))))
          (raise "Out of range??")
          x))

       ((when (and (vl-weirdint-p original)
                   (posp (vl-weirdint->origwidth original))))
        (b* ((width (vl-weirdint->origwidth original))
             (bits  (vl-weirdint->bits original)))
          (make-vl-atom
           :guts (make-vl-weirdint
                  :origwidth (* num-copies width)
                  :origtype :vl-unsigned ;; multiconcat always produced unsigned results
                  :bits (vl-replicate-weirdint-bits num-copies bits))))))

      x))

(define vl-op-oprewrite
  :short "Main operator rewriting function."
  ((op       vl-op-p            "Some operator")
   (args     vl-exprlist-p      "The arguments to the operator (already rewritten).")
   (atts     vl-atts-p          "The attributes for the operator.")
   (warnings vl-warninglist-p   "Ordinary @(see warnings) accumulator."))
  :guard
  (or (not (vl-op-arity op))
      (equal (len args) (vl-op-arity op)))
  :returns
  (mv (warnings vl-warninglist-p)
      (expr     vl-expr-p "Possibly simplified, rewritten version of @('op(args)')."))
  :long "<p>Keeping this function separate from @(see vl-expr-oprewrite) helps
         to keep the mutual recursion as simple as possible.</p>"
  :guard-hints (("Goal" :in-theory (enable vl-op-p vl-op-arity vl-ops-table)))
  :verbosep t
  (case (vl-op-fix op)
    (:vl-qmark
     (b* (((list a b c) args)
          (or-a (make-vl-nonatom :op :vl-unary-bitor
                                 :args (list a)
                                 :atts (acons "VL_CONDITIONAL_FIX" nil atts))))

       (if (vl-zatom-p b)
           ;; a ? z : c -->  ~(|a) ? c : z
           (let ((nor-a (make-vl-nonatom :op :vl-unary-bitnot
                                         :args (list or-a)
                                         :atts (acons "VL_CONDITIONAL_FIX" nil atts)
                                         )))
             (mv (ok) (make-vl-nonatom :op :vl-qmark
                                       :atts atts
                                       :args (list nor-a c b))))
         ;; a ? b : c --> (|a) ? b : c
         (mv (ok) (make-vl-nonatom :op :vl-qmark
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
       (mv (ok) result)))

    (:vl-binary-logor
     ;; a || b --> (|a) | (|b)
     (b* (((list a b) args)
          (or-a   (make-vl-nonatom :op :vl-unary-bitor :args (list a)))
          (or-b   (make-vl-nonatom :op :vl-unary-bitor :args (list b)))
          (result (make-vl-nonatom :op :vl-binary-bitor
                                   :atts atts
                                   :args (list or-a or-b))))
       (mv (ok) result)))


    (:vl-unary-plus
     ;; +a --> a + 1'sb0

     ;; What is the meaning of +a?  In Verilog-XL it seems to be equal to A.
     ;; In NCVerilog it is equal to (a + 1'sb0).
     ;;
     ;; This difference matters because, e.g., if a is 4'b000X, then in
     ;; Verilog-XL +a is also 4'b000X, whereas in NCVerilog it is 4'bXXXX.  We
     ;; choose to implement NCVerilog's behavior since it is more conservative.
     ;;
     ;; It's important to add a signed zero since otherwise we could
     ;; inadvertently be changing the sign of the expression.  If A is signed
     ;; we preserve this since signed + signed is signed.  If A is unsigned, we
     ;; also preserve it since unsigned + signed is unsigned.
     ;;
     ;; It's important to add a one-bit zero since that way we know that we are
     ;; not increasing the size of the expression.  If A is one bit we won't be
     ;; changing its size.  If A is larger, we'll inherit its size.
     (b* (((list a) args)
          (|1'sb0|  (make-vl-atom
                     :guts (make-vl-constint :value 0
                                             :origwidth 1
                                             :origtype :vl-signed)))
          (result   (make-vl-nonatom :op :vl-binary-plus
                                     :atts atts
                                     :args (list a |1'sb0|))))
       (mv (ok) result)))


    (:vl-unary-minus
     ;; -a --> 1'sb0 - a

     ;; Verilog-XL and NCVerilog both agree on this for the meaning of -a.
     (b* (((list a) args)
          (|1'sb0|  (make-vl-atom
                     :guts (make-vl-constint :value 0
                                             :origwidth 1
                                             :origtype :vl-signed)))
          (result   (make-vl-nonatom :op :vl-binary-minus
                                     :atts atts
                                     :args (list |1'sb0| a))))
       (mv (ok) result)))


    (:vl-unary-lognot
     ;; !a -->  {~(|a)}

     ;; BUG FOUND ON 2011-09-22.  We used to not put in the concatenation.
     ;; This was correct for one-bit contexts, but if a !a was being used in a
     ;; wider context, there could be a problem.  For instance, if a was
     ;; 4'b1011, then something like:
     ;;
     ;;    wire [3:0] w = !a;
     ;;
     ;; should yield w = 4'b0000.  But without the concatenation, the ~ gets
     ;; applied to 4'b0001, and yields 4'b1110, which is just totally wrong.
     ;;
     ;; We therefore add the concatenation to force the ~ to be self-determined
     ;; and hence to be carried out in one bit.  This creates an unsigned
     ;; result, but that is okay because (we think) !a should produce a one-bit
     ;; unsigned result anyway.
     (b* (((list a) args)
          (or-a   (make-vl-nonatom :op :vl-unary-bitor  :args (list a)))
          (~or-a  (make-vl-nonatom :op :vl-unary-bitnot :args (list or-a)))
          (result (make-vl-nonatom :op :vl-concat
                                   :atts atts
                                   :args (list ~or-a))))
       (mv (ok) result)))


    (:vl-unary-nand
     ;; ~& (a)  -->  {~( &a )}

     ;; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.
     (b* (((list a) args)
          (and-a    (make-vl-nonatom :op :vl-unary-bitand :args (list a)))
          (~and-a   (make-vl-nonatom :op :vl-unary-bitnot :args (list and-a)))
          (result   (make-vl-nonatom :op :vl-concat
                                     :atts atts
                                     :args (list ~and-a))))
       (mv (ok) result)))


    (:vl-unary-nor
     ;; ~| (a)  -->  {~( |a )}

     ;; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.
     (b* (((list a) args)
          (or-a     (make-vl-nonatom :op :vl-unary-bitor  :args (list a)))
          (~or-a    (make-vl-nonatom :op :vl-unary-bitnot :args (list or-a)))
          (result   (make-vl-nonatom :op :vl-concat
                                     :atts atts
                                     :args (list ~or-a))))
       (mv (ok) result)))


    (:vl-unary-xnor
     ;; ~^ (a)  -->  {~( ^a )}

     ;; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.
     (b* (((list a) args)
          (^a       (make-vl-nonatom :op :vl-unary-xor    :args (list a)))
          (~^a      (make-vl-nonatom :op :vl-unary-bitnot :args (list ^a)))
          (result   (make-vl-nonatom :op :vl-concat
                                     :atts atts
                                     :args (list ~^a))))
       (mv (ok) result)))


    ((:vl-binary-eq)
     ;; a == b    -->  &(a ~^ b)

     ;; We once also rewrite a === b and warned that it was a dangerous
     ;; operator.  But we now treat === as a primitive instead, and leave it up
     ;; to warn about it and perhaps to explain how it is being handled.
     (b* (((list a b) args)
          (a~^b   (make-vl-nonatom :op :vl-binary-xnor :args (list a b)))
          (result (make-vl-nonatom :op :vl-unary-bitand
                                   :atts atts
                                   :args (list a~^b))))
       (mv (ok) result)))


    ((:vl-binary-neq)
     ;; a != b    -->  |(a ^ b)

     ;; We once rewrite a !== b in the same way, but now it is handled
     ;; separately since === is a primitive.
     (b* (((list a b) args)
          (a^b        (make-vl-nonatom :op :vl-binary-xor :args (list a b)))
          (result     (make-vl-nonatom :op :vl-unary-bitor
                                       :atts atts
                                       :args (list a^b))))
       (mv (ok) result)))

    (:vl-binary-cne
     ;; a !== b   -->  {~(a === b)}
     (b* (((list a b) args)
          (a===b      (make-vl-nonatom :op :vl-binary-ceq :args (list a b)))
          (~a===b     (make-vl-nonatom :op :vl-unary-bitnot :args (list a===b)))
          (result     (make-vl-nonatom :op :vl-concat
                                       :atts atts
                                       :args (list ~a===b))))
       (mv (ok) result)))

    (:vl-binary-lt
     ;; a < b     -->  {~(a >= b)}

     ;; BUG FOUND ON 2011-09-22.  Same deal as unary-lognot.

     ;; Note that on Verilog-XL, in a 4-bit context, when there are X bits
     ;; involved, a < b produces 4'bXXXX instead of 4'b000X like NCVerilog
     ;; produces.  From the Verilog-2005 standard, it seems that NCVerilog gets
     ;; it right: the answer from an addition is supposed to be one-bit
     ;; unsigned.  So, this rewrite doesn't agree with the Verilog-XL
     ;; interpretation in all cases, but that's okay because Verilog-XL is
     ;; wrong.
     (b* (((list a b) args)
          (a>=b       (make-vl-nonatom :op :vl-binary-gte   :args (list a b)))
          (~a>=b      (make-vl-nonatom :op :vl-unary-bitnot :args (list a>=b)))
          (result     (make-vl-nonatom :op :vl-concat
                                       :atts atts
                                       :args (list ~a>=b))))
       (mv (ok) result)))

    (:vl-binary-gt
     ;; a > b     -->  {~(b >= a)}

     ;; BUG FOUND ON 2011-09-22.  Same deal as binary-lt.
     (b* (((list a b) args)
          (b>=a       (make-vl-nonatom :op :vl-binary-gte   :args (list b a)))
          (~b>=a      (make-vl-nonatom :op :vl-unary-bitnot :args (list b>=a)))
          (result     (make-vl-nonatom :op :vl-concat
                                       :atts atts
                                       :args (list ~b>=a))))
       (mv (ok) result)))


    (:vl-binary-lte
     ;; a <= b    -->  b >= a
     (b* (((list a b) args)
          (result (make-vl-nonatom :op :vl-binary-gte
                                   :atts atts
                                   :args (list b a))))
       (mv (ok) result)))

    (:vl-multiconcat
     (let ((result (vl-maybe-consolidate-multiconcat
                    (make-vl-nonatom :op :vl-multiconcat
                                     :args args
                                     :atts atts))))
       (mv (ok) result)))

    (otherwise
     (mv (ok) (make-vl-nonatom :op op
                               :args args
                               :atts atts)))))


; Special outside-in rewrite for strange muxes

(define vl-qmark-p
  :short "Recognize @('a ? b : c') and return the components, or return
@('nil')s for each when it's not a @('?:') expression."
  ((x vl-expr-p))
  :returns (mv (a (equal (vl-expr-p a) (if a t nil)))
               (b (equal (vl-expr-p b) (if a t nil)))
               (c (equal (vl-expr-p c) (if a t nil))))
  (b* (((when (vl-fast-atom-p x))
        (mv nil nil nil))
       ((unless (and (eq (vl-nonatom->op x) :vl-qmark)
                     (mbt (equal (len (vl-nonatom->args x)) 3))))
        (mv nil nil nil))
       ((list a b c) (vl-nonatom->args x)))
    (mv a b c)))

(define vl-goofymux-p
  :short "Recognize certain special muxes."
  :long "<p>We match expressions of the following forms:</p>
@({
    1. (i1 === i2) ? i1 : (s ? i1 : i2)
    2. (i1 === i2) ? i2 : (s ? i1 : i2)
    3. (i1 === i2) ? i1 : (s ? i2 : i1)
    4. (i1 === i2) ? i2 : (s ? i2 : i1)
})"
  ((x vl-expr-p))
  :returns (mv (s   (equal (vl-expr-p s)  (if s t nil)))
               (i1  (equal (vl-expr-p i1) (if s t nil)))
               (i2  (equal (vl-expr-p i2) (if s t nil))))
  (b* (((mv equiv i1 mux)
        (vl-qmark-p x))
       ((unless equiv)
        (mv nil nil nil))
       ((unless (and (not (vl-fast-atom-p equiv))
                     (eq (vl-nonatom->op equiv) :vl-binary-ceq)))
        (mv nil nil nil))

       (i1-fix    (vl-expr-strip i1))
       (equiv-lhs (vl-expr-strip (first (vl-nonatom->args equiv))))
       (equiv-rhs (vl-expr-strip (second (vl-nonatom->args equiv))))
       ((unless (or (equal equiv-lhs i1-fix)
                    (equal equiv-rhs i1-fix)))
        (mv nil nil nil))

       ((mv sel mi1 mi2) (vl-qmark-p mux))
       ((unless sel)
        (mv nil nil nil))

       (mi1-fix (vl-expr-strip mi1))
       (mi2-fix (vl-expr-strip mi2))

       ((unless (or (and (equal equiv-lhs mi1-fix)
                         (equal equiv-rhs mi2-fix))
                    (and (equal equiv-lhs mi2-fix)
                         (equal equiv-rhs mi1-fix))))
        (mv nil nil nil)))
    (mv sel mi1 mi2)))

(define vl-goofymux-rewrite
  :short "Annotate weird muxes with less conservative X behavior."
  ((x vl-expr-p))
  :returns (new-x vl-expr-p)
  (b* (((mv sel i1 i2) (vl-goofymux-p x))
       ((unless sel)
        (vl-expr-fix x)))
      (make-vl-nonatom
       :op :vl-qmark
       :args (list sel i1 i2)
       ;; See vl-mux-occform; this uses a less-conservative version of the mux,
       ;; which is what we want if we're writing this goofy === thing.
       :atts (acons "VL_X_SELECT" nil (vl-nonatom->atts x))))
  :prepwork
  ((local (defthm crock
            (implies (and (mv-nth 0 (vl-goofymux-p x))
                          (vl-expr-p x))
                     (equal (vl-expr-kind x) :nonatom))
            :hints(("Goal" :in-theory (enable vl-goofymux-p
                                              vl-qmark-p))))))
  ///
  (local (defthm l0
           (implies (vl-atom-p x)
                    (equal (vl-expr-count x)
                           1))
           :hints(("Goal" :in-theory (enable vl-expr-count)))))

  (local (defthm l1
           (implies (not (vl-atom-p x))
                    (equal (vl-expr-count-noatts x)
                           (+ 1 (vl-exprlist-count-noatts (vl-nonatom->args x)))))
           :hints(("Goal" :in-theory (enable vl-expr-count-noatts)))))

  (local (defthm l2a
           (implies (equal (vl-nonatom->op x) :vl-qmark)
                    (not (consp (cdddr (vl-nonatom->args x)))))
           :hints(("Goal"
                   :in-theory (e/d (vl-arity-ok-p)
                                   (vl-nonatom-requirements len-of-vl-nonatom->args))
                   :use ((:instance vl-nonatom-requirements))))))

  (local (defthm l2b
           (implies (atom x)
                    (equal (vl-exprlist-count-noatts x)
                           1))
           :hints(("Goal" :in-theory (enable vl-exprlist-count-noatts)))))

  (local (defthm l2
           (implies (mv-nth 0 (vl-qmark-p x))
                    (equal (vl-expr-count-noatts x)
                           (+ 5 (vl-expr-count-noatts (mv-nth 0 (vl-qmark-p x)))
                              (vl-expr-count-noatts (mv-nth 1 (vl-qmark-p x)))
                              (vl-expr-count-noatts (mv-nth 2 (vl-qmark-p x))))))
           :hints(("Goal"
                   :in-theory (e/d (vl-qmark-p)
                                   ((force)))
                   :expand ((vl-expr-count-noatts x)
                            (vl-exprlist-count-noatts (vl-nonatom->args x))
                            (vl-exprlist-count-noatts (cdr (vl-nonatom->args x)))
                            (vl-exprlist-count-noatts (cddr (vl-nonatom->args x))))))))

  (defthm vl-goofymux-rewrite-count-weak
    (<= (vl-expr-count-noatts (vl-goofymux-rewrite x))
        (vl-expr-count-noatts x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :in-theory (enable vl-goofymux-p))))

  (defthm vl-goofymux-rewrite-count-strong
    (implies (not (equal (vl-expr-kind x) :atom))
             (< (vl-exprlist-count-noatts (vl-nonatom->args (vl-goofymux-rewrite x)))
                (vl-expr-count-noatts x)))
    :hints(("Goal"
            :in-theory (enable vl-goofymux-p
                               vl-qmark-p)
            :expand ((vl-expr-count-noatts x)
                     (vl-exprlist-count-noatts (vl-nonatom->args x))
                     (vl-exprlist-count-noatts (cdr (vl-nonatom->args x)))
                     (vl-exprlist-count-noatts (cddr (vl-nonatom->args x)))))))

  (defthm vl-expr-kind-of-vl-goofymux-rewrite
    (equal (vl-expr-kind (vl-goofymux-rewrite x))
           (vl-expr-kind x))
    :hints(("Goal" :in-theory (enable vl-goofymux-p
                                      vl-qmark-p)))))




(defines vl-expr-oprewrite
  :short "@(call vl-expr-oprewrite) rewrites operators throughout the @(see
vl-expr-p) @('x') and returns @('(mv warnings-prime x-prime)')."

   (define vl-expr-oprewrite
     ((x vl-expr-p)
      (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (new-x    vl-expr-p))
     :verify-guards nil
     :measure (vl-expr-count-noatts x)
     (b* ((x (vl-expr-fix x))
          ((when (vl-fast-atom-p x))
           (mv (ok) x))

          ;; Outside-in rewriting of any goofy mux expressions.  We might
          ;; eventually want to expand this to include other kinds of rules
          ;; about === or other operators that we're too conservative for...
          (x (vl-goofymux-rewrite x))
          ((vl-nonatom x) x)

          ((mv warnings args-prime)
           (vl-exprlist-oprewrite x.args warnings)))
       (vl-op-oprewrite x.op args-prime x.atts warnings)))

   (define vl-exprlist-oprewrite
     ((x vl-exprlist-p)
      (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (new-x (and (vl-exprlist-p new-x)
                              (equal (len new-x) (len x)))))
     :measure (vl-exprlist-count-noatts x)
     (b* (((when (atom x))
           (mv (ok) nil))
          ((mv warnings car-prime) (vl-expr-oprewrite (car x) warnings))
          ((mv warnings cdr-prime) (vl-exprlist-oprewrite (cdr x) warnings)))
       (mv warnings (cons car-prime cdr-prime))))
   ///
   (verify-guards vl-expr-oprewrite)
   (deffixequiv-mutual vl-expr-oprewrite))


(defmacro def-vl-oprewrite (name &key body verbosep prepwork)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (type (mksym name '-p))
       (fix  (mksym name '-fix))
       (fn   (mksym name '-oprewrite)))
  `(define ,fn
     :short ,(cat "Rewrite operators throughout a @(see " (symbol-name type) ")")
     ((x ,type)
      (warnings vl-warninglist-p))
     :returns (mv (warnings vl-warninglist-p)
                  (new-x    ,type))
     :verbosep ,verbosep
     :prepwork ,prepwork
     (b* ((x (,fix x)))
       ,body))))

(defmacro def-vl-oprewrite-list (name &key element)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (type    (mksym name '-p))
       (fn      (mksym name '-oprewrite))
       (elem-fn (mksym element '-oprewrite)))
    `(define ,fn
       :short ,(cat "Rewrite operators throughout a @(see " (symbol-name type) ")")
       ((x ,type)
        (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       (b* (((when (atom x))
             (mv (ok) nil))
            ((mv warnings car-prime) (,elem-fn (car x) warnings))
            ((mv warnings cdr-prime) (,fn (cdr x) warnings)))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defmvtypes ,fn (nil true-listp)))))

(def-vl-oprewrite vl-maybe-expr
  :body (if (not x)
            (mv (ok) nil)
          (vl-expr-oprewrite x warnings)))

(def-vl-oprewrite vl-assign
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-oprewrite x.lvalue warnings))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings
                (change-vl-assign x
                                  :lvalue lvalue-prime
                                  :expr expr-prime))))

(def-vl-oprewrite-list vl-assignlist :element vl-assign)

(def-vl-oprewrite vl-plainarg
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv (ok) x))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-oprewrite-list vl-plainarglist :element vl-plainarg)


(def-vl-oprewrite vl-namedarg
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv (ok) x))
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-oprewrite-list vl-namedarglist :element vl-namedarg)

(def-vl-oprewrite vl-arguments
  :body (vl-arguments-case x
          :vl-arguments-named
          (b* (((mv warnings args-prime)
                (vl-namedarglist-oprewrite x.args warnings)))
            (mv warnings (change-vl-arguments-named x :args args-prime)))
          :vl-arguments-plain
          (b* (((mv warnings args-prime)
                (vl-plainarglist-oprewrite x.args warnings)))
            (mv warnings (change-vl-arguments-plain x :args args-prime)))))

(def-vl-oprewrite vl-modinst
  :body (b* (((vl-modinst x) x)
             ((mv warnings args-prime)
              (vl-arguments-oprewrite x.portargs warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-oprewrite-list vl-modinstlist :element vl-modinst)

(def-vl-oprewrite vl-gateinst
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args-prime)
              (vl-plainarglist-oprewrite x.args warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-oprewrite-list vl-gateinstlist :element vl-gateinst)

(def-vl-oprewrite vl-delaycontrol
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime)
              (vl-expr-oprewrite x.value warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-oprewrite vl-evatom
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-oprewrite-list vl-evatomlist :element vl-evatom)

(def-vl-oprewrite vl-eventcontrol
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime)
              (vl-evatomlist-oprewrite x.atoms warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-oprewrite vl-repeateventcontrol
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime)
              (vl-expr-oprewrite x.expr warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-oprewrite x.ctrl warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-oprewrite vl-delayoreventcontrol
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-oprewrite x warnings))
          (:vl-eventcontrol (vl-eventcontrol-oprewrite x warnings))
          (otherwise        (vl-repeateventcontrol-oprewrite x warnings))))

(def-vl-oprewrite vl-maybe-delayoreventcontrol
  :body (if x
            (vl-delayoreventcontrol-oprewrite x warnings)
          (mv (ok) nil)))

(defthm vl-maybe-delayoreventcontrol-oprewrite-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-oprewrite x warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-oprewrite
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-oprewrite.new-x))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-oprewrite.new-x)))))


(defines vl-stmt-oprewrite

  (define vl-stmt-oprewrite
    ((x        vl-stmt-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv (ok) x))
            (:vl-assignstmt
             (b* (((vl-assignstmt x) x)
                  ((mv warnings lvalue) (vl-expr-oprewrite x.lvalue warnings))
                  ((mv warnings expr)   (vl-expr-oprewrite x.expr warnings))
                  ((mv warnings ctrl)   (vl-maybe-delayoreventcontrol-oprewrite x.ctrl warnings)))
               (mv warnings (change-vl-assignstmt x
                                                  :lvalue lvalue
                                                  :expr expr
                                                  :ctrl ctrl))))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv warnings lvalue) (vl-expr-oprewrite x.lvalue warnings)))
               (mv warnings (change-vl-deassignstmt x :lvalue lvalue))))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv warnings id)   (vl-expr-oprewrite x.id warnings))
                  ((mv warnings args) (vl-exprlist-oprewrite x.args warnings)))
               (mv warnings (change-vl-enablestmt x
                                                  :id id
                                                  :args args))))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv warnings id) (vl-expr-oprewrite x.id warnings)))
               (mv warnings (change-vl-disablestmt x :id id))))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x)
                  ((mv warnings val)
                   (if x.val
                       (vl-expr-oprewrite x.val warnings)
                     (mv warnings x.val))))
               (mv (ok) (change-vl-returnstmt x :val val))))
            (:vl-eventtriggerstmt
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv warnings id) (vl-expr-oprewrite x.id warnings)))
               (mv warnings (change-vl-eventtriggerstmt x :id id))))
            (otherwise
             (progn$ (impossible)
                     (mv warnings x)))))
         ((mv warnings exprs) (vl-exprlist-oprewrite (vl-compoundstmt->exprs x) warnings))
         ((mv warnings stmts) (vl-stmtlist-oprewrite (vl-compoundstmt->stmts x) warnings))
         ((mv warnings ctrl)  (vl-maybe-delayoreventcontrol-oprewrite (vl-compoundstmt->ctrl x) warnings)))
      (mv warnings
          (change-vl-compoundstmt x
                                  :exprs exprs
                                  :stmts stmts
                                  :ctrl ctrl))))
  (define vl-stmtlist-oprewrite
    ((x        vl-stmtlist-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (implies (vl-stmtlist-p x)
                                         (vl-stmtlist-p new-x))
                                (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car) (vl-stmt-oprewrite (car x) warnings))
         ((mv warnings cdr) (vl-stmtlist-oprewrite (cdr x) warnings)))
      (mv warnings (cons car cdr))))

  ///
  (verify-guards vl-stmt-oprewrite)
  (deffixequiv-mutual vl-stmt-oprewrite))

(def-vl-oprewrite vl-always
  :body
  (b* (((vl-always x) x)
       ((mv warnings stmt) (vl-stmt-oprewrite x.stmt warnings)))
    (mv warnings (change-vl-always x :stmt stmt))))

(def-vl-oprewrite-list vl-alwayslist :element vl-always)

(def-vl-oprewrite vl-initial
  :body
  (b* (((vl-initial x) x)
       ((mv warnings stmt) (vl-stmt-oprewrite x.stmt warnings)))
    (mv warnings (change-vl-initial x :stmt stmt))))

(def-vl-oprewrite-list vl-initiallist :element vl-initial)


(define vl-module-oprewrite ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
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

(defprojection vl-modulelist-oprewrite ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-oprewrite x))

(define vl-design-oprewrite
  :short "Top-level @(see oprewrite) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-oprewrite x.mods)))
    (clear-memoize-table 'vl-expr-strip)
    (change-vl-design x :mods new-mods)))
