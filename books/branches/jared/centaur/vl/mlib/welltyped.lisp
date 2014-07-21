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
(include-book "expr-tools")
(include-book "expr-building")
(include-book "range-tools")
(include-book "hid-tools")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (enable tag-reasoning)))

(defsection welltyped
  :parents (mlib vl-expr-p expression-sizing)
  :short "Expressions whose sizes and types are sensible."

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
that the width of @('foo') itself is non-zero.</p>")

(local (xdoc::set-default-parents welltyped))

(define vl-atom-welltyped-p
  :short "@(call vl-atom-welltyped-p) determines if an atomic expression is
well-typed."
 ((x vl-expr-p))
 :returns (welltyped-p booleanp :rule-classes :type-prescription)
 :guard (vl-atom-p x)
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

(define vl-hidexpr-welltyped-p ((x vl-expr-p))
  :guard (not (vl-atom-p x))
  (b* (((vl-nonatom x) x)
       (width (vl-hid-width x)))
    (and (eq x.finaltype :vl-unsigned)
         width
         (eql x.finalwidth width))))

(defines vl-expr-welltyped-p

  (define vl-expr-welltyped-p ((x vl-expr-p))
    :measure (vl-expr-count x)
    :returns (welltyped-p booleanp :rule-classes :type-prescription)
    (b* (((when (vl-fast-atom-p x))
          (vl-atom-welltyped-p x))
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

  (define vl-exprlist-welltyped-p ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    :returns (welltyped-p booleanp :rule-classes :type-prescription)
    (or (atom x)
        (and (vl-expr-welltyped-p (car x))
             (vl-exprlist-welltyped-p (cdr x)))))

  ///
  (deflist vl-exprlist-welltyped-p (x)
    (vl-expr-welltyped-p x)
    :guard (vl-exprlist-p x)
    :already-definedp t)

  (deffixequiv-mutual vl-expr-welltyped-p))

(defthm vl-expr-welltyped-p-of-vl-make-bitselect
  (implies (force (vl-expr-welltyped-p expr))
           (vl-expr-welltyped-p (vl-make-bitselect expr n)))
  :hints(("Goal" :in-theory (enable vl-make-bitselect
                                    vl-make-index
                                    vl-atom-welltyped-p
                                    vl-expr-welltyped-p)
          :expand ((:free (args atts finalwidth finaltype)
                    (vl-expr-welltyped-p
                     (make-vl-nonatom :op :vl-bitselect
                                      :args args
                                      :atts atts
                                      :finalwidth finalwidth
                                      :finaltype finaltype)))))))

(defthm vl-exprlist-welltyped-p-of-vl-make-list-of-bitselects
  (implies (force (vl-expr-welltyped-p expr))
           (vl-exprlist-welltyped-p (vl-make-list-of-bitselects expr low high)))
  :hints(("Goal" :in-theory (enable vl-make-list-of-bitselects))))

(defthm vl-expr-welltyped-p-of-vl-idexpr
  (implies (and (vl-exprtype-p finaltype)
                (posp finalwidth))
           (vl-expr-welltyped-p (vl-idexpr name finalwidth finaltype)))
  :hints(("Goal" :in-theory (e/d (vl-idexpr
                                  vl-expr-welltyped-p
                                  vl-atom-welltyped-p)))))

