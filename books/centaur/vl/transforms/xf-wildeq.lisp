; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "always/caseelim")
(include-book "../mlib/delta")
(include-book "occform/util")
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (defthm natp-when-unsigned-byte-p-width
         (implies (unsigned-byte-p n x)
                  (natp n))))

(local (defthm natp-when-unsigned-byte-p-value
         (implies (unsigned-byte-p n x)
                  (natp x))))


(defsection wildelim
  :parents (transforms)
  :short "Elimination of wildcard equality operators, @('==?') and @('!=?')."

  :long "<p>See SystemVerilog 2012, Section 11.4.6 Wildcard Equality Operators.
In brief:</p>

<ul>

<li>@('a ==? b') determines whether a equals b, except that X and Z values in b
act as wildcards.</li>

<li>@('a !=? b') determines whether a does not equal b, except that X and Z
values in b act as wildcards.</li>

</ul>

<p>These operators produce 1-bit, self-determined results.  If @('a') and
@('b') are of unequal bit lengths, they are extended in the same manner as for
the logical equality/inequality operators.  The result is @('X') if the @('a')
operand contains any @('X') or @('Z') bit that is not being compared with a
wildcard in the @('b') operand.</p>

<p>These operators are basically fine and sensible when @('b') is a constant
integer literal like @('4'b0101') or a weird integer like @('4'b01xx').
However, in the more general case where @('b') is some expression that is
computed at runtime, these operators are fundamentally broken because they do
not treat @('X') bits within @('b') as unknowns.  This poses problems for
back-end tools like @(see esim) that expect operators to behave
monotonically.</p>

<p>VL attempts to support simple uses of @('==?') and @('!=?'), i.e., when the
right-hand argument is a constant or weird integer literal.  In this case, we
can compute the mask of bits that we care about, and then consider the equality
of the masked expressions.</p>

<p>Ordering notes.  We expect that this transform should be run after sizing.
Typically you will want to run it after sizing but before, e.g., truncating or
splitting expressions.</p>")



(local (xdoc::set-default-parents vl-expr-wildelim))

(define vl-wildeq-msb-bits-to-care-mask
  :short "Construct a bit-mask that captures the non-wild bits from the
right-hand side of a @('==?') or @('!=?') expression."
  ((msb-bits vl-bitlist-p "MSB-ordered bits from the RHS.")
   (value    natp         "Value we're constructing, zero to begin with."))
  :returns (care-mask natp :rule-classes :type-prescription)
  (b* ((value (lnfix value))
       ((when (atom msb-bits))
        value)
       (bit1  (vl-bit-fix (car msb-bits)))
       (value (if (or (eq bit1 :vl-0val)
                      (eq bit1 :vl-1val))
                  (logior 1 (ash value 1))
                (ash value 1))))
    (vl-wildeq-msb-bits-to-care-mask (cdr msb-bits) value))
  ///
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-zval) 0) #b0))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-1val) 0) #b1))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-zval :vl-zval) 0) #b00))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-zval :vl-1val) 0) #b01))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-1val :vl-zval) 0) #b10))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-1val :vl-1val) 0) #b11))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-1val :vl-zval :vl-0val :vl-1val :vl-xval) 0) #b10110))
  (assert! (equal (vl-wildeq-msb-bits-to-care-mask '(:vl-zval :vl-zval :vl-1val :vl-zval) 0) #b0010))

  (local (defun my-induct (n msb-bits value)
           (if (atom msb-bits)
               (list n msb-bits value)
             (my-induct (+ 1 n)
                        (cdr msb-bits)
                        (let ((bit1 (vl-bit-fix (car msb-bits))))
                          (if (or (eq bit1 :vl-0val)
                                  (eq bit1 :vl-1val))
                              (logior 1 (ash value 1))
                            (ash value 1)))))))

  (defthm unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-general
    (implies (unsigned-byte-p n value)
             (unsigned-byte-p (+ n (len msb-bits))
                              (vl-wildeq-msb-bits-to-care-mask msb-bits value)))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :do-not-induct t
            :induct (my-induct n msb-bits value)
            :in-theory (e/d (acl2::ihsext-recursive-redefs
                             acl2::unsigned-byte-p**)
                            (unsigned-byte-p)))))

  (defthm unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-zero
    (unsigned-byte-p (len msb-bits) (vl-wildeq-msb-bits-to-care-mask msb-bits 0))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-general
                                vl-wildeq-msb-bits-to-care-mask
                                unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-general
                   (value 0) (n 0))))))

  (defthm upper-bound-of-vl-wildeq-msb-bits-to-care-mask-zero
    (< (vl-wildeq-msb-bits-to-care-mask msb-bits 0)
       (expt 2 (len msb-bits)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-zero
                                       unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-general
                                       vl-wildeq-msb-bits-to-care-mask
                                       unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-wildeq-msb-bits-to-care-mask-zero))))))

(define vl-wildeq-msb-bits-zap
  :short "Zero out the wild bits from the right-hand side of a @('==?') or
  @('!=?') expression."
  ((msb-bits vl-bitlist-p "MSB-ordered bits from the RHS.")
   (value    natp         "Value we're constructing, zero to begin with."))
  :returns (new-value natp :rule-classes :type-prescription)
  (b* ((value (lnfix value))
       ((when (atom msb-bits))
        value)
       (bit1  (vl-bit-fix (car msb-bits)))
       (value (if (eq bit1 :vl-1val)
                  (logior 1 (ash value 1))
                ;; Just replace any other bit with 0.
                (ash value 1))))
    (vl-wildeq-msb-bits-zap (cdr msb-bits) value))
  ///
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-zval) 0) #b0))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-xval) 0) #b0))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-0val) 0) #b0))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-1val) 0) #b1))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-zval :vl-zval) 0) #b00))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-zval :vl-1val) 0) #b01))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-1val :vl-zval) 0) #b10))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-1val :vl-1val) 0) #b11))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-zval :vl-zval) 0) #b00))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-zval :vl-0val) 0) #b00))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-0val :vl-zval) 0) #b00))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-0val :vl-0val) 0) #b00))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-1val :vl-zval :vl-0val :vl-1val :vl-xval) 0) #b10010))
  (assert! (equal (vl-wildeq-msb-bits-zap '(:vl-zval :vl-zval :vl-1val :vl-zval) 0) #b0010))

  (local (defun my-induct (n msb-bits value)
           (if (atom msb-bits)
               (list n msb-bits value)
             (my-induct (+ 1 n)
                        (cdr msb-bits)
                        (let ((bit1 (vl-bit-fix (car msb-bits))))
                          (if (eq bit1 :vl-1val)
                              (logior 1 (ash value 1))
                            (ash value 1)))))))

  (defthm unsigned-byte-p-of-vl-wildeq-msb-bits-zap-general
    (implies (unsigned-byte-p n value)
             (unsigned-byte-p (+ n (len msb-bits))
                              (vl-wildeq-msb-bits-zap msb-bits value)))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :do-not-induct t
            :induct (my-induct n msb-bits value)
            :in-theory (e/d (acl2::ihsext-recursive-redefs
                             acl2::unsigned-byte-p**)
                            (unsigned-byte-p)))))

  (defthm unsigned-byte-p-of-vl-wildeq-msb-bits-zap-zero
    (unsigned-byte-p (len msb-bits) (vl-wildeq-msb-bits-zap msb-bits 0))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p-of-vl-wildeq-msb-bits-zap-general
                                vl-wildeq-msb-bits-zap
                                unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-wildeq-msb-bits-zap-general
                   (value 0) (n 0))))))

  (defthm upper-bound-of-vl-wildeq-msb-bits-zap-zero
    (< (vl-wildeq-msb-bits-zap msb-bits 0)
       (expt 2 (len msb-bits)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable unsigned-byte-p-of-vl-wildeq-msb-bits-zap-zero
                                       unsigned-byte-p-of-vl-wildeq-msb-bits-zap-general
                                       vl-wildeq-msb-bits-zap
                                       unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-wildeq-msb-bits-zap-zero))))))


(define vl-wildeq-decompose-rhs
  :short "Compute the care mask and zapped right-hand side for an @('==?') or
          @('!=?') operator."
  ((rhs vl-expr-p))
  :guard (vl-expr-welltyped-p rhs)
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (care-mask (equal (vl-expr-p care-mask) (if okp t nil)))
               (zapped    (equal (vl-expr-p zapped)    (if okp t nil))))
  :verify-guards nil
  (b* (((mv okp msb-bits) (vl-casezx-match-bits rhs))
       ((unless okp)
        (mv nil nil nil))

       ;; Note that by len-of-vl-casezx-match-bits we know that the finalwidth
       ;; is exactly the length of msb-bits.
       (finalwidth (vl-expr->finalwidth rhs))
       (finaltype  (vl-expr->finaltype rhs))

       ((unless (posp finalwidth))
        ;; Zero bit long right-hand side: could possibly happen if someone
        ;; writes something like foo ==? {0{bar}}.  This seems crazy so let's
        ;; not try to support it.
        (mv nil nil nil))

       ((unless finaltype)
        ;; Not sure if this can even happen, but if somehow it does, then we
        ;; won't create properly signed expressions in vl-wildeq-rewrite-expr,
        ;; so fail.
        (mv nil nil nil))

       ;; Care mask computation.
       (cm-value (vl-wildeq-msb-bits-to-care-mask msb-bits 0))
       (cm-guts  (make-vl-constint :value cm-value
                                   :origwidth finalwidth
                                   :origtype finaltype))
       (cm-expr  (make-vl-atom :guts cm-guts
                               :finalwidth finalwidth
                               :finaltype finaltype))

       ;; Zapped value computation.
       (zap-value (vl-wildeq-msb-bits-zap msb-bits 0))
       (zap-guts  (make-vl-constint :value zap-value
                                    :origwidth finalwidth
                                    :origtype finaltype))
       (zap-expr  (make-vl-atom :guts zap-guts
                                :finalwidth finalwidth
                                :finaltype finaltype)))
    (mv t cm-expr zap-expr))
  ///
  (verify-guards vl-wildeq-decompose-rhs
    :hints(("Goal"
            :in-theory (disable upper-bound-of-vl-wildeq-msb-bits-to-care-mask-zero)
            :use ((:instance upper-bound-of-vl-wildeq-msb-bits-to-care-mask-zero
                   (msb-bits (mv-nth 1 (vl-casezx-match-bits rhs))))))))

  (local (in-theory (enable vl-expr-welltyped-p
                            vl-atom-welltyped-p)))

  (more-returns
   (care-mask (implies okp
                       (and (vl-expr-welltyped-p care-mask)
                            (equal (vl-expr->finalwidth care-mask)
                                   (vl-expr->finalwidth rhs))
                            (equal (vl-expr->finaltype care-mask)
                                   (vl-expr->finaltype rhs))))
              :hyp (vl-expr-welltyped-p rhs)
              :name vl-expr-welltyped-p-of-vl-wildeq-decompose-rhs.care-mask)
   (zapped    (implies okp
                       (and (vl-expr-welltyped-p zapped)
                            (equal (vl-expr->finalwidth zapped)
                                   (vl-expr->finalwidth rhs))
                            (equal (vl-expr->finaltype zapped)
                                   (vl-expr->finaltype rhs))))
              :hyp (vl-expr-welltyped-p rhs)
              :name vl-expr-welltyped-p-of-vl-wildeq-decompose-rhs.zapped)))


(define vl-wildeq-replacement-expr
  :short "Construct the expression to replace @('lhs ==? rhs')."

  ((lhs       vl-expr-p "Left hand side of some @('lhs ==? rhs') expression.")
   (care-mask vl-expr-p "Care mask computed for @('rhs'); see @(see vl-wildeq-decompose-rhs).")
   (zapped    vl-expr-p "Zapped version of @('rhs'); see @(see vl-wildeq-decompose-rhs).")
   (atts      vl-atts-p "Attributes for the new expression."))

  :guard (and (vl-expr-welltyped-p lhs)
              (vl-expr-welltyped-p care-mask)
              (vl-expr-welltyped-p zapped)
              (posp (vl-expr->finalwidth lhs))
              (equal (vl-expr->finalwidth care-mask) (vl-expr->finalwidth lhs))
              (equal (vl-expr->finalwidth zapped) (vl-expr->finalwidth lhs))
              (vl-expr->finaltype lhs)
              (equal (vl-expr->finaltype care-mask) (vl-expr->finaltype lhs))
              (equal (vl-expr->finaltype zapped) (vl-expr->finaltype lhs)))

  :returns (new-x vl-expr-p)

  :long "<p>LHS could be anything, but since X is well-typed we know that its
width is positive and that its signedness agrees with the signedness of RHS.
Moreover we constructed the care-mask and zap-expr in such a way that they also
agree on this width and signedness.  Hence, everything lines up perfectly and
we're ready to go.</p>

<p>In the ==? case, we want to make sure that LHS agrees with RHS
on all of the care bits, i.e., that</p>

@({
    (LHS & CARE-MASK) == (RHS & CARE-MASK)
})

<p>It is perhaps nicer to write @('RHS & CARE-MASK') as @('ZAPPED'), since that
is just a constant integer.  So this is just:</p>

@({
    (LHS & CARE-MASK) == ZAPPED
})

<p>Except that, per @(see oprewrite), we would rather write this as:</p>

@({
     & (  (LHS & CARE-MASK) ~^ ZAPPED )
})"

  (b* ((width      (vl-expr->finalwidth lhs))
       (type       (vl-expr->finaltype lhs))
       (masked-lhs (make-vl-nonatom :op :vl-binary-bitand
                                    :args (list lhs care-mask)
                                    :finalwidth width
                                    :finaltype type))
       (inner-iff  (make-vl-nonatom :op :vl-binary-xnor
                                    :args (list masked-lhs zapped)
                                    :finalwidth width
                                    :finaltype type)))
    (make-vl-nonatom :op :vl-unary-bitand
                     :args (list inner-iff)
                     :finalwidth 1
                     :finaltype :vl-unsigned
                     :atts atts))
  ///
  (more-returns
   (new-x vl-expr-welltyped-p
          :hyp :fguard
          :hints(("Goal" :in-theory (enable vl-expr-welltyped-p))))
   (new-x (and (equal (vl-expr->finalwidth new-x) 1)
               (equal (vl-expr->finaltype new-x) :vl-unsigned))
          :name vl-wildeq-replacement-expr-basics)))


(define vl-wildneq-replacement-expr
  :short "Construct the expression to replace @('lhs !=? rhs')."

  ((lhs       vl-expr-p "Left hand side of some @('lhs !=? rhs') expression.")
   (care-mask vl-expr-p "Care mask computed for @('rhs'); see @(see vl-wildeq-decompose-rhs).")
   (zapped    vl-expr-p "Zapped version of @('rhs'); see @(see vl-wildeq-decompose-rhs).")
   (atts      vl-atts-p "Attributes for the new expression."))

  :guard (and (vl-expr-welltyped-p lhs)
              (vl-expr-welltyped-p care-mask)
              (vl-expr-welltyped-p zapped)
              (posp (vl-expr->finalwidth lhs))
              (equal (vl-expr->finalwidth care-mask) (vl-expr->finalwidth lhs))
              (equal (vl-expr->finalwidth zapped) (vl-expr->finalwidth lhs))
              (vl-expr->finaltype lhs)
              (equal (vl-expr->finaltype care-mask) (vl-expr->finaltype lhs))
              (equal (vl-expr->finaltype zapped) (vl-expr->finaltype lhs)))

  :returns (new-x vl-expr-p)

  :long "<p>This is very much like @(see vl-wildeq-replacement-expr) except that we target
@('!=?') instead of @('==?').</p>

<p>Here we want to check whether</p>

@({
    (LHS & CARE-MASK) != ZAPPED
})

<p>But, per @(see oprewrite), we actually want to write:</p>

@({
    | (  (LHS & CARE-MASK) ^ ZAPPED )
})"

  (b* ((width      (vl-expr->finalwidth lhs))
       (type       (vl-expr->finaltype lhs))
       (masked-lhs (make-vl-nonatom :op :vl-binary-bitand
                                    :args (list lhs care-mask)
                                    :finalwidth width
                                    :finaltype type))
       (inner-xor  (make-vl-nonatom :op :vl-binary-xor
                                    :args (list masked-lhs zapped)
                                    :finalwidth width
                                    :finaltype type)))
    (make-vl-nonatom :op :vl-unary-bitor
                     :args (list inner-xor)
                     :finalwidth 1
                     :finaltype :vl-unsigned
                     :atts atts))
  ///
  (more-returns
   (new-x vl-expr-welltyped-p
          :hyp :fguard
          :hints(("Goal" :in-theory (enable vl-expr-welltyped-p))))
   (new-x (and (equal (vl-expr->finalwidth new-x) 1)
               (equal (vl-expr->finaltype new-x) :vl-unsigned))
          :name vl-wildneq-replacement-expr-basics)))


(define vl-wildeq-rewrite-main ((x        vl-expr-p)
                                (elem     vl-modelement-p)
                                (warnings vl-warninglist-p))
  :guard (and (not (vl-atom-p x))
              (or (eq (vl-nonatom->op x) :vl-binary-wildeq)
                  (eq (vl-nonatom->op x) :vl-binary-wildneq)))
  :returns (mv (new-warnings vl-warninglist-p)
               (new-x        vl-expr-p))
  :verify-guards nil
  (b* ((x    (vl-expr-fix x))
       (elem (vl-modelement-fix elem))

       ((unless (vl-expr-welltyped-p x))
        (mv (warn :type :vl-wildeq-fail
                  :msg "~a0: failing to simplify wildcard equality operator ~
                        because it is not well-typed: ~a1."
                  :args (list elem x))
            x))

       ((vl-nonatom x) x)
       ((list lhs rhs) x.args)
       ((mv okp care-mask zap-expr) (vl-wildeq-decompose-rhs rhs))

       ((unless okp)
        (mv (warn :type :vl-wildeq-fail
                  :msg  "~a0: right-hand side of wildcard equality operator ~
                         is too complex; we only support constants.  ~
                         Expression: ~a1."
                  :args (list elem x))
            x))

       (new-x (if (eq x.op :vl-binary-wildeq)
                  (vl-wildeq-replacement-expr lhs care-mask zap-expr x.atts)
                (vl-wildneq-replacement-expr lhs care-mask zap-expr x.atts))))

    (mv (ok) new-x))
  ///
  (verify-guards vl-wildeq-rewrite-main
    :hints(("Goal" :expand (vl-expr-welltyped-p x))))

  (local (defthm l0
           (implies (not (equal (vl-expr-kind x) :atom))
                    (equal (vl-nonatom->finalwidth x)
                           (vl-expr->finalwidth x)))
           :hints(("Goal" :in-theory (enable vl-expr->finalwidth)))))

  (local (defthm l1
           (implies (not (equal (vl-expr-kind x) :atom))
                    (equal (vl-nonatom->finaltype x)
                           (vl-expr->finaltype x)))
           :hints(("Goal" :in-theory (enable vl-expr->finaltype)))))

  (defthm vl-expr-welltyped-p-after-vl-wildeq-rewrite-main
    (implies (and (vl-expr-welltyped-p x)
                  (not (vl-atom-p x))
                  (or (eq (vl-nonatom->op x) :vl-binary-wildeq)
                      (eq (vl-nonatom->op x) :vl-binary-wildneq)))
             (b* (((mv ?warnings new-x) (vl-wildeq-rewrite-main x elem warnings)))
               (and (vl-expr-welltyped-p new-x)
                    (equal (vl-expr->finalwidth new-x)
                           (vl-expr->finalwidth x))
                    (equal (vl-expr->finaltype new-x)
                           (vl-expr->finaltype x)))))
    :hints(("Goal" :expand (vl-expr-welltyped-p x)))))



(defines vl-wildeq-rewrite-expr

  (define vl-wildeq-rewrite-expr
    :short "Eliminate @('==?') and @('!=?') operators from an expression."
    ((x        vl-expr-p       "Expression to process.")
     (elem     vl-modelement-p "Context for error messages.")
     (warnings vl-warninglist-p))
    :verify-guards nil
    :returns (mv (new-warnings vl-warninglist-p)
                 (new-x        vl-expr-p))
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((x (vl-expr-fix x))

         ((when (vl-fast-atom-p x))
          (mv (ok) x))

         ((vl-nonatom x) x)
         ((when (or (eq x.op :vl-hid-dot)
                    (eq x.op :vl-index)))
          (mv (ok) x))

         ((mv warnings new-args)
          (vl-wildeq-rewrite-exprlist x.args elem warnings))
         (new-x (change-vl-nonatom x :args new-args))

         ((when (or (eq x.op :vl-binary-wildeq)
                    (eq x.op :vl-binary-wildneq)))
          (vl-wildeq-rewrite-main new-x elem warnings)))

      (mv warnings (change-vl-nonatom x :args new-args))))

  (define vl-wildeq-rewrite-exprlist
    :short "Eliminate @('==?') and @('!=?') operators from an expression list."
    ((x        vl-exprlist-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (vl-exprlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) x))
         ((mv warnings car) (vl-wildeq-rewrite-expr (car x) elem warnings))
         ((mv warnings cdr) (vl-wildeq-rewrite-exprlist (cdr x) elem warnings)))
      (mv warnings (cons car cdr))))

  ///
  (verify-guards vl-wildeq-rewrite-expr
    :hints(("goal" :expand (vl-expr-welltyped-p x))))

  (deffixequiv-mutual vl-wildeq-rewrite-expr)

  ;; I'm not going to try to extend the proof of well-typedness to cover the
  ;; mutual recursion, because that turns out to be pretty hard.  We do at
  ;; least show, above, that we preserve the types of the expressions that we
  ;; actually rewrite.

  (defthm vl-wildeq-rewrite-exprlist-when-atom
    (implies (atom x)
             (equal (vl-wildeq-rewrite-exprlist x elem warnings)
                    (mv (ok) x))))

  (defthm vl-wildeq-rewrite-exprlist-of-cons
    (equal (vl-wildeq-rewrite-exprlist (cons a x) elem warnings)
           (b* (((mv warnings car) (vl-wildeq-rewrite-expr a elem warnings))
                ((mv warnings cdr) (vl-wildeq-rewrite-exprlist x elem warnings)))
             (mv warnings (cons car cdr)))))

  (defthm len-of-vl-wildeq-rewrite-exprlist
    (equal (len (mv-nth 1 (vl-wildeq-rewrite-exprlist x elem warnings)))
           (len x)))

  (local (defthm l0
           (implies (and (member a (vl-exprlist-ops (vl-nonatom->args x)))
                         (not (vl-atom-p x)))
                    (member a (vl-expr-ops x)))
           :hints(("Goal" :in-theory (enable vl-expr-ops)))))

  (local (defthm l1
           (implies (and (equal a (vl-nonatom->op x))
                         (not (vl-atom-p x)))
                    (member a (vl-expr-ops x)))
           :hints(("Goal" :expand (vl-expr-ops x)))))

  (defthm-vl-wildeq-rewrite-expr-flag
    (defthm vl-wildeq-rewrite-expr-optimization
      (implies (not (vl-expr-has-ops '(:vl-binary-wildeq :vl-binary-wildneq) x))
               (equal (vl-wildeq-rewrite-expr x elem warnings)
                      (mv (ok) (vl-expr-fix x))))
      :flag :expr)
    (defthm vl-wildeq-rewrite-exprlist-optimization
      (implies (not (vl-exprlist-has-ops '(:vl-binary-wildeq :vl-binary-wildneq) x))
               (equal (vl-wildeq-rewrite-exprlist x elem warnings)
                      (mv (ok) (vl-exprlist-fix x))))
      :flag :list)
    :hints(("Goal"
            :expand ((vl-wildeq-rewrite-expr x elem warnings)
                     (vl-exprlist-ops x))
            :do-not '(generalize fertilize)))))

(define vl-expr-wildelim
  :parents (wildelim)
  :short "Top-level wrapper for eliminating @('==?') and @('!=?') from an
          expression.  Avoids reconsing when there are no @('==?') or @('!=?')
          operators."
  ((x        vl-expr-p)
   (elem     vl-modelement-p)
   (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (new-x vl-expr-p))
  :enabled t
  (mbe :logic
       (vl-wildeq-rewrite-expr x elem warnings)
       :exec
       (if (not (vl-expr-has-ops '(:vl-binary-wildeq :vl-binary-wildneq) x))
           (mv warnings x)
         (vl-wildeq-rewrite-expr x elem warnings))))





;; Normal thing to extend the wildelim rewrite across modules

(local (xdoc::set-default-parents vl-design-wildelim))

(defmacro def-vl-wildelim (name &key body takes-elem enabled inline)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn   (mksym name '-wildelim))
       (fix  (mksym name '-fix))
       (type (mksym name '-p)))
    `(define ,fn ((x      ,type)
                  ,@(and takes-elem '((elem vl-modelement-p)))
                  (warnings vl-warninglist-p))
       :short ,(cat "Eliminate @('==?') and @('!=?') operators throughout a @(see " (symbol-name type) ")")
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       :enabled ,enabled
       :inline ,inline
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-wildelim-list (name &key element takes-elem)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn      (mksym name    '-wildelim))
       (elem-fn (mksym element '-wildelim))
       (type    (mksym name    '-p))
       (formals (append '(x)
                        (if takes-elem '(elem) nil)
                        '(warnings))))
    `(define ,fn ((x      ,type)
                  ,@(and takes-elem '((elem vl-modelement-p)))
                  (warnings vl-warninglist-p))
       :returns (mv (warnings vl-warninglist-p)
                    (new-x    ,type))
       :short ,(cat "Eliminate @('==?') and @('!=?') operators throughout a @(see " (symbol-name type) ").")
       (b* (((when (atom x))
             (mv (ok) x))
            ((mv warnings car-prime) (,elem-fn . ,(subst '(car x) 'x formals)))
            ((mv warnings cdr-prime) (,fn . ,(subst '(cdr x) 'x formals))))
         (mv warnings (cons car-prime cdr-prime)))
       ///
       (defthm ,(mksym fn '-when-atom)
         (implies (atom x)
                  (equal (,fn . ,formals)
                         (mv (ok) x))))

       (defthm ,(mksym fn '-of-cons)
         (equal (,fn . ,(subst '(cons a x) 'x formals))
                (b* (((mv warnings car-prime) (,elem-fn . ,(subst 'a 'x formals)))
                     ((mv warnings cdr-prime) (,fn . ,formals)))
                  (mv warnings (cons car-prime cdr-prime)))))

       (defthm ,(mksym 'len-of- fn)
         (equal (len (mv-nth 1 (,fn . ,formals)))
                (len x))))))

(def-vl-wildelim vl-exprlist
  :takes-elem t
  :enabled t
  :body
  (mbe :logic
       (vl-wildeq-rewrite-exprlist x elem warnings)
       :exec
       ;; Optimization to avoid reconsing.  If there aren't any ==? or !=?
       ;; operators, don't do anything.
       (if (not (vl-exprlist-has-ops '(:vl-binary-wildeq :vl-binary-wildneq) x))
           (mv warnings x)
         (vl-wildeq-rewrite-exprlist x elem warnings))))

(def-vl-wildelim vl-maybe-expr
  :takes-elem t
  :inline t
  :body (if x
            (vl-expr-wildelim x elem warnings)
          (mv warnings nil)))

(def-vl-wildelim vl-range
  :takes-elem t
  :body (b* (((vl-range x) x)
             ((mv warnings msb-prime) (vl-expr-wildelim x.msb elem warnings))
             ((mv warnings lsb-prime) (vl-expr-wildelim x.lsb elem warnings))
             (x-prime  (change-vl-range x
                                        :msb msb-prime
                                        :lsb lsb-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim vl-maybe-range
  :takes-elem t
  :inline t
  :body (if x
            (vl-range-wildelim x elem warnings)
          (mv warnings nil)))

(def-vl-wildelim-list vl-rangelist
  :takes-elem t
  :element vl-range)

(def-vl-wildelim vl-packeddimension
  :takes-elem t
  :inline t
  :body
  (b* ((x (vl-packeddimension-fix x)))
    (if (eq x :vl-unsized-dimension)
        (mv warnings x)
      (vl-range-wildelim x elem warnings))))

(def-vl-wildelim vl-maybe-packeddimension
  :takes-elem t
  :inline t
  :body
  (if x
      (vl-packeddimension-wildelim x elem warnings)
    (mv warnings x)))

(def-vl-wildelim-list vl-packeddimensionlist
  :takes-elem t
  :element vl-packeddimension)

(def-vl-wildelim vl-enumbasetype
  :takes-elem t
  :body (b* (((vl-enumbasetype x) x)
             ((mv warnings dim)
              (vl-maybe-packeddimension-wildelim x.dim elem warnings)))
          (mv warnings (change-vl-enumbasetype x :dim dim))))

(def-vl-wildelim vl-enumitem
  :takes-elem t
  :body
  (b* (((vl-enumitem x) x)
       ((mv warnings new-range) (vl-maybe-range-wildelim x.range elem warnings))
       ((mv warnings new-value) (vl-maybe-expr-wildelim x.value elem warnings))
       (new-x    (change-vl-enumitem x
                                     :range new-range
                                     :value new-value)))
    (mv warnings new-x)))

(def-vl-wildelim-list vl-enumitemlist
  :takes-elem t
  :element vl-enumitem)


(defines vl-datatype-wildelim
  :verify-guards nil

  (define vl-datatype-wildelim ((x        vl-datatype-p)
                                (elem     vl-modelement-p)
                                (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      (:vl-coretype
       (b* (((mv warnings new-dims) (vl-packeddimensionlist-wildelim x.dims elem warnings))
            (new-x (change-vl-coretype x :dims new-dims)))
         (mv warnings new-x)))
      (:vl-struct
       (b* (((mv warnings new-members) (vl-structmemberlist-wildelim x.members elem warnings))
            ((mv warnings new-dims) (vl-packeddimensionlist-wildelim x.dims elem warnings))
            (new-x    (change-vl-struct x :members new-members :dims new-dims)))
         (mv warnings new-x)))
      (:vl-union
       (b* (((mv warnings new-members) (vl-structmemberlist-wildelim x.members elem warnings))
            ((mv warnings new-dims) (vl-packeddimensionlist-wildelim x.dims elem warnings))
            (new-x    (change-vl-union x :members new-members :dims new-dims)))
         (mv warnings new-x)))
      (:vl-enum
       (b* (((mv warnings new-basetype) (vl-enumbasetype-wildelim x.basetype elem warnings))
            ((mv warnings new-items) (vl-enumitemlist-wildelim x.items elem warnings))
            ((mv warnings new-dims) (vl-packeddimensionlist-wildelim x.dims elem warnings))
            (new-x    (change-vl-enum x
                                      :basetype new-basetype
                                      :items new-items
                                      :dims new-dims)))
         (mv warnings new-x)))
      (:vl-usertype
       (b* (((mv warnings new-kind) (vl-expr-wildelim x.kind elem warnings))
            ((mv warnings new-dims) (vl-packeddimensionlist-wildelim x.dims elem warnings))
            (new-x    (change-vl-usertype x :kind new-kind :dims new-dims)))
         (mv warnings new-x)))))

  (define vl-structmemberlist-wildelim ((x        vl-structmemberlist-p)
                                        (elem     vl-modelement-p)
                                        (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings new-car) (vl-structmember-wildelim (car x) elem warnings))
         ((mv warnings new-cdr) (vl-structmemberlist-wildelim (cdr x) elem warnings))
         (new-x    (cons new-car new-cdr)))
      (mv warnings new-x)))

  (define vl-structmember-wildelim ((x        vl-structmember-p)
                                    (elem     vl-modelement-p)
                                    (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-structmember-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x)
         ((mv warnings new-type) (vl-datatype-wildelim x.type elem warnings))
         ((mv warnings new-dims) (vl-packeddimensionlist-wildelim x.dims elem warnings))
         ((mv warnings new-rhs) (vl-maybe-expr-wildelim x.rhs elem warnings))
         (new-x    (change-vl-structmember x
                                           :type new-type
                                           :dims new-dims
                                           :rhs new-rhs)))
      (mv warnings new-x)))
  ///
  (verify-guards vl-datatype-wildelim)
  (deffixequiv-mutual vl-datatype-wildelim))

(def-vl-wildelim vl-gatedelay
  :takes-elem t
  :body (b* (((vl-gatedelay x) x)
             ((mv warnings rise-prime) (vl-expr-wildelim x.rise elem warnings))
             ((mv warnings fall-prime) (vl-expr-wildelim x.fall elem warnings))
             ((mv warnings high-prime) (vl-maybe-expr-wildelim x.high elem warnings))
             (x-prime  (change-vl-gatedelay x
                                            :rise rise-prime
                                            :fall fall-prime
                                            :high high-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim vl-maybe-gatedelay
  :takes-elem t
  :inline t
  :body (if x
            (vl-gatedelay-wildelim x elem warnings)
          (mv warnings x)))

(def-vl-wildelim vl-assign
  :body
  (b* (((vl-assign x) x)
       (elem x)
       ((mv warnings lhs-prime)   (vl-expr-wildelim x.lvalue elem warnings))
       ((mv warnings rhs-prime)   (vl-expr-wildelim x.expr elem warnings))
       ((mv warnings delay-prime) (vl-maybe-gatedelay-wildelim x.delay elem warnings))
       (x-prime
        (change-vl-assign x
                          :lvalue lhs-prime
                          :expr rhs-prime
                          :delay delay-prime)))
    (mv warnings x-prime)))

(def-vl-wildelim-list vl-assignlist :element vl-assign)


(def-vl-wildelim vl-plainarg
  :takes-elem t
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime) (vl-expr-wildelim x.expr elem warnings))
             (x-prime (change-vl-plainarg x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim-list vl-plainarglist
  :takes-elem t
  :element vl-plainarg)

(def-vl-wildelim vl-namedarg
  :takes-elem t
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime) (vl-expr-wildelim x.expr elem warnings))
             (x-prime (change-vl-namedarg x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim-list vl-namedarglist
  :takes-elem t
  :element vl-namedarg)

(def-vl-wildelim vl-arguments
  :takes-elem t
  :body
  (vl-arguments-case x
    :named
    (b* (((mv warnings args-prime) (vl-namedarglist-wildelim x.args elem warnings))
         (x-prime (change-vl-arguments-named x :args args-prime)))
      (mv warnings x-prime))
    :plain
    (b* (((mv warnings args-prime) (vl-plainarglist-wildelim x.args elem warnings))
         (x-prime (change-vl-arguments-plain x :args args-prime)))
      (mv warnings x-prime))))

(def-vl-wildelim vl-modinst
  :body
  (b* (((vl-modinst x) x)
       (elem x)
       ((mv warnings portargs-prime)  (vl-arguments-wildelim x.portargs elem warnings))
       ((mv warnings paramargs-prime) (vl-arguments-wildelim x.paramargs elem warnings))
       ((mv warnings range-prime)     (vl-maybe-range-wildelim x.range elem warnings))
       ((mv warnings delay-prime)     (vl-maybe-gatedelay-wildelim x.delay elem warnings))
       (x-prime (change-vl-modinst x
                                   :portargs portargs-prime
                                   :paramargs paramargs-prime
                                   :range range-prime
                                   :delay delay-prime)))
      (mv warnings x-prime)))

(def-vl-wildelim-list vl-modinstlist :element vl-modinst)

(def-vl-wildelim vl-gateinst
  :body
  (b* (((vl-gateinst x) x)
       (elem x)
       ((mv warnings args-prime) (vl-plainarglist-wildelim x.args elem warnings))
       ((mv warnings range-prime) (vl-maybe-range-wildelim x.range elem warnings))
       ((mv warnings delay-prime) (vl-maybe-gatedelay-wildelim x.delay elem warnings))
       (x-prime (change-vl-gateinst x
                                    :args args-prime
                                    :range range-prime
                                    :delay delay-prime)))
      (mv warnings x-prime)))

(def-vl-wildelim-list vl-gateinstlist :element vl-gateinst)


(def-vl-wildelim vl-port
  :body (b* (((vl-port x) x)
             (elem x)
             ((mv warnings expr-prime) (vl-maybe-expr-wildelim x.expr elem warnings))
             (x-prime (change-vl-port x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim-list vl-portlist :element vl-port)


; It doesn't necessarily make a lot of sense to size the expressions in
; declarations, but on the other hand it doesn't seem like it's a bad thing to
; do.

(def-vl-wildelim vl-portdecl
  :body (b* (((vl-portdecl x) x)
             (elem x)
             ((mv warnings range-prime) (vl-maybe-range-wildelim x.range elem warnings))
             (x-prime (change-vl-portdecl x :range range-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim-list vl-portdecllist :element vl-portdecl)

(def-vl-wildelim vl-netdecl
  :body
  (b* (((vl-netdecl x) x)
       (elem x)
       ((mv warnings range-prime)   (vl-maybe-range-wildelim x.range elem warnings))
       ((mv warnings arrdims-prime) (vl-rangelist-wildelim x.arrdims elem warnings))
       ((mv warnings delay-prime)   (vl-maybe-gatedelay-wildelim x.delay elem warnings))
       (x-prime  (change-vl-netdecl x
                                    :range range-prime
                                    :arrdims arrdims-prime
                                    :delay delay-prime)))
    (mv warnings x-prime)))

(def-vl-wildelim-list vl-netdecllist :element vl-netdecl)

(def-vl-wildelim vl-vardecl
  :body
  (b* (((vl-vardecl x) x)
       (elem x)
       ((mv warnings vartype-prime) (vl-datatype-wildelim x.vartype elem warnings))
       ((mv warnings dims-prime)    (vl-packeddimensionlist-wildelim x.dims elem warnings))
       ((mv warnings initval-prime) (vl-maybe-expr-wildelim x.initval elem warnings))
       (x-prime (change-vl-vardecl x
                                   :vartype vartype-prime
                                   :dims    dims-prime
                                   :initval initval-prime)))
    (mv warnings x-prime)))

(def-vl-wildelim-list vl-vardecllist :element vl-vardecl)

(def-vl-wildelim vl-paramdecl
  :body
  (b* (((vl-paramdecl x) x)
       (elem x)
       ((mv warnings expr-prime)    (vl-expr-wildelim x.expr elem warnings))
       ((mv warnings range-prime)   (vl-maybe-range-wildelim x.range elem warnings))
       (x-prime (change-vl-paramdecl x
                                     :expr  expr-prime
                                     :range range-prime)))
    (mv warnings x-prime)))

(def-vl-wildelim-list vl-paramdecllist :element vl-paramdecl)

(def-vl-wildelim vl-blockitem
  :body
  (let ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl (vl-vardecl-wildelim x warnings))
      (otherwise   (vl-paramdecl-wildelim x warnings)))))

(def-vl-wildelim-list vl-blockitemlist :element vl-blockitem)

(def-vl-wildelim vl-delaycontrol
  :takes-elem t
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime) (vl-expr-wildelim x.value elem warnings))
             (x-prime (change-vl-delaycontrol x :value value-prime)))
            (mv warnings x-prime)))

(def-vl-wildelim vl-evatom
  :takes-elem t
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime) (vl-expr-wildelim x.expr elem warnings))
             (x-prime (change-vl-evatom x :expr expr-prime)))
            (mv warnings x-prime)))

(def-vl-wildelim-list vl-evatomlist
  :takes-elem t
  :element vl-evatom)

(def-vl-wildelim vl-eventcontrol
  :takes-elem t
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime) (vl-evatomlist-wildelim x.atoms elem warnings))
             (x-prime (change-vl-eventcontrol x :atoms atoms-prime)))
          (mv warnings x-prime)))

(def-vl-wildelim vl-repeateventcontrol
  :takes-elem t
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime) (vl-expr-wildelim x.expr elem warnings))
             ((mv warnings ctrl-prime) (vl-eventcontrol-wildelim x.ctrl elem warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-wildelim vl-delayoreventcontrol
  :takes-elem t
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-wildelim x elem warnings))
          (:vl-eventcontrol (vl-eventcontrol-wildelim x elem warnings))
          (otherwise        (vl-repeateventcontrol-wildelim x elem warnings))))

(def-vl-wildelim vl-maybe-delayoreventcontrol
  :takes-elem t
  :inline t
  :body (if x
            (vl-delayoreventcontrol-wildelim x elem warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-wildelim-under-iff
  (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-wildelim x elem warnings))
       x)
  :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-wildelim))))

(defines vl-stmt-wildelim

  (define vl-stmt-wildelim
    ((x        vl-stmt-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    (b* ((x        (vl-stmt-fix x))
         (elem     (vl-modelement-fix elem))
         (warnings (vl-warninglist-fix warnings))

         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv warnings x))
            (:vl-assignstmt
             (b* (((vl-assignstmt x) x)
                  ((mv warnings lhs-prime) (vl-expr-wildelim x.lvalue elem warnings))
                  ((mv warnings rhs-prime) (vl-expr-wildelim x.expr elem warnings))
                  ((mv warnings ctrl-prime) (vl-maybe-delayoreventcontrol-wildelim x.ctrl elem warnings))
                  (x-prime (change-vl-assignstmt x
                                                 :lvalue lhs-prime
                                                 :expr rhs-prime
                                                 :ctrl ctrl-prime)))
               (mv warnings x-prime)))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv warnings lvalue-prime) (vl-expr-wildelim x.lvalue elem warnings))
                  (x-prime (change-vl-deassignstmt x :lvalue lvalue-prime)))
               (mv warnings x-prime)))
            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv warnings id-prime)   (vl-expr-wildelim x.id elem warnings))
                  ((mv warnings args-prime) (vl-exprlist-wildelim x.args elem warnings))
                  (x-prime (change-vl-enablestmt x
                                                 :id id-prime
                                                 :args args-prime)))
               (mv warnings x-prime)))
            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv warnings id-prime) (vl-expr-wildelim x.id elem warnings))
                  (x-prime (change-vl-disablestmt x :id id-prime)))
               (mv warnings x-prime)))
            (otherwise
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv warnings id-prime) (vl-expr-wildelim x.id elem warnings))
                  (x-prime (change-vl-eventtriggerstmt x :id id-prime)))
               (mv warnings x-prime)))))

         (x.exprs (vl-compoundstmt->exprs x))
         (x.stmts (vl-compoundstmt->stmts x))
         (x.ctrl  (vl-compoundstmt->ctrl x))
         (x.decls (vl-compoundstmt->decls x))
         ((mv warnings exprs-prime) (vl-exprlist-wildelim x.exprs elem warnings))
         ((mv warnings stmts-prime) (vl-stmtlist-wildelim x.stmts elem warnings))
         ((mv warnings ctrl-prime)  (vl-maybe-delayoreventcontrol-wildelim x.ctrl elem warnings))
         ((mv warnings decls-prime) (vl-blockitemlist-wildelim x.decls warnings))
         (x-prime (change-vl-compoundstmt x
                                          :exprs exprs-prime
                                          :stmts stmts-prime
                                          :ctrl ctrl-prime
                                          :decls decls-prime)))
      (mv warnings x-prime)))

  (define vl-stmtlist-wildelim
    ((x        vl-stmtlist-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :measure (vl-stmtlist-count x)
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    (and (vl-stmtlist-p new-x)
                                (equal (len new-x) (len x)))))
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime) (vl-stmt-wildelim (car x) elem warnings))
         ((mv warnings cdr-prime) (vl-stmtlist-wildelim (cdr x) elem warnings)))
      (mv warnings (cons car-prime cdr-prime))))
  ///
  (verify-guards vl-stmt-wildelim)
  (deffixequiv-mutual vl-stmt-wildelim))

(def-vl-wildelim vl-always
  :body (b* (((vl-always x) x)
             (elem x)
             ((mv warnings stmt-prime) (vl-stmt-wildelim x.stmt elem warnings))
             (x-prime (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-wildelim-list vl-alwayslist :element vl-always)


(def-vl-wildelim vl-initial
  :body (b* (((vl-initial x) x)
             (elem x)
             ((mv warnings stmt-prime)
              (vl-stmt-wildelim x.stmt elem warnings))
             (x-prime (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-wildelim-list vl-initiallist :element vl-initial)



(define vl-module-wildelim ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       ((vl-module x) x)
       (warnings  x.warnings)
       ((mv warnings assigns)    (vl-assignlist-wildelim    x.assigns    warnings))
       ((mv warnings modinsts)   (vl-modinstlist-wildelim   x.modinsts   warnings))
       ((mv warnings gateinsts)  (vl-gateinstlist-wildelim  x.gateinsts  warnings))
       ((mv warnings alwayses)   (vl-alwayslist-wildelim    x.alwayses   warnings))
       ((mv warnings initials)   (vl-initiallist-wildelim   x.initials   warnings))
       ((mv warnings ports)      (vl-portlist-wildelim      x.ports      warnings))
       ((mv warnings portdecls)  (vl-portdecllist-wildelim  x.portdecls  warnings))
       ((mv warnings paramdecls) (vl-paramdecllist-wildelim x.paramdecls warnings))
       ((mv warnings netdecls)   (vl-netdecllist-wildelim   x.netdecls   warnings))
       ((mv warnings vardecls)   (vl-vardecllist-wildelim   x.vardecls   warnings)))
    (change-vl-module x
                      :assigns assigns
                      :modinsts modinsts
                      :gateinsts gateinsts
                      :alwayses alwayses
                      :initials initials
                      :ports ports
                      :portdecls portdecls
                      :paramdecls paramdecls
                      :netdecls netdecls
                      :vardecls vardecls
                      :warnings warnings)))

(defprojection vl-modulelist-wildelim ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-wildelim x))

(define vl-design-wildelim
  :parents (wildelim)
  :short "Top-level @(see wildelim) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-wildelim x.mods))))

