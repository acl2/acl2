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
(include-book "constint-bits")
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (std::add-default-post-define-hook :fix))


(defxdoc caremask
  :parents (mlib)
  :short "Functions for computing bitmasks for, e.g., casez/casezx statements
and wildcard equality operators.")

(local (xdoc::set-default-parents caremask))

(define vl-intliteral-msb-bits
  :short "Try to explode a match-expression into a @(see vl-bitlist-p)."

  ((x vl-expr-p
      "A match expression in a @('casex') or @('casez') statement, e.g.,
       typically this is a weirdint with some wildcard bits, such as
       @('4'b10??')."))
  :guard (vl-expr-welltyped-p x)
  :returns
  (mv (okp      booleanp     :rule-classes :type-prescription)
      (msb-bits vl-bitlist-p))

  :long "<p>For now we just support simple weirdints and constints.  We could
probably easily extend this to arbitrary concatenations of weirdints and
constints, but that's probably overkill.</p>"

  (b* (((unless (vl-fast-atom-p x))
        ;; We only support weirdints and constints for now.
        (mv nil nil))
       (guts (vl-atom->guts x))
       ((when (vl-fast-weirdint-p guts))
        (mv t (vl-weirdint->bits guts)))
       ((unless (vl-constint-p guts))
        (mv nil nil)))
    (mv t (vl-constint->msb-bits x)))

  :prepwork
  ((local (in-theory (enable vl-expr-welltyped-p
                             vl-expr->finalwidth
                             vl-atom-welltyped-p))))
  ///
  (defthm len-of-vl-intliteral-msb-bits
    (b* (((mv okp msb-bits) (vl-intliteral-msb-bits x)))
      (implies (and okp
                    (vl-expr-welltyped-p x))
               (equal (len msb-bits)
                      (vl-expr->finalwidth x))))
    :hints(("Goal" :in-theory (enable tag-reasoning))))

  (defthm consp-of-vl-intliteral-msb-bits
    (b* (((mv okp msb-bits) (vl-intliteral-msb-bits x)))
      (implies (and okp
                    (vl-expr-welltyped-p x))
               (equal (consp msb-bits)
                      (posp (vl-expr->finalwidth x)))))
    :hints(("Goal" :use len-of-vl-intliteral-msb-bits
            :in-theory (e/d ()
                            (len-of-vl-intliteral-msb-bits
                             vl-expr-welltyped-p
                             vl-intliteral-msb-bits))))))

(define vl-msb-bits-to-intliteral ((x vl-bitlist-p) (type vl-exprtype-p))
  :short "Puts a list of bits into a constint or weirdint atom, as appropriate.
Assumes the finalwidth should be the length of the bitlist."
  :guard (consp x) ;; b/c widths need to be positive
  :returns (lit vl-expr-p)
  :prepwork ((local (defthm posp-of-len
                      (equal (posp (len x))
                             (consp x)))))
  (b* ((x (mbe :logic (if (consp x) x '(:vl-0val))
               :exec x))
       (natval (vl-msb-bits->maybe-nat-val x 0))
       (type (vl-exprtype-fix type))
       ((when natval)
        (make-vl-atom :guts (make-vl-constint :value natval
                                              :origwidth (len x)
                                              :origtype type
                                              :wasunsized nil)
                      :finalwidth (len x)
                      :finaltype type)))
    (make-vl-atom :guts (make-vl-weirdint :bits x
                                          :origwidth (len x)
                                          :origtype type
                                          :wasunsized nil)
                  :finalwidth (len x)
                  :finaltype type))
  ///
  (defthm vl-expr-welltyped-p-of-vl-msb-bits-to-intliteral
    (vl-expr-welltyped-p (vl-msb-bits-to-intliteral x type))
    :hints(("Goal" :in-theory (enable vl-expr-welltyped-p
                                      vl-atom-welltyped-p
                                      tag-reasoning))))

  (defthm vl-expr->finalwidth-of-vl-msb-bits-to-intliteral
    (equal (vl-expr->finalwidth (vl-msb-bits-to-intliteral x type))
           (pos-fix (len x))))

  (defthm vl-expr->finaltype-of-vl-msb-bits-to-intliteral
    (equal (vl-expr->finaltype (vl-msb-bits-to-intliteral x type))
           (vl-exprtype-fix type))))

(defmacro vl-msb-bits-to-zx-care-mask (msb-bits value)
  `(vl-msb-bits-to-care-mask ,msb-bits '(:vl-0val :vl-1val) ,value))

(defmacro vl-msb-bits-to-z-care-mask (msb-bits value)
  `(vl-msb-bits-to-care-mask ,msb-bits '(:vl-0val :vl-1val :vl-xval) ,value))


(define vl-msb-bits-to-care-mask
  :short "Construct a bit-mask that captures the non-wild bits from a casex
pattern or the right-hand side of a @('==?') or @('!=?') expression."
  ((msb-bits vl-bitlist-p "MSB-ordered bits from the RHS.")
   (care-bits vl-bitlist-p "Set of bit values that are cares; usually {1,0} or {1,0,X}.")
   (value    natp         "Value we're constructing, zero to begin with."))
  :guard (true-listp care-bits)
  :returns (care-mask natp :rule-classes :type-prescription)
  (b* ((value (lnfix value))
       ((when (atom msb-bits))
        value)
       (bit1  (vl-bit-fix (car msb-bits)))
       (value (if (member-eq bit1 (vl-bitlist-fix care-bits))
                  (logior 1 (ash value 1))
                (ash value 1))))
    (vl-msb-bits-to-care-mask (cdr msb-bits) care-bits value))
  ///
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-zval) 0) #b0))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-1val) 0) #b1))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-zval :vl-zval) 0) #b00))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-zval :vl-1val) 0) #b01))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-1val :vl-zval) 0) #b10))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-1val :vl-1val) 0) #b11))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-1val :vl-zval :vl-0val :vl-1val :vl-xval) 0) #b10110))
  (assert! (equal (vl-msb-bits-to-zx-care-mask '(:vl-zval :vl-zval :vl-1val :vl-zval) 0) #b0010))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-zval) 0) #b0))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-1val) 0) #b1))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-zval :vl-zval) 0) #b00))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-zval :vl-1val) 0) #b01))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-1val :vl-zval) 0) #b10))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-1val :vl-1val) 0) #b11))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-1val :vl-zval :vl-0val :vl-1val :vl-xval) 0) #b10111))
  (assert! (equal (vl-msb-bits-to-z-care-mask '(:vl-zval :vl-zval :vl-1val :vl-zval) 0) #b0010))
  (local (defun my-induct (n msb-bits care-bits value)
           (if (atom msb-bits)
               (list n msb-bits value)
             (my-induct (+ 1 n)
                        (cdr msb-bits)
                        care-bits
                        (let ((bit1 (vl-bit-fix (car msb-bits))))
                          (if (member bit1 (vl-bitlist-fix care-bits))
                              (logior 1 (ash (nfix value) 1))
                            (ash (nfix value) 1)))))))

  (local (defthm unsigned-byte-p-implies-natp-n
           (implies (unsigned-byte-p n x)
                    (natp n))
           :rule-classes :forward-chaining))

  (defthm unsigned-byte-p-of-vl-msb-bits-to-care-mask-general
    (implies (unsigned-byte-p n value)
             (unsigned-byte-p (+ n (len msb-bits))
                              (vl-msb-bits-to-care-mask msb-bits cares value)))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :do-not-induct t
            :induct (my-induct n msb-bits cares value)
            :expand ((vl-msb-bits-to-care-mask msb-bits cares value))
            :in-theory (e/d (acl2::ihsext-recursive-redefs
                             acl2::unsigned-byte-p**
                             len)
                            (unsigned-byte-p)))))

  (defthm unsigned-byte-p-of-vl-msb-bits-to-care-mask-zero
    (unsigned-byte-p (len msb-bits) (vl-msb-bits-to-care-mask msb-bits cares 0))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p-of-vl-msb-bits-to-care-mask-general
                                vl-msb-bits-to-care-mask
                                unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-msb-bits-to-care-mask-general
                   (value 0) (n 0))))))

  (defthm upper-bound-of-vl-msb-bits-to-care-mask-zero
    (< (vl-msb-bits-to-care-mask msb-bits cares 0)
       (expt 2 (len msb-bits)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable unsigned-byte-p-of-vl-msb-bits-to-care-mask-zero
                                       unsigned-byte-p-of-vl-msb-bits-to-care-mask-general
                                       vl-msb-bits-to-care-mask
                                       unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-msb-bits-to-care-mask-zero))))))


(defmacro vl-msb-bits-zap-dontcares-zx (msb-bits)
  `(vl-msb-bits-zap-dontcares ,msb-bits '(:vl-0val :vl-1val)))

(defmacro vl-msb-bits-zap-dontcares-z (msb-bits)
  `(vl-msb-bits-zap-dontcares ,msb-bits '(:vl-0val :vl-1val :vl-xval)))

(define vl-msb-bits-zap-dontcares
  :short "Zero out the don't-care bits from the right-hand side of a @('==?') or
  @('!=?') expression."
  :long "<p>Note: If there is ever a case where Z is one of the care bits,
think about whether this does the right thing.  Specifically: it is not the
case that if Z is among the care bits, then this function produces the same
bitlist value as @('msb-bits & caremask'), because a Z among the msb-bits won't
be fixed to an X.</p>"
  ((msb-bits  vl-bitlist-p "MSB-ordered bits from the RHS.")
   (care-bits vl-bitlist-p "Set of bit values that are cares; usually {1,0} or {1,0,X}."))
  :guard (true-listp care-bits)
  :returns (new-bitlist vl-bitlist-p)
  (b* (((when (atom msb-bits))
        nil)
       (bit1  (vl-bit-fix (car msb-bits)))
       (value (if (member-eq bit1 (vl-bitlist-fix care-bits))
                  bit1
                :vl-0val)))
    (cons value (vl-msb-bits-zap-dontcares (cdr msb-bits) care-bits)))
  ///
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-zval)) '(:vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-xval)) '(:vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-0val)) '(:vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-1val)) '(:vl-1val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-zval :vl-zval)) '(:vl-0val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-zval :vl-1val)) '(:vl-0val :vl-1val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-1val :vl-zval)) '(:vl-1val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-1val :vl-1val)) '(:vl-1val :vl-1val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-zval :vl-zval)) '(:vl-0val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-zval :vl-0val)) '(:vl-0val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-0val :vl-zval)) '(:vl-0val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-0val :vl-0val)) '(:vl-0val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-1val :vl-zval :vl-0val :vl-1val :vl-xval))
                                                '(:vl-1val :vl-0val :vl-0val :vl-1val :vl-0val)))
  (assert! (equal (vl-msb-bits-zap-dontcares-zx '(:vl-zval :vl-zval :vl-1val :vl-zval))
                                                '(:vl-0val :vl-0val :vl-1val :vl-0val)))


  (defthm len-of-vl-msb-bits-zap-dontcares
    (equal (len (vl-msb-bits-zap-dontcares msb-bits cares))
           (len msb-bits)))

  (defthm vl-msb-bits-zap-dontcares-under-iff
    (iff (vl-msb-bits-zap-dontcares msb-bits cares)
         (consp msb-bits))))


