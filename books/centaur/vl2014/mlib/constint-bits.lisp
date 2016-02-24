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
(include-book "welltyped")
(local (include-book "../util/arithmetic"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

;; The code here is styled after vl-msb-bitslice-constint, but whereas that
;; code produces new expressions, here we just produce a bit list.



(define vl-constint-lsb-bits-aux
  :parents (vl-constint->msb-bits)
  ((len   natp)
   (value natp))
  :returns (lsb-bits vl-bitlist-p)
  :verbosep t
  :measure (nfix len)
  (b* (((when (zp len))
        nil)
       (bit             (if (logbitp 0 (lnfix value))
                            :vl-1val
                          :vl-0val)))
    (cons bit
          (vl-constint-lsb-bits-aux (1- len) (ash (lnfix value) -1))))
  ///
  (defthm true-listp-of-vl-constint-lsb-bits-aux
    (true-listp (vl-constint-lsb-bits-aux len value))
    :rule-classes :type-prescription)
  (defthm len-of-vl-constint-lsb-bits-aux
    (equal (len (vl-constint-lsb-bits-aux len value))
           (nfix len))))


(define vl-constint-msb-bits-aux
  :parents (vl-constint->msb-bits)
  :short "Accumulate lsb's into acc, which produces an MSB-ordered list."
  ((len natp)
   (value natp)
   acc)
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (nfix len)
  :enabled t
  (mbe :logic
       (revappend (vl-constint-lsb-bits-aux len value) acc)
       :exec
       (b* (((when (zp len))
             acc)
            (bit              (if (logbitp 0 value)
                                  :vl-1val
                                :vl-0val)))
         (vl-constint-msb-bits-aux (1- len)
                                   (ash (lnfix value) -1)
                                   (cons bit acc))))
    :prepwork
    ((local (in-theory (enable vl-constint-lsb-bits-aux)))))


(define vl-constint->msb-bits
  :parents (vl-constint-p)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>
@(see vl-constint-p) atom into MSB-ordered @(see vl-bitlist-p)."

  ((x vl-expr-p))
  :guard (and (vl-atom-p x)
              (vl-atom-welltyped-p x)
              (vl-fast-constint-p (vl-atom->guts x)))
  :returns (bits vl-bitlist-p)

  :long "<p>We require that @('X') is a well-typed constant integer expression,
i.e., our @(see expression-sizing) transform should have already been run.
Note that the \"propagation step\" of expression sizing should have already
handled any sign/zero extensions, so we assume here that the atom's
@('finalwidth') is already correct and that no extensions are necessary.</p>"

  :prepwork
  ((local (in-theory (enable vl-atom-welltyped-p))))

  (vl-constint-msb-bits-aux (vl-atom->finalwidth x)
                            (vl-constint->value (vl-atom->guts x))
                            nil)
  ///
  (defthm true-listp-of-vl-constint->msb-bits
    (true-listp (vl-constint->msb-bits x))
    :rule-classes :type-prescription)
  (defthm len-of-vl-constint->msb-bits
    (equal (len (vl-constint->msb-bits x))
           (nfix (vl-atom->finalwidth x)))))


(local
 (assert! (equal (vl-constint->msb-bits
                  (make-vl-atom :guts (make-vl-constint :origwidth 5
                                                        :origtype :vl-signed
                                                        :value 7)
                                :finalwidth 5
                                :finaltype :vl-signed))
                 (list :vl-0val
                       :vl-0val
                       :vl-1val
                       :vl-1val
                       :vl-1val))))


(local
 (assert! (equal (vl-constint->msb-bits
                  (make-vl-atom :guts (make-vl-constint :origwidth 5
                                                        :origtype :vl-unsigned
                                                        :value 15)
                                :finalwidth 5
                                :finaltype :vl-unsigned))
                 (list :vl-0val
                       :vl-1val
                       :vl-1val
                       :vl-1val
                       :vl-1val))))

(define vl-msb-bits->maybe-nat-val ((x vl-bitlist-p) (val-acc natp))
  :returns (val maybe-natp :rule-classes :type-prescription)
  (b* ((val-acc (lnfix val-acc))
       ((when (atom x)) val-acc)
       (bit1 (vl-bit-fix (car x)))
       (val-acc (case bit1
                  (:vl-1val (logior 1 (ash val-acc 1)))
                  (:vl-0val (ash val-acc 1))
                  (otherwise nil)))
       ((unless val-acc) nil))
    (vl-msb-bits->maybe-nat-val (cdr x) val-acc))
  ///

  (assert! (equal (vl-msb-bits->maybe-nat-val '(:vl-1val :vl-0val) 0) 2))

  (local (defun my-induct (n msb-bits value)
           (if (atom msb-bits)
               (list n msb-bits value)
             (my-induct (+ 1 n)
                        (cdr msb-bits)
                        (let ((bit1 (vl-bit-fix (car msb-bits))))
                          (if (eq bit1 :vl-1val)
                              (logior 1 (ash value 1))
                            (ash value 1)))))))

  (local (defthm unsigned-byte-p-implies-natp-n
           (implies (unsigned-byte-p n value)
                    (natp n))
           :rule-classes :forward-chaining))

  (defthm unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-general
    (implies (unsigned-byte-p n value)
             (equal (unsigned-byte-p (+ n (len msb-bits))
                                     (vl-msb-bits->maybe-nat-val msb-bits value))
                    (natp (vl-msb-bits->maybe-nat-val msb-bits value))))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :do-not-induct t
            :induct (my-induct n msb-bits value)
            :expand ((vl-msb-bits->maybe-nat-val msb-bits value))
            :in-theory (e/d (acl2::ihsext-recursive-redefs
                             acl2::unsigned-byte-p**)
                            (unsigned-byte-p)))))

  (defthm unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-zero
    (equal (unsigned-byte-p (len msb-bits) (vl-msb-bits->maybe-nat-val msb-bits 0))
           (natp (vl-msb-bits->maybe-nat-val msb-bits 0)))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-general
                                vl-msb-bits->maybe-nat-val
                                unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-general
                   (value 0) (n 0))))))

  (defthm upper-bound-of-vl-msb-bits->maybe-nat-val-zero
    (implies (vl-msb-bits->maybe-nat-val msb-bits 0)
             (< (vl-msb-bits->maybe-nat-val msb-bits 0)
                (expt 2 (len msb-bits))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (disable unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-zero
                                       unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-general
                                       vl-msb-bits->maybe-nat-val
                                       unsigned-byte-p)
            :use ((:instance unsigned-byte-p-of-vl-msb-bits->maybe-nat-val-zero))))))



