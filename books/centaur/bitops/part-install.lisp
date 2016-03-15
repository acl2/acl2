; Centaur Bitops Library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Shilpi Goel <shilpi@centtech.com>

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "part-select")

(local (include-book "ihs-extensions"))
(local (include-book "signed-byte-p"))
(local (in-theory (enable bitops::ash-1-removal)))

;; ======================================================================

(defsection bitops/part-install
  :parents (bitops)
  :short "This book provides a way to set a portion of an integer to
some value.")

;; ======================================================================

(defsection part-install
  :parents (bitops/part-install)
  :short "Set a portion of bits of an integer to some value"
  :long "<p>@('part-install') is a macro that is defined in terms of
  the function @('part-install-width-low').  This macro can be used to
  set a portion of bits from an integer to some value.</p>

<p>Usage:</p>
@({
     (part-install val x :low 8 :high  15)   ;; x[15:8] = val
     (part-install val x :low 8 :width  8)   ;; x[15:8] = val

})

@(def part-install-width-low)

@(def part-install)
"

  (local
   (defthm logmask-and-ash
     (implies (natp n)
              (equal (logmask n)
                     (+ -1 (ash 1 n))))))

  (defun-inline part-install-width-low (val x width low)
    (declare (xargs :guard (and (integerp x)
                                (integerp val)
                                (natp width)
                                (natp low))
                    :guard-hints (("Goal" :in-theory
                                   (disable
                                    logmask ash-1-removal)))))
    (mbe :logic
         (let* ((x     (ifix x))
                (val   (ifix val))
                (width (nfix width))
                (low   (nfix low))
                (val   (loghead width val))
                (mask  (logmask width)))
           (logior (logand x (lognot (ash mask low)))
                   (ash val low)))
         :exec
         (let* ((mask (1- (ash 1 width)))
                (val  (logand mask val)))
           (logior (logand x (lognot (ash mask low)))
                   (ash val low)))))

  ;; [Shilpi]: Would be nice to have a theorem like this...

  ;; (defthm part-install-width-low**
  ;;   (equal (part-install-width-low val x width low)
  ;;          (if (zp width)
  ;;              (ifix x)
  ;;            (part-install-width-low
  ;;             (logcdr val)
  ;;             (install-bit low (logcar val) x)
  ;;             (1- width)
  ;;             (1+ low))))
  ;;   :hints (("Goal" :in-theory (e/d (install-bit) (ash-1-removal)))))

  (defthm natp-part-install-width-low
    (implies (<= 0 x)
             (natp (part-install-width-low val x width low)))
    :rule-classes :type-prescription)

  (defcong int-equiv equal (part-install-width-low val x width low) 1)
  (defcong int-equiv equal (part-install-width-low val x width low) 2)
  (defcong nat-equiv equal (part-install-width-low val x width low) 3)
  (defcong nat-equiv equal (part-install-width-low val x width low) 4)

  (defmacro part-install (val x &key low high width)
    (cond ((and high width)
           (er hard? 'part-install "Can't use :high and :width together."))
          ((and low high (integerp low) (integerp high))
           `(part-install-width-low ,val ,x ,(+ 1 high (- low)) ,low))
          ((and low high)
           `(part-install-width-low ,val ,x (+ 1 ,high (- ,low)) ,low))
          ((and low width)
           `(part-install-width-low ,val ,x ,width ,low))
          (t
           (er hard? 'part-install
               "Need either :low and :width, or :low and :high."))))

  (defthm unsigned-byte-p-=-n-of-part-install-width-low
    (implies (and (unsigned-byte-p n x)
                  (<= (+ width low) n)
                  (natp n)
                  (natp low)
                  (natp width))
             (unsigned-byte-p n (part-install-width-low val x width low)))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p)))))

  (defthm unsigned-byte-p->-n-of-part-install-width-low
    (implies (and (unsigned-byte-p n x)
                  (< n (+ width low))
                  (natp low)
                  (natp width))
             (unsigned-byte-p
              (+ low width)
              (part-install-width-low val x width low)))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p)))))

  )

;; ======================================================================

(defsection part-select-and-part-install
  :parents (bitops/part-install bitops/part-select)
  :short "Interactions between @('part-select') and @('part-install')"

  (local
   (encapsulate
    ()
    (local (include-book "arithmetic-5/top" :dir :system))

    (defthm loghead-b-of-lognot-ash-a-where-a->=-b
      (implies (and (natp a)
                    (natp b)
                    (integerp x)
                    (<= b a))
               (equal (loghead b (lognot (ash x a)))
                      (1- (ash 1 b))))
      :hints (("Goal" :in-theory (e/d (loghead lognot) ()))))

    ))

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (local
   (defthm loghead-with-zero-or-negative-size-=-0
     (implies (<= n 0)
              (equal (loghead n x) 0))
     :hints (("Goal" :in-theory (e/d (loghead**) ())))))

  (local
   (defthm lognot-of-logmask
     (implies (natp width)
              (equal (lognot (logmask width))
                     (- (ash 1 width))))
     :hints (("Goal" :in-theory (e/d (ifix lognot expt) ())))))

  (local
   (defthm logcdr-minus-logcons-0-n
     (implies (integerp n)
              (equal (logcdr (- (logcons 0 n)))
                     (- n)))
     :hints (("Goal" :in-theory (e/d (logcdr logcons floor) ())))))

  (local
   (defthm loghead-lognot-and-logmask
     (implies (natp width)
              (equal (loghead width (lognot (logmask width))) 0))
     :hints (("Goal" :in-theory
              (e/d* (ihsext-recursive-redefs ihsext-inductions)
                    (logmask ash-1-removal))))))

  (defthm part-select-and-part-install-same
    (implies (natp width)
             (equal (part-select-width-low
                     (part-install-width-low val x width low)
                     width low)
                    (loghead width val)))
    :hints (("Goal" :in-theory (disable
                                logmask lognot-of-logmask
                                ash-1-removal logand-with-negated-bitmask))))

  (defthm logtail-a-of-logmask-b-where-a->=-b
    (implies (and (natp a)
                  (natp b)
                  (integerp x)
                  (<= b a))
             (equal (logtail a (logmask b))
                    0))
    :hints (("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                      ihsext-inductions logcar logcdr)
                                     (ash-1-removal)))))

  (defthm part-select-and-part-install-completely-different-1
    (implies (and (<= (+ low-i width-i) low-s)
                  (natp low-s)
                  (natp width-i)
                  (natp low-i))
             (equal (part-select-width-low
                     (part-install-width-low val x width-i low-i)
                     width-s low-s)
                    (part-select-width-low x width-s low-s)))
    :hints (("Goal" :in-theory (e/d () (ash-1-removal logmask)))))

  (local
   (defthm loghead-b-of-shift-by-a-where-a->=-b
     (implies (and (natp a)
                   (natp b)
                   (<= b a))
              (equal (loghead b (ash x a))
                     0))
     :hints (("Goal" :in-theory (e/d () (loghead-of-ash))
              :use ((:instance loghead-of-ash
                               (n b)
                               (x x)
                               (m a)))))))


  (defthm part-select-and-part-install-completely-different-2
    (implies (and (<= (+ low-s width-s) low-i)
                  (natp width-s)
                  (natp low-s)
                  (natp low-i))
             (equal (part-select-width-low
                     (part-install-width-low val x width-i low-i)
                     width-s low-s)
                    (part-select-width-low x width-s low-s)))
    :hints (("Goal" :in-theory (e/d () (ash-1-removal logmask)))))

  ;; [Shilpi]: Prove theorems about over-lapping bit portions of
  ;; select and install?

  )


;; ======================================================================
