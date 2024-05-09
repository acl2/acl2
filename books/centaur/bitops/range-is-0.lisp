; Bitops library
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "BITOPS")

(include-book "std/bitsets/bignum-extract" :dir :system)

(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "equal-by-logbitp"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (disable unsigned-byte-p)))

; Added by Matt K. 2/2/2024, in analogy to a similar addition already made to
; equal-by-logbitp.lisp:
(local (include-book "std/system/non-parallel-book" :dir :system))
(local (non-parallel-book)) ; probably need not be local

(local (defthmd loghead-decomp
         (implies (<= (nfix m) (nfix n))
                  (iff (equal 0 (loghead n x))
                       (and (equal 0 (loghead m x))
                            (equal 0 (loghead (- (nfix n) (nfix m))
                                              (logtail m x))))))
         :hints ((bitops::logbitp-reasoning :prune-examples nil))))


(define range-is-0-rec ((slice-idx natp)
                        (top-bit natp)
                        (x integerp))
  :guard (<= (* 32 (lnfix slice-idx)) (lnfix top-bit))
  :measure (nfix (- (nfix top-bit) (* 32 (nfix slice-idx))))
  :returns (is-0)
  ;; :guard-debug t
  (b* (((unless (mbt (<= (* 32 (nfix slice-idx)) (nfix top-bit))))
        t)
       ((when (<= (lnfix top-bit) (* 32 (+ 1 (lnfix slice-idx)))))
        (eql 0 (the (unsigned-byte 32)
                    (loghead (the (integer 0 32)
                                  (- (lnfix top-bit) (* 32 (nfix slice-idx))))
                             (the (unsigned-byte 32)
                                  (bitsets::bignum-extract x slice-idx)))))))
    (and (eql 0 (the (unsigned-byte 32)
                     (bitsets::bignum-extract x slice-idx)))
         (range-is-0-rec (1+ (lnfix slice-idx)) top-bit x)))
  ///
  (local (defthmd loghead-equal-0-when-loghead-of-minus-32
           (implies (< 32 (nfix n))
                    (iff (equal 0 (loghead n (logtail m x)))
                         (and (equal 0 (loghead 32 (logtail m x)))
                              (equal 0 (loghead (+ -32 (nfix n)) (logtail (+ 32 (nfix m)) x))))))
           :hints (("goal" :use ((:instance loghead-decomp
                                  (x (logtail m x))
                                  (m 32)))))))

  (local (defthm loghead-of-zp
           (implies (zp n)
                    (Equal (loghead n x) 0))
           :hints(("Goal" :in-theory (enable bitops::loghead**)))))

  (defretd range-is-0-rec-in-terms-of-logtail-of-loghead
    (iff is-0
         (equal 0 (logtail (* 32 (nfix slice-idx)) (loghead top-bit x))))
    :hints(("Goal" :in-theory (enable bitsets::bignum-extract
                                      loghead-equal-0-when-loghead-of-minus-32)))))

(define range-is-0 ((lsb natp)
                    (width natp)
                    (x integerp))
  :prepwork ((local (defthm lte-31-when-unsigned-byte-p
                      (implies (unsigned-byte-p 5 x)
                               (<= x 31))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p)))))
             (local (defthm lt-2^32-when-unsigned-byte-p
                      (implies (unsigned-byte-p 32 x)
                               (< x #ux1_0000_0000))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p)))))
             (local (defthm nfix->-x
                      (implies (natp x)
                               (equal (> (nfix y) x)
                                      (and (natp y) (> y x))))
                      :hints(("Goal" :in-theory (enable nfix)))))
             (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
             (local (defthmd loghead-plus-logtail
                      (equal (+ (loghead 5 x) (* 32 (logtail 5 x)))
                             (ifix x))
                      :hints(("Goal" :in-theory (enable loghead logtail)))))
             (local (defthm loghead-5-<=-31
                      (<= (loghead 5 x) 31)
                      :rule-classes :linear)))
  :guard-hints (("goal" :in-theory (enable ;; bitsets::bignum-extract
                                           ;; range-is-0-rec-in-terms-of-logtail-of-loghead
                                           ))
                (and stable-under-simplificationp
                     '(:use ((:instance loghead-plus-logtail
                              (x lsb))
                             ;; (:instance loghead-decomp
                             ;;  (x (logtail lsb x))
                             ;;  (n width)
                             ;;  (m (+ 32 (- (loghead 5 lsb)))))
                             ))))
  :ruler-extenders :lambdas
  (b* ((lsb-slice-idx (logtail 5 (lnfix lsb)))
       (lsb-slice-lowbit (loghead 5 (lnfix lsb)))
       (lsb-slice (the (unsigned-byte 32) (bitsets::bignum-extract x lsb-slice-idx)))
       (lsb-slice-tail (the (unsigned-byte 32)
                            (logtail (the (integer 0 31) lsb-slice-lowbit)
                                     (the (unsigned-byte 32) lsb-slice))))
       (no-rec (<= (+ lsb-slice-lowbit (lnfix width)) 32))
       (lsb-slice-segment (if no-rec
                              (loghead width (the (unsigned-byte 32) lsb-slice-tail))
                            lsb-slice-tail)))
    (and (eql (the (unsigned-byte 32) lsb-slice-segment) 0)
         (or no-rec
             (range-is-0-rec  (+ 1 lsb-slice-idx)
                              (+ (lnfix lsb) (lnfix width))
                              x))))
  ///
  (defthm range-is-0-in-terms-of-loghead-of-logtail
    (equal (range-is-0 lsb width x)
           (equal 0 (loghead width (logtail lsb x))))
    :hints (("goal" :in-theory (enable bitsets::bignum-extract
                                           range-is-0-rec-in-terms-of-logtail-of-loghead
                                           ))
                (and stable-under-simplificationp
                     '(:use ((:instance loghead-plus-logtail
                              (x (nfix lsb)))
                             (:instance loghead-decomp
                              (x (logtail lsb x))
                              (n width)
                              (m (+ 32 (- (loghead 5 (nfix lsb))))))))))))

