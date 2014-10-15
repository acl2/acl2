; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "expt")
(include-book "floor")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(local (in-theory (enable definition-of-bitwise-shl
                          definition-of-bitwise-shr)))


;; One option for reasoning about shifting operations is to just remove them
;; entirely by nonrecursively redefining them in terms of floor, *, and expt.
;; To do this, just enable the following theorems.

(defthmd bitwise-shl-as-expt
  (equal (bitwise-shl a n)
         (* (expt 2 n) a))
  :hints(("Goal" :in-theory (enable definition-of-expt))))

;; BOZO prove me
;; (defthmd bitwise-shr-as-expt
;;    (equal (bitwise-shr a n)
;;           (floor a (expt 2 n)))
;;    :hints(("Goal" :in-theory (enable definition-of-expt))))



;; Otherwise, you can leave the functions in and reason about them directly.

(defthm natp-of-bitwise-shl
  (equal (natp (bitwise-shl a n))
         t))

(defthm bitwise-shl-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (bitwise-shl a n)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm bitwise-shl-when-not-natp-right-cheap
  (implies (not (natp n))
           (equal (bitwise-shl a n)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm |(bitwise-shl 0 n)|
  (equal (bitwise-shl 0 n)
         0))

(defthm |(bitwise-shl a 0)|
  (equal (bitwise-shl a 0)
         (nfix a)))

(defthm |(bitwise-shl (nfix a) n)|
  (equal (bitwise-shl (nfix a) n)
         (bitwise-shl a n)))

(defthm |(bitwise-shl a (nfix n))|
  (equal (bitwise-shl a (nfix n))
         (bitwise-shl a n)))

(defthm bitwise-shl-of-bitwise-shl
  (equal (bitwise-shl (bitwise-shl a n) m)
         (bitwise-shl a (+ n m)))
  :hints(("Goal" :in-theory (enable bitwise-shl-as-expt))))

(defthm |(= a (bitwise-shl a n))|
  (equal (equal a (bitwise-shl a n))
         (if (zp a)
             (natp a)
           (zp n)))
  :hints(("Goal" :in-theory (enable bitwise-shl-as-expt))))




(defthm natp-of-bitwise-shr
  (equal (natp (bitwise-shr a n))
         t))

(defthm bitwise-shr-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (bitwise-shr a n)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm bitwise-shr-when-not-natp-right-cheap
  (implies (not (natp n))
           (equal (bitwise-shr a n)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm |(bitwise-shr 0 n)|
  (equal (bitwise-shr 0 n)
         0))

(defthm |(bitwise-shr a 0)|
  (equal (bitwise-shr a 0)
         (nfix a)))

(defthm |(bitwise-shr (nfix a) n)|
  (equal (bitwise-shr (nfix a) n)
         (bitwise-shr a n)))

(defthm |(bitwise-shr a (nfix n))|
  (equal (bitwise-shr a (nfix n))
         (bitwise-shr a n)))

(defthm |(< (bitwise-shr a n) a)|
  (equal (< (bitwise-shr a n) a)
         (and (not (zp a))
              (not (zp n))))
  :hints(("Goal"
          :in-theory (enable definition-of-bitwise-shr)
          :induct (dec-induction n))))