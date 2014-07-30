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
(include-book "dividesp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defthm |(< a 2) when not 1|
  (implies (not (equal a 1))
           (equal (< a 2)
                  (zp a)))
  :hints(("Goal" :use ((:instance squeeze-law-three (a 1) (b a))))))

;; (defthm |(< n 2) when non-zp and not 1|
;;   (implies (and (not (zp n))
;;                 (not (equal n 1)))
;;            (equal (< n 2)
;;                   nil))
;;   :hints(("Goal" :use ((:instance squeeze-law-three (a 1) (b n))))))


(defund aux-smallest-prime-factor (i n)
  ;; Returns the smallest factor of n which is greater than i.  In degenerate
  ;; cases where i > n, we just return n.
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n))))

  (if (<= n i)
      (nfix n)
    (if (dividesp i n)
        (nfix i)
      (aux-smallest-prime-factor (+ 1 i) n))))

(defund smallest-prime-factor (n)
  (declare (xargs :guard (and (natp n)
                              (not (zp n))
                              (not (equal n 1)))))
  (if (or (zp n)
          (equal n 1))
      nil
    (aux-smallest-prime-factor 2 n)))

(defthm natp-of-aux-smallest-prime-factor
  (equal (natp (aux-smallest-prime-factor i n))
         t)
  :hints(("Goal" :in-theory (enable aux-smallest-prime-factor))))

(defthm natp-of-smallest-prime-factor
  (implies (force (and (not (zp n))
                       (not (equal n 1))))
           (equal (natp (smallest-prime-factor n))
                  t))
  :hints(("Goal" :in-theory (enable smallest-prime-factor))))

(defthmd lemma-for-dividesp-when-no-aux-smallest-prime-factor
  (implies (and (equal (nfix d) (nfix i))
                (syntaxp (ACL2::term-order d i)))
           (equal (dividesp i n)
                  (dividesp d n)))
  :hints(("Goal"
          :in-theory (disable dividesp-of-nfix-left)
          :use ((:instance dividesp-of-nfix-left
                           (a d) (b n))
                (:instance dividesp-of-nfix-left
                           (a i) (b n))))))

(defthmd dividesp-when-no-aux-smallest-prime-factor
  (implies (and (equal (aux-smallest-prime-factor i n) n)
                (<= i d)
                (< d n))
           (equal (dividesp d n)
                  nil))
  :hints(("Goal"
          :induct (aux-smallest-prime-factor i n)
          :in-theory (enable aux-smallest-prime-factor
                             lemma-for-dividesp-when-no-aux-smallest-prime-factor))))

(defthmd dividesp-when-smallest-prime-factor-is-n
  (implies (and (not (zp n))
                (not (equal n 1))
                (equal (smallest-prime-factor n) n))
           (equal (dividesp d n)
                  (or (equal d 1)
                      (equal d n))))
  :hints(("Goal"
          :in-theory (enable smallest-prime-factor)
          :use ((:instance dividesp-when-no-aux-smallest-prime-factor
                           (i 2))))))



(defund primep (n)
  (declare (xargs :guard (natp n)))
  (and (not (zp n))
       (not (equal n 1))
       (not (equal (smallest-prime-factor n) n))))

(defthm booleanp-of-primep
  (equal (booleanp (primep n))
         t)
  :hints(("Goal" :in-theory (enable primep))))

#|


(i-am-here)

(defthm dividesp-when-primep
  (implies (primep n)
           (equal (dividesp d n)
                  (or (equal d 1)
                      (equal d n))))
  :hints(("Goal"
          :in-theory (enable primep)
          :use ((:instance dividesp-when-smallest-prime-factor-is-n)))))










(defund aux-primep (i n)
  ;; This is an inefficient primality check via trial division.  We check if n
  ;; has any divisors in [2, ..., i].
  (declare (xargs :guard (and (natp i)
                              (natp n))
                  :measure (nfix i)))
  (or (zp i)
      (equal i 1)
      (and (not (dividesp i n))
           (aux-primep (- i 1) n))))

(defund primep (n)
  ;; We return true if n is a prime number in the true mathematical sense.  That
  ;; is, [2, 3, 5, 7, ...] are primes, but 0 and 1 are not.
  (declare (xargs :guard (natp n)))
  (and (not (zp n))
       (not (equal n 1))
       (aux-primep (- n 1) n)))

(defthm booleanp-of-aux-primep
  (equal (booleanp (aux-primep i n))
         t)
  :hints(("Goal"
          :induct (dec-induction i)
          :expand (aux-primep i n))))

(defthm booleanp-of-primep
  (equal (booleanp (primep n))
         t)
  :hints(("Goal" :in-theory (enable primep))))

(defthmd dividesp-when-in-aux-primep-range
  (implies (and (aux-primep i n)
                (< 1 d)
                (<= d i))
           (equal (dividesp d n)
                  nil))
  :hints(("Goal"
          :induct (dec-induction i)
          :expand ((aux-primep i n)
                   (aux-primep d n)))))

(defthm dividesp-when-primep
  (implies (primep n)
           (equal (dividesp d n)
                  (or (equal d 1)
                      (equal d n))))
  :hints(("Goal"
          :in-theory (enable primep)
          :use ((:instance dividesp-when-in-aux-primep-range
                           (i (- n 1)))))))


(defthm primep-of-smallest-prime-factor
  (implies (force (and (not (zp n))
                       (not (equal n 1))))
           (equal (primep (smallest-prime-factor n))
                  t))
  :hints(("Goal" :in-theory (enable smallest-prime-factor))))


(smallest-prime-factor 3)
(smallest-prime-factor 17)


(defun factor (n)
  (if (primep n)
      nil


|#