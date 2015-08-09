; Copyright David Rager 2006

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

; This is a library used to compute diffie helman keys.  We prove that the
; diffie helman computation produces the same key for two different parties.
; Thanks go to Robert Krug (rkrug@cs.utexas.edu) for figuring out how to use
; the arithmetic libraries to make the proofs go through.

(in-package "CRYPTO")
(set-verify-guards-eagerness 2)

(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(local (set-default-hints '((acl2::nonlinearp-default-hint
                             acl2::stable-under-simplificationp
                             acl2::hist acl2::pspv))))

(defun compute-public-dh-value (g exponent-value b)
  (declare (xargs :guard (and (integerp g)
                              (natp exponent-value)
                              (integerp b)
                              (not (equal b 0)))))
  ;; notice that we require the exponent-value to be passed in
  (mod (expt g exponent-value) b))

#|
(defthm expt-returns-integer->=1
  (implies (and (integerp base)
                (<= 1 base)
                (integerp exponent)
                (<= 1 exponent))
           (and (integerp (expt base exponent))
                (<= 1 (expt base exponent)))))

(defthm mod-returns-integer->=0
  (implies (and (integerp base)
                (<= 1 base)
                (integerp modulo)
                (<= 1 modulo))
           (and (integerp (mod base modulo))
                (<= 0 (mod base modulo)))))
|#

(defthm compute-public-dh-value-makes-integer->=0
  (implies (and (integerp g)
                (<= 0 exponent-value)
                (integerp b)
                (<= 1 b))
           (and (integerp (CRYPTO::compute-public-dh-value g exponent-value b))
                (<= 0 (CRYPTO::compute-public-dh-value g exponent-value b)))))

(defun compute-dh-key (a-public-exponentiation a-private-value b)
  (declare (xargs :guard (and (integerp a-public-exponentiation)
                              (natp a-private-value)
                              (integerp b)
                              (not (equal b 0)))))
  (mod (expt a-public-exponentiation a-private-value) b))

(defthm compute-dh-key-returns-integer->=0
  (implies (and (integerp g)
                (<= 0 public-exponent-value)
                (integerp b)
                (<= 1 b))
           (and (integerp (compute-dh-key g public-exponent-value b))
                (<= 0 (compute-dh-key g public-exponent-value b)))))

(defthm compute-public-dh-value-returns-integer
  (implies (and (integerp g)
                (natp exponent-value)
                (integerp b)
                (not (equal b 0)))
           (integerp (compute-public-dh-value g exponent-value b))))

(local (defthm mod-*
         (implies (and (integerp x)
                       (< 0 x)
                       (integerp y)
                       (< 0 y)
                       (integerp b)
                       (< 0 b))
                  (equal (mod (* x y) b)
                         (mod (* (mod x b) (mod y b)) b)))))

(local (defun ind (x)
         (if (and (integerp x)
                  (< 0 x))
             (ind (1- x))
           t)))

(local (acl2::scatter-exponents))

(local (defthm proper-induction-thm
         (implies (and (and (integerp y) (< 1 y))
                       (implies (and (integerp x)
                                     (< 0 x)
                                     (integerp y)
                                     (< 1 y)
                                     (integerp b)
                                     (< 0 b))
                                (equal (mod (expt (mod x b) y) b)
                                       (mod (expt x y) b))))
                  (implies (and (integerp x)
                                (< 0 x)
                                (integerp y)
                                (< 1 y)
                                (integerp b)
                                (< 0 b))
                           (equal (mod (expt (mod x b) (+ 1 y)) b)
                                  (mod (expt x (+ 1 y)) b))))))

(local (defthm mod-expt-thm
         (implies (and (integerp x)
                       (< 0 x)
                       (integerp y)
                       (< 0 y)
                       (integerp b)
                       (< 0 b))
                  (equal (mod (expt (mod x b) y) b)
                         (mod (expt x y) b)))
         :hints (("Goal" :induct (ind y))
                 ("Subgoal *1/" :use (:instance proper-induction-thm
                                                (y (+ -1 y)))))))

(local (acl2::gather-exponents))

(local (defthm mod-exponentiation-equivalent
         (implies (and (integerp g)
                       (<= 1 g)
                       (integerp b)
                       (<= 1 b)
                       (integerp x)
                       (<= 1 x)
                       (integerp y)
                       (<= 1 y))
                  (equal (mod (expt (mod (expt g x) b)
                                    y)
                              b)
                         (mod (expt (mod (expt g y) b)
                                    x)
                              b)))))



; This theorem is useful for showing that two actors derive the same key if
; they use each other's public exponential values
(defthm dh-computation-produces-the-same-key
  (implies (and (force (integerp g))
                (force (<= 1 g))
                (force (integerp b))
                (force (<= 1 b))
                (force (integerp x-exponent))
                (force (<= 1 x-exponent))
                (force (integerp y-exponent))
                (force (<= 1 y-exponent)))
           (equal (compute-dh-key (compute-public-dh-value g x-exponent b)
                                  y-exponent
                                  b)
                  (compute-dh-key (compute-public-dh-value g y-exponent b)
                                  x-exponent
                                  b))))

; i is the intruder
(defun session-key-requires-one-part-of-key (g b x-exponent y-exponent i-exponent)

  ;; we set the guards to nil to ensure that this function never executes and
  ;; is only used in the logical reasoning of a proof
  (declare (xargs :guard nil
                  :verify-guards nil))

  (implies (and (force (integerp g))
                (force (<= 1 g))
                (force (integerp b))
                (force (<= 1 b))
                (force (integerp x-exponent))
                (force (<= 1 x-exponent))
                (force (integerp y-exponent))
                (force (<= 1 y-exponent))
                (force (integerp i-exponent))
                (force (<= 1 i-exponent))
                (not (equal i-exponent x-exponent))
                (not (equal i-exponent y-exponent)))

           (let ((x-public-value (compute-public-dh-value g x-exponent b))
                 (y-public-value (compute-public-dh-value g y-exponent b))
                 (session-key
                  (compute-dh-key (compute-public-dh-value g x-exponent b)
                                  y-exponent
                                  b)))
             (and (not (equal (compute-dh-key x-public-value i-exponent b)
                              session-key))
                  (not (equal (compute-dh-key y-public-value i-exponent b)
                              session-key))))))

(in-theory (disable compute-public-dh-value compute-dh-key))