; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")


;; This book contains functions for transforming integers (two's complement and
;; unsigned) into two- and four-valued bit-vectors, and theorems about those
;; functions.

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "ihs/math-lemmas" :dir :system))
(local (in-theory (disable floor)))


(defun int-to-v (x n)
  (declare (xargs :guard (and (integerp x) (natp n))))
  (if (zp n)
      nil
    (let ((rest (int-to-v (ash x -1) (1- n))))
      (cons (logbitp 0 x) rest))))

(defmacro nat-to-v (&rest args)
  (cons 'int-to-v args))

(add-macro-alias nat-to-v int-to-v)

(defun v-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (let ((rst (* 2 (v-to-nat (cdr a)))))
      (+ (if (car a) 1 0) rst))))

(defun v-to-int (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (if (atom (cdr a))
        (if (car a) -1 0)
      (let ((rest (* 2 (v-to-int (cdr a)))))
        (+ (if (car a) 1 0) rest)))))

(defun int-to-fv (x n)
  (declare (xargs :guard (and (integerp x) (natp n))))
  (if (zp n)
      nil
    (let ((rest (int-to-fv (ash x -1) (1- n))))
      (cons (if (logbitp 0 x) '(t . nil) '(nil . t)) rest))))

(defmacro nat-to-fv (&rest args)
  (cons 'int-to-fv args))

(add-macro-alias nat-to-fv int-to-fv)


(defun fv-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (let ((rest (fv-to-nat (cdr a))))
      (if (integerp rest)
          (cond ((equal (car a) '(t . nil)) (+ 1 (* 2 rest)))
                ((equal (car a) '(nil . t)) (* 2 rest))
                (t 'x))
        rest))))

(defun fv-to-int (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (if (atom (cdr a))
        (cond ((equal (car a) '(t . nil)) -1)
              ((equal (car a) '(nil . t)) 0)
              (t 'x))
      (let ((rest (fv-to-int (cdr a))))
        (if (integerp rest)
            (cond ((equal (car a) '(t . nil)) (+ 1 (* 2 rest)))
                  ((equal (car a) '(nil . t)) (* 2 rest))
                  (t 'x))
          rest)))))


; (allow-arith5-help)

(defthm consp-int-to-v
  (equal (consp (int-to-v n len))
         (not (zp len))))

(defthm len-int-to-v
  (equal (len (int-to-v n len))
         (nfix len)))

(defthm boolean-listp-int-to-v
  (boolean-listp (int-to-v x n)))

(defthm v-to-nat-type-rw
  (and (integerp (v-to-nat a))
       (natp (v-to-nat a))
       (<= 0 (v-to-nat a))))


(defthm v-to-nat-linear
  (and (<= 0 (v-to-nat a))
       (< (v-to-nat a) (expt 2 (len a))))
  :rule-classes ((:linear :trigger-terms ((v-to-nat a)))))


(defthm v-to-int-linear-1
  (<= (- (expt 2 (+ -1 (len a)))) (v-to-int a))
  :rule-classes ((:linear :trigger-terms ((v-to-int a)))))

(defthm v-to-int-linear-2
  (< (v-to-int a) (expt 2 (+ -1 (len a))))
  :hints (("goal" :induct (v-to-int a))
          (and stable-under-simplificationp
               '(:expand
                 ((expt 2 (len (cdr a)))))))
  :rule-classes ((:linear :trigger-terms ((v-to-int a)))))


(local
 (encapsulate nil
  (local (defthmd expt-2-positive-integer-is-even-1
           (implies (and (integerp exp)
                         (< 0 exp))
                    (integerp (* 1/2 (expt 2 exp))))))

  (defthm expt-2-positive-integer-is-even
    (implies (and (equal (expt 2 exp) (- n))
                  (integerp exp)
                  (< 0 exp)
                  (integerp n))
             (integerp (* 1/2 n)))
    :hints(("Goal" :use ((:instance expt-2-positive-integer-is-even-1)))))))


(defthm v-to-nat-int-to-v
  (implies (and (integerp n)
                (<= 0 n)
                (< n (expt 2 len)))
           (equal (v-to-nat (int-to-v n len)) n)))


(local
 (progn
   (defthm integerp-half-exp-2-greater-0
     (implies (and (integerp n)
                   (< 0 n))
              (integerp (* 1/2 (expt 2 n)))))

   (defthm integer-lower-bound-floor
     (implies (and (integerp k)
                   (rationalp r)
                   (<= k r))
              (<= k (floor r 1)))
     :rule-classes nil)

   (defthm product-integer-lower-bound-floor
     (implies (and (integerp k)
                   (integerp n)
                   (rationalp f)
                   (integerp (* f k))
                   (<= 0 f)
                   (<= k n))
              (<= (* f k) (floor (* f n) 1)))
     :hints (("goal" :use ((:instance integer-lower-bound-floor
                                      (r (* f n))
                                      (k (* f k))))))
     :rule-classes nil)

   (defthm expt-2-lte-zero
     (implies (and (integerp x)
                   (<= x 0))
              (and (< 0 (expt 2 x))
                   (<= (expt 2 x) 1)))
     :rule-classes nil)))


(local (defthm lousy-lemma-1
           (IMPLIES (AND (< (FLOOR (* 1/2 N) 1)
                            (- (* 1/2 (EXPT 2 (+ -1 LEN)))))
                         (<= (- (EXPT 2 (+ -1 LEN))) N)
                         (INTEGERP N)
                         (natp len)
                         (< 1 LEN))
                    (EQUAL (+ 1
                              (* 2
                                 (V-TO-INT (INT-TO-V (FLOOR (* 1/2 N) 1)
                                                     (+ -1 LEN)))))
                           N))
           :hints(("Goal"
                   :use ((:instance product-integer-lower-bound-floor
                                    (n n)
                                    (k (- (expt 2 (+ -1 len))))
                                    (f 1/2)))))))

(local (defthm lousy-lemma-2
         (IMPLIES (AND (ZP LEN)
                       (INTEGERP N)
                       (<= (- (* 1/2 (EXPT 2 LEN))) N)
                       (< (* 2 N) (EXPT 2 LEN)))
                  (equal (EQUAL 0 N)
                         t))
         :hints(("goal"
                 :use ((:instance expt-2-lte-zero (x len)))))))

(defthm v-to-int-int-to-v
  (implies (and (integerp n)
                (<= (- (expt 2 (1- (ifix len)))) n)
                (< n (expt 2 (1- (ifix len)))))
           (equal (v-to-int (int-to-v n len)) n)))


(defthm int-to-v-v-to-nat
  (implies (and (boolean-listp lst)
                (equal len (len lst)))
           (equal (int-to-v (v-to-nat lst) len)
                  lst)))


(defthm int-to-v-v-to-int
  (implies (and (boolean-listp lst)
                (equal len (len lst)))
           (equal (int-to-v (v-to-int lst) len)
                  lst)))





(defthm consp-int-to-fv
  (equal (consp (int-to-fv n len))
         (not (zp len))))

(defthm len-int-to-fv
  (equal (len (int-to-fv n len))
         (nfix len)))


(defun fv-const-bool-listp (a)
  (if (atom a)
      (equal a nil)
    (and (or (equal (car a) '(t . nil))
             (equal (car a) '(nil . t)))
         (fv-const-bool-listp (cdr a)))))

(defthm fv-const-bool-listp-int-to-fv
  (fv-const-bool-listp (int-to-fv x n)))

(defthm fv-to-nat-type-rw
  (implies (fv-const-bool-listp a)
           (and (integerp (fv-to-nat a))
                (natp (fv-to-nat a))
                (<= 0 (fv-to-nat a))))
  :rule-classes (:rewrite :type-prescription))


(defthm fv-to-nat-linear
  (implies (fv-const-bool-listp a)
           (and (<= 0 (fv-to-nat a))
                (< (fv-to-nat a) (expt 2 (len a)))))
  :rule-classes ((:linear :trigger-terms ((fv-to-nat a)))))



(defthm fv-to-int-type-rw
  (implies (fv-const-bool-listp a)
           (integerp (fv-to-int a)))
  :rule-classes (:rewrite :type-prescription))

(defthm fv-to-int-linear
  (implies (fv-const-bool-listp lst)
           (and (<= (- (expt 2 (1- (len lst)))) (fv-to-int lst))
                (< (fv-to-int lst) (expt 2 (1- (len lst))))))
  :hints (("goal" :induct (fv-to-int lst))
          (and stable-under-simplificationp
               '(:expand
                 ((expt 2 (len (cdr lst)))))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((fv-to-int lst)))))



(defthm fv-to-nat-int-to-fv
  (implies (and (integerp n)
                (<= 0 n)
                (< n (expt 2 len)))
           (equal (fv-to-nat (int-to-fv n len)) n)))



(local (defthm lousy-lemma-3
         (IMPLIES (AND (< (FLOOR (* 1/2 N) 1) (- (* 1/2 (EXPT 2 (+ -1 LEN)))))
                       (<= (- (EXPT 2 (+ -1 LEN))) N)
                       (< 1 LEN)
                       (natp len)
                       (INTEGERP N))
                  (EQUAL (+ 1
                            (* 2
                               (FV-TO-INT (INT-TO-FV (FLOOR (* 1/2 N) 1)
                                                     (+ -1 LEN)))))
                         N))
         :hints(("Goal" :use ((:instance product-integer-lower-bound-floor
                                         (n n)
                                         (k (- (expt 2 (+ -1 len))))
                                         (f 1/2)))))))

(defthm fv-to-int-int-to-fv
  (implies (and (integerp n)
                (<= (- (expt 2 (1- (ifix len)))) n)
                (< n (expt 2 (1- (ifix len)))))
           (equal (fv-to-int (int-to-fv n len)) n)))

(defthm int-to-fv-fv-to-nat
  (implies (and (fv-const-bool-listp lst)
                (equal len (len lst)))
           (equal (int-to-fv (fv-to-nat lst) len)
                  lst)))


(defthm int-to-fv-fv-to-int
  (implies (and (fv-const-bool-listp lst)
                (equal len (len lst)))
           (equal (int-to-fv (fv-to-int lst) len)
                  lst)))

(defthm logbitp-of-v-to-nat
  (equal (logbitp n (v-to-nat a))
         (if (nth (nfix n) a)
             t
           nil))
  :hints(("Goal"
          :induct (nth n a)
          :in-theory (enable v-to-nat))))

