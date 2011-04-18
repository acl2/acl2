; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

(in-package "ACL2")

; ihs-extensions.lisp
;
; This book is can be used instead of ihs/logops-lemmas to add a bunch of
; additional theorems and provide a more sensible theory.  This book should
; typically be only locally included since it makes various changes to the
; global theory such as disabling floor, mod, expt, etc.

(include-book "ihs/logops-lemmas" :dir :system)
(include-book "defaults")
(include-book "integer-length")

(local (include-book "arithmetic-3/extra/top-ext" :dir :system))
(local (include-book "equal-by-logbitp"))

(local (in-theory (disable expt-between-one-and-two)))


(defconst *ihs-extensions-disables*
  '(floor mod expt ash evenp oddp
          logbitp logior logand lognot logxor
          logcons logcar logcdr
          integer-length))

(make-event
 (prog2$ (cw "Note (from ihs-extensions): disabling ~&0.~%~%"
             *ihs-extensions-disables*)
         '(value-triple :invisible))
 :check-expansion t)

(in-theory (set-difference-theories (current-theory :here)
                                    *ihs-extensions-disables*))


(local (defun dec-induct (n)
         (if (zp n)
             n
           (dec-induct (1- n)))))

(local (defun dec-dec-induct (a b)
         (if (zp a)
             (list a b)
           (dec-dec-induct (- a 1) (- b 1)))))

(local (defun logcdr-logcdr-induct (x y)
         (if (zp x)
             nil
           (if (zp y)
               nil
             (logcdr-logcdr-induct (logcdr x) (logcdr y))))))

(local (defun dec-logcdr-induct (a x)
         (if (zp a)
             (list a x)
           (dec-logcdr-induct (1- a) (logcdr x)))))

(local (defun dec-logcdr-logcdr-induct (a x y)
         (if (zp a)
             (list a x y)
           (dec-logcdr-logcdr-induct (- a 1)
                                     (logcdr x)
                                     (logcdr y)))))


(defthm ash-zero
  (equal (ash x 0)
         (ifix x))
  :hints(("Goal" :in-theory (enable ash))))

(defthm ash-1-removal
  (equal (ash 1 n)
         (if (integerp n)
             (if (<= 0 n)
                 (expt 2 n)
               0)
           1))
  :hints(("Goal" :in-theory (enable ash))))

(defthm logcar-possibilities
  (or (equal (logcar a) 0)
      (equal (logcar a) 1))
  :rule-classes ((:forward-chaining :trigger-terms ((logcar a))))
  :hints(("Goal" :in-theory (enable logcar))))

(defthm |(logbitp 0 x)|
  (equal (logbitp 0 x)
         (equal (logcar x) 1))
  :hints(("Goal" :in-theory (enable logbitp logcar oddp evenp))))

(encapsulate
  ()
  ;; The following theorems improve logbitp-0-minus-1 by eliminating
  ;; the unnecessary hyps.

  (local (defthm l0
           (implies (zp a)
                    (not (logbitp a 0)))
           :hints(("Goal" :in-theory (enable logbitp)))))

  (local (defthm l1
           (implies (zp a)
                    (logbitp a -1))
           :hints(("Goal" :in-theory (enable logbitp)))))

  (defthm |(logbitp a 0)|
    (equal (logbitp a 0) nil)
    :hints(("Goal"
            :induct (dec-induct a)
            :in-theory (enable logbitp*))))

  (defthm |(logbitp a -1)|
    (equal (logbitp a -1) t)
    :hints(("Goal"
            :induct (dec-induct a)
            :in-theory (enable logbitp*))))

  (in-theory (disable logbitp-0-minus-1)))


(defthmd logbitp**
  ;; This is a better replacement for logbitp* that doesn't have unnecessary
  ;; type restrictions.
  (equal (logbitp pos i)
         (cond ((zp pos)
                (equal (logcar i) 1))
               (t
                (logbitp (1- pos) (logcdr i)))))
  :rule-classes ((:definition :clique (logbitp) :controller-alist ((logbitp t t))))
  :hints(("Goal" :use ((:instance logbitp*)))))

(theory-invariant (not (active-runep '(:definition logbitp*)))
                  :key |Use LOGBITP** instead of LOGBITP*|)


(defthmd logand**
  ;; Better than logand* since there are no hyps.
  (equal (logand i j)
         (logcons (b-and (logcar i) (logcar j))
                  (logand (logcdr i) (logcdr j))))
  :rule-classes
  ((:definition :clique (binary-logand)
                :controller-alist ((binary-logand t t))))
  :hints(("Goal" :use ((:instance logand*)))))

(theory-invariant (not (active-runep '(:definition logand*)))
                  :key |Use LOGAND** instead of LOGAND*|)



(defthmd logior**
  ;; Better than logand* since there are no hyps.
  (equal (logior i j)
         (logcons (b-ior (logcar i) (logcar j))
                  (logior (logcdr i) (logcdr j))))
  :rule-classes
  ((:definition :clique (binary-logior)
                :controller-alist ((binary-logior t t))))
  :hints(("Goal" :use ((:instance logior*)))))

(theory-invariant (not (active-runep '(:definition logior*)))
                  :key |Use LOGIOR** instead of LOGIOR*|)



(defthmd logxor**
  ;; Better than logxor* since there are no hyps.
  (equal (logxor i j)
         (logcons (b-xor (logcar i) (logcar j))
                  (logxor (logcdr i) (logcdr j))))
  :rule-classes
  ((:definition :clique (binary-logxor)
                :controller-alist ((binary-logxor t t))))
  :hints(("Goal"
          :in-theory (e/d (logxor) (logmaskp))
          :use ((:instance logxor*)))))

(theory-invariant (not (active-runep '(:definition logxor*)))
                  :key |Use LOGXOR** instead of LOGXOR*|)


(defthmd lognot**
  ;; Better than lognot* since there are no hyps.
  (equal (lognot i)
         (logcons (b-not (logcar i))
                  (lognot (logcdr i))))
  :rule-classes ((:definition :clique (lognot)
                              :controller-alist ((lognot t))))
  :hints(("Goal"
          :in-theory (enable lognot)
          :use ((:instance lognot*)))))

(theory-invariant (not (active-runep '(:definition lognot*)))
                  :key |Use LOGNOT** instead of LOGNOT*|)




(defthm logbitp-upper-bound
  (implies (and (logbitp a x)
                (natp a)
                (natp x))
           (< a (integer-length x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :induct (dec-logcdr-induct a x)
          :in-theory (enable logbitp**))))

(defthm logcar-of-logior
  (equal (logcar (logior x y))
         (if (or (= (logcar x) 1)
                 (= (logcar y) 1))
             1
           0))
  :hints(("Goal"
          :expand (logior x y)
          :in-theory (enable logior**))))

(defthm logbitp-of-logior
  (equal (logbitp a (logior x y))
         (or (logbitp a x)
             (logbitp a y)))
  :hints(("Goal"
          :induct (dec-logcdr-logcdr-induct a x y)
          :in-theory (enable logior** logbitp**))))

(defthm logcar-of-logand
  (equal (logcar (logand x y))
         (if (and (= (logcar x) 1)
                  (= (logcar y) 1))
             1
           0))
  :hints(("Goal"
          :expand (logand x y)
          :in-theory (enable logand**))))

(defthm logbitp-of-logand
  (equal (logbitp a (logand x y))
         (and (logbitp a x)
              (logbitp a y)))
  :hints(("Goal"
          :induct (dec-logcdr-logcdr-induct a x y)
          :in-theory (enable logand** logbitp**))))

(defthm logcar-of-lognot
  (equal (logcar (lognot x))
         (if (= (logcar x) 1)
             0
           1))
  :hints(("Goal" :in-theory (enable lognot**))))

(defthm logbitp-of-lognot
  (equal (logbitp a (lognot x))
         (not (logbitp (nfix a) x)))
  :hints(("Goal"
          :induct (dec-logcdr-induct a x)
          :in-theory (enable lognot** logbitp**))))

(defthm logcar-of-logxor
  (equal (logcar (logxor x y))
         (if (or (and (= (logcar x) 1)
                      (= (logcar y) 1))
                 (and (= (logcar x) 0)
                      (= (logcar y) 0)))
             0
           1))
  :hints(("Goal"
          :expand (logxor x y)
          :in-theory (enable logxor**))))

(defthm logbitp-of-logxor
  (equal (logbitp a (logxor x y))
         (xor (logbitp a x)
              (logbitp a y)))
  :hints(("Goal"
          :induct (dec-logcdr-logcdr-induct a x y)
          :in-theory (enable logxor** logbitp**))))



(defthm |(< (lognot a) 0)|
  (equal (< (lognot a) 0)
         (if (integerp a)
             (<= 0 a)
           t))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                                     (implies (natp a)
                                              (and (integerp (lognot a))
                                                   (< (lognot a) 0))))
                 (:type-prescription :corollary
                                     (implies (and (integerp a)
                                                   (< a 0))
                                              (and (integerp (lognot a))
                                                   (<= 0 (lognot a)))))
                 (:linear :corollary
                          (implies (natp a)
                                   (< (lognot a) 0)))
                 (:linear :corollary
                          (implies (and (integerp a)
                                        (< a 0))
                                   (<= 0 (lognot a)))))
  :hints(("Goal" :in-theory (enable lognot))))

(defthm |(equal (lognot a) 0)|
  ;; This isn't really necessary since cancel-equal-lognot can get it instead.
  ;; On the other hand, this can be an abbreviation rule.
  (equal (equal (lognot a) 0)
         (equal a -1)))


(defthm |(<= 0 (logand a b))|
  (equal (< (logand a b) 0)
         (not (or (not (integerp a))
                  (not (integerp b))
                  (<= 0 a)
                  (<= 0 b))))
  :rule-classes ((:rewrite)
                 (:linear :corollary (implies (natp a)
                                              (<= 0 (logand a b))))
                 (:linear :corollary (implies (natp b)
                                              (<= 0 (logand a b))))
                 (:linear :corollary (implies (and (< a 0)
                                                   (< b 0)
                                                   (integerp a)
                                                   (integerp b))
                                              (< (logand a b) 0)))
                 (:type-prescription :corollary (implies (natp a)
                                                         (and (integerp (logand a b))
                                                              (<= 0 (logand a b)))))
                 (:type-prescription :corollary (implies (natp b)
                                                         (and (integerp (logand a b))
                                                              (<= 0 (logand a b)))))
                 (:type-prescription :corollary (implies (and (< a 0)
                                                              (< b 0)
                                                              (integerp a)
                                                              (integerp b))
                                                         (and (integerp (logand a b))
                                                              (< (logand a b) 0)))))
  :hints(("Goal" :in-theory (enable logand))))

(defthm |(< (logior a b) 0)|
  (equal (< (logior a b) 0)
         (or (and (integerp a)
                  (< a 0))
             (and (integerp b)
                  (< b 0))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                          (implies (and (natp a)
                                        (natp b))
                                   (<= 0 (logior a b))))
                 (:type-prescription :corollary
                                     (implies (and (natp a)
                                                   (natp b))
                                              (and (integerp (logior a b))
                                                   (<= 0 (logior a b)))))
                 (:linear :corollary
                          (implies (and (integerp a)
                                        (< a 0))
                                   (< (logior a b) 0)))
                 (:type-prescription :corollary
                                     (implies (and (integerp a)
                                                   (< a 0))
                                              (and (integerp (logior a b))
                                                   (< (logior a b) 0))))
                 (:linear :corollary
                          (implies (and (integerp b)
                                        (< b 0))
                                   (< (logior a b) 0)))
                 (:type-prescription :corollary
                                     (implies (and (integerp b)
                                                   (< b 0))
                                              (and (integerp (logior a b))
                                                   (< (logior a b) 0)))))
  :hints(("Goal" :in-theory (enable logior))))


(defthm |(< (logxor a b) 0)|
  (equal (< (logxor a b) 0)
         (if (< (ifix a) 0)
             (not (< (ifix b) 0))
           (< (ifix b) 0)))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                          (implies (and (natp a)
                                        (natp b))
                                   (<= 0 (logxor a b))))
                 (:type-prescription :corollary
                                     (implies (and (natp a)
                                                   (natp b))
                                              (and (integerp (logxor a b))
                                                   (<= 0 (logxor a b)))))
                 (:linear :corollary
                          (implies (and (< a 0)
                                        (integerp a)
                                        (natp b))
                                   (< (logxor a b) 0)))
                 (:type-prescription :corollary
                                     (implies (and (< a 0)
                                                   (integerp a)
                                                   (natp b))
                                              (and (integerp (logxor a b))
                                                   (< (logxor a b) 0))))

                 (:linear :corollary
                          (implies (and (< b 0)
                                        (integerp b)
                                        (natp a))
                                   (< (logxor a b) 0)))
                 (:type-prescription :corollary
                                     (implies (and (< b 0)
                                                   (integerp b)
                                                   (natp a))
                                              (and (integerp (logxor a b))
                                                   (< (logxor a b) 0))))

                 (:linear :corollary
                          (implies (and (< a 0)
                                        (< b 0)
                                        (integerp a)
                                        (integerp b))
                                   (<= 0 (logxor a b))))
                 (:type-prescription :corollary
                                     (implies (and (< a 0)
                                                   (< b 0)
                                                   (integerp a)
                                                   (integerp b))
                                              (and (integerp (logxor a b))
                                                   (<= 0 (logxor a b)))))
                 )
  :hints(("Goal" :in-theory (enable logxor))))




(defthm |(integerp (expt x n))|
  (implies (and (integerp n)
                (integerp x)
                (< 1 x))
           (equal (integerp (expt x n))
                  (<= 0 n)))
  :hints(("Goal" :in-theory (enable expt))))


(defthm |(logcdr (expt 2 n))|
  (equal (logcdr (expt 2 n))
         (if (posp n)
             (expt 2 (1- n))
           0))
  :hints(("Goal" :in-theory (enable logcdr))))

(defthm |(logcar (expt 2 n))|
  (equal (logcar (expt 2 n))
         (if (= (ifix n) 0)
             1
           0))
  :hints(("Goal" :in-theory (enable logcar))))

(defthm logand-with-2^n-is-logbitp
  (implies (natp n)
           (equal (equal (logand x (expt 2 n)) 0)
                  (not (logbitp n x))))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (natp n)
                                    (equal (equal (logand (expt 2 n) x) 0)
                                           (not (logbitp n x))))))
  :hints(("Goal"
          :in-theory (enable logand** logbitp**)
          :induct (dec-logcdr-induct n x))))


(encapsulate
  ()
  (local (in-theory (disable not-integerp-4a not-integerp-4b
                             not-integerp-3a not-integerp-3b
                             not-integerp-2a not-integerp-2b
                             not-integerp-1a not-integerp-1b
                             nintegerp-/
                             (:type-prescription floor-zero . 1)
                             (:type-prescription floor-zero . 2)
                             (:type-prescription floor-zero . 3)
                             (:rewrite floor-zero . 4)
                             floor-non-negative-integerp-type-prescription
                             expt-type-prescription-nonpositive-base-odd-exponent
                             expt-type-prescription-negative-base-odd-exponent)))
  (local (defthm l0
           (implies (and (natp a)
                         (integerp n)
                         (< n 0))
                    (equal (logbitp a (ash x n))
                           (logbitp (- a n) x)))
           :hints(("Goal" :in-theory (enable logbitp ash)))))

  (local (defthm l1
           (implies (and (natp a)
                         (natp n))
                    (equal (logbitp a (ash x n))
                           (if (< a n)
                               nil
                             (logbitp (- a n) x))))
           :hints(("Goal" :in-theory (enable logbitp ash oddp evenp)))))

  (defthm logbitp-of-ash
    (implies (natp a)
             (equal (logbitp a (ash x n))
                    (cond ((or (not (integerp n))
                               (= n 0))
                           (logbitp a x))
                          ((< n 0)
                           (logbitp (- a n) x))
                          ((< a n)
                           nil)
                          (t
                           (logbitp (- a n) x)))))
    :hints(("Goal" :use ((:instance l0)
                         (:instance l1))))))


(encapsulate
  ()
  (local (defthm l0
           (implies (natp a)
                    (equal (logbitp a (expt 2 a))
                           t))
           :hints(("Goal"
                   :induct (dec-induct a)
                   :in-theory (enable logbitp**)))))

  (local (defthm l1
           (implies (and (not (equal a b))
                         (natp a)
                         (natp b))
                    (not (logbitp a (expt2 b))))
           :hints(("Goal"
                   :in-theory (enable logbitp**)
                   :expand (logbitp a (expt 2 b))
                   :induct (dec-dec-induct a b)))))

  (defthm logbitp-of-expt-2
    (implies (natp b)
             (equal (logbitp a (expt 2 b))
                    (equal (nfix a) b)))
    :hints(("Goal" :use ((:instance l0)
                         (:instance l1))))))




(defthm |(mod a (expt 2 n)) < (expt 2 n)|
  (implies (integerp a)
           (< (mod a (expt 2 n))
              (expt 2 n)))
  :rule-classes ((:rewrite) (:linear)))

(defthm expt-2-monotonic
  (implies (and (< a b)
                (integerp a)
                (integerp b))
           (< (expt 2 a)
              (expt 2 b)))
  :rule-classes ((:rewrite) (:linear)))

(defthm expt-2-lower-bound-by-logbitp
  (implies (and (logbitp n x)
                (natp n)
                (natp x))
           (<= (expt 2 n)
               x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable logbitp evenp oddp))))

(defthmd logbitp-when-too-small
  (implies (and (< a (expt 2 n))
                (natp a)
                (natp n))
           (equal (logbitp n a)
                  nil)))


(encapsulate
 ()
 (local (defthm l0
          (implies (and (< bit n)
                        (natp bit)
                        (integerp a)
                        (natp n))
                   (equal (logbitp bit (mod a (expt 2 n)))
                          (logbitp bit a)))
          :hints(("Goal"
                  :in-theory (enable logbitp evenp oddp)
                  :nonlinearp t))))

 (local (defthm l1
          (implies (and (<= n bit)
                        (natp bit)
                        (integerp a)
                        (natp n))
                   (equal (logbitp bit (mod a (expt 2 n)))
                          nil))))

 (defthm |(logbitp bit (mod a (expt 2 n)))|
   (implies (and (natp bit)
                 (integerp a)
                 (natp n))
            (equal (logbitp bit (mod a (expt 2 n)))
                   (if (< bit n)
                       (logbitp bit a)
                     nil)))))


(defthm |(logbitp n (+ (expt 2 n) a))|
  (implies (and (integerp a)
                (natp n))
           (equal (logbitp n (+ (expt 2 n) a))
                  (not (logbitp n a))))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (and (integerp a)
                                         (natp n))
                                    (equal (logbitp n (+ a (expt 2 n)))
                                           (not (logbitp n a))))))
  :hints(("Goal" :in-theory (enable logbitp evenp oddp))))

(defthm normalize-logbitp-when-mods-equal
  (implies (and (equal (mod a (expt 2 n))
                       (mod b (expt 2 n)))
                (syntaxp (term-order b a))
                (< bit n)
                (natp bit)
                (natp n)
                (integerp a)
                (integerp b))
           (equal (logbitp bit b)
                  (logbitp bit a)))
  :hints(("Goal"
          :in-theory (disable |(logbitp bit (mod a (expt 2 n)))|)
          :use ((:instance |(logbitp bit (mod a (expt 2 n)))|)
                (:instance |(logbitp bit (mod a (expt 2 n)))|
                           (a b))))))

(defthm smaller-mods-are-still-the-same
  (implies (and (equal (mod a (expt 2 n))
                       (mod b (expt 2 n)))
                (< k n)
                (integerp a)
                (integerp b)
                (natp k)
                (natp n))
           (equal (equal (mod a (expt 2 k))
                         (mod b (expt 2 k)))
                  t))
  :hints(("Goal"
          :in-theory (disable mod-force-equal-ext
                              mod-zero cancel-mod-+
                              mod-negative mod-positive
                              mod-nonpositive
                              mod-does-nothing)
          :use ((:functional-instance
                 equal-by-logbitp
                 (logbitp-hyp (lambda ()
                                (and (equal (mod b (expt 2 n))
                                            (mod a (expt 2 n)))
                                     (< k n)
                                     (integerp a)
                                     (integerp b)
                                     (natp k)
                                     (natp n))))
                 (logbitp-lhs (lambda () (mod b (expt 2 k))))
                 (logbitp-rhs (lambda () (mod a (expt 2 k)))))))))

(defthm |(2^n + a mod 2^n) when a < 2^n+1|
  (implies (and (case-split (< a (expt 2 (+ 1 n))))
                (natp a)
                (natp n))
           (equal (+ (expt 2 n) (mod a (expt 2 n)))
                  (cond ((< a (expt 2 n))
                         (+ (expt 2 n) a))
                        ((< a (expt 2 (+ 1 n)))
                         a))))
  :hints(("Goal" :nonlinearp t)))


(defthm |(2^n + a mod 2^n) when 2^n+1 <= a, a[n] = 1|
  (implies (and (case-split (not (< a (expt 2 (+ 1 n)))))
                (logbitp n a)
                (natp a)
                (natp n))
           (equal (+ (expt 2 n) (mod a (expt 2 n)))
                  (mod a (expt 2 (+ 1 n)))))
  :hints(("goal"
          :nonlinearp t
          :in-theory (e/d (logbitp oddp evenp)
                          (nintegerp-expt)))))

(defthm upper-bound-of-logior-for-naturals
  (implies (and (< x (expt 2 n))
                (< y (expt 2 n))
                (natp x)
                (natp y)
                (posp n))
           (< (logior x y) (expt 2 n)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :in-theory (disable unsigned-byte-p-logior)
          :use ((:instance unsigned-byte-p-logior
                           (i x)
                           (j y)
                           (size n))))))

(defthm upper-bound-of-logxor-for-naturals
  (implies (and (< x (expt 2 n))
                (< y (expt 2 n))
                (natp x)
                (natp y)
                (posp n))
           (< (logxor x y) (expt 2 n)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :in-theory (disable unsigned-byte-p-logxor)
          :use ((:instance unsigned-byte-p-logxor
                           (i x)
                           (j y)
                           (size n))))))