; A lightweight book about the built-in function integer-length
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;; TODO: which do we prefer, lg or integer-length?  i think i like lg best,
;; but my current rules may target integer-length?

(local (include-book "floor")) ; reduce?
;(local (include-book "mod")) ; floor-mod-elim-rule was used in integer-length-of-+-of--1-when-not-power-of-2
(local (include-book "expt"))
;(local (include-book "expt2"))
(local (include-book "plus"))
(local (include-book "times"))
(local (include-book "numerator")) ; since floor calls numerator
(local (include-book "denominator"))
(local (include-book "nonnegative-integer-quotient"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(in-theory (disable integer-length))

(defthm integer-length-when-not-integerp-cheap
  (implies (not (integerp i))
           (equal (integer-length i)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-expt-of-integer-length-same
  (implies (integerp n)
           (< n (expt 2 (integer-length n))))
  :hints (("Goal" :in-theory (enable integer-length EXPT-OF-+))))

(defthm <-of-expt-of-integer-length-same-linear
  (implies (integerp n)
           (< n (expt 2 (integer-length n))))
  :rule-classes :linear)

(defthm integer-length-of-expt2
  (implies (integerp n)
           (equal (integer-length (expt 2 n))
                  (if (< n 0)
                      0
                    (+ 1 n))))
  :hints (("Goal" :in-theory (enable integer-length expt))))

(defthm integer-length-of-mask
  (implies (natp size)
           (equal (integer-length (+ -1 (expt 2 size)))
                  size))
  :hints (("Goal" :in-theory (enable integer-length expt mod))))

(local
 (defun double-floor-by-2-induct (i j)
   (if (zip i)
       0
     (if (= i -1)
         0
       (if (zip j)
           0
         (if (= j -1)
             0
           (double-floor-by-2-induct (floor i 2) (floor j 2))))))))

(defthm integer-length-monotonic
  (implies (and (<= x y)
                (natp x)
                (integerp y))
           (<= (integer-length x) (integer-length y)))
  :hints (("Goal"
           :induct (double-floor-by-2-induct x y)
           :in-theory (enable integer-length))))

(defthm integer-length-of-times-2
  (implies (posp n)
           (equal (integer-length (* 2 n))
                  (+ 1 (integer-length n))))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm integer-length-of-floor-by-2
  (implies (integerp i)
           (equal (integer-length (floor i 2))
                  (if (or (equal 0 i)
                          (equal -1 i))
                      0
                    (+ -1 (integer-length i)))))
  :hints (("Goal" :in-theory (enable integer-length zp zip))))

(defthm equal-of-0-and-integer-length
  (implies (natp i)
           (equal (equal 0 (integer-length i))
                  (equal i 0)))
  :hints (("Goal" :expand ((integer-length i))
           :in-theory (disable integer-length-of-floor-by-2))))

(defthm equal-of-1-and-integer-length
  (implies (natp i)
           (equal (equal 1 (integer-length i))
                  (equal 1 i)))
  :hints (("Goal" :expand ((integer-length i))
           :in-theory (disable integer-length-of-floor-by-2))))

(defthm <-of-1-and-integer-length
  (implies (and (< 1 k)
                (integerp k))
           (< 1 (integer-length k)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-1-and-integer-length-linear
  (implies (and (< 1 x) (integerp x))
           (< 1 (integer-length x)))
  :rule-classes :linear)

(defthm <-of-integer-length-and-1
  (equal (< (integer-length i) 1)
         (or (not (integerp i))
             (equal i 0)
             (equal i -1)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-0-and-integer-length
  (implies (natp x)
           (equal (< 0 (integer-length x))
                  (< 0 x)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm unsigned-byte-p-of-integer-length
  (implies (natp x)
           (unsigned-byte-p (integer-length x) x))
  :hints (("Goal" :in-theory (enable integer-length))))

;expensive, newly disabled
(defthmd unsigned-byte-p-of-integer-length-gen
  (implies (and (<= (integer-length x) n)
                (integerp n)
                (natp x))
           (unsigned-byte-p n x))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-integer-length)
           :in-theory (disable unsigned-byte-p-of-integer-length))))

(defthm unsigned-byte-p-integer-length-one-less
  (implies (and (integerp index)
                (< index len) ;move to conclusion?
                (integerp len))
           (equal (unsigned-byte-p (integer-length (+ -1 len)) index)
                  (<= 0 index)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-length))))

(local
 (defun sub1-induct (n)
  (if (zp n)
      n
    (sub1-induct (+ -1 n)))))

(defthm integer-length-of-*-of-2
  (implies (integerp n)
           (equal (integer-length (* 2 n))
                  (if (equal n 0)
                      0
                    (+ 1 (integer-length n)))))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm integer-length-of-*-of-expt2
  (implies (and (natp n)
                (integerp x))
           (equal (integer-length (* x (expt 2 n)))
                  (if (equal 0 x)
                      0
                    (+ n (integer-length x)))))
  :hints (("Goal" ;:expand (INTEGER-LENGTH (* X (EXPT 2 (+ -1 N))))
           :induct (sub1-induct n)
           :in-theory (e/d (integer-length expt)
                           (;expt-hack
                            )))))

;; conflicts with expanding integer-length?
(defthm integer-length-of-*-of-1/2
  (implies (and (evenp x)
                (rationalp x))
           (equal (integer-length (* 1/2 x))
                  (if (equal x 0)
                      0
                    (+ -1 (integer-length x)))))
  :hints (("Goal" :expand (integer-length x)
           :in-theory (e/d (integer-length floor)
                           (integer-length-of-floor-by-2)))))

(local
 (defun sub1-floor-by-2-induct (n j)
   (if (zp n)
       0
     (if (zip j)
           0
         (if (= j -1)
             0
           (sub1-floor-by-2-induct (+ -1 n) (floor j 2)))))))

(defthm <-of-integer-length-arg2
  (implies (and (posp x)
                (integerp n))
           (equal (< n (integer-length x))
                  (<= (expt 2 n) x)))
  :hints (("Goal"
           :induct (sub1-floor-by-2-induct n x)
           :in-theory (enable integer-length expt zp))))

(defthm <-of-expt-of-one-less-of-integer-length
  (implies (posp x)
           (not (< x (expt 2 (+ -1 (integer-length x))))))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-expt-of-one-less-of-integer-length-linear
  (implies (posp x)
           (not (< x (expt 2 (+ -1 (integer-length x))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-integer-length-arg1
  (implies (and (syntaxp (not (and (quotep n) (< 1000 (unquote n))))) ;prevent huge calls to expt
                (posp x)
                (natp n))
           (equal (< (integer-length x) n)
                  (< x (expt 2 (+ -1 n)))))
  :hints (("subgoal *1/3" :use ((:instance <-of-expt-of-integer-length-same-linear (n x))
                                (:instance <=-of-expt-and-expt-same-base-linear (r 2) (i1 (integer-length x)) (i2 (+ -1 n))))
           :in-theory (disable <-of-expt-of-integer-length-same
                               <-of-expt-and-expt-same-base
                               <-of-integer-length-arg2))
          ("Goal" :in-theory (enable integer-length posp))))

;; or move to expt2.lisp
(defthm <-of-expt-2-and-constant
  (implies (and (syntaxp (quotep k))
                (integerp k) ;gen?
                ;(integerp i)
                )
           (equal (< (expt 2 i) k)
                  (and (< 0 k)
                       (not (equal k (expt 2 i)))
                       (< (ifix i) (integer-length k))))))

;; or move to expt2.lisp
(defthm <-of-constant-and-expt-2
  (implies (and (syntaxp (quotep k))
                (integerp k) ;gen?
                ;(integerp i)
                )
           (equal (< k (expt 2 i))
                  (or (<= k 0)
                      (<= (integer-length k) (ifix i))))))

(local
 (defthm integer-length-of-+-of--1-when-power-of-2
   (implies (and (natp i)
                 (equal i (expt 2 (+ -1 (integer-length i)))) ; power of 2
                 )
            (equal (integer-length (+ -1 i))
                   (+ -1 (integer-length i))))
   :hints (("Goal" :in-theory (enable integer-length)))))

(local
 (defthm integer-length-of-+-of--1-when-not-power-of-2
   (implies (and (natp i)
                 (not (equal i (expt 2 (+ -1 (integer-length i))))) ; power of 2
                 )
            (equal (integer-length (+ -1 i))
                   (integer-length i)))
   :hints (("Goal" :expand ((integer-length i)
                            (integer-length (+ -1 i)))
            :induct (integer-length i)
            :in-theory (e/d (integer-length mod) (integer-length-of-floor-by-2))))))

(defthmd integer-length-of-+-of--1
  (implies (natp i)
           (equal (integer-length (+ -1 i))
                  (if (equal i (expt 2 (+ -1 (integer-length i)))) ; power of 2
                      (+ -1 (integer-length i))
                    (integer-length i))))
  :hints (("Goal" :cases ((not (equal i (expt 2 (+ -1 (integer-length i)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm integer-length-of-+-of-1-when-power-of-2
   (implies (and (natp i)
                 (equal (+ 1 i) (expt 2 (+ -1 (integer-length (+ 1 i))))) ; i+1 is a power of 2
                 )
            (equal (integer-length (+ 1 i))
                   (+ 1 (integer-length i))))
   :hints (("Goal" :use (:instance integer-length-of-+-of--1-when-power-of-2 (i (+ 1 i)))
            :in-theory (disable integer-length-of-+-of--1-when-power-of-2)))))

(local
 (defthm integer-length-of-+-of-1-when-not-power-of-2
   (implies (and (natp i)
                 (not (equal (+ 1 i) (expt 2 (+ -1 (integer-length (+ 1 i)))))) ; i+1 is not a power of 2
                 )
            (equal (integer-length (+ 1 i))
                   (integer-length i)))
   :hints (("Goal" :use (:instance integer-length-of-+-of--1-when-not-power-of-2 (i (+ 1 i)))
            :in-theory (disable integer-length-of-+-of--1-when-not-power-of-2)))))

;loops if made a rewrite rule
(defthm integer-length-of-+-of-1
  (implies (natp i)
           (equal (integer-length (+ 1 i))
                  (if (equal (+ 1 i) (expt 2 (+ -1 (integer-length (+ 1 i))))) ; i+1 is a power of 2
                      (+ 1 (integer-length i))
                    (integer-length i))))
  :rule-classes nil)

(defthm integer-length-of-nonnegative-integer-quotient-of-2
  (equal (integer-length (nonnegative-integer-quotient i 2))
         (if (zp i)
             0
           (+ -1 (integer-length i))))
  :hints (("Goal" :use (:instance integer-length-of-floor-by-2)
           :cases ((equal 0 i))
           :in-theory (e/d (nonnegative-integer-quotient-becomes-floor)
                           (integer-length-of-floor-by-2
                            nonnegative-integer-quotient)))))
