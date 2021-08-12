; A lightweight book about the built-in function integer-length
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;; TODO: which do we prefer, lg or integer-length?  i think i like lg best,
;; but my current rules may target integer-length?

(local (include-book "floor"))
(local (include-book "mod"))
(local (include-book "expt"))
(local (include-book "expt2"))
(local (include-book "plus"))
(local (include-book "times"))
(local (include-book "numerator"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;move?
(defthm integer-length-bound
  (implies (and (integerp n)
                ;; (< 0 n)
                )
           (< n (expt 2 (integer-length n))))
  :rule-classes (:rewrite :linear)
  :hints ( ;("subgoal *1/5" :use (:instance floor-bound (x n)))
          ("Goal"
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (integer-length EXPT-OF-+)
                           (floor-bound
                            ;;COLLECT-CONSTANTS-TIMES-EQUAL ;bozo looped
                            )))))

(defthm integer-length-of-expt2
  (implies (integerp n)
           (equal (integer-length (expt 2 n))
                  (if (< n 0)
                      0
                    (+ 1 n))))
  :hints
  (("Goal" :in-theory (e/d (integer-length expt)
                           ()))))

(defthm integer-length-of-mask
  (implies (natp size)
           (equal (integer-length (+ -1 (expt 2 size)))
                  size))
  :hints (("Goal" :in-theory (e/d (integer-length expt)
                                  ()))))

;for integer-length proofs
(defun double-floor-by-2-induct (i j)
  (if (zip i)
      0
      (if (= i -1)
          0
          (if (zip j)
              0
              (if (= j -1)
                  0
                  (+ 1 (double-floor-by-2-induct (floor i 2) (floor j 2))))))))

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

(in-theory (disable integer-length))

(defthm integer-length-of-floor-by-2
  (implies (posp i)
           (equal (integer-length (floor i 2))
                  (+ -1 (integer-length i))))
  :hints (("Goal" :in-theory (enable integer-length))))

;enable?
(defthmd floor-when-multiple
  (implies (integerp (/ i j))
           (equal (floor i j)
                  (/ i j)))
  :hints (("Goal" :in-theory (enable floor numerator))))

(defthm floor-by-2-bound-even-linear
  (implies (and (<= k x)
                (syntaxp (quotep k))
                (natp x) ;gen?
                (natp k)  ;gets computed
                (evenp k) ;gets computed
                )
           (<= (/ k 2) (floor x 2)))
  :rule-classes ((:linear :trigger-terms ((floor x 2))))
  :hints (("Goal" :cases ((equal x k))
           :in-theory (e/d (evenp) (floor-weak-monotone))
           :use (:instance floor-weak-monotone (i1 k) (i2 x) (j 2)))))

;gen?
(defthm <-of-1-and-floor-of-2
  (implies (rationalp x) ;(natp x)
           (equal (< 1 (floor x 2))
                  (<= 4 x))))

(defthm equal-of-0-and-integer-length
  (implies (natp i)
           (equal (equal 0 (integer-length i))
                  (equal i 0)))
  :hints (("Goal" :expand ((integer-length i))
           :in-theory (disable integer-length-of-floor-by-2))))

(defthm equal-of-1-and-integer-length
  (implies (natp i)
           (equal (equal (integer-length i) 1)
                  (equal i 1)))
  :hints (("Goal" :expand ((integer-length i))
           :in-theory (disable integer-length-of-floor-by-2))))

(defthm <-of-1-and-integer-length
  (implies (and (integerp k)
                (< 1 k))
           (< 1 (integer-length k)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm unsigned-byte-p-of-integer-length
  (implies (natp x)
           (unsigned-byte-p (integer-length x) x))
  :hints (("Goal" :in-theory (e/d (integer-length)
                                  ( )))))

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
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p integer-length)
                                  ()))))

(defthm <-of-integer-length-and-1
  (equal (< (integer-length i) 1)
         (or (not (integerp i))
             (equal i 0)
             (equal i -1)))
  :hints (("Goal" :in-theory (enable integer-length))))

(local
 (defun sub1-induct (n)
  (if (zp n)
      n
    (sub1-induct (+ -1 n)))))

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
                           (expt-hack)))))

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

(defthm <-of-integer-length-arg2
  (implies (and (posp x)
                (integerp n))
           (equal (< n (integer-length x))
                  (<= (expt 2 n) x)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-expt-of-one-less-of-integer-length
  (implies (posp x)
           (not (< x (expt 2 (+ -1 (integer-length x))))))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-integer-length-arg1
  (implies (and (syntaxp (not (and (quotep n) (< 1000 (unquote n))))) ;prevent huge calls to EXPT
                (posp x)
                (natp n))
           (equal (< (integer-length x) n)
                  (< x (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (enable integer-length posp))))
