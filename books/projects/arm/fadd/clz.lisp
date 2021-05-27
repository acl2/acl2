(in-package "RTL")

(include-book "addition")

;; If a bit vector x is partitioned into slices of width 2^k, then the ith
;; slice is extracted as follows:

(defund slice (i k x)
  (bits x (1- (* (expt 2 k) (1+ i))) (*  (expt 2 k) i)))

;; Number of leading zeroes of a bit vector x of width w:

(defun lzcnt (x w)
  (if (or (zp w) (= (bitn x (1- w)) 1))
       0
    (1+ (lzcnt x (1- w)))))

(defthmd lzcnt-expo
  (implies (and (bvecp x w) (> x 0) (natp w))
           (equal (lzcnt x w) (1- (- w (expo x)))))
  :hints (("Subgoal *1/1" :in-theory (enable bvecp)
           :use ((:instance bitn-plus-bits (n (1- w)) (m 0))
                 (:instance expo>= (n (1- w)))
                 (:instance expo<= (n (1- w)))))
          ("Subgoal *1/2" :in-theory (enable bvecp)
                          :use ((:instance bitn-plus-bits (n (1- w)) (m 0))
                                (:instance bits-bounds (i (- w 2)) (j 0))))))

(defthm lzcnt-0
  (implies (natp w)
           (equal (lzcnt 0 w) w)))

(defthm lzcnt-bound-1
  (implies (natp w)
           (<= (lzcnt x w) w))
  :rule-classes ())

(defthm lzcnt-bound-2
  (implies (and (natp w) (not (= (bits x (1- w) 0) 0)))
           (< (lzcnt x w) w))
  :rule-classes ()
  :hints (("Goal" :induct (lzcnt x w))
          ("Subgoal *1/2" :use ((:instance lzcnt-bound-1 (w (1- w)))
                                (:instance bitn-plus-bits (n (1- w)) (m 0))
                                (:instance bitn-0-1 (n (1- w)))))))

(defthmd lzcnt-bvecp
  (implies (and (natp n) (natp w) (>= w n) (bvecp x n))
           (equal (lzcnt x w)
                  (+ (- w n) (lzcnt x n))))
  :hints (("Subgoal *1/1" :cases ((= n w)) :in-theory (enable bvecp-monotone))))

(defthmd lzcnt-bits
  (implies (and (natp n) (natp w) (<= w (1+ n)))
           (equal (lzcnt (bits x n 0) w)
                  (lzcnt x w)))
  :hints (("Goal" :induct (nats w))
          ("Subgoal *1/2" :use ((:instance bitn-0-1 (n (1- w))))
                          :in-theory (enable bitn-bits))))

;; lzcnt of a concatenation:

;; The next two should be in lib:

(defthm cat-bits-3
  (implies (and (integerp i) (integerp m) (>= i (1- m)))
           (equal (cat (bits x i 0) m y n)
                  (cat x m y n)))
  :hints (("Goal" :in-theory (enable cat))))

(defthm cat-bits-4
  (implies (and (integerp i) (integerp n) (>= i (1- n)))
           (equal (cat x m (bits y i 0) n)
                  (cat x m y n)))
  :hints (("Goal" :in-theory (enable cat))))

(local-defthmd lzcnt-split-1
  (implies (and (natp x) (natp y) (natp m) (natp n) (> m 0)
                (= (bitn x (1- m)) 1))
           (equal (lzcnt (cat x m y n) (+ m n)) (lzcnt x m)))
  :hints (("Goal" :in-theory (enable bitn-cat bits-cat))))

(local-defthmd lzcnt-split-2
  (implies (and (natp x) (natp y) (natp m) (natp n) (> m 0)
                (= (bits x (1- m) 0) 0))
           (equal (lzcnt (cat x m y n) (+ m n))
                  (+ m (lzcnt y n))))
  :hints (("Goal" :in-theory (enable cat lzcnt-bits)
                  :cases ((= n 0))
                  :use ((:instance lzcnt-bvecp (x (bits y (1- n) 0))
                                               (w (+ m n)))))))
(local-defthmd lzcnt-split-3
  (implies (and (natp x) (natp y) (natp m) (natp n) (> m 0)
                (= (bitn x (1- m)) 0) (not (= (bits x (1- m) 0) 0)))
           (equal (lzcnt (cat x m y n) (+ m n))
                  (1+ (lzcnt (cat x (1- m) y n) (+ (1- m) n)))))
  :hints (("Goal" :in-theory (enable bitn-bits bitn-cat bits-cat)
                  :use ((:instance lzcnt-bits (x (cat x m y n)) (w (+ n m -1))
                                   (n (+ n m -2)))))))

(defthmd lzcnt-split
  (implies (and (natp x) (natp y) (natp m) (natp n))
           (equal (lzcnt (cat x m y n) (+ m n))
                  (if (= (bits x (1- m) 0) 0)
                      (+ m (lzcnt y n))
                    (lzcnt x m))))
  :hints (("Goal" :induct (nats m))
          ("Subgoal *1/1" :in-theory (enable lzcnt-bits bitn-bits cat))
          ("Subgoal *1/2" :use (lzcnt-split-1 lzcnt-split-2 lzcnt-split-3
                                (:instance bitn-plus-bits (n (1- m)) (m 0))
                                (:instance bitn-0-1 (n (1- m)))))))

;; We apply the above to slice(i, k, x):

(defthmd lzcnt-split-slice
  (implies (and (bvecp x 128)
                (not (zp k))
                (<= k 7)
                (natp i)
                (< i (expt 2 (- 7 k))))
           (equal (lzcnt (slice i k x) (expt 2 k))
                  (if (= (slice (1+ (* 2 i)) (1- k) x) 0)
                      (+ (expt 2 (1- k)) (lzcnt (slice (* 2 i) (1- k) x) (expt 2 (1- k))))
                    (lzcnt (slice (1+ (* 2 i)) (1- k) x) (expt 2 (1- k))))))
  :hints (("Goal" :in-theory (enable cat bitn-bits slice)
                  :nonlinearp t
                  :use ((:instance lzcnt-split (x (slice (1+ (* 2 i)) (1- k) x))
                                               (y (slice (* 2 i) (1- k) x))
                                               (m (expt 2 (1- k)))
                                               (n (expt 2 (1- k))))
                        (:instance bits-plus-bits (n (1- (* (expt 2 k) (1+ i))))
                                                  (p (*  (expt 2 (1- k)) (1+ (* 2 i))))
                                                  (m (*  (expt 2 k) i)))))))





;; Check that the array entries z[i] and c[i] are consistent with  slice(i, k, x)
;; relative to x and k, which means that
;;   (a) z[i] = 1 <=> slice(i, k, x) = 0, and
;;   (b) z[i] = 0 => c[i] is the number of leading zeroes of slice(i, k, x):

(defund check-index (i k c z x)
  (if (= (slice i k x) 0)
      (= (ag i z) 1)
    (and (= (ag i z) 0)
         (= (ag i c) (lzcnt (slice i k x) (expt 2 k))))))

;; Check the low i indices:

(defun check-low (i k c z x)
  (if (and (natp i) (> i 0))
      (and (check-index (1- i) k c z x)
           (check-low (1- i) k c z x))           
    t))

(defthm check-low-check-index
  (implies (and (natp i)
                (natp j)
                (< j i)
                (check-low i k c z x))
           (check-index j k c z x)))

;; Check all 2^(7-k) indices:

(defund check-all (k c z x)
  (check-low (expt 2 (- 7 k)) k c z x))

(defthm check-all-check-index
  (implies (and (natp k)
                (<= k 7)
                (natp j)
                (< j (expt 2 (- 7 k)))
                (check-all k c z x))
           (check-index j k c z x))
  :hints (("Goal" :in-theory (enable check-all)
                  :use ((:instance check-low-check-index (i (expt 2 (- 7 k))))))))

;; For k = 7, there is only one slice, which is x itself.  If x > 0, then
;; c[0] = lzcnt(z, 128):

(defthm check-all-lzcnt
  (implies (and (bvecp x 128)
                (> x 0)
                (check-all 7 c z x))
           (equal (ag 0 c) (lzcnt x 128)))
  :hints (("Goal" :in-theory (enable slice check-index check-all))))

;; Assume that upon entering loop-0, c and z are correct for partion k, where 0 < k <=7.
;; i.e., check-all(k-1, c, z, x) = t.  We shall prove that upon exiting the loop,
;; check-all(k-1, c, z, x) = t.

;; We must establish a loop invariant, i.e., a predicate that holds after i iterations.
;; On iteration i, c[i] and z[i] are computed.  Thus, part of the invariant is
;; check-low(i, k, c, z, x).  But the invariant must also ensure that the arrays hold the
;; information required to compute the remaining entries:

(defun check-high (i k c z x)
  (declare (xargs :measure (nfix (- (expt 2 (- 7 k)) i))))
  (if (and (not (zp k)) (<= k 7) (natp i) (< i (expt 2 (- 7 k))))
      (and (check-index (* 2 i) (1- k) c z x)
           (check-index (1+ (* 2 i)) (1- k) c z x)
           (check-high (1+ i) k c z x))
    t))

(defthmd check-high-check-index
  (implies (and (not (zp k))
                (<= k 7)
                (natp i)
                (natp j)
                (>= j i)
                (< j (expt 2 (- 7 k)))
                (check-high i k c z x))
           (and (check-index (* 2 j) (1- k) c z x)
                (check-index (1+ (* 2 j)) (1- k) c z x))))

(defund loop-0-invariant (i k c z x)
  (and (check-low i k c z x)
       (check-high i k c z x)))

;; Proof of invariance:

(defthm check-index-inv-1
  (implies (and (check-index j k c z x)
                (not (= i j)))
           (check-index j k (as i w c) z x))
  :hints (("Goal" :in-theory (enable check-index))))

(defthm check-index-inv-2
  (implies (and (check-index j k c z x)
                (not (= i j)))
           (check-index j k c (as i w z) x))
  :hints (("Goal" :in-theory (enable check-index))))

(defthm check-low-inv-1
  (implies (and (natp i) (natp j) (>= i j) (check-low j k c z x))
           (check-low j k (as i w c) z x)))

(defthm check-low-inv-2
  (implies (and (natp i) (natp j) (>= i j) (check-low j k c z x))
           (check-low j k c (as i w z) x)))

(defthm check-high-inv-1
  (implies (and (natp i) (not (zp j)) (<= i j) (check-high j k c z x))
           (check-high j k (as i w c) z x)))

(defthm check-high-inv-2
  (implies (and (natp i) (not (zp j)) (<= i j) (check-high j k c z x))
           (check-high j k c (as i w z) x)))

(defthmd loop-0-check-index
  (implies (and (bvecp x 128)
                (not (zp k))
                (<= k 7)
                (natp i)
                (< i (expt 2 (- 7 k)))
                (loop-0-invariant i k c z x))
           (and (check-index (* 2 i) (1- k) c z x)
                (check-index (1+ (* 2 i)) (1- k) c z x)))
  :hints (("Goal" :in-theory (enable loop-0-invariant)
                  :use ((:instance check-high-check-index (j i))))))
                          
(local-defthmd loop-0-z-rewrite
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x))
           (and (equal (ag (* 2 i) z)
                       (if (= (slice (* 2 i) k x) 0)
                           1 0))
                (equal (ag (+ 1 (* 2 i)) z)
                       (if (= (slice (1+ (* 2 i)) k x) 0)
                           1 0))))
  :hints (("Goal" :in-theory (enable check-index)
           :use ((:instance loop-0-check-index (k (1+ k)))))))

(local-defthmd loop-0-c-rewrite-1
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x)
                (= (ag (* 2 i) z) 0))
           (equal (ag (* 2 i) c)
                  (lzcnt (slice (* 2 i) k x) (expt 2 k))))
  :hints (("Goal" :in-theory (enable check-index)
           :use ((:instance loop-0-check-index (k (1+ k)))))))

(local-defthmd loop-0-c-rewrite-2
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x)
                (= (ag (+ 1 (* 2 i)) z) 0))
           (equal (ag (+ 1 (* 2 i)) c)
                  (lzcnt (slice (+ 1 (* 2 i)) k x) (expt 2 k))))
  :hints (("Goal" :in-theory (enable check-index)
           :use ((:instance loop-0-check-index (k (1+ k)))))))

(defthmd loop-0-z
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x))
           (let ((z (as i
                         (logand1 (ag (+ (* 2 i) 1) z) (ag (* 2 i) z))
                         z)))
             (equal (ag i z)
                    (if (= (slice i (1+ k) x) 0) 1 0))))
  :hints (("Goal" :in-theory (enable loop-0-z-rewrite slice)
                  :nonlinearp t
                  :use ((:instance bits-plus-bits (n (1- (* (expt 2 (1+ k)) (1+ i))))
                                                  (p (*  (expt 2 k) (1+ (* 2 i))))
                                                  (m (*  (expt 2 (1+ k)) i)))))))

(local-defthm loop-0-c-1
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x)
                (not (= (slice (1+ (* 2 i)) k x) 0)))
           (let* ((c (as i
                         (if1 (ag (+ (* 2 i) 1) z)
                              (ag (* 2 i) c)
                              (ag (+ (* 2 i) 1) c))
                         c))
                  (c (as i
                         (setbitn (ag i c) 7 k (ag (+ (* 2 i) 1) z))
                         c)))
             (equal (ag i c)
                    (lzcnt (slice (+ (* 2 i) 1) k x) (expt 2 k)))))
  :hints (("Goal" :in-theory (e/d (bvecp-bits-0 bvecp slice cat) (lzcnt))
                  :use (loop-0-z-rewrite loop-0-c-rewrite-1 loop-0-c-rewrite-2
                        (:instance lzcnt-bound-2 (x (SLICE (+ 1 (* 2 I)) K X)) (w (EXPT 2 K))))
                  :nonlinearp t)))

(local-defthm loop-0-c-2
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x)
                (= (slice (1+ (* 2 i)) k x) 0)
                (not (= (slice (* 2 i) k x) 0)))
           (let* ((c (as i
                         (if1 (ag (+ (* 2 i) 1) z)
                              (ag (* 2 i) c)
                              (ag (+ (* 2 i) 1) c))
                         c))
                  (c (as i
                         (setbitn (ag i c) 7 k (ag (+ (* 2 i) 1) z))
                         c)))
             (equal (ag i c)
                    (+ (expt 2 k) (lzcnt (slice (* 2 i) k x) (expt 2 k))))))
  :hints (("Goal" :in-theory (e/d (bvecp-bits-0 bvecp slice cat) (lzcnt))
                  :use (loop-0-z-rewrite loop-0-c-rewrite-1 loop-0-c-rewrite-2
                        (:instance lzcnt-bound-2 (x (SLICE (* 2 I) K X)) (w (EXPT 2 K))))
                  :nonlinearp t)))

(local-defthm loop-0-c-3
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x)                
                (not (and (= (slice (* 2 i) k x) 0) (= (slice (1+ (* 2 i)) k x) 0))))
           (let* ((c (as i
                         (if1 (ag (+ (* 2 i) 1) z)
                              (ag (* 2 i) c)
                              (ag (+ (* 2 i) 1) c))
                         c))
                  (c (as i
                         (setbitn (ag i c) 7 k (ag (+ (* 2 i) 1) z))
                         c)))
             (equal (ag i c)
                    (lzcnt (slice i (1+ k) x) (expt 2 (1+ k))))))
  :hints (("Goal" :use (loop-0-c-1 loop-0-c-2 (:instance lzcnt-split-slice (k (1+ k)))))))

(defthmd loop-0-c
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x)                
                (not (= (slice i (1+ k) x) 0)))
           (let* ((c (as i
                         (if1 (ag (+ (* 2 i) 1) z)
                              (ag (* 2 i) c)
                              (ag (+ (* 2 i) 1) c))
                         c))
                  (c (as i
                         (setbitn (ag i c) 7 k (ag (+ (* 2 i) 1) z))
                         c)))
             (equal (ag i c)
                    (lzcnt (slice i (1+ k) x) (expt 2 (1+ k))))))
  :hints (("Goal" :in-theory (enable slice)
                  :nonlinearp t
                  :use (loop-0-c-3
                        (:instance bits-plus-bits (n (1- (* (expt 2 (1+ k)) (1+ i))))
                                                  (p (*  (expt 2 k) (1+ (* 2 i))))
                                                  (m (*  (expt 2 (1+ k)) i)))))))

(local-defthmd loop-0-check-next
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x))                
           (let* ((c (as i
                         (bits (if1 (ag (+ (* 2 i) 1) z)
                                    (ag (* 2 i) c)
                                    (ag (+ (* 2 i) 1) c))
                               6 0)
                         c))
                  (c (as i
                         (setbitn (ag i c) 7 k (ag (+ (* 2 i) 1) z))
                         c))
                  (z (as i
                         (logand1 (ag (+ (* 2 i) 1) z) (ag (* 2 i) z))
                         z)))
             (check-index i (1+ k) c z x)))
  :hints (("Goal" :in-theory (enable check-index)
                  :use (loop-0-c loop-0-z))))

(defthmd loop-0-step-lemma
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (< i (expt 2 (- 6 k)))
                (loop-0-invariant i (1+ k) c z x))               
           (let* ((c (as i
                         (bits (if1 (ag (+ (* 2 i) 1) z)
                                    (ag (* 2 i) c)
                                    (ag (+ (* 2 i) 1) c))
                               6 0)
                         c))
                  (c (as i
                         (setbitn (ag i c) 7 k (ag (+ (* 2 i) 1) z))
                         c))
                  (z (as i
                         (logand1 (ag (+ (* 2 i) 1) z) (ag (* 2 i) z))
                         z)))
             (loop-0-invariant (1+ i) (1+ k) c z x)))
  :hints (("Goal" :in-theory (enable loop-0-invariant)
                  :use (loop-0-check-next))))

(defthmd loop-0-induct
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (= n (expt 2 (- 6 k)))
                (natp i)
                (<= i n)
                (loop-0-invariant i (1+ k) c z x))
           (mv-let (c z) (clz128-loop-0 i n k c z)
             (loop-0-invariant n (1+ k) c z x)))
  :hints (("Subgoal *1/4" :use (loop-0-step-lemma))))

(defthmd loop-0-lemma
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (= n (expt 2 (- 6 k)))
                (loop-0-invariant 0 (1+ k) c z x))
           (mv-let (c z) (clz128-loop-0 0 n k c z)
             (loop-0-invariant n (1+ k) c z x)))
  :hints (("Goal" :use ((:instance loop-0-induct (i 0))))))

;; Note that

;;  loop-0-invariant(n, k+1, c, z, x) = check-low(n, k+1, c, z, x) = check-all(k+1, c, z, x)            

;; and

;;  loop-0-invariant(0, k+1, c, z, x) = check-high(0, k+1, c, z, x).

;; In fact, check-high(0, k+1, c, z, x) is equivalent to check-all(k, c, z, x).
;; We shall require only half of this result:

(local-defthm why-do-i-need-this?
  (implies (and (natp i) (natp m) (< i m))
           (< (1+ (* 2 i)) (* 2 m)))
  :rule-classes ())

(defthmd check-high-low-induct
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (natp i)
                (check-all k c z x))
           (check-high i (1+ k) c z x))
  :hints (("Subgoal *1/4" :nonlinearp t
                          :in-theory (disable check-all-check-index)
                          :use ((:instance why-do-i-need-this? (m (expt 2 (- 6 k))))
                                (:instance check-all-check-index (j (* 2 i)))
                                (:instance check-all-check-index (j (1+ (* 2 i))))))))

(defthmd check-high-low
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (check-all k c z x))
           (check-high 0 (1+ k) c z x))
  :hints (("Goal" :use ((:instance check-high-low-induct (i 0))))))

;; loop-0-lemma may now be restated as follows, showing that check-all(k, c, z, x) is
;; an invariant of loop-1:

(defthmd loop-1-step-lemma
  (implies (and (bvecp x 128)
                (natp k)
                (< k 7)
                (= n (expt 2 (- 6 k)))
                (check-all k c z x))
           (mv-let (c z) (clz128-loop-0 0 n k c z)
             (check-all (1+ k) c z x)))
  :hints (("Goal" :use (loop-0-lemma check-high-low)
                  :in-theory (enable check-all loop-0-invariant))))

(defthmd loop-1-induct
  (implies (and (bvecp x 128)
                (natp k)
                (<= k 7)
                (check-all k c z x))
           (mv-let (n c z) (clz128-loop-1 k (/ 128 (expt 2 k)) c z)
             (declare (ignore n))
             (check-all 7 c z x)))
  :hints (("Subgoal *1/4" :use ((:instance loop-1-step-lemma (n (expt 2 (- 6 k))))))))

(defthmd loop-1-lemma
  (implies (and (bvecp x 128)
                (check-all 0 c z x))
           (mv-let (n c z) (clz128-loop-1 0 128 c z)
             (declare (ignore n))
             (check-all 7 c z x)))
  :hints (("Goal" :use ((:instance loop-1-induct (k 0))))))

;; It remains to show that loop-2 establishes check-all(0, c, z, x):

(defthmd loop-2-step-lemma
  (implies (and (bvecp x 128)
                (natp i)
                (< i 128)
                (check-low i 0 c z x))
           (let ((z (as i (lognot1 (bitn x i)) z))
                 (c (as i 0 c)))
             (check-low (1+ i) 0 c z x)))
  :hints (("Goal" :in-theory (enable slice check-index))))

(defthm loop-2-induct
  (implies (and (bvecp x 128)
                (natp i)
                (< i 128)
                (check-low i 0 c z x))
           (mv-let (z c) (clz128-loop-2 i x z c)
             (check-low 128 0 c z x)))
  :hints (("Goal" :induct (clz128-loop-2 i x z c))
          ("Subgoal *1/1" :use (loop-2-step-lemma))))

(defthmd loop-2-lemma
  (implies (bvecp x 128)
           (mv-let (z c) (clz128-loop-2 0 x z c)
             (check-all 0 c z x)))
  :hints (("Goal" :in-theory (enable check-all) :use ((:instance loop-2-induct (i 0))))))

;; Our main result follows from loop-1-lemma, loop-2-lemma, check-all-lzcnt,
;; and lzcnt-expo:

(defthmd clz128-lzcnt
  (implies (and (bvecp x 128) (> x 0))
           (equal (clz128 x) (lzcnt x 128)))
  :hints (("Goal" :expand ((clz128 x))
                  :use ((:instance loop-2-lemma (z ()) (c ()))
                        (:instance loop-1-lemma (z (mv-nth 0 (clz128-loop-2 0 x () ())))
			                        (c (mv-nth 1 (clz128-loop-2 0 x () ()))))
                        (:instance check-all-lzcnt
			  (z (mv-nth 2 (clz128-loop-1 0 128
			                           (mv-nth 1 (clz128-loop-2 0 x () ()))
                                                   (mv-nth 0 (clz128-loop-2 0 x () ())))))
			  (c (mv-nth 1 (clz128-loop-1 0 128
			                           (mv-nth 1 (clz128-loop-2 0 x () ()))
                                                   (mv-nth 0 (clz128-loop-2 0 x ()
                                                                         ()))))))))))

(defthm clz128-0
  (equal (clz128 0) 127)
  :hints (("Goal" :in-theory (enable clz128))))
						   
(defthmd clz128-expo
  (implies (bvecp x 128)
           (equal (clz128 x) (- 127 (expo x))))
  :hints (("Goal" :cases ((= x 0)) :in-theory (enable clz128-lzcnt lzcnt-expo))))

