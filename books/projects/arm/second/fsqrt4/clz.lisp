(in-package "RTL")

(include-book "special")

;;----------------------------------------------------------------------------------
;; Objective
;;----------------------------------------------------------------------------------

;; This is our objective:

;; (defthmd clz-expo
;;   (implies (and (bvecp s 53) (> s 0))
;;            (equal (clz53 s) (- 52 (expo s)))))

;; The above will be reformulated in terms of the following function, which computes
;; the number of leading zeroes of a bit vector x of width w:

(defun lzcnt (x w)
  (if (or (zp w) (= (bitn x (1- w)) 1))
       0
    (1+ (lzcnt x (1- w)))))

;; lzcnt is related to expo as follows:

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

;; The desired result will be derived from the following:

;; (defthmd clz-lzcnt
;;   (implies (and (bvecp s 53) (> s 0))
;;            (equal (clz53 s) (lzcnt (* (expt 2 11) s) 64))))

;; gl proves the following in about 13 minutes:
#|
(local (acl2::def-gl-thm foo
  :hyp  (and (bvecp s 53) (> s 0))
  :concl (equal (clz53 s) (lzcnt (* (expt 2 11) s) 64))
  :g-bindings (gl::auto-bindings (:nat s 53))))
|#
;; But we prefer the following proof, which may be adapted to bit vectors of
;; arbitrary width.

;;----------------------------------------------------------------------------------
;; Some properties of lzcnt
;;----------------------------------------------------------------------------------

(defthm lzcnt-bound-1
  (implies (natp w)
           (<= (lzcnt x w) w))
  :rule-classes ())

(defthm lzcnt-bound
  (implies (and (natp w) (not (= (bits x (1- w) 0) 0)))
           (< (lzcnt x w) w))
  :rule-classes ()
  :hints (("Goal" :induct (lzcnt x w))
          ("Subgoal *1/2" :use ((:instance lzcnt-bound-1 (w (1- w)))
                                (:instance bitn-plus-bits (n (1- w)) (m 0))
                                (:instance bitn-0-1 (n (1- w)))))))

(defthmd lzcnt-bits
  (implies (and (natp n) (natp w) (<= w (1+ n)))
           (equal (lzcnt (bits x n 0) w)
                  (lzcnt x w)))
  :hints (("Goal" :induct (nats w))
          ("Subgoal *1/2" :use ((:instance bitn-0-1 (n (1- w))))
                          :in-theory (enable bitn-bits))))

(defthmd lzcnt-bvecp
  (implies (and (natp n) (natp w) (>= w n) (bvecp x n))
           (equal (lzcnt x w)
                  (+ (- w n) (lzcnt x n))))
  :hints (("Subgoal *1/1" :cases ((= n w)) :in-theory (enable bvecp-monotone))))

(defthmd lzcnt-cat-1
  (implies (and (natp x) (natp y) (natp m) (natp n) (> m 0)
                (= (bitn x (1- m)) 1))
           (equal (lzcnt (cat x m y n) (+ m n)) (lzcnt x m)))
  :hints (("Goal" :in-theory (enable bitn-cat bits-cat))))

(defthmd lzcnt-cat-2
  (implies (and (natp x) (natp y) (natp m) (natp n) (> m 0)
                (= (bits x (1- m) 0) 0))
           (equal (lzcnt (cat x m y n) (+ m n))
                  (+ m (lzcnt y n))))
  :hints (("Goal" :in-theory (enable cat lzcnt-bits)
                  :cases ((= n 0))
                  :use ((:instance lzcnt-bvecp (x (bits y (1- n) 0)) (w (+ m n)))))))
(defthmd lzcnt-cat-3
  (implies (and (natp x) (natp y) (natp m) (natp n) (> m 0)
                (= (bitn x (1- m)) 0) (not (= (bits x (1- m) 0) 0)))
           (equal (lzcnt (cat x m y n) (+ m n))
                  (1+ (lzcnt (cat x (1- m) y n) (+ (1- m) n)))))
  :hints (("Goal" :in-theory (enable bitn-bits bitn-cat bits-cat)
                  :use ((:instance lzcnt-bits (x (cat x m y n)) (w (+ n m -1))
                                   (n (+ n m -2)))))))

(defthmd lzcnt-cat
  (implies (and (natp x) (natp y) (natp m) (natp n))
           (equal (lzcnt (cat x m y n) (+ m n))
                  (if (= (bits x (1- m) 0) 0)
                      (+ m (lzcnt y n))
                    (lzcnt x m))))
  :hints (("Goal" :induct (nats m))
          ("Subgoal *1/1" :in-theory (enable lzcnt-bits bitn-bits cat))
          ("Subgoal *1/2" :use (lzcnt-cat-1 lzcnt-cat-2 lzcnt-cat-3
                                (:instance bitn-plus-bits (n (1- m)) (m 0))
                                (:instance bitn-0-1 (n (1- m)))))))

;;----------------------------------------------------------------------------------
;; Outer loop invariant
;;----------------------------------------------------------------------------------

;; We shall define an invariant for the main loop, clz53-loop-1, i.e., a predicate
;; loop-1-inv(k, c, z, x) that is satisfied after k iterations of the loop, where
;; 0 <= k <= 6.  We must prove the following properties of loop-1-inv:

;; (1) Upon entering the loop, loop-1-inv(0, c, z, x) holds.

;; (2) If loop-1-inv(k, c, z, x) holds after k iterations,
;;     then loop-1-inv(k+1, c, z, x) holds after k+1 iterations.

;; (3) loop-1-inv(6, c, z, x) implies c[0] = lzcnt(x, 64).

;; Then, by induction, loop-1-inv(k, c, z, x) holds for 0 <= k <= 6, and the
;; desired result follows.

;; After k iterations, the bit vector x is conceptually partitioned into slices of 
;; width 2^k.  The ith slice is extracted as follows:

(defund slice (i k x)
  (bits x (1- (* (expt 2 k) (1+ i))) (*  (expt 2 k) i)))

;; The array entries z[i] and c[i] are related to slice(i, k, x) as follows:
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

;; The loop invariant checks all 2^(6-k) indices:

 (defund loop-1-inv (k c z x)
  (check-low (expt 2 (- 6 k)) k c z x))

;; For k = 6, there is only one slice, which is x itself.  The proof of (3)
;; is trivial:

(defthm loop-1-final
  (implies (and (bvecp x 64)
                (> x 0)
                (loop-1-inv 6 c z x))
           (equal (ag 0 c) (lzcnt x 64)))
  :hints (("Goal" :in-theory (enable slice check-index loop-1-inv))))

;;----------------------------------------------------------------------------------
;; Outer loop initialization: proof of (1)
;;----------------------------------------------------------------------------------

;; We must show that loop-2 establishes loop-1-inv(0, c, z, x):

;; (defthmd loop-1-init
;;   (implies (bvecp x 64)
;;            (mv-let (z c) (clz53-loop-2 0 x z c)
;;              (loop-1-inv 0 c z x))))

;; The invariant for clz53-loop-2 is check-low(i, 0, c, z, x), i.e., this
;; predicate is true after i iterations of the loop.  Since it holds vacuously
;; for i = 0 and check-low(64, 0, c, z, x) = loop-1-inv(0, c, z, x), we need only
;; show that the invariant is preserved by each iteration (loop-2-step
;; below).  The desired result, loop-1-init, then followis by induction.
	     
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

(defthm loop-2-step
  (implies (and (bvecp x 64)
                (natp i)
                (< i 64)
                (check-low i 0 c z x))
           (let ((z (as i (lognot1 (bitn x i)) z))
                 (c (as i 0 c)))
             (check-low (1+ i) 0 c z x)))
  :hints (("Goal" :in-theory (enable slice check-index))))

(in-theory (enable clz53-loop-2))

(defthm loop-2-induct
  (implies (and (bvecp x 64)
                (natp i)
                (< i 64)
                (check-low i 0 c z x))
           (mv-let (z c) (clz53-loop-2 i x z c)
             (check-low 64 0 c z x)))
  :hints (("Goal" :induct (clz53-loop-2 i x z c))
          ("Subgoal *1/1" :use (loop-2-step))))

(defthmd loop-1-init
  (implies (bvecp x 64)
           (mv-let (z c) (clz53-loop-2 0 x z c)
             (loop-1-inv 0 c z x)))
  :hints (("Goal" :in-theory (enable loop-1-inv) :use ((:instance loop-2-induct (i 0))))))

;;----------------------------------------------------------------------------------
;; Inner loop invariant
;;----------------------------------------------------------------------------------

;; To prove (2), we must show that cl353-loop-0 preserves the loop invariant:

;; (defthmd loop-1-step
;;   (implies (and (bvecp x 64)
;;                 (natp k)
;;                 (< k 6)
;;                 (= n (expt 2 (- 5 k)))
;;                 (loop-1-inv k c z x))
;;            (mv-let (c z) (clz53-loop-0 0 n k c z)
;;              (loop-1-inv (1+ k) c z x))))

;; This lemma will also be proved by induction.  This will require a loop invariant
;; loop-0-inv(i, k, c, z, x) for clz53-loop-0, which holds after i iterations of clz53-loop-0
;; during the (k+1)st iteration of clz53-loop-1.  This invariant must satisfy the following:

;; (a) loop-1-inv(k, c, z, x) implies loop-0-inv(0, k, c, z, x).

;; (b) If loop-0-inv(i. k, c, z, x) holds after i iterations of clz53-loop-0,
;;     then loop-0-inv(i+1, k, c, z, x) holds after i+1 iterations.

;; (c) loop-0-inv(n, k, c, z, x) implies loop-1-inv(k+1, c, z, x)

;; On iteration i, c[i] and z[i] are computed.  Thus, part of the invariant is
;; check-low(i, k+1, c, z, x).  But the invariant must also ensure that the arrays hold the
;; information required to compute the remaining entries:

(defun check-high (i k c z x)
  (declare (xargs :measure (nfix (- (expt 2 (- 5 k)) i))))
  (if (and (natp k) (< k 6) (natp i) (< i (expt 2 (- 5 k))))
      (and (check-index (* 2 i) k c z x)
           (check-index (1+ (* 2 i)) k c z x)
           (check-high (1+ i) k c z x))
    t))

(defund loop-0-inv (i k c z x)
  (and (check-low i (1+ k) c z x)
       (check-high i k c z x)))

;; (c) is trivial:

(defthmd loop-0-final
  (implies (and (natp k)
                (< k 6)
		(loop-0-inv (expt 2 (- 5 k)) k c z x))
	   (loop-1-inv (1+ k) c z x))
  :hints (("Goal" :in-theory (enable loop-0-inv loop-1-inv))))

;;----------------------------------------------------------------------------------
;; Inner loop initialization: proof of (a)
;;----------------------------------------------------------------------------------

(defthmd check-low-check-index
  (implies (and (natp i)
                (natp j)
                (< j i)
                (check-low i k c z x))
           (check-index j k c z x)))

(defthm loop-1-inv-check-index
  (implies (and (natp k)
                (<= k 6)
                (natp j)
                (< j (expt 2 (- 6 k)))
                (loop-1-inv k c z x))
           (check-index j k c z x))
  :hints (("Goal" :in-theory (enable loop-1-inv)
                  :use ((:instance check-low-check-index (i (expt 2 (- 6 k))))))))

(defthm why-do-i-need-this?
  (implies (and (natp i) (natp m) (< i m))
           (< (1+ (* 2 i)) (* 2 m)))
  :rule-classes ())

(defthmd loop-0-init-induct
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (natp i)
                (loop-1-inv k c z x))
           (check-high i k c z x))	   
  :hints (("Subgoal *1/4" :use ((:instance why-do-i-need-this? (m (expt 2 (- 5 k))))))))

(defthmd loop-0-init
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (loop-1-inv k c z x))
           (loop-0-inv 0 k c z x))
  :hints (("Goal" :in-theory (enable loop-0-inv)
                  :use ((:instance loop-0-init-induct (i 0))))))

;;----------------------------------------------------------------------------------
;; Inner loop step: proof of (b)
;;----------------------------------------------------------------------------------

(defthmd lzcnt-split-slice
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (natp i)
                (< i (expt 2 (- 5 k))))
           (equal (lzcnt (slice i (1+ k) x) (expt 2 (1+ k)))
                  (if (= (slice (1+ (* 2 i)) k x) 0)
                      (+ (expt 2 k) (lzcnt (slice (* 2 i) k x) (expt 2 k)))
                    (lzcnt (slice (1+ (* 2 i)) k x) (expt 2 k)))))
  :hints (("Goal" :in-theory (enable cat bitn-bits slice)
                  :nonlinearp t
                  :use ((:instance lzcnt-cat (x (slice (1+ (* 2 i)) k x))
                                               (y (slice (* 2 i) k x))
                                               (m (expt 2 k))
                                               (n (expt 2 k)))
                        (:instance bits-plus-bits (n (1- (* (expt 2 (1+ k)) (1+ i))))
                                                  (p (*  (expt 2 k) (1+ (* 2 i))))
                                                  (m (*  (expt 2 (1+ k)) i)))))))

(defthmd loop-0-inv-rewrite
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (natp i)
                (< i (expt 2 (- 5 k)))
                (loop-0-inv i k c z x))
           (and (equal (ag (* 2 i) z)
                       (if (= (slice (* 2 i) k x) 0)
                           1 0))
                (equal (ag (+ 1 (* 2 i)) z)
                       (if (= (slice (1+ (* 2 i)) k x) 0)
                           1 0))
		(implies (= (ag (* 2 i) z) 0)
		         (equal (ag (* 2 i) c)
                                (lzcnt (slice (* 2 i) k x) (expt 2 k))))
		(implies (= (ag (+ 1 (* 2 i)) z) 0)
		         (equal (ag (+ 1 (* 2 i)) c)
                                (lzcnt (slice (+ 1 (* 2 i)) k x) (expt 2 k))))))
  :hints (("Goal" :in-theory (enable loop-0-inv check-high check-index))))

(defthmd loop-0-z
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (natp i)
                (< i (expt 2 (- 5 k)))
                (loop-0-inv i k c z x))
           (let ((z (as i
                         (logand1 (ag (+ (* 2 i) 1) z) (ag (* 2 i) z))
                         z)))
             (equal (ag i z)
                    (if (= (slice i (1+ k) x) 0) 1 0))))
  :hints (("Goal" :in-theory (enable loop-0-inv-rewrite slice)
                  :nonlinearp t
                  :use ((:instance bits-plus-bits (n (1- (* (expt 2 (1+ k)) (1+ i))))
                                                  (p (*  (expt 2 k) (1+ (* 2 i))))
                                                  (m (*  (expt 2 (1+ k)) i)))))))

(defthmd loop-0-c
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (natp i)
                (< i (expt 2 (- 5 k)))
                (loop-0-inv i k c z x)                
                (not (= (slice i (1+ k) x) 0)))
           (let* ((c (as i
                         (if1 (ag (+ (* 2 i) 1) z)
                              (ag (* 2 i) c)
                              (ag (+ (* 2 i) 1) c))
                         c))
                  (c (as i
                         (setbitn (ag i c) 6 k (ag (+ (* 2 i) 1) z))
                         c)))
             (equal (ag i c)
                    (lzcnt (slice i (1+ k) x) (expt 2 (1+ k))))))
  :hints (("Goal" :in-theory (e/d (bvecp-bits-0 bvecp slice cat) (lzcnt))
                  :nonlinearp t
                  :use (loop-0-inv-rewrite lzcnt-split-slice
                        (:instance lzcnt-bound (x (slice (* 2 i) k x)) (w (expt 2 k)))
                        (:instance lzcnt-bound (x (slice (+ 1 (* 2 i)) k x)) (w (expt 2 k)))
			(:instance bits-plus-bits (n (1- (* (expt 2 (1+ k)) (1+ i))))
                                                  (p (*  (expt 2 k) (1+ (* 2 i))))
                                                  (m (*  (expt 2 (1+ k)) i)))))))

(defthm check-high-inv
  (implies (and (natp i) (not (zp j)) (<= i j) (check-high j k c z x))
           (check-high j k (as i v c) (as i w z) x)))

(defthmd loop-0-step
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (natp i)
                (< i (expt 2 (- 5 k)))
                (loop-0-inv i k c z x))               
           (let* ((c (as i
                         (bits (if1 (ag (+ (* 2 i) 1) z)
                                    (ag (* 2 i) c)
                                    (ag (+ (* 2 i) 1) c))
                               6 0)
                         c))
                  (c (as i
                         (setbitn (ag i c) 6 k (ag (+ (* 2 i) 1) z))
                         c))
                  (z (as i
                         (logand1 (ag (+ (* 2 i) 1) z) (ag (* 2 i) z))
                         z)))
             (loop-0-inv (1+ i) k c z x)))
  :hints (("Goal" :in-theory (enable check-index loop-0-inv)
           :use (loop-0-c loop-0-z))))

;;----------------------------------------------------------------------------------
;; Inner loop induction
;;----------------------------------------------------------------------------------

(defthmd loop-0-induct
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (= n (expt 2 (- 5 k)))
                (natp i)
                (<= i n)
                (loop-0-inv i k c z x))
           (mv-let (c z) (clz53-loop-0 i n k c z)
             (loop-0-inv n k c z x)))
  :hints (("Goal" :in-theory (enable clz53-loop-0))
          ("Subgoal *1/4" :use (loop-0-step))))

(defthmd loop-0-lemma
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (= n (expt 2 (- 5 k)))
                (loop-0-inv 0 k c z x))
           (mv-let (c z) (clz53-loop-0 0 n k c z)
             (loop-0-inv n k c z x)))
  :hints (("Goal" :use ((:instance loop-0-induct (i 0))))))

;;----------------------------------------------------------------------------------
;; Outer loop step: proof of (2)
;;----------------------------------------------------------------------------------

(defthmd loop-1-step
  (implies (and (bvecp x 64)
                (natp k)
                (< k 6)
                (= n (expt 2 (- 5 k)))
                (loop-1-inv k c z x))
           (mv-let (c z) (clz53-loop-0 0 n k c z)
             (loop-1-inv (1+ k) c z x)))
  :hints (("Goal" :use (loop-0-lemma loop-0-init)
                  :in-theory (enable loop-1-inv loop-0-inv))))

;;----------------------------------------------------------------------------------
;; Outer loop induction
;;----------------------------------------------------------------------------------

(defthmd loop-1-induct
  (implies (and (bvecp x 64)
                (natp k)
                (<= k 6)
                (loop-1-inv k c z x))
           (mv-let (n c z) (clz53-loop-1 k (/ 64 (expt 2 k)) c z)
             (declare (ignore n))
             (loop-1-inv 6 c z x)))
  :hints (("Goal" :in-theory (enable clz53-loop-1))
          ("Subgoal *1/4" :use ((:instance loop-1-step (n (expt 2 (- 5 k))))))))

(defthmd loop-1-lemma
  (implies (and (bvecp x 64)
                (loop-1-inv 0 c z x))
           (mv-let (n c z) (clz53-loop-1 0 64 c z)
             (declare (ignore n))
             (loop-1-inv 6 c z x)))
  :hints (("Goal" :use ((:instance loop-1-induct (k 0))))))

;;----------------------------------------------------------------------------------
;; Final result
;;----------------------------------------------------------------------------------

;; The following result combines loop-1-lemma, loop-1-init, loop-1-final,

(defthmd clz-lzcnt
  (implies (and (bvecp s 53) (> s 0))
           (equal (clz53 s) (lzcnt (* (expt 2 11) s) 64)))
  :hints (("Goal" :expand ((clz53 s))
                  :in-theory (enable bvecp cat)
                  :use ((:instance loop-1-init (x (* (expt 2 11) s)) (z ()) (c ()))
                        (:instance loop-1-lemma (x (* (expt 2 11) s))
			                        (z (mv-nth 0 (clz53-loop-2 0 (* (expt 2 11) s) () ())))
			                        (c (mv-nth 1 (clz53-loop-2 0 (* (expt 2 11) s) () ()))))
                        (:instance loop-1-final
			  (x (* (expt 2 11) s))
			  (z (mv-nth 2 (clz53-loop-1 0 64
			                             (mv-nth 1 (clz53-loop-2 0 (* (expt 2 11) s) () ()))
                                                     (mv-nth 0 (clz53-loop-2 0 (* (expt 2 11) s) () ())))))
			  (c (mv-nth 1 (clz53-loop-1 0 64
			                             (mv-nth 1 (clz53-loop-2 0 (* (expt 2 11) s) () ()))
                                                     (mv-nth 0 (clz53-loop-2 0 (* (expt 2 11) s) () ()))))))))))

(defthmd clz-expo
  (implies (and (bvecp s 53) (> s 0))
           (equal (clz53 s) (- 52 (expo s))))
  :hints (("Goal" :use (clz-lzcnt
                        (:instance lzcnt-expo (x (setbits 0 64 63 11 s)) (w 64))
			(:instance expo-shift (x s) (n 11)))			
                  :in-theory (enable bvecp cat))))










