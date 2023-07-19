(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

;; Our objective is to prove that the harmonic series diverges to infinity.
;; The nth partial sum of the series is computed as follows:

(defun harmonic-sum (n)
  (if (zp n)
      0
    (+ (/ n) (harmonic-sum (1- n)))))

;; Divergence to infinity means that for any given m, there exists N such that
;; if n >= N, then (harmonic-sum n) > m.  We shall show that this holds for
;; N = (expt 2 (* 2 m)):

;; (defthm harmonic-series-diverges
;;   (implies (and (natp m) (natp n) (>= n (expt 2 (* 2 m))))
;;                  (> (harmonic-sum n)
;;                     m)))

;; Decomposition of a partial sum of the series:

(defun harmonic-extend (m n)
  (if (and (natp m) (natp n) (< m n))
      (+ (/ n) (harmonic-extend m (1- n)))
    0))

(defthmd harmonic-sum-decomp
  (implies (and (natp m) (natp n) (<= m n))
	   (equal (+ (harmonic-sum m) (harmonic-extend m n))
		  (harmonic-sum n))))

;; A lower bound on harmonic-extend, proved by induction on n:

(defthmd harmonic-extend-lower-bound
  (implies (and (natp m) (natp n) (natp p) (<= m n) (<= n p))
	   (>= (harmonic-extend m n) (/ (- n m) p)))
  :hints (("Goal" :nonlinearp t)))

;; A special case of the above lemma:

(defthmd harmonic-extend-lower-bound-corollary
  (implies (posp k)
	   (>= (harmonic-extend (expt 2 (1- k)) (expt 2 k))
	       1/2))
  :hints (("Goal" :use ((:instance harmonic-extend-lower-bound (m (expt 2 (1- k)))
				                               (n (expt 2 k))
				                               (p (expt 2 k)))))))

;; We derive a lower bound on (harmonic-sum (expt 2 k)) by induction on k:

(defun nat-induct (k)
  (if (zp k)
      1
    (* k (nat-induct (1- k)))))

(defthmd harmonic-sum-lower-bound
  (implies (posp k)
	   (>= (harmonic-sum (expt 2 k))
	       (1+ (/ k 2))))
  :hints (("Goal" :induct (nat-induct k))
	  ("Subgoal *1/2" :use (harmonic-extend-lower-bound-corollary
				(:instance harmonic-sum-decomp (m (expt 2 (1- k)))
					                    (n (expt 2 k)))))))

;; The desired result follows, once we observe that the partial sum is increasing:

(defthmd harmonic-sum-monotone
  (implies (and (natp m) (natp n) (> n m))
	   (> (harmonic-sum n) (harmonic-sum m)))
  :hints (("Goal" :induct (nat-induct n))))

(defthm harmonic-series-diverges
  (implies (and (natp m) (natp n) (>= n (expt 2 (* m 2))))
	   (> (harmonic-sum n)
	      m))
  :hints (("Goal" :use ((:instance harmonic-sum-monotone (m (expt 2 (* 2 m))))
			(:instance harmonic-sum-lower-bound (k (* 2 m)))))))
