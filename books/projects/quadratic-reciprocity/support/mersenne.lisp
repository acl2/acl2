(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; This book illustrates a simple application of the theory of quadratic
;; residues to the Mersenne prime problem.  We show that certain Mersenne
;; numbers may be factored by applying a theorem of Euler, which combines
;; two results: (1) Euler's criterion for quadratic residues and (2) the
;; second supplement to the law of quadratic reciprocity, which computes
;; the quadratic character of 2 modulo an odd prime p.

;; The two theorems and the relevant definitions are contained in the
;; book "gauss":

(include-book "gauss")

(comp t)

; We skip some forms by default, because they take a long time to run.
(defmacro maybe-skip (x)
; Redefine to be x if you want to execute forms inside (maybe-skip ...).
  (declare (ignore x))
  '(value-triple nil))

;; For a prime p, the Mersenne number Mp is defined to be 2^p-1:

(defun m (p) (1- (expt 2 p)))

;; We would like to determine the primality of Mp.  For small values of p,
;; this can be done simply by executing the function primep:

(defthm mersenne-19
    (primep (m 19)))

;;[Time: 0.14 seconds]

(maybe-skip
(defthm mersenne-31
    (primep (m 31)))
)

;;[Time: 14 minutes]

;; The timing of mersenne-31 suggests that the computation of mersenne-61
;; is intractable:

;;(defthm mersenne-61
;;    (primep (m 61)))

;;[Time: 14 billion minutes?]

;; Naturally, we can handle larger composites than primes:

(defthm mersenne-23
    (not (primep (m 23))))

;;[Time: .00 seconds]

(maybe-skip
(defthm mersenne-67
    (not (primep (m 67))))
)

;;[Time: 115 seconds]

(maybe-skip
(defthm mersenne-999671
    (not (primep (m 999671))))
)

;;[Time: 19 minutes]

;;(defthm mersenne-19876271
;;    (not (primep (m 19876271))))

;;[Error: Attempt to create an integer that is too large to represent.]

;; There is an obvious optimization of this procedure, based on
;; the observation that if n has a proper divisor, then it has one
;; that is at most sqrt(n).  Thus, we define an alternative to
;; the function least-divisor that stops at sqrt(n), and
;; establish a rewrite rule:

(defun least-divisor-2 (k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (integerp n)
	   (integerp k)
	   (< 1 k)
	   (<= k n))
      (if (> (* k k) n)
	  n
	(if (divides k n)
	    k
	  (least-divisor-2 (1+ k) n)))
    nil))

(comp t)

(local-defthm hack-1
  (implies (and (not (zp a)) (not (zp b)) (not (zp c)) (not (zp d))
                (<= a c) (<= b d))
           (<= (* a b) (* c b)))
  :rule-classes ())

(local-defthm hack-2
  (implies (and (not (zp a)) (not (zp b)) (not (zp c)) (not (zp d))
                (<= a c) (<= b d))
           (<= (* c b) (* c d)))
  :rule-classes ())

(local-defthm hack-3
  (implies (and (not (zp a)) (not (zp b)) (not (zp c)) (not (zp d))
                (<= a c) (<= b d))
           (<= (* a b) (* c d)))
  :hints (("Goal" :use (hack-1 hack-2)
                  :in-theory (theory 'minimal-theory))))

(local-defthm hack-4
  (implies (and (not (zp k)) (not (zp ld)) (<= k ld))
           (<= (* k k) (* ld ld)))
  :hints (("Goal" :use ((:instance hack-3 (a k) (b k) (c ld) (d ld)))))
  :rule-classes ())

(defthm least-divisor-rewrite-lemma-1
    (implies (and (integerp n)
		  (integerp k)
		  (< 1 k)
		  (<= k n)
		  (<= (* (least-divisor k n) (least-divisor k n)) n))
	     (equal (least-divisor k n)
		    (least-divisor-2 k n)))
  :rule-classes ()
  :hints (("Subgoal *1/7" :use (least-divisor-divides (:instance hack-4 (ld (least-divisor (1+ k) n)))))
	  ("Subgoal *1/1" :use (least-divisor-divides (:instance hack-4 (ld (least-divisor (1+ k) n)))))))

(local-defthm hack-5
  (implies (and (not (zp a)) (not (zp n))
                (<= 1 (/ n a)))
           (<= a n))
  :rule-classes ())

(defthm least-divisor-rewrite-lemma-2
    (implies (and (integerp n)
		  (> n 1)
		  (not (= n (least-divisor 2 n))))
	     (<= (* (least-divisor 2 n) (least-divisor 2 n)) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance least-divisor-divides (k 2))
			(:instance least-divisor-is-least (k 2) (d (/ n (least-divisor 2 n))))
                        (:instance hack-5 (a (* (least-divisor 2 n) (least-divisor 2 n))))))))

(defthm least-divisor-rewrite-lemma-3
    (implies (and (integerp n)
		  (integerp k)
		  (< 1 k)
		  (<= k n)
		  (= n (least-divisor k n)))
	     (= n (least-divisor-2 k n)))
  :rule-classes ()
  :hints (("Goal" :use (least-divisor-divides
			(:instance least-divisor-is-least (d (least-divisor-2 2 n)))))))

(defthm least-divisor-rewrite
    (equal (least-divisor 2 n)
	   (least-divisor-2 2 n))
  :hints (("Goal" :use (least-divisor-rewrite-lemma-2
			(:instance least-divisor-rewrite-lemma-3 (k 2))
			(:instance least-divisor-rewrite-lemma-1 (k 2))))))

;; In order to arrange that the more efficient variant is executed, we must
;; disable the executable counterparts of primep and least-proper-divisor
;; and enable the logical function primep.  This allows us to establish
;; primality somewhat more efficiently:

(in-theory (enable primep))

(in-theory (disable (primep) (least-divisor)))

(defthm mersenne-31-revisited
    (primep (m 31)))

;;[Time: .05 seconds]

(maybe-skip
(defthm mersenne-61
    (primep (m 61)))
)

;;[Time: 18  minutes]

;; However, the above optimization does not help at all in the composite case.
;; In the special case where mod(p,4) = 3 and 2*p+1 is prime, the following
;; theorem may be used.  This theorem is attributed to Euler in Hardy and
;; Wright, where it appears as Theorem 103.  It is an immediate comsequence
;; of Euler's Criterion and the Second Supplement.

(defthm theorem-103
    (implies (and (primep p)
		  (= (mod p 4) 3)
		  (primep (1+ (* 2 p))))
	     (divides (1+ (* 2 p)) (m p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance second-supplement (p (1+ (* 2 p))))
			(:instance euler-criterion (m 2) (p (1+ (* 2 p))))
			(:instance mod-sum (a 1) (b (* 2 p)) (n 8))
			(:instance mod-prod (k 2) (m p) (n 4))
			(:instance divides-leq (x (1+ (* 2 p))) (y 2))
			(:instance divides-mod-equal (a (expt 2 p)) (b 1) (n (1+ (* 2 p))))))))

;; With the exception of p = 3 (in which case Mp = 2*p+1), Mp is composite
;; for any p satisfying the hypothesis of theorem-103:

(local-defthm hack-6
  (implies (and (not (zp a))
                (>= a (* 4 (1- p)))
                (integerp p)
		(> p 3))
	     (>= (* 2 a) (* 4 p)))
  :rule-classes ())

(local-defthm hack-7
  (implies (and (>= (expt 2 (1- p)) (* 4 (1- p)))
                (integerp p)
		(> p 3))
	     (>= (expt 2 p) (* 4 p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-6 (a (expt 2 (1- p))))))))

(local-defthm hack-8
  (implies (and (integerp p)
		(> p 3))
	     (>= (expt 2 p) (* 4 p)))
  :rule-classes ()
  :hints (("Goal" :induct (fact p))
          ("Subgoal *1/2" :use hack-7)))

(local-defthm hack-9
    (implies (and (integerp p)
		  (> p 3))
	     (> (* 4 p) (* 2 (1+ p))))
  :rule-classes ())

(defthm expt-2-p-bnd
    (implies (and (integerp p)
		  (> p 3))
	     (> (expt 2 p) (* 2 (1+ p))))
  :rule-classes ()
  :hints (("Goal" :use (hack-8 hack-9)
                  :in-theory (theory 'minimal-theory))))

(defthm theorem-103-corollary
    (implies (and (primep p)
		  (= (mod p 4) 3)
		  (> p 3)
		  (primep (1+ (* 2 p))))
	     (not (primep (m p))))
  :hints (("Goal" :use (theorem-103
			expt-2-p-bnd
			(:instance primep-no-divisor (p (1- (expt 2 p))) (d (1+ (* 2 p))))))))

;; In order to arrange for theorem-103-corollary to be used as a
;; rewrite rule, we must disable the logical expansion of both
;; primep and m.  We must also re-enable the executable counterpart
;; of primep to allow the computation of primep(p) and primep(2*p+1):

(local-in-theory (disable primep m (m)))
(local-in-theory (enable (primep)))

(defthm mersenne-23-revisited
    (not (primep (m 23))))

;;[Time: .00 seconds]

(defthm mersenne-999671-revisited
    (not (primep (m 999671))))

;;[Time: .00 seconds]

(maybe-skip
(defthm mersenne-19876271
    (not (primep (m 19876271))))
)

;;[Time: 27 seconds]

