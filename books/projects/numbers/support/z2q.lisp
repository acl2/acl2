(in-package "DM")

(include-book "arithmetic-5/top" :dir :system)

(include-book "euclid")

;; We define a surjective function n2q from the integers to the rationals.  This
;; function is a formalization of Cantor's diagonal enumeration, graphically represented
;; in the diagram below.  If the positive integer n appears in row p and column q,
;; then (n2q n) = (/ p q):

;;        1    2   3  4   5
;;      _________________________
;;     |
;;   1 |  1    2   4  7   ...
;;     |
;;   2 |  3    5   8  ...
;;     |
;;   3 |  6    9   ...
;;     |
;;   4 | 10    ...
;;     |
;;   5 |  ...

(defun n2q (n k)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (natp n) (natp k) (> n k))
      (n2q (- n k) (1+ k))
    (/ n (1+ (- k n)))))

(defun z2q (n)
  (if (>= n 0)
      (n2q n 1)
    (- (n2q (- n) 1))))

;; To prove that z2q is surjective, we shall define a function q2n and prove that
;; for every rational x, (q2n x) is an integer and (z2q (q2n x)) = x.  The definition
;; of q2n is based on the function tri, which computes the sequence of triangular
;; numbers:

(defun tri (k)
  (if (zp k)
      0
    (+ k (tri (1- k)))))

(defun q2n (p q) (+ (tri (+ p q -2)) p))

(defun q2z (x)
  (if (>= x 0)
      (q2n (numerator x) (denominator x))
    (- (q2n (numerator (- x)) (denominator (- x))))))

;; The following is proved by induction on k:

(defthmd n2q-rewrite
  (implies (and (natp k)
                (natp n)
                (> n (tri k)))
           (equal (z2q n)
                  (n2q (- n (tri k)) (1+ k)))))

;; This follows from n2q-rewrite and the definitions:

(defthmd z2q-q2n
  (implies (and (posp p) (posp q))
           (equal (z2q (q2n p q))
                  (/ p q)))
  :hints (("Goal" :use ((:instance n2q-rewrite (k (+ p q -2)) (n (+ (tri (+ p q -2)) p)))))))

;; We instantiate the above result for the case x > 0 and again for the case x < 0:

(defthm z2q-q2z
  (implies (rationalp x)
           (and (integerp (q2z x))
                (equal (z2q (q2z x)) x)))
  :hints (("Goal" :use ((:instance z2q-q2n (p (numerator x)) (q (denominator x)))
                        (:instance z2q-q2n (p (- (numerator x))) (q (denominator x)))))))

;;-----------------------------------------------------------------------------------------

;; We shall construct a bijection z2q-bi from the integers to the rationals and
;; its inverse q2n-bi.  We begin with a bijection from the positive integers to
;; the positive rationals, based on the following tree:

;;                1/1
;;               /   \
;;              /     \
;;             /       \
;;            1/2      2/1
;;           /   \    /   \
;;          1/3 3/2  2/3  3/1
;;         /  \  / \ / \  / \

;; Each node of the tree is a rational p/q and has 2 subnodes, p/(p+q) and (p+q)/q.
;; Our bijection maps the positive integer n to the nth node of the tree, listed
;; in breadth-first order, i.e., 1/1, 1/2, 2/1, 1/3, 3/2, 2/3, 3/1, 1/4, 4/3, ...
;; The function n2q-bi computes the pair (p . q) consisting of the numerator and
;; denominator of the rational p/q corresponding to a given n:

(defun n2q-bi (n)
  (if (or (zp n) (= n 1))
      (cons 1 1)
    (let ((pq (n2q-bi (floor n 2))))
      (if (evenp n)
          (cons (car pq) (+ (car pq) (cdr pq)))
	(cons (+ (car pq) (cdr pq)) (cdr pq))))))

;; The bijection from the integers to the rationals is defined as follows:

(defun z2q-bi (n)
  (if (= n 0)
      0
    (if (> n 0)
        (/ (car (n2q-bi n)) (cdr (n2q-bi n)))
      (- (/ (car (n2q-bi (- n))) (cdr (n2q-bi (- n))))))))

;; The inverse of n2q-bi maps a pair of relatively prime positive integers to a
;; positive integer:

(defun q2n-bi (p q)
  (declare (xargs :measure (nfix (+ p q))))
  (if (or (zp p) (zp q) (= p q))
      1
    (if (> p q)
        (1+ (* 2 (q2n-bi (- p q) q)))
      (* 2 (q2n-bi p (- q p))))))

;; The inverse of z2q-bi is a bijection from the rationals to the integers:

(defun q2z-bi(x)
  (if (= x 0)
      0
    (if (> x 0)
        (q2n-bi (numerator x) (denominator x))
      (- (q2n-bi (numerator (- x)) (denominator (- x)))))))

;; By induction, if n is a positive integer, then (n2q-bi n) is a pair of positive integers:

(defthmd posp-n2q-bi
  (implies (posp n)
           (and (posp (car (n2q-bi n)))
	        (posp (cdr (n2q-bi n))))))

;; By induction and the definition of gcd, if n is a positive integer, then (n2q-bi n) is a
;; pair of relatively prime integers:

(defthmd gcd-n2q-bi
  (implies (posp n)
           (equal (gcd (car (n2q-bi n)) (cdr (n2q-bi n)))
	          1))
  :hints (("Subgoal *1/7" :use ((:instance gcd-diff-2 (p (+ (car (n2q-bi (floor n 2))) (cdr (n2q-bi (floor n 2)))))
                                                      (q (cdr (n2q-bi (floor n 2)))))
				(:instance posp-n2q-bi (n (floor n 2)))))
	  ("Subgoal *1/4" :use ((:instance gcd-diff-1 (q (+ (car (n2q-bi (floor n 2))) (cdr (n2q-bi (floor n 2)))))
                                                      (p (car (n2q-bi (floor n 2)))))
				(:instance posp-n2q-bi (n (floor n 2)))))))

;; q2n-bi and n2q-bi are inverse functions:

(defthmd q2n-n2q-bi
  (implies (posp n)
           (equal (q2n-bi (car (n2q-bi n)) (cdr (n2q-bi n)))
	          n))
  :hints (("Subgoal *1/7" :use ((:instance posp-n2q-bi (n (floor n 2)))))
          ("Subgoal *1/4" :use ((:instance posp-n2q-bi (n (floor n 2)))))))

(defthmd n2q-q2n-bi
  (implies (and (posp p) (posp q) (= (gcd p q) 1))
           (equal (n2q-bi (q2n-bi p q))
	          (cons p q)))
  :hints (("Subgoal *1/8" :use (gcd-diff-1))
          ("Subgoal *1/4" :use (gcd-diff-2))
	  ("Subgoal *1/1" :use ((:instance gcd-quotient-2 (x p) (y p) (d p))))))

;; q2z-bi and z2q-bi are inverse functions:

(defthmd q2z-bi-z2q
  (implies (integerp n)
           (and (rationalp (z2q-bi n))
                (equal (q2z-bi (z2q-bi n))
	               n)))
  :hints (("Goal" :use (q2n-n2q-bi posp-n2q-bi gcd-n2q-bi
                        (:instance q2n-n2q-bi (n (- n)))
			(:instance posp-n2q-bi (n (- n)))
			(:instance gcd-n2q-bi (n (- n)))
			(:instance gcd-num-den (x (/ (car (n2q-bi n)) (cdr (n2q-bi n)))))
			(:instance gcd-num-den (x (/ (car (n2q-bi (- n))) (cdr (n2q-bi (- n))))))
			(:instance lowest-terms-unique (p (car (n2q-bi n)))
			                               (q (cdr (n2q-bi n)))
						       (n (numerator (/ (car (n2q-bi n)) (cdr (n2q-bi n)))))
						       (d (denominator (/ (car (n2q-bi n)) (cdr (n2q-bi n))))))
			(:instance lowest-terms-unique (p (car (n2q-bi (- n))))
			                               (q (cdr (n2q-bi (- n))))
						       (n (numerator (/ (car (n2q-bi (- n))) (cdr (n2q-bi (- n))))))
						       (d (denominator (/ (car (n2q-bi (- n))) (cdr (n2q-bi (- n)))))))))))

(defthmd z2q-q2z-bi
  (implies (rationalp x)
           (and (integerp (q2z-bi x))
	        (equal (z2q-bi (q2z-bi x))
		       x)))
  :hints (("Goal" :use (gcd-num-den
                        (:instance n2q-q2n-bi (p (numerator x)) (q (denominator x)))
                        (:instance gcd-num-den (x (- x)))
			(:instance n2q-q2n-bi (p (numerator (- x))) (q (denominator (- x))))))))


