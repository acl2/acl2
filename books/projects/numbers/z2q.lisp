(in-package "DM")

(include-book "euclid")
(local (include-book "support/z2q"))

;; We shall construct a surjection z2q from the integers to the rationals and a
;; somewhat more complicated bijection z2q-bi from the integers to the rationals.

;; We begin by defining a surjection n2q from the positive integers to the positive
;; rationals.  This is a formalization of Cantor's diagonal enumeration, graphically
;; represented in the diagram below.  If the positive integer n appears in row p and
;; column q, then (n2q n 1) = (/ p q):

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

;; We extend n2q to a mapping of the integers onto the rationals:

(defun z2q (n)
  (if (>= n 0)
      (n2q n 1)
    (- (n2q (- n) 1))))

;; To prove that z2q is surjective, we shall define a function q2z and prove that
;; for every rational x, (q2z x) is an integer and (z2q (q2z x)) = x.
;; First we define a binary function q2n with the following property: If x is a
;; positive rational expressed in lowest terms as p/q, then (q2n p q) is a positive
;; integer and (n2q (q2n p q)) = x.  The definition of q2n is based on the function
;; tri, which computes the sequence of triangular numbers:

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
                  (/ p q))))

;; We instantiate the above result for the case x > 0 and again for the case x < 0:

(defthm z2q-q2z
  (implies (rationalp x)
           (and (integerp (q2z x))
                (equal (z2q (q2z x)) x))))

;;-----------------------------------------------------------------------------------------

;; We shall construct a bijection z2q-bi from the integers to the rationals and
;; its inverse q2z-bi.  We begin with a bijection from the positive integers to
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

;; The inverse of n2q-bi:

(defun q2n-bi (p q)
  (declare (xargs :measure (nfix (+ p q))))
  (if (or (zp p) (zp q) (= p q))
      1
    (if (> p q)
        (1+ (* 2 (q2n-bi (- p q) q)))
      (* 2 (q2n-bi p (- q p))))))

;; The inverse of z2q-bi:

(defun q2z-bi(x)
  (if (= x 0)
      0
    (if (> x 0)
        (q2n-bi (numerator x) (denominator x))
      (- (q2n-bi (numerator (- x)) (denominator (- x)))))))

;; We prove by induction that if n is a positive integer, then (n2q-bi n) is a pair of
;; relatively prime positive integers:

(defthmd posp-n2q-bi
  (implies (posp n)
           (and (posp (car (n2q-bi n)))
	        (posp (cdr (n2q-bi n))))))

(defthmd gcd-n2q-bi
  (implies (posp n)
           (equal (gcd (car (n2q-bi n)) (cdr (n2q-bi n)))
	          1)))

;; The next two lemmas, which state that q2n-bi and n2q-bi are inverse functions, are
;; easily proved by induction:

(defthmd q2n-n2q-bi
  (implies (posp n)
           (equal (q2n-bi (car (n2q-bi n)) (cdr (n2q-bi n)))
	          n)))

(defthmd n2q-q2n-bi
  (implies (and (posp p) (posp q) (= (gcd p q) 1))
           (equal (n2q-bi (q2n-bi p q))
	          (cons p q))))

;; The proof that q2z-bi and z2q-bi are inverse functions requires two results from
;; euclid.lisp:
;;  (1) gcd-num-den: The numerator and denominator of a rational are relatively prime.
;;  (2) lowest-terms-unique: If a rational x is the quotient (/ p q) of reatively prime
;;      positive integers , then p = (numerator x) and q = (denominator x).

(defthmd q2z-bi-z2q
  (implies (integerp n)
           (and (rationalp (z2q-bi n))
                (equal (q2z-bi (z2q-bi n))
	               n))))

(defthmd z2q-q2z-bi
  (implies (rationalp x)
           (and (integerp (q2z-bi x))
	        (equal (z2q-bi (q2z-bi x))
		       x))))


