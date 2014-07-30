(in-package "ACL2")
; cert_param: (uses-acl2r)

(defmacro standard-numberp (x)
  `(and (acl2-numberp ,x)
	(standardp ,x)))

(defun partitionp (p)
  (and (consp p)
       (realp (car p))
       (or (null (cdr p))
           (and (realp (cadr p)) ; could omit but may be useful
                (< (car p) (cadr p))
                (partitionp (cdr p))))))

(defun partitionp2 (p1 p2)
  (and (partitionp p1)
       (partitionp p2)
       (equal (car p1) (car p2))
       (equal (car (last p1)) (car (last p2)))))

(defun refinement-p (p1 p2)
  ;; Answers whether p2 is a subsequence of p1, assuming both are
  ;; strictly increasing.  When we also required that they have the
  ;; same last element, theorem common-refinement-is-refinement-1
  ;; failed; so, we prefer not to make that requirement.
  (if (consp p2)
      (let ((p1-tail (member (car p2) p1)))
        (and p1-tail
             (refinement-p (cdr p1-tail) (cdr p2))))
    t))

(defun strong-refinement-p (p1 p2)
  ;; Here is a stronger notion of refinementp that we will use on occasion.
  (and (partitionp2 p1 p2)
       (refinement-p p1 p2)))

(defun common-refinement (p1 p2)
  ;; merge increasing lists
  (declare (xargs :measure (+ (len p1) (len p2))))
  (if (consp p1)
      (if (consp p2)
          (cond
           ((< (car p1) (car p2))
            (cons (car p1) (common-refinement (cdr p1) p2)))
           ((< (car p2) (car p1))
            (cons (car p2) (common-refinement p1 (cdr p2))))
           (t ;; equal
            (cons (car p1) (common-refinement (cdr p1) (cdr p2)))))
        p1)
    p2))

;;; Perhaps not needed, but eliminates some forcing rounds:
(defthm partitionp-forward-to-realp-car
  (implies (partitionp p)
           (realp (car p)))
  :rule-classes :forward-chaining)

(defthm common-refinement-preserves-partitionp
  (implies (and (partitionp p1)
                (partitionp p2))
           (partitionp (common-refinement p1 p2))))

;;; Lemmas to prove common-refinement-is-refinement-of-first

(defthm refinement-p-reflexive
  (implies (partitionp p)
           (refinement-p p p)))

(defthm refinement-p-cons
  (implies (and (partitionp p1)
                (partitionp p2)
                (< a (car p2)))
           (equal (refinement-p (cons a p1) p2)
                  (and (consp p2) (refinement-p p1 p2))))
  :hints (("Goal" :expand ((refinement-p (cons a p1) p2)))))

;;; The plan is to form two sums over the refinement p1 of a partition p2:
;;; (1) Riemann sum of f(x) over p1;
;;; (2) As in (1), but using next element of p2 as the x.

(defun sumlist (x)
  (if (consp x)
      (+ (car x) (sumlist (cdr x)))
    0))

(defun deltas (p)
  ;; the list of differences, e.g.:
  ;; (deltas '(3 5 6 10 15)) = (2 1 4 5)
  (if (and (consp p) (consp (cdr p)))
      (cons (- (cadr p) (car p))
            (deltas (cdr p)))
    nil))

(defun map-times (x y)
  ;; the pairwise product of lists x and y
  (if (consp x)
      (cons (* (car x) (car y))
            (map-times (cdr x) (cdr y)))
    nil))

(defun dotprod (x y)
  ;; dot product
  (sumlist (map-times x y)))

;;; From continuity.lisp:
(encapsulate
 ((rcfn (x) t))

 ;; Our witness continuous function is the identity function.

 (local (defun rcfn (x) x))

 ;; The function returns standard values for standard arguments.

 (defthm rcfn-standard
   (implies (standard-numberp x)
	    (standard-numberp (rcfn x)))
   :rule-classes (:rewrite :type-prescription))

 ;; For real arguments, the function returns real values.

 (defthm rcfn-real
   (implies (realp x)
	    (realp (rcfn x)))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y is a real close to x, then rcfn(x)
 ;; is close to rcfn(y).

 (defthm rcfn-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
	    (i-close (rcfn x) (rcfn y))))
 )

(defun map-rcfn (p)
  ;; map rcfn over the list p
  (if (consp p)
      (cons (rcfn (car p)) (map-rcfn (cdr p)))
    nil))

(defun riemann-rcfn (p)
  ;; for partition p, take the Riemann sum of rcfn over p using right
  ;; endpoints
  (dotprod (deltas p) (map-rcfn (cdr p))))

(defun next-gte (x p)
  ;; next member of partition p that is greater than or equal to x
  (if (<= x (car p))
      (car p)
    (if (consp p)
        (next-gte x (cdr p))
      nil)))

(defun map-rcfn-refinement (p1 p2)
  ;; p1 should be a refinement of p2
  (if (consp p1)
      (cons (rcfn (next-gte (car p1) p2))
            (map-rcfn-refinement (cdr p1) p2))
    nil))

(defun riemann-rcfn-refinement (p1 p2)
  ;; p1 should be a refinement of p2
  (dotprod (deltas p1)
           (map-rcfn-refinement (cdr p1) p2)))

(defun maxlist (x)
  ;; the maximum of non-empty list x of non-negative numbers
  (if (consp x)
      (max (car x) (maxlist (cdr x)))
    0))

(defun mesh (p)
  ;; mesh of the partition p
  (maxlist (deltas p)))

(defun abslist (x)
  ;; pointwise absolute values of list x
  (if (consp x)
      (cons (abs (car x))
            (abslist (cdr x)))
    nil))

(defthm abslist-deltas
  ;; trivial lemma saying that each delta is non-negative
  (implies (partitionp p)
           (equal (abslist (deltas p)) (deltas p))))

(defun bounded-by (lst a)
  (if (consp lst)
      (and (<= (abs (car lst)) a)
           (bounded-by (cdr lst) a))
    t))

(defun non-negative-listp (x)
  (if (consp x)
      (and (<= 0 (car x))
           (non-negative-listp (cdr x)))
    t))

(defun span (p)
  ;; b - a, where p partitions the interval [a,b]
  (- (car (last p))
     (car p)))

(defun difflist (x y)
  (if (consp x)
      (cons (- (car x) (car y))
            (difflist (cdr x) (cdr y)))
    nil))
