(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(include-book "nonstd/nsa/intervals" :dir :system)

;; Originally by Matt Kaufmann for ACL2 Workshop 1999

(defun partitionp (p)
  (and (consp p)
       (realp (car p))
       (or (null (cdr p))
           (and (realp (cadr p))
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

(defun maxlist (x)
  ;; the maximum of non-empty list x of non-negative numbers
  (if (consp x)
      (max (car x) (maxlist (cdr x)))
    0))

(defun mesh (p)
  ;; mesh of the partition p
  (maxlist (deltas p)))

(encapsulate
 ( ((rifn *) => *)
   ((strict-int-rifn * *) => *)
   ((domain-rifn) => *)
   ;((map-rifn *) => *)
   ;((riemann-rifn *) => *)
   )

 (local
  (defun rifn (x)
    (declare (ignore x))
    0))

 (defthm rifn-real
   (implies (realp x)
	    (realp (rifn x))))

 (local
  (defun strict-int-rifn (a b)
    (declare (ignore a b))
    0))

 (defthm strict-int-rifn-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn a b))))

 (local
  (defun domain-rifn ()
    (interval nil nil)))

 (defthm domain-rifn-is-non-trivial-interval
   (and (interval-p (domain-rifn))
	(implies (and (interval-left-inclusive-p (domain-rifn))
		      (interval-right-inclusive-p (domain-rifn)))
		 (not (equal (interval-left-endpoint (domain-rifn))
			     (interval-right-endpoint (domain-rifn)))))))

 (defun map-rifn (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn (car p))
	     (map-rifn (cdr p)))
     nil))

 (defun riemann-rifn (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn (cdr p))))

 (defun int-rifn (a b)
   (if (<= a b)
       (strict-int-rifn a b)
     (- (strict-int-rifn b a))))

 (local
  (defthm map-rifn-zero
    (implies (consp p)
	     (equal (car (map-rifn p)) 0))))

 (local
  (defthm riemann-rifn-zero
    (implies (partitionp p)
	     (equal (riemann-rifn p) 0))))

 (defthm strict-int-rifn-is-integral-of-rifn
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn))
		 (inside-interval-p b (domain-rifn))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn p)
		     (strict-int-rifn a b))))
 )

(defthm-std standardp-strict-int-rifn
  (implies (and (standardp a)
		(standardp b))
	   (standardp (strict-int-rifn a b))))

(defthm true-listp-partition
  (implies (partitionp p)
	   (true-listp p)))

(defthm real-listp-partition
  (implies (partitionp p)
	   (real-listp p)))



