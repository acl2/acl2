;;; Contributed by Ruben A. Gamboa

;;; This book develops the (very small) theory of the sum of a list of
;;; numbers.  It is used to develop the theory of series from
;;; sequences in other books.

(in-package "ACL2")

;; First, the definition of sumlist -- it's the obvious defun :-)

(defun sumlist (x)
  (if (consp x)
      (+ (car x)
	 (sumlist (cdr x)))
    0))

;; ACL2 can conclude that sumlist is a numeric function.  We'd like
;; for it to know that when the list contains only real numbers, its
;; sum is also a real number.

(defthm rationalp-sumlist
  (implies (rational-listp x)
	   (rationalp (sumlist x))))

#+:non-standard-analysis
(defthm realp-sumlist
  (implies (real-listp x)
	   (realp (sumlist x))))

;; This is the main lemma.  The sum of a list can be computed by
;; splitting the list up into two parts and adding each part separately.

(defthm sumlist-append
  (equal (sumlist (append x y))
	 (+ (sumlist x) (sumlist y))))

