;; This book develops the theory of alternating series.  The key
;; property is that if a_1+a_2+...+a_n is an alternating series,
;; then the sum of the a_i is at most a_1.  Moreover, the remaining
;; terms in the sequence are positive if a_1 is negative and vice
;; versa.

(in-package "ACL2")
; cert_param: (uses-acl2r)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(include-book "arithmetic/sumlist" :dir :system)

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; We define the function sign that returns -1, 0, or 1, depending on
;; the sign of x.

(defun sign (x)
  (if (< x 0)
      -1
    (if (= x 0)
	0
      1)))

;; A simple theorem.  The sign of x*x*y is the same as the sign of y.

(defthm sign-*-x-x-y
  (implies (and (realp x)
		(case-split (not (= 0 x)))
		(realp y))
	   (equal (sign (* x x y))
		  (sign y))))

;; If x is positive, then sign(x*y)=sign(y).

(defthm sign-*-x-y
  (implies (and (realp x)
		(< 0 x)
		(realp y))
	   (equal (sign (* x y))
		  (sign y))))

;; Now, sign(-x) = -sign(x)!

(defthm sign--x
  (implies (acl2-numberp x)
	   (equal (sign (- x))
		  (- (sign x)))))

(in-theory (disable sign))

;; We define what we mean by x and y having opposite signs.
;; Basically, if either x or y is zero, we consider them to be of
;; opposite signs, otherwise sign(x) must be equal to -sign(y).

(defun opposite-signs-p (x y)
      (or (= x 0)
          (= y 0)
          (equal (sign x) (- (sign y)))))

;; The first requirement for an alternating sequence is that
;; successive elements have opposite signs.

(defun alternating-sequence-1-p (lst)
  (if (null lst)
      t
    (if (null (cdr lst))
	t
      (and (opposite-signs-p (car lst) (cadr lst))
	   (alternating-sequence-1-p (cdr lst))))))

;; The second requirement is that successive elements decrease in
;; magnitude, or at least if one element is zero, all subsequent
;; elements are also zero.  The special treatment of zero allows a
;; sequence consisting of all zeros (or with a tail consisting of all
;; zeros) to be admitted as an alternating sequence.

(defun alternating-sequence-2-p (lst)
  (if (null lst)
      t
    (if (null (cdr lst))
	t
      (and (or (and (equal (car lst) 0)
		    (equal (cadr lst) 0))
	       (< (abs (cadr lst))
		  (abs (car lst))))
	   (alternating-sequence-2-p (cdr lst))))))

;; The two properties above define alternating sequences.

(defun alternating-sequence-p (lst)
  (and (alternating-sequence-1-p lst)
       (alternating-sequence-2-p lst)))

;; Now, we show the key properties of the sum of an alternating
;; series.  Basically, the first element is a bound on the sum of the
;; remaining elements.

(defthm sumlist-alternating-sequence-lemma
  (implies (and (alternating-sequence-p x)
		(real-listp x)
		(not (null x)))
	   (cond ((< 0 (car x))
		  (and (< (- (car x)) (sumlist (cdr x)))
		       (<= (sumlist (cdr x)) 0)))
		 ((equal 0 (car x))
		  (and (equal (sumlist x) 0)
		       (equal (sumlist (cdr x)) 0)))
		 ((< (car x) 0)
		  (and (< (sumlist (cdr x)) (- (car x)))
		       (<= 0 (sumlist (cdr x)))))))
  :hints (("Subgoal *1/1"
	   :cases ((= 0 (car x))
		   (= 0 (cadr x))
		   (and (< 0 (car x)) (> 0 (cadr x)))
		   (and (< 0 (car x)) (< 0 (cadr x)))
		   (and (> 0 (car x)) (> 0 (cadr x)))
		   (and (> 0 (car x)) (< 0 (cadr x))))
	   :in-theory (enable sign)))
  :rule-classes nil)

;; That allows us to prove the key property of alternating series,
;; that the first element is a bound on the sum of the sum of the
;; series.

(defthm sumlist-alternating-sequence
  (implies (and (alternating-sequence-p x)
		(real-listp x)
		(not (null x)))
	   (not (< (abs (car x)) (abs (sumlist x)))))
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence-lemma)))
	  ("Goal'"
	   :cases ((< 0 (car x))
		   (= 0 (car x))
		   (> 0 (car x))))))

