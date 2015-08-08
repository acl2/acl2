(in-package "ACL2")

; This time we start with a standard arithmetic book.

(include-book "arithmetic/top-with-meta" :dir :system)

; ---------------------------------------------------------------------------
; Exercise 11.26

#| ; Deleted for v2-8 (ordinals changes introduced natp).
(defun natp (n)
  (and (integerp n)
       (<= 0 n)))
|#

(defun sum1 (n)
  (if (zp n)
      0
    (+ n (sum1 (1- n)))))

(defthm sum1-thm
  (implies (natp n)
	   (equal (sum1 n) (/ (* n (1+ n)) 2))))

; ---------------------------------------------------------------------------
; Exercise 11.27

(defun sum2 (n)
  (if (zp n)
      0
    (+ (* 3 n n) (* -3 n) 1 (sum2 (1- n)))))

(defthm sum2-thm
  (implies (natp n)
	   (equal (sum2 n) (* n n n))))

; ---------------------------------------------------------------------------
; Exercise 11.28

(defun sum3 (n)
  (if (zp n)
      0
    (+ (* n n) (sum3 (1- n)))))

(defthm sum3-thm
  (implies (natp n)
	   (equal (sum3 n)
                  (/ (* n (1+ n) (1+ (* 2 n)))
                     6))))

; ---------------------------------------------------------------------------
; Exercise 11.29

(defun sum4 (n)
  (if (zp n)
      0
    (+ (expt (* 2 n) 2)
       (sum4 (1- n)))))

(defthm sum4-thm
  (implies (natp n)
	   (equal (sum4 n) (/ (* 2 n (1+ n) (1+ (* 2 n))) 3))))

; ---------------------------------------------------------------------------
; Exercise 11.30

(defun sum5 (n)
  (if (zp n)
      0
    (+ (* n n n) (sum5 (1- n)))))

(defthm sum5-thm
  (implies (natp n)
	   (equal (sum5 n)
                  (/ (* n n (1+ n) (1+ n))
                     4))))

; ---------------------------------------------------------------------------
; Exercise 11.31

(defun sum6 (n)
  (if (zp n)
      0
    (+ (/ 1 (* n (1+ n)))
       (sum6 (1- n)))))

(defthm absorb-1
  (implies (and (integerp y) (> y 0))
           (equal (+ 1 (- (/ x y))) (/ (- y x) y))))

(defthm combine-numerator
  (equal (+ (- (* x (/  y)))
	    (- (* z (/ y))))
	 (* (+ (- x) (- z)) (/ y)))
  :rule-classes nil)

(defthm combine-fractions
  (equal (+ (- n) (- (* n n)))
         (* (- n) (+ 1 n)))
  :rule-classes nil)

(defthm simplify-fractions-*
  (implies (natp n)
           (equal
            (* (+ (- N) (- (* N N))) (/ (+ 1 N)))
            (- n)))
  :hints (("goal" :in-theory (disable distributivity)
           :use ((:instance combine-fractions)))))

(defthm sum6-thm-aux
  (implies (and (integerp n)
		(> n 0))
	   (equal (/ 1 (+ n (* n n)))
		  (- (/ 1 n) (/ 1 (1+ n)))))
  :hints (("goal''"
           :use ((:instance combine-numerator (x n) (z (* n n)) (y (+ 1 n)))))))

(defthm sum6-thm
  (implies (natp n)
	   (equal (sum6 n) (/  n (1+ n))))
  :hints(("goal" :induct t)
	 ("subgoal *1/2''"
	  :use ((:instance absorb-1 (y (+ 1 n)) (x 1)))
	  :in-theory (disable absorb-1))))

; ---------------------------------------------------------------------------
; Exercise 11.32

(defun sum7 (n)
  (if (zp n)
      0
    (+ (- (* 4 n) 1) (sum7 (1- n)))))

(defthm sum7-thm
  (implies (natp n)
	   (equal (sum7 n)  (* n (1+ (* 2 n))))))

; ---------------------------------------------------------------------------
; Exercise 11.33

(defthm sum8-thm
  (implies (natp n)
	   (equal (* (sum1 n) (sum1 n)) (sum5 n))))
