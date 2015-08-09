(in-package "ACL2")
(include-book "../chap10/ac-example")

; To prove the first theorem, we have to prove some basic arithmetic theorems.
; In another approach to these exercises, we use one of the standard
; books distributed with ACL2.  But here we start from scratch.

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

;; [Jared] Removed this commutativity-2 macro call in order to build the rule
;; into ACL2.  (The macro generates a commutativity-2-of-+ theorem that uses
;; different variable names than the built-in rule, so it's incompatible.)
;;
;; (commutativity-2 +)

(defthm fold-consts-in-+
  (implies (and (syntaxp (quotep x))
		(syntaxp (quotep y)))
	   (equal (+ x (+ y z)) (+ (+ x y) z))))

(defthm fold-consts-in-*
  (implies (and (syntaxp (quotep x))
		(syntaxp (quotep y)))
	   (equal (* x (* y z)) (* (* x y) z))))

(defthm distributivity-of-minus-over-+
  (equal (- (+ x y)) (+ (- x) (- y))))

(defthm minus-cancellation-on-left
  (equal (+ x (- x) y) (fix y)))

(defthm left-distributivity-of-*-over-+
  (equal (*  x (+ y z))
	 (+ (* x y)
	    (* x z))))

(defthm uniqueness-of-+-inverse
  (implies (and (acl2-numberp y)
		(equal (+ x y) 0))
           (equal y (- x)))
  :rule-classes nil)

(defthm commutativity-of---*-right
  (equal (* x (- y))
	 (- (* x y)))
  :hints
  (("Goal"
    :use ((:instance uniqueness-of-+-inverse (x (* x y)) (y (* x (- y))))
          (:instance left-distributivity-of-*-over-+ (z (- y)))))))

(defthm commutativity-of---*-left
  (equal (* (- x) y)
         (- (* x y))))

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

(defthm right-unicity-of-1-for-expt
  (equal (expt r 1) (fix r))
  :hints (("goal" :expand (expt r 1))))

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
  (equal (+ (- (* x (/ y)))
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
            (* (+ (- n) (- (* n n))) (/ (+ 1 n)))
            (- n)))
  :hints (("goal" :in-theory
	   (disable distributivity
		    left-distributivity-of-*-over-+)
           :use ((:instance combine-fractions)))))

(defthm simplify-fractions-+
  (implies (natp n)
           (equal (+ (- (* n (/ (1+ n))))
                     (- (* n n (/ (1+ n)))))
                  (- n)))
  :hints
  (("Goal"
    :use ((:instance combine-numerator (x n) (z (* n n)) (y (+ 1 n)))))))

(defthm right-cancellation-for-*
  (equal (equal (* x z) (* y z))
	 (or (equal 0 (fix z))
	     (equal (fix x) (fix y))))
  :hints (("goal" :use (:instance
			(:theorem (implies (equal x y)
					   (equal (* x (/ z))
						  (* y (/ z)))))
			(x (* x z))
			(y (* y z))))))

(defthm equal-/
  (implies (and (acl2-numberp x)
		(not (equal 0 x)))
	   (equal (equal (/ x) y)
		  (equal 1 (* x y))))
  :hints (("Goal"
	   :use
	   ((:instance
	     right-cancellation-for-* (x y) (y (/ x)) ( z x))))))

(defthm sum6-thm-aux
  (implies (and (integerp n)
		(> n 0))
	   (equal (/ 1 (+ n (* n n)))
		  (- (/ 1 n) (/ 1 (1+ n)))))
  :hints
  (("goal''"
    :use ((:instance combine-numerator (x n) (z (* n n)) (y (+ 1 n)))))))

(defthm sum6-thm
  (implies (natp n)
	   (equal (sum6 n) (/ n (1+ n))))
  :hints(("goal" :induct t)
	 ("subgoal *1/2''"
	  :use ((:instance absorb-1 (y (+ 1 n)) (x 1))))))

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

