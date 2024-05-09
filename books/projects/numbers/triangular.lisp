(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

;; The nth triangular number:

(defun tri (n)
  (if (zp n)
      0
    (+ (tri (1- n)) n)))

;; The value of (tri n), derived by induction:

(defthm tri-val
  (implies (natp n)
	   (equal (tri n) (/ (* n (1+ n)) 2))))

;; The sum of the reciprocls of the first n triangular numbers:

(defun tri-recip-sum (n)
  (if (zp n)
      0
    (+ (tri-recip-sum (1- n))
       (/ (tri n)))))

;; The value of (tri-recip-sum n), derived by induction:

(defthmd hack-1
  (implies (and (posp b) (posp d))
	   (equal (+ (/ b) (/ (* b d)))
		  (/ (1+ d) (* b d)))))

(defthmd hack-2
  (implies (posp n)
	   (equal (+ (* 2 (/ n)) (tri-recip-sum (+ -1 n)))
                  (+ (tri-recip-sum (+ -1 n))
                     (* 2 (/ (+ 1 n)))
                     (* 2 (/ (+ n (expt n 2)))))))
  :hints (("goal" :use ((:instance hack-1 (b (1+ n)) (d n))))))

(defthm tri-recip-sum-val
  (implies (natp n)
	   (equal (tri-recip-sum n)
		  (* 2 (- 1 (/ (1+ n))))))
  :hints (("Subgoal *1/4" :use (hack-2))))

;; Convergence follows easily:

(defthmd hack-3
  (implies (and (rationalp a) (> a 0) (rationalp b))
	   (iff (< (/ 2 a) b) (< 2 (* a b))))
  :hints (("Goal" :nonlinearp t)))

(defthm tri-recip-sum-limit
  (implies (and (rationalp e)
                (> e 0)
		(posp n)
		(> n (/ 2 e)))
	   (< (abs (- (tri-recip-sum n) 2))
	      e))
  :hints (("Goal" :use ((:instance hack-3 (a e) (b n))
			(:instance hack-3 (a (1+ n)) (b e))))))
