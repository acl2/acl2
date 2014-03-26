;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "sticky")

(defun inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))

(defun minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defun IEEE-MODE-P (mode)
  (member mode '(trunc inf minf near)))

(defun RND (x mode n)
  (case mode
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))))

(defun RND-CONST (e mode n)
  (case mode
    (near (expt 2 (- e n)))
    (inf (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(local (defthm rnd-const-thm-1
    (implies (and (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (near x n)
		(if (and (exactp x (1+ n))
			 (not (exactp x n)))
		    (trunc (+ x (rnd-const (expo x) 'near n)) (1- n))
		  (trunc (+ x (rnd-const (expo x) 'near n)) n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc))))))

(local (defthm hack1
    (equal (+ (- (EXPO X)) -1 1 (EXPO X))
	   0)))

(local (defthm rnd-const-thm-2
    (implies (and (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (away x n)
		(trunc (+ x (rnd-const (expo x) 'inf n)) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance away-imp (m (1+ (expo x)))))))))

(defthm RND-CONST-THM
    (implies (and (ieee-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (rnd x mode n)
		(if (and (eql mode 'near)
			 (exactp x (1+ n))
			 (not (exactp x n)))
		    (trunc (+ x (rnd-const (expo x) mode n)) (1- n))
		  (trunc (+ x (rnd-const (expo x) mode n)) n))))
  :rule-classes ()
  :hints (("Goal" :use (rnd-const-thm-1 rnd-const-thm-2))))

(defthm RND-STICKY
    (implies (and (ieee-mode-p mode)
		  (rationalp x) (> x 0)
		  (integerp k) (> k 0)
		  (integerp n) (> n (1+ k)))
	     (= (rnd x mode k)
		(rnd (sticky x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use (sticky-pos
			(:instance trunc-sticky (m k))
			(:instance away-sticky (m k))
			(:instance near-sticky (m k))))))
