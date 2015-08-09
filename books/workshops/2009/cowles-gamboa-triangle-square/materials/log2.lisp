#| To certify:
(certify-book "log2")
|#

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book to help certify this book,

(local (include-book "arithmetic-3/top" :dir :system))


(defun
 flog2 (n)
 ;; Return floor of log,
 ;;  base 2, of n.
 (if (zp n)
     0
     (if (evenp n)
	  (+ 1 (flog2 (/ n 2)))
	  (flog2 (- n 1)))))

(defthm
 flog2-is-correct
 (implies (posp n)
	   (and (<= (expt 2 (flog2 n))
		    n)
		(< n
		   (expt 2 (+ 1 (flog2 n)))))))

(defun
 clog2 (n)
 ;; Return ceiling of log,
 ;;  base 2, of n.
 (if (zp n)
     -1
     (if (= n 1)
	  0
	  (if (evenp n)
	      (+ 1
		 (clog2 (/ n 2)))
	      (+ 1
		 (clog2 (/ (+ 1 n) 2)))))))

(defthm
 natp-clog2
 (implies (and (integerp n)
		(> n 0))
	   (>= (clog2 n)
	       0))
 :rule-classes :type-prescription)

(defthm
 posp-1/2+1/2*n
 (implies (and (integerp n)
		(not (integerp (* 1/2 n)))
		(> n 1))
	   (and (integerp (+ 1/2 (* 1/2 N)))
		(> (+ 1/2 (* 1/2 N)) 0)))
 :rule-classes :type-prescription)

(defthm
 posp-clog2
 (implies (and (integerp n)
		(> n 1))
	   (> (clog2 n)
	      0))
 :rule-classes :type-prescription)

(defthm
 clog2-lemma-a
 (implies (and (not (equal n 1))
		(not (integerp (* 1/2 n)))
		(< (expt 2 (+ -1 (clog2 (+ 1/2 (* 1/2 n)))))
		   (+ 1/2 (* 1/2 n)))
		(integerp n)
		(< 0 n))
	   (< (expt 2 (clog2 (+ 1/2 (* 1/2 n))))
	      (+ 1 n)))
 :hints (("goal"
	   :use (:instance
		 (:theorem
		  (implies (< x y)
			   (< (* 2 x)(* 2 y))))
		 (x (expt 2 (+ -1 (clog2 (+ 1/2 (* 1/2 n))))))
		 (y (+ 1/2 (* 1/2 n)))))))

(defthm
 clog2-lemma-b
 (implies (and (not (equal n 1))
		(not (integerp (* 1/2 n)))
		(< (expt 2 (+ -1 (clog2 (+ 1/2 (* 1/2 n)))))
		   (+ 1/2 (* 1/2 n)))
		(integerp n)
		(< 0 n))
	   (< (expt 2 (clog2 (+ 1/2 (* 1/2 n))))
	      n))
 :hints (("goal"
	   :use (:instance
		 (:theorem
		  (implies (and (integerp i)
				(integerp j)
				(evenp i)
				(oddp j)
				(< i (+ 1 j)))
			   (< i j)))
		 (i (expt 2 (clog2 (+ 1/2 (* 1/2 n)))))
		 (j n)))))

(defthm
 clog2-is-correct-lower
 (implies (posp n)
	   (< (expt 2 (+ -1 (clog2 n)))
	      n))
 :hints (("Subgoal *1/5"
	   :use (:instance
		 (:theorem
		  (implies (< x y)
			   (< (* 2 x)(* 2 y))))
		 (x (expt 2 (+ -1 (clog2 (* n 1/2)))))
		 (y (* 1/2 n))))))

(defthm
 clog2-is-correct-upper
 (implies (natp n)
	   (<= n
	       (expt 2 (clog2 n))))
 :hints (("Subgoal *1/8"
	   :use (:instance
		 (:theorem
		  (implies (<= x y)
			   (<= (* 2 x)(* 2 y))))
		 (x (+ 1/2 (* 1/2 N)))
		 (y (expt 2 (clog2 (+ 1/2 (* 1/2 n)))))))
	 ("Subgoal *1/5"
	  :use (:instance
		(:theorem
		 (implies (<= x y)
			  (<= (* 2 x)(* 2 y))))
		(x (* 1/2 N))
		(y (expt 2 (clog2 (* 1/2 n))))))))

(defthm
 clog2-is-correct
 (implies (posp n)
	   (and (< (expt 2 (+ -1 (clog2 n)))
		   n)
		(<= n
		    (expt 2 (clog2 n))))))

(in-theory (disable clog2-is-correct))

(defun
 nbr-calls-clog2 (n)
 (if (zp n)
     1
     (if (= n 1)
	  1
	  (if (evenp n)
	      (+ 1
		 (nbr-calls-clog2 (/ n 2)))
	      (+ 1
		 (nbr-calls-clog2 (/ (+ 1 n) 2)))))))

;;                           ceiling
;;                             lg2
;; (nbr-calls-clog2 0)  = 1
;; (nbr-calls-clog2 1)  = 1     0
;; (nbr-calls-clog2 2)  = 2     1
;; (nbr-calls-clog2 3)  = 3     2
;; (nbr-calls-clog2 4)  = 3     2
;; (nbr-calls-clog2 5)  = 4     3
;; (nbr-calls-clog2 6)  = 4     3
;; (nbr-calls-clog2 7)  = 4     3
;; (nbr-calls-clog2 8)  = 4     3
;; (nbr-calls-clog2 9)  = 5     4
;; (nbr-calls-clog2 10) = 5     4
;; (nbr-calls-clog2 11) = 5     4
;; (nbr-calls-clog2 12) = 5     4
;; (nbr-calls-clog2 13) = 5     4
;; (nbr-calls-clog2 14) = 5     4
;; (nbr-calls-clog2 15) = 5     4
;; (nbr-calls-clog2 16) = 5     4
;; (nbr-calls-clog2 17) = 6     5

(defthm
 nbr-calls-clog2=1+clog2
 (implies (posp n)
	   (equal (nbr-calls-clog2 n)
		  (+ 1 (clog2 n)))))

(defun
 nbr-calls-flog2 (n)
 (if (zp n)
     1
     (if (evenp n)
	  (+ 1 (nbr-calls-flog2 (/ n 2)))
	  (+ 1 (nbr-calls-flog2 (- n 1))))))

;;                           floor  ceiling
;;                            lg2     lg2
;; (nbr-calls-flog2 0)  =  1
;; (nbr-calls-flog2 1)  =  2   0       0
;; (nbr-calls-flog2 2)  =  3   1       1
;; (nbr-calls-flog2 3)  =  4   1       2
;; (nbr-calls-flog2 4)  =  4   2       2
;; (nbr-calls-flog2 5)  =  5   2       3
;; (nbr-calls-flog2 6)  =  5   2       3
;; (nbr-calls-flog2 7)  =  6   2       3
;; (nbr-calls-flog2 8)  =  5   3       3
;; (nbr-calls-flog2 9)  =  6   3       4
;; (nbr-calls-flog2 10) =  6   3       4
;; (nbr-calls-flog2 11) =  7   3       4
;; (nbr-calls-flog2 12) =  6   3       4
;; (nbr-calls-flog2 13) =  7   3       4
;; (nbr-calls-flog2 14) =  7   3       4
;; (nbr-calls-flog2 15) =  8   3       4
;; (nbr-calls-flog2 16) =  6   4       4

;; (nbr-calls-flog2 31) = 10   4       5
;; (nbr-calls-flog2 32) =  7   5       5
;; (nbr-calls-flog2 33) =  8   5       6

;; conjecture:
;; For n >= 3
;;   2 + (floorlg2 n) <= (nbr-calls-flog2 n) <= 2 * (ceilinglg2 n)
;; This conjecture seems difficult for ACL2 to verify.

;; Modify the above conjecture.
;; conjecture:
;; For n >= 1
;;   2 + (floorlg2 n) <= (nbr-calls-flog2 n) <= 2 + 2 * (floorlg2 n)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
 nbr-calls-flog2-lower-bound
 (implies (posp n)
	   (<= (+ 2 (flog2 n))
	       (nbr-calls-flog2 n))))

(defthm
 nbr-calls-flog2-upper-bound
 (and (implies (and (posp n)
		     (evenp n))
		(<= (nbr-calls-flog2 n)
		    (+ 1 (* 2 (flog2 n)))))
      (implies (and (posp n)
		     (oddp n))
		(<= (nbr-calls-flog2 n)
		    (+ 2 (* 2 (flog2 n)))))))

(defthm
 nbr-calls-flog2-is-logarithmic
 (implies (posp n)
	   (and (<= (+ 2 (flog2 n))
		    (nbr-calls-flog2 n))
		(<= (nbr-calls-flog2 n)
		    (+ 2 (* 2 (flog2 n))))))
 :hints (("Goal"
	   :use nbr-calls-flog2-upper-bound)))