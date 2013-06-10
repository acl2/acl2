;;; ===================================================================
;;; Definitions of functions needed by a  small benchmark for the performance
;;; of the unification algorithm. 
;;; ===================================================================


(include-book "dag-unification-st")

;;; Some examples:

(dag-mgu '(f x x) '(f (h y) z))
; (T ((Z H Y) (X H Y)))
(dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h u) v)))
; (T ((V H (H Z)) (U H Z) (X H Z)))
(dag-mgu '(f (h z) (g (h x) (h u))) '(f x (g (h y) v)))
; (T ((V H U) (Y H Z) (X H Z)))
(dag-mgu '(f y x) '(f (k x) y))
; (NIL NIL)


;;; Unifiability (note thta we do not require to rebuild the unifier,
;;; only a boolean indicating unifiability):

(defun dag-unifiable-aux (t1 t2 terms-dag)
  (declare (xargs :stobjs terms-dag
		  :guard (and (term-p t1) (term-p t2)
			      (empty-graph-p-st terms-dag))))

  (mv-let (sol bool terms-dag)
	  (dag-mgu-st t1 t2 terms-dag)
	  (declare (ignore sol))
	  (mv bool terms-dag)))

(defun dag-unifiable (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (with-local-stobj
   terms-dag
   (mv-let (bool terms-dag)
	   (dag-unifiable-aux t1 t2 terms-dag)
	   bool)))


;;; -------------------------------------------------------------------------------
;;; Building the unification problem 
;;; T_n={ x_n=f(x_{n-1},x_{n-1}), ....,
;;;        x_2=f(x_1,x_1), x_1=f(x_0,x_0)} 

;;; This problem is very easy to solve
;;; (it is already in dag form), in linear time and constant space:


(defun list-of-n-bis (n)
   (declare (xargs :guard (and (integerp n) (>= n 0))))
   (if (zp n)
       nil
     (cons n (list-of-n-bis (1- n)))))

(defun list-of-f (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (list 'f (1- n) (1- n))
	  (list-of-f (1- n)))))

(defun exp-unif-problem-t1 (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (list-of-n-bis n)))

(defun exp-unif-problem-t2 (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (list-of-f n)))

(defun exp-unif-problem (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (dag-unifiable (exp-unif-problem-t1 n)
		 (exp-unif-problem-t2 n)))


(comp t)
;;; Benchamark: we can easily compute (exp-unif-problem n) for n=500
;;; *********



;;; -------------------------------------------------------------------------------
;;; Building the unification problem 
;;; U_n={ x_1=f(x_0,x_0), x_2=f(x_1,x_1), ...., 
;;;          x_n=f(x_{n-1},x_{n-1})} 
;;; This problem is solved in exponential time, because when solving the
;;; last equation it needes to do occur check in a a complete binary
;;; tree of height n.


(defun exp-unif-problem-t1-rev (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (reverse (list-of-n-bis n))))

(defun exp-unif-problem-t2-rev (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (reverse (list-of-f n))))


(defun exp-unif-problem-rev (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (dag-unifiable (exp-unif-problem-t1-rev n)
		 (exp-unif-problem-t2-rev n)))


(comp t)
;;; Benchmark: evaluate (exp-unif-problem-rev n) for n=20 to n=27
;;; *********

;;; -------------------------------------------------------------------------------
;;; We could fix the problem that appeared in the last example, but
;;; the algorithm we describe here is still exponential in time,as we
;;; have seen for the last example. The following unification problem
;;; reach also that complexity. This unification problem solves the
;;; following system of equations:
;;; $\{x_n=f(x_{n-1},x_{n-1}),\ldots,x_1=f(x_0,x_0),
;;; y_n=f(y_{n-1},y_{n-1}),\ldots,y_1=f(y_0,y_0), x_n=y_n,\ldots,x_0=y_0 \}$


(defun list-of-n- (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (- n) (list-of-n- (1- n)))))

(defun list-of-f- (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
    (cons (list 'f (- (1- n)) (- (1- n)))
	  (list-of-f- (1- n)))))

(local
 (defthm term-p-aux-append
   (implies (and (not flg) (true-listp l1) (true-listp l2))
	    (equal (term-p-aux flg (append l1 l2))
		   (and (term-p-aux flg l1)
			(term-p-aux flg l2))))
   :hints (("Goal" :induct (term-p-aux flg l1)))))

(defun exp-unif-problem-t1-q (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-n-bis n) (list-of-n- n) (list n))))

(defun exp-unif-problem-t2-q (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-f n) (list-of-f- n) (list (- n)))))

(defun exp-unif-problem-q (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (dag-unifiable (exp-unif-problem-t1-q n)
		 (exp-unif-problem-t2-q n)))


(comp t)
;;; Benchmark: evaluate (exp-unif-problem-q n) for n=20 to n=27
;;; *********


;;; -------------------------------------------------------------------------------
;;; Analogue to the previous unification problem, but not unifiable. 

(defun exp-unif-problem-t1-qn (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-n-bis n) (list-of-n- n) (list n '(a)))))

(defun exp-unif-problem-t2-qn (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cons 'l (append (list-of-f n) (list-of-f- n) (list (- n) '(b)))))

(defun exp-unif-problem-qn (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (dag-unifiable (exp-unif-problem-t1-qn n)
		 (exp-unif-problem-t2-qn n)))


(comp t)
;;; Benchmark: evaluate (exp-unif-problem-qn n) for n=20 to n=27
;;; *********

;;; ===============================================================
;;; REMARK:
;;; We have a verified implementation of a quadratic unification
;;; algorithm. See the paper in ACL2 Workshop 2004
;;; ===============================================================


