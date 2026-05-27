(in-package "DM")

(include-book "projects/linear/support/reduction" :dir :system)
(include-book "projects/linear/support/cramer" :dir :system)

;;---------------------------------------------------------------------------------------------------------------------
;;  Vector Space Axioms
;;---------------------------------------------------------------------------------------------------------------------

;; Finite dimensional vector space over f:

(encapsulate (((vp *) => *)        ;vector recognizer
              ((v+ * *) => *)      ;vector addition
	      ((v0) => *)          ;zero vector
	      ((v- *) => *)        ;additive inverse
	      ((v* * *) => *)      ;scalar multiplication
	      ((vbasis0) => *)     ;canonical basis
	      ((vcoords0 *) => *)) ;coordinates relative ro basis
  (local (defun vp (x) (fp x)))
  (local (defun v+ (x y) (f+ x y)))
  (local (defun v0 () (f0)))
  (local (defun v- (x) (f- x)))
  (local (defun v* (c x) (f* c x)))
  (local (defun vbasis0 () (list (f1))))
  (local (defun vcoords0 (x) (list x)))
  (defthm vp-v0
    (vp (v0)))
  (defthm vp-v-
    (implies (vp x) (vp (v- x))))
  ;; Vector addition:
  (defthm v+closed (implies (and (vp x) (vp y)) (vp (v+ x y))))
  (defthmd v+comm
    (implies (and (vp x) (vp y)) (equal (v+ x y) (v+ y x)))
    :hints (("Goal" :use (f+comm))))
  (defthmd v+assoc
    (implies (and (vp x) (vp y) (vp z)) (equal (v+ x (v+ y z)) (v+ (v+ x y) z)))
    :hints (("Goal" :use (f+assoc))))
  (defthm v+id
    (implies (vp x) (equal (v+ x (v0)) x)))
  (defthm v+inv
    (implies (vp x) (equal (v+ x (v- x)) (v0))))
  ;; Scalar multiplication:
  (defthm v*closed
    (implies (and (fp c) (vp x)) (vp (v* c x))))
  (defthm v*id
    (implies (vp x) (equal (v* (f1) x) x)))
  (defthmd v*assoc
    (implies (and (fp c) (fp d) (vp x)) (equal (v* c (v* d x)) (v* (f* c d) x)))
    :hints (("Goal" :use ((:instance f*assoc (x c) (y d) (z x))))))
  (defthmd vdistf
    (implies (and (fp c) (fp d) (vp x)) (equal (v+ (v* c x) (v* d x)) (v* (f+ c d) x)))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y d) (z x))))))
  (defthmd vdistv
    (implies (and (fp c) (vp x) (vp y)) (equal (v+ (v* c x) (v* c y)) (v* c (v+ x y))))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y x) (z y))))))
  ;; List of vectors:
  (defun vlistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (vp (car x))
	   (vlistnp (cdr x) (1- n)))))
  ;; Linear combination of a list of vectors:
  (defun vcomb (flist vlist)
    (if (consp flist)
        (v+ (v* (car flist) (car vlist))
	    (vcomb (cdr flist) (cdr vlist)))
      (v0)))
  ;; Basis and coordinates:
  (defun vdim () (len (vbasis0)))
  (defthmd posp-vdim
    (posp (vdim)))
  (in-theory (disable (vdim) (vlistnp) (vcomb)))
  (defthm vlistnp-basis
    (vlistnp (vbasis0) (vdim)))
  (defthm flistnp-vcoords0
    (implies (vp x) (flistnp (vcoords0 x) (vdim))))
  (defthm vbasis0-spans
    (implies (vp x)
             (equal (vcomb (vcoords0 x) (vbasis0))
		    x)))
  (defthmd vbasis0-lin-indep
    (implies (and (flistnp c (vdim))
                  (equal (vcomb c (vbasis0)) (v0)))
	     (equal (flistn0 (vdim)) c)))
  (in-theory (disable vdim)))

;; Some simple consequences of the axioms and definitions:

(defthm v+id-comm
  (implies (vp x) (equal (v+ (v0) x) x))
  :hints (("Goal" :use ((:instance v+comm (y (v0)))))))

(defthm v+inv-comm
  (implies (vp x) (equal (v+ (v- x) x) (v0)))
  :hints (("Goal" :use ((:instance v+comm (y (v- x)))))))

(defthm f0*v0
  (implies (vp x) (equal (v* (f0) x) (v0)))
  :hints (("Goal" :use ((:instance vdistf (c (f1)) (d (f0)))
			(:instance v+assoc (x (v- x)) (y x) (z (v* (f0) x)))))))

(defthm c*v0
  (implies (fp c) (equal (v* c (v0)) (v0)))
  :hints (("Goal" :use ((:instance vdistv (x (v0)) (y (v0)))
			(:instance v+assoc (x (v- (v* c (v0)))) (y (v* c (v0))) (z (v* c (v0))))))))

(defthm vp-vcomb
  (implies (and (flistnp c n) (vlistnp l n))
	   (vp (vcomb c l))))

(defthm len-vlistnp
  (implies (and (natp n) (vlistnp x n))
           (equal (len x) n))
  :hints (("Goal" :induct (nthcdr n x))))

(defun vp-nth-vlistnp-induct (x n j)
  (if (zp j)
      (list x n j)
    (list (vp-nth-vlistnp-induct (cdr x) (1- n) (1- j)))))

(defthm vp-nth-vlistnp
  (implies (and (vlistnp x n) (natp n) (natp j) (< j n))
           (vp (nth j x)))
  :hints (("Goal" :induct (vp-nth-vlistnp-induct x n j))))

(local-defthmd hack-1
  (implies (and (fp x0) (fp y0) (vp l0) (vp lx) (vp ly))
	   (equal (v+ (v* (f+ x0 y0) l0) (v+ lx ly))
		  (v+ (v+ (v* x0 l0) lx) (v+ (v* y0 l0) ly))))
  :hints (("Goal" :use ((:instance v+assoc (x (v+ (v* x0 l0) lx)) (y (v* y0 l0)) (z ly))
			(:instance v+assoc (x (v* x0 l0)) (y lx) (z (v* y0 l0)))
			(:instance v+comm (x lx) (y (v* y0 l0)))
			(:instance v+assoc (x (v* x0 l0)) (y (v* y0 l0)) (z lx))
			(:instance v+assoc (x (v+ (v* x0 l0) (v* y0 l0))) (y lx) (z ly))
			(:instance vdistf (c x0) (d y0) (x l0))))))

(defthmd vcomb-add
  (implies (and (natp n) (vlistnp l n) (flistnp x n) (flistnp y n))
	   (equal (vcomb (flist-add x y) l)
		  (v+ (vcomb x l) (vcomb y l))))
  :hints (("Subgoal *1/6" :use ((:instance hack-1 (x0 (car x)) (y0 (car y)) (l0 (car l))
					   (lx (VCOMB (CDR X) (CDR L))) (ly (VCOMB (CDR y) (CDR L))))))))

(defthmd vcomb-scalar-mul
  (implies (and (natp n) (vlistnp l n) (flistnp x n) (fp c))
	   (equal (vcomb (flist-scalar-mul c x) l)
		  (v* c (vcomb x l))))
  :hints (("Subgoal *1/5" :use ((:instance v*assoc (d (car x)) (x (car l)))
				(:instance vdistv (x (v* (car x) (car l))) (y (VCOMB (CDR X) (CDR L))))))))

;; The list of coordinates of a vector is unique:

(local-defthmd vcoords0-unique-1
  (implies (and (natp n) (flistnp x n) (flistnp y n) (vlistnp l n)
		(= (vcomb x l) (vcomb y l)))
	   (equal (vcomb (flist-add x (flist-scalar-mul (f- (f1)) y)) l)
		  (v0)))
  :hints (("Goal" :in-theory (enable vcomb-add vcomb-scalar-mul)
	          :use ((:instance vdistf (c (f1)) (d (f- (f1))) (x (vcomb x l)))))))

(local-defthmd vcoords0-unique-2
  (implies (and (flistnp x (vdim)) (flistnp y (vdim))
		(= (vcomb x (vbasis0)) (vcomb y (vbasis0))))
	   (equal (flist-add x (flist-scalar-mul (f- (f1)) y))
		  (flistn0 (vdim))))
  :hints (("Goal" :in-theory (enable vdim)
                  :use (vlistnp-basis
		        (:instance vcoords0-unique-1 (n (vdim)) (l (vbasis0)))
                        (:instance vbasis0-lin-indep (c (flist-add x (flist-scalar-mul (f- (f1)) y))))))))

(local-defthm vcoords0-unique-3
  (implies (and (fp x) (fp y) (= (f+ x (f* (f- (f1)) y)) (f0)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance f+assoc (y (f* (f- (f1)) y)) (z y))
                        (:instance fdist-comm (x (f- (f1))) (y (f1)) (z y))))))

(local-defthm vcoords0-unique-4
  (implies (and (natp n) (flistnp x n) (flistnp y n)
	        (equal (flist-add x (flist-scalar-mul (f- (f1)) y))
		       (flistn0 n)))
	   (equal x y))
  :rule-classes ()
  :hints (("Subgoal *1/7" :use ((:instance vcoords0-unique-3 (x (car x)) (y (car y)))))))

(defthmd vcoords0-unique
  (implies (and (vp x) (flistnp c (vdim))
		(equal (vcomb c (vbasis0)) x))
	   (equal (vcoords0 x) c))
  :hints (("Goal" :use ((:instance vcoords0-unique-4 (n (vdim)) (x c) (y (vcoords0 x)))
                        (:instance vcoords0-unique-2 (x c) (y (vcoords0 x)))))))

;; In particular, since (vcomb (flistn0 (vdim)) (vbasis0)) = (v0), (vcoords0 (v0)) = (flistn0 (vdim)):

(defthm vcomb-flistn0
  (implies (vlistnp l n)
           (equal (vcomb (flistn0 n) l)
	          (v0)))
  :hints (("Goal" :induct (nthcdr n l))))

(defthm vcoords0-v0
  (equal (vcoords0 (v0))
         (flistn0 (vdim)))
  :hints (("Goal" :use ((:instance vcoords0-unique (x (v0)) (c (flistn0 (vdim))))))))


;;---------------------------------------------------------------------------------------------------------------------
;;  Linear Dependence
;;---------------------------------------------------------------------------------------------------------------------

;; We define the coordinate matrix of a list of vectors:

(defun vcoord-mat (l)
  (if (consp l)
      (cons (vcoords0 (car l))
	    (vcoord-mat (cdr l)))
    ()))

(in-theory (enable fmatp))

(defthm fmatp-vcoord-mat
  (implies (vlistnp l m)
           (fmatp (vcoord-mat l) m (vdim)))
  :hints (("Goal" :induct (nthcdr m l))))

;; Assume (vlistnp l m) ,where m > 0.  We shall show that the coordinates of any linear combination (vcomb c l) of l
;; may be derived by multiplying the row matrix of c by the coordinate matrix of l and extracting the single row of
;; the result:

;;    (vcoords0 (vcomb c l)) = (row 0 (fmat* (row-mat c) (vcoord-mat l))).

;; By vcoords0-unique, it suffices to show that (vcomb (row 0 (fmat* (list c) (vcoord-mat l))) (vbasis0)) = (vcomb c l).
;; We shall prove this by induction.  If m = 1, then

;;    (vcomb (row 0 (fmat* (list c) (vcoord-mat l))) (vbasis0)
;;      = (vcomb (flist-scalar-mul (car c) (vcoords0 (car l))) (vbasis0))
;;      = (v* (car c) (vcomb (vcoords0 (car l)) (vbasis0)))
;;      = (v* (car c) (car l))
;;      = (vcomb c l).

(local-defthmd vcoords0-vcomb-1
  (implies (and (vlistnp l 1) (flistnp c 1) (natp j) (< j (vdim)))
           (equal (nth j (car (fmat* (list c) (vcoord-mat l))))
	          (f* (car c) (nth j (vcoords0 (car l))))))
  :hints (("Goal" :use ((:instance fmat*-entry (i 0) (m 1) (n 1) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance fp-flistnp (i j) (n (vdim)) (x (vcoords0 (car l)))))
                  :in-theory (disable (fdot))
                  :expand ((flistnp c 1) (vlistnp l 1)))))

(local-defthmd vcoords0-vcomb-2
  (implies (and (vlistnp l 1) (flistnp c 1) (natp j) (< j (vdim)))
           (equal (nth j (flist-scalar-mul (car c) (vcoords0 (car l))))
	          (nth j (car (fmat* (list c) (vcoord-mat l))))))
  :hints (("Goal" :use (vcoords0-vcomb-1
                        (:instance nth-flist-scalar-mul (c (car c)) (x (vcoords0 (car l))) (n (vdim)) (i j))))))

(local-defthmd vcoords0-vcomb-3
  (implies (and (vlistnp l 1) (flistnp c 1))
           (equal (car (fmat* (list c) (vcoord-mat l)))
	          (flist-scalar-mul (car c) (vcoords0 (car l)))))
  :hints (("Goal" :use (posp-vdim
                        (:instance nth-diff-diff (x (car (fmat* (list c) (vcoord-mat l))))
                                                 (y (flist-scalar-mul (car c) (vcoords0 (car l)))))
			(:instance vcoords0-vcomb-2 (j (nth-diff (car (fmat* (list c) (vcoord-mat l)))
			                                        (flist-scalar-mul (car c) (vcoords0 (car l))))))
			(:instance fmatp-fmat* (m 1) (n 1) (p (vdim)) (a (list c)) (b (vcoord-mat l))))
		  :expand ((fmatp (fmat* (list c) (vcoord-mat l)) 1 (vdim))))))

(local-defthmd vcoords0-vcomb-4
  (implies (and (vlistnp l 1) (flistnp c 1))
           (equal (vcomb (car (fmat* (list c) (vcoord-mat l))) (vbasis0))
	          (vcomb c l)))
  :hints (("Goal" :use (posp-vdim) :in-theory (enable vcomb-scalar-mul vcoords0-vcomb-3))))

;; Now suppose m > 1 and assume the claim is true when c and l are repaced by (cdr c) and (cdr l).
;; Let a = (vcoord-mat l).  We shall show first that

;;    (car (fmat* (list c) a) = (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))).

;; To prove this, it suffices to show that for j < (vdim), the jth members of these lists are equal.  But

;;    (nth j (car (fmat* (list c) a))) = (entry 0 j (fmat* (list c) a))
;;                                     = (fdot c (col j a))
;;                                     = (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a))))

(local-defthmd vcoords0-vcomb-5
  (implies (and (posp m) (vlistnp l m) (flistnp c m) (natp j) (< j (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (nth j (car (fmat* (list c) a)))
	            (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a)))))))
  :hints (("Goal" :use ((:instance fmat*-entry (i 0) (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))))))

;; and

;;    (nth j (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))))
;;      = (f+ (f* (car c) (nth j (car a))) (entry 0 j (fmat* (list (cdr c)) (cdr a))))
;;      = (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a)))).

(local-defthmd vcoords0-vcomb-6
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)) (natp j) (< j (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (nth j (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a)))))
		    (f+ (f* (car c) (nth j (car a)))
		        (entry 0 j (fmat* (list (cdr c)) (cdr a)))))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :expand ((FLISTNP (CAR (VCOORD-MAT L)) (VDIM)))
                  :use (fmatp-vcoord-mat
                        (:instance nth-flist-add (x (flist-scalar-mul (car c) (car (vcoord-mat l))))
                                                 (y (car (fmat* (list (cdr c)) (cdr (vcoord-mat l)))))
						 (i j) (n (vdim)))
			(:instance nth-flist-scalar-mul (i j) (n (vdim)) (c (car c)) (x (vcoords0 (car l))))
                        (:instance flist-scalar-mul (c (car c)) (x (car (vcoord-mat l))))			
			(:instance fmatp-fmat* (m 1) (n (1- m)) (p (vdim)) (a (LIST (CDR C))) (b (CDR (VCOORD-MAT L))))))))

(local-defthmd vcoords0-vcomb-7
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)) (natp j) (< j (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (nth j (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a)))))
		    (nth j (car (fmat* (list c) a))))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :use (vcoords0-vcomb-5 vcoords0-vcomb-6 fmatp-vcoord-mat
                        (:instance fmat*-entry (m 1) (n (1- m)) (p (vdim))
			                       (a (list (cdr c))) (b (cdr (vcoord-mat l))) (i 0))))))

(local-defthmd vcoords0-vcomb-8
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (flist-add (flist-scalar-mul (car c) (car a))
	                       (car (fmat* (list (cdr c)) (cdr a))))
		    (car (fmat* (list c) a)))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :use (fmatp-vcoord-mat
		        (:instance vcoords0-vcomb-7 (j (nth-diff (flist-add (flist-scalar-mul (car c) (car (vcoord-mat l)))
	                                                                   (car (fmat* (list (cdr c)) (cdr (vcoord-mat l)))))
						                (car (fmat* (list c) (vcoord-mat l))))))
			(:instance nth-diff-diff (x (flist-add (flist-scalar-mul (car c) (car (vcoord-mat l)))
	                                                       (car (fmat* (list (cdr c)) (cdr (vcoord-mat l))))))
						 (y (car (fmat* (list c) (vcoord-mat l)))))
			(:instance flistnp-row (a (FMAT* (LIST C) (VCOORD-MAT L))) (i 0) (m 1) (n (vdim)))
			(:instance flistnp-flist-add (x (FLIST-SCALAR-MUL (CAR C) (CAR (VCOORD-MAT L))))
                                                     (y (CAR (FMAT* (LIST (CDR C)) (CDR (VCOORD-MAT L)))))
						     (n (vdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance fmatp-fmat* (m 1) (n (1- m)) (p (vdim)) (a (LIST (CDR C))) (b (CDR (VCOORD-MAT L))))))))

;; Now complete the proof:

;;   (vcomb (car (fmat* (list c) a)) (vbasis0))
;;     = (vcomb (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))) (vbasis0))
;;     = (v+ (v* (car c) (vcomb (car a) (vbasis0)))
;;           (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0)))
;;     = (v+ (v* (car c) (car l))
;;           (vcomb (cdr c) (cdr l)))
;;     = (vcomb c l).

(local-defthmd vcoords0-vcomb-9
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (vcomb (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a))))
			   (vbasis0))
		    (v+ (v* (car c) (vcomb (car a) (vbasis0)))
		        (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0))))))
  :hints (("Goal" :in-theory (e/d (vcomb-scalar-mul) (fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
		        (:instance vcomb-add (x (flist-scalar-mul (car c) (car (vcoord-mat l))))
			                     (y (car (fmat* (list (cdr c)) (cdr (vcoord-mat l)))))
					     (n (vdim)) (l (vbasis0)))
			(:instance flistnp-row (a (FMAT* (LIST C) (VCOORD-MAT L))) (i 0) (m 1) (n (vdim)))
			(:instance flistnp-flist-scalar-mul (c (car c)) (x (car (vcoord-mat l))) (n (vdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance fmatp-fmat* (m 1) (n (1- m)) (p (vdim)) (a (LIST (CDR C))) (b (CDR (VCOORD-MAT L))))))))

(local-defthmd vcoords0-vcomb-10
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (implies (equal (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0))
	                     (vcomb (cdr c) (cdr l)))
	              (equal (vcomb (flist-add (flist-scalar-mul (car c) (car a))
	                                       (car (fmat* (list (cdr c)) (cdr a))))
			            (vbasis0))
		             (vcomb c l)))))
  :hints (("Goal" :use (vcoords0-vcomb-9))))

(local-defthmd vcoords0-vcomb-11
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (implies (equal (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0))
	                     (vcomb (cdr c) (cdr l)))
	              (equal (vcomb (car (fmat* (list c) a)) (vbasis0))
		             (vcomb c l)))))
  :hints (("Goal" :use (vcoords0-vcomb-10 vcoords0-vcomb-8))))

(local-defthmd vcoords0-vcomb-12
  (implies (and (posp m) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (equal (vcomb (car (fmat* (list c) (vcoord-mat l))) (vbasis0))
		  (vcomb c l)))
  :hints (("Subgoal *1/5" :use (vcoords0-vcomb-4 vcoords0-vcomb-11))
          ("Subgoal *1/2" :use (vcoords0-vcomb-4))))

(defthmd vcoords0-vcomb
  (implies (and (posp m) (vlistnp l m) (flistnp c m))
	   (equal (vcoords0 (vcomb c l))
		  (car (fmat* (list c) (vcoord-mat l)))))
  :hints (("Goal" :use (posp-vdim vcoords0-vcomb-12
			(:instance fmatp-fmat* (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance vcoords0-unique (x (vcomb c l)) (c (car (fmat* (list c) (vcoord-mat l)))))))))

;; This formula is the basis of our definition of linear independence:

(defund vindepp (l)
  (equal (row-rank (vcoord-mat l))
         (len l)))

(defund vdepp (l)
  (not (vindepp l)))

;; To confirm that the definition has the intended meaning, we must first show that if (vdepp l), then
;; (v0) is a nontrivial linearly combination of l.  The required  coefficients may be constructed as follows:

(defun vdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (vcoord-mat l))))

(in-theory (enable fmat*))

(defthmd fmat*-nth
  (implies (and (fmatp a m n) (fmatp b n p) (posp m) (natp n) (natp p) (natp i) (< i m))
           (equal (car (fmat* (list (nth i a)) b))
	          (nth i (fmat* a b)))))

;; Let m = (len l), a = (vcoord-mat l), c = (vdep-coeffs l), and p = (row-reduce-mat (vcoord-mat l)).  
;; Then c is the last row of p.  Since p is invertible, (vdep-coeffs l) != (flistn0 m).  But

;;   (vcoords0 (vcomb c l)) = (car (fmat* (list c) a))
;;                         = (nth (1- m) (fmat* p a))
;;                         = (nth (1- m) (row-reduce a))
;;                         = (flistn0 (vdim)),

;; which implies (vcomb c l) = (v0):

(local-defthmd vdepp-vcomb-v0-1
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
	   (let ((c (vdep-coeffs l)))
             (equal (vcoords0 (vcomb c l))
	            (nth (1- m) (row-reduce (vcoord-mat l))))))
  :hints (("Goal" :in-theory (e/d (row-ops-mat-row-reduce) (fmat* fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
                        (:instance vcoords0-vcomb (c (vdep-coeffs l)))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (a (row-reduce-mat (vcoord-mat l))) (n m) (i (1- m)))
			(:instance fmat*-nth (i (1- m)) (n m) (p (vdim)) (b (vcoord-mat l))
			                     (a (row-reduce-mat (vcoord-mat l))))))))
                        
(local-defthmd vdepp-vcomb-v0-2
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
  	   (equal (nth (1- m) (row-reduce (vcoord-mat l)))
	          (flistn0 (vdim))))
  :hints (("Goal" :in-theory (enable vindepp vdepp)
                  :use (vdepp-vcomb-v0-1
		        (:instance num-nonzero-rows-nonzero (a (row-reduce (vcoord-mat l))) (n (vdim)) (i (1- m)))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (a (row-reduce-mat (vcoord-mat l))) (n m) (i (1- m)))
		        (:instance flist0p-flistn0-len (x (vcoords0 (vcomb (vdep-coeffs l) l))))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance row-rank<=m (a (vcoord-mat l)) (n (vdim)))
                        (:instance row-echelon-p-row-reduce (n (vdim)) (a (vcoord-mat l)))))))

(local-defthmd vdepp-vcomb-v0-3
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
	   (let ((c (vdep-coeffs l)))
  	     (equal (vcoords0 (vcomb c l))
	            (flistn0 (vdim)))))
  :hints (("Goal" :use (vdepp-vcomb-v0-1 vdepp-vcomb-v0-2))))

(local-defthmd vdepp-vcomb-v0-4
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
	          (not (equal c (flistn0 m))))))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (a (row-reduce-mat (vcoord-mat l))) (n m) (i (1- m)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-fdet-not-zero (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fdet-row-0 (a (row-reduce-mat (vcoord-mat l))) (n m) (k (1- m)))))))

(local-defthmd vdepp-vcomb-v0-5
  (implies (and (natp n) (vlistnp b n))
           (equal (vcomb (flistn0 n) b)
	          (v0))))

(defthmd vdepp-vcomb-v0
  (implies (and (posp m) (vlistnp l m) (vdepp l))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (= c (flistn0 m)))
		  (equal (vcomb c l) (v0)))))
  :hints (("Goal" :in-theory (disable vbasis0-spans)
                  :use (vdepp-vcomb-v0-3 vdepp-vcomb-v0-4 posp-vdim
                        (:instance vdepp-vcomb-v0-5 (n (vdim)) (b (vbasis0)))
			(:instance vbasis0-spans (x (vcomb (vdep-coeffs l) l)))
		        (:instance flist0p-flistn0-len (x (vcoords0 (vcomb (vdep-coeffs l) l))))))))

;; Note that the axiom vbasis0-lin-indep ensures that vbasis0 is a linearly independent list:

(defthm vindepp-vbasis0
  (vindepp (vbasis0))
  :hints (("Goal" :use (posp-vdim
                        (:instance vdepp-vcomb-v0 (m (vdim)) (l (vbasis0)))
                        (:instance vbasis0-lin-indep (c (vdep-coeffs (vbasis0))))))))

;; We must also show that if (vindepp l), then (v0) is not a nontrivial linearly combination of l.
;; Assume (flistnp c m).  We must show that if (car (fmat* (list c) a)) = (flistn0 (vdim)), then
;; c = (flistn0 m).  We first show that this holds if a is replaced by r = (row-reduce a).
;; Let i < m and j = (nth i (lead-inds r)).  By fmat*-entry,

;;    (nth j (car (fmat* (list c) r))) = (entry 0 j (fmat* (list c) r)) = (fdot c (col j r)),

;; and it follows from  nth-col-lead-inds that (fdot c (col j r)) = (nth i c):

(local-defthmd row-echelon-p-vindepp-1
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m)
		(dlistp l)
		(sublistp l (ninit m)))
	   (equal (fdot-select l c (col (nth i (lead-inds r)) r))
	          (if (member i l) (nth i c) (f0))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance nth-col-lead-inds (a r) (k (car l)))
	                        (:instance member-ninit (n m) (x (car l)))))))

(local-defthmd row-echelon-p-vindepp-2
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (fdot c (col (nth i (lead-inds r)) r))
	          (nth i c)))
  :hints (("Goal" :in-theory (e/d (row-rank) (member-sublist))
                  :use ((:instance len-lead-inds-num-nonzero-rows (a r))
		        (:instance sublistp-lead-inds-ninit (a r))
		        (:instance row-echelon-p-vindepp-1 (l (ninit m)))
			(:instance member-ninit (x i) (n m))
			(:instance row-reduce-row-echelon-p (a r))
			(:instance member-ninit (x (nth i (lead-inds r))))
			(:instance member-sublist (x (nth i (lead-inds r))) (l (lead-inds r)) (m (ninit n)))
                        (:instance fdot-select-ninit (n m) (x c) (y (col (nth i (lead-inds r)) r)))
			(:instance flistnp-col (a r) (j (nth i (lead-inds r))))))))

(defthmd entry-fmat*-row-echelon-p
  (implies (and (posp m) (posp n) (fmatp r m n)
                (row-echelon-p r) (= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (nth (nth i (lead-inds r)) (car (fmat* (list c) r)))
	          (nth i c)))
  :hints (("Goal" :in-theory (e/d (row-rank) (fmat*))
                  :use (row-echelon-p-vindepp-2
		        (:instance len-lead-inds-num-nonzero-rows (a r))
			(:instance row-reduce-row-echelon-p (a r))
			(:instance nth-lead-inds-bound (a r) (k i))
                        (:instance fmat*-entry (i 0) (j (nth i (lead-inds r))) (m 1) (n m) (p n) (a (list c)) (b r))))))

;; But since (car (fmat* (list c) a)) = (flistn0 (vdim)), (nth i c) = (f0) for all i, i.e., c = (flistn0 m):

(local-defthmd row-echelon-p-vindepp-3
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n))
		(natp j)
		(< j n))
	   (equal (nth j (car (fmat* (list c) r)))
	          (f0))))

(local-defthmd row-echelon-p-vindepp-4
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n))
		(natp i)
		(< i m))
	   (equal (nth i c) (f0)))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use (entry-fmat*-row-echelon-p
                        (:instance nth-lead-inds-bound (a r) (k i))
			(:instance row-reduce-row-echelon-p (a r))
                        (:instance row-echelon-p-vindepp-3 (j (nth i (lead-inds r))))))))

(defthm row-echelon-p-vindepp
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n)))
	   (equal c (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance nth-diff-diff (x c) (y (flistn0 m)))
                        (:instance row-echelon-p-vindepp-4 (i (nth-diff c (flistn0 m))))))))

;; Suppose (vcomb c l) = (v0).  Then (car (fmat* (list c) a)) = (vcoords0 (v0)) = (flistn0 (vdim)).
;; Let r = (row-reduce a), p = (row-reduce-mat a), and c' = (car (fmat* (list c) (inverse-mat p))).
;; Then r = (fmat* p a), which implies a = (fmat* (inverse-mat p) r) and

;;   (fmat* (list c') r) = (fmat* (fmat* (list c) (inverse-mat p)) r)
;;                       = (fmat* (list c) (fmat* (inverse-mat p) r))
;;                       = (fmat* (list c) a):

(local-defthmd vindepp-vcomb-v0-1
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (equal (car (fmat* (list c) (vcoord-mat l)))
	          (flistn0 (vdim))))
  :hints (("Goal" :use (vcoords0-vcomb vcoords0-v0))))

(local-defthmd vindepp-vcomb-v0-2
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (fmat* (list c) (inverse-mat p)) r)
	            (fmat* (list c) (fmat* (inverse-mat p) r)))))
  :hints (("Goal" :in-theory (e/d (fmatp) (fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
		        (:instance fmat*-assoc (m 1) (n m) (p m) (q (vdim)) (a (list c))
                                               (b (inverse-mat (row-reduce-mat (vcoord-mat l))))
					       (c (row-reduce (vcoord-mat l))))
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))))))

(local-defthmd vindepp-vcomb-v0-3
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (inverse-mat p) r)
	            a)))
  :hints (("Goal" :in-theory (e/d (fmatp) (fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
		        (:instance fmat*-assoc (n m) (p m) (q (vdim))
                                               (a (inverse-mat (row-reduce-mat (vcoord-mat l))))
                                               (b (row-reduce-mat (vcoord-mat l)))
					       (c (vcoord-mat l)))
			(:instance id-fmat-left (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance row-ops-mat-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))))))

(defthmd fmat*-vcomb-row-reduce
  (implies (and (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (fmat* (list c1) r)
	            (fmat* (list c) a))))
  :hints (("Goal" :use (posp-vdim vindepp-vcomb-v0-2 vindepp-vcomb-v0-3))))

;; Thus, (car (fmat* (list c') r) = (flistn0 (vdim)).  By row-echelon-p-vindepp, c' = (flistn0 m),
;; which implies

;;   (list c) = (fmat* (list (flistn0 m)) p) = (list (flistn0 m))

;; and we have the following:

(local-defthmd vindepp-vcomb-v0-4
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (car (fmat* (fmat* (list c) (inverse-mat p)) r))
	            (flistn0 (vdim)))))
  :hints (("Goal" :use (vindepp-vcomb-v0-1 vindepp-vcomb-v0-2 vindepp-vcomb-v0-3))))

(local-defthm vindepp-vcomb-v0-5
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (list (car (fmat* (list c) (inverse-mat p))))
	            (fmat* (list c) (inverse-mat p)))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :use (fmatp-vcoord-mat
			(:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l)))))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))))))

(local-defthm vindepp-vcomb-v0-6
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (list c) (inverse-mat p))
	            (list (flistn0 m)))))
  :hints (("Goal" :in-theory (e/d (row-echelon-p-row-reduce row-reduce-row-echelon-p vindepp) (fmatp-vcoord-mat fmat*))
                  :use (vindepp-vcomb-v0-4 vindepp-vcomb-v0-5 fmatp-vcoord-mat
                        (:instance row-echelon-p-vindepp
			  (c (car (fmat* (list c) (inverse-mat (row-reduce-mat (vcoord-mat l))))))
			  (r (row-reduce (vcoord-mat l)))
                          (n (vdim)))
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l)))))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))))))

(local-defthm vindepp-vcomb-v0-7
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
 		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (car (fmat* (list (flistn0 m)) p))
	            c)))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat fmat*)
                  :use (vindepp-vcomb-v0-6 fmatp-vcoord-mat
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance id-fmat-right (m 1) (n m) (a (list c)))
			(:instance fmat*-assoc (m 1) (n m) (p m) (q m)
			                       (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l))))
					       (c (row-reduce-mat (vcoord-mat l))))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))))))

(local-defthm vindepp-vcomb-v0-8
  (implies (and (posp m)
		(flistnp c m)
 		(fmatp p m m)
		(natp j)
		(< j m))
	   (equal (nth j (car (fmat* (list (flistn0 m)) p)))
		  (f0)))
  :hints (("Goal" :use ((:instance fmat*-entry (a (list (flistn0 m))) (b p) (m 1) (n m) (p m) (i 0))))))

(local-defthm vindepp-vcomb-v0-9
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
 		(equal (vcomb c l) (v0))
		(natp j)
		(< j m))
	   (equal (nth j c)
		  (f0)))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat fmat*)
                  :use (vindepp-vcomb-v0-7 fmatp-vcoord-mat
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
                        (:instance vindepp-vcomb-v0-8 (p (row-reduce-mat (vcoord-mat l))))))))

(defthm vindepp-vcomb-v0
  (implies (and (posp m)
		(vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (equal c (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use (posp-vdim
                        (:instance nth-diff-diff (x c) (y (flistn0 m)))
                        (:instance vindepp-vcomb-v0-9 (j (nth-diff c (flistn0 m))))))))

;; (v0) is not a member of any linearly independent list:

(defthm vcomb-funit
  (implies (and (natp n) (natp j) (< j n) (vlistnp l n))
           (equal (vcomb (funit j n) l)
	          (nth j l))))

(defthm nth-vindepp-not-v0
  (implies (and (posp m)
		(vlistnp l m)
		(vindepp l)
		(natp j)
		(< j m))
	   (not (equal (nth j l) (v0))))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (posp-vdim
		        (:instance vcomb-funit (n m))
		        (:instance vindepp-vcomb-v0 (c (funit j m)))
			(:instance nth-funit (n m) (i j))))))

(defthm v0-not-member-vindepp
  (implies (and (natp m)
		(vlistnp l m)
		(vindepp l))
	   (not (member (v0) l)))
  :hints (("Goal" :use (posp-vdim
                        (:instance nth-vindepp-not-v0 (j (index (v0) l)))
                        (:instance ind<len (x (v0)))))))

;; If m > (vdim), then since (fmatp a m (vdim)), (row-rank a) <= (vdim) < m, i.e., (vdepp l):

(defthmd vdep-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp l))
  :hints (("Goal" :in-theory (enable vdepp vindepp)
                  :use (posp-vdim (:instance row-rank<=n (a (vcoord-mat l)) (n (vdim)))))))

;; Let l be a list of vectors and let x be a vector.  Suppose l is linearly independent and (cons x l)
;; is linearly dependent.  We shall construct a list of scalars (vcoords x l) such that
;; x = (vcomb (vcoords x l) l).  By vdepp-vcomb-v0,  we have a list c = (vdep-coeffs (cons x b)) such that

;;    (vcomb c (cons x l)) = (v+ (v* (car c) x) (vcomb (cdr c) l)) = (v0).

;; Since l is linearly independent, by vindepp-vcomb-v0, we cannot have (car c) = (f0), and therefore,

;;    x = (vcomb (flist-scalar-mul (f- (f/ (car c))) (cdr c)) l).

;; Thus, we define

(defund vcoords (x l)
  (let ((c (vdep-coeffs (cons x l))))
    (flist-scalar-mul (f- (f/ (car c))) (cdr c))))

;; and we have

(in-theory (disable vdep-coeffs))

(defthmd vdepp-vcomb-1
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)) (posp (vdim)))
           (let ((c (vdep-coeffs (cons x l))))
	     (and (flistnp c (1+ n))
		  (not (= (car c) (f0)))
	          (equal (vcomb c (cons x l)) (v0)))))
  :hints (("Goal" :use ((:instance vdepp-vcomb-v0 (m (1+ n)) (l (cons x l)))
                        (:instance vindepp-vcomb-v0 (m n) (c (cdr (vdep-coeffs (cons x l)))))))))

(defthmd hack-2
  (implies (and (vp x) (vp d) (fp c) (not (= c (f0))) (= (v+ (v* c x) d) (v0)))
           (equal (v* (f- (f/ c)) d) x))
  :hints (("Goal" :use ((:instance vdistv (c (f/ c)) (x (v* c x)) (y d))
                        (:instance v*assoc (c (f/ c)) (d c))
			(:instance v+assoc (y (v* (f/ c) d)) (z (v* (f- (f/ c)) d)))
			(:instance vdistf (c (f/ c)) (d (f- (f/ c))) (x d))))))

(defthmd vdepp-vcomb
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)))
           (and (flistnp (vcoords x l) n)
	        (equal (vcomb (vcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable vcomb-scalar-mul vcoords)
                  :use (vdepp-vcomb-1 posp-vdim
		        (:instance hack-2 (c (CAR (VDEP-COEFFS (CONS X L)))) (d (VCOMB (CDR (VDEP-COEFFS (CONS X L))) L)))))))

;; Conversely, suppose  x is a linear combination of l, say x = (vcomb c l).  Let c' = (cons (f- (f1)) c).
;; Then (vcomb c' (cons x l)) = (v+ (v* (f- (f1)) x) (vcomb c l)) = (v+ (v- x) x) = (v0), and by vindepp-vcomb-v0,
;; (vdepp (cons x l)):

(defthmd vcomb-vdepp
  (implies (and (vlistnp l n) (flistnp c n) (natp n))
           (vdepp (cons (vcomb c l) l)))
  :hints (("Goal" :in-theory (e/d (vdepp) (f-f0))
                  :use (f-f0 posp-vdim
		        (:instance vindepp-vcomb-v0 (c (cons (f- (f1)) c)) (l (cons (vcomb c l) l)) (m (1+ n)))
		        (:instance vdistf (c (f- (f1))) (d (f1)) (x (vcomb c l)))))))

;; An equivalent formulation of linear independence using defun-sk:

(defun-sk vindepp-sk (l)
  (forall (c)
    (implies (and (flistnp c (len l))
                  (equal (vcomb c l) (v0)))
	     (equal c (flistn0 (len l))))))

(defthmd vindepp-sk-lemma
  (implies (and (vindepp-sk l)
                (flistnp c (len l))
                (equal (vcomb c l) (v0)))
	   (equal (flistn0 (len l)) c))
  :hints (("Goal" :use (vindepp-sk-necc))))

(defthmd vindepp-sk-witness-lemma
  (let ((c (vindepp-sk-witness l)))
     (implies (implies (and (flistnp c (len l))
                            (equal (vcomb c l) (v0)))
	               (equal (flistn0 (len l)) c))
	      (vindepp-sk l))))

(in-theory (disable vindepp-sk))

(defthmd vindepp-equivalence
  (implies (and (posp m) (vlistnp l m))
           (iff (vindepp-sk l)
	        (vindepp l)))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (posp-vdim vdepp-vcomb-v0 vindepp-sk-witness-lemma
		        (:instance vindepp-sk-lemma (c (vdep-coeffs l)))
			(:instance vindepp-vcomb-v0 (c (vindepp-sk-witness l)))))))

(defthmd not-vindepp-sk-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (not (vindepp-sk l)))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vindepp-equivalence vdep-if->-dim))))


;;---------------------------------------------------------------------------------------------------------------------
;;  Bases
;;---------------------------------------------------------------------------------------------------------------------

;; We define a vbasis to be a linearly independent list of (vdim) vectors:

(defund vbasisp (l)
  (and (vlistnp l (vdim))
       (vindepp l)))

;; Obviously, the canonical basis is a vbasis:

(defthm vbasisp-vbasis0
  (vbasisp (vbasis0))
  :hints (("Goal" :in-theory (enable vbasisp)))) 

;; By vdep-if->-dim, for any vector x, the list (cons x b) is linearly dependent, and therefore, by vdepp-vcomb,
;; b spans the space:

(defthmd vbasis-spans
  (implies (and (vbasisp b) (vp x))
           (and (flistnp (vcoords x b) (vdim))
	        (equal (vcomb (vcoords x b) b)
	               x)))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use ((:instance vdep-if->-dim (m (1+ (vdim))) (l (cons x b)))
		        (:instance vdepp-vcomb (l b) (n (vdim)))))))

;; By functional instantiation of vcoords0-unique, this representation is unique:

(defthmd vcoords-unique
  (implies (and (vbasisp b) (vp x) (flistnp c (vdim))
		(equal (vcomb c b) x))
	   (equal (vcoords x b) c))
  :hints (("Goal" :use ((:functional-instance vcoords0-unique
                          (vbasis0 (lambda () (if (and (posp (vdim)) (vbasisp b)) b (vbasis0))))
			  (vcoords0 (lambda (x) (if (and (posp (vdim)) (vbasisp b)) (vcoords x b) (vcoords0 x)))))))
	  ("Subgoal 5" :in-theory (enable vbasisp)
	               :use (vbasis0-lin-indep
		             (:instance vindepp-vcomb-v0 (l b) (m (vdim)))))
	  ("Subgoal 4" :in-theory (enable vbasisp)
	               :use (vbasis-spans))
	  ("Subgoal 3" :in-theory (disable flistnp-vcoords0)
	               :use (vbasis-spans flistnp-vcoords0))
	  ("Subgoal 2" :in-theory (enable vbasisp))
	  ("Subgoal 1" :in-theory (enable vdim vbasisp))))

;; Consequently,

(defthm vcoords-vcoords0
  (implies (vp x)
           (equal (vcoords x (vbasis0))
	          (vcoords0 x)))
  :hints (("Goal" :use ((:instance vcoords-unique (b (vbasis0)) (c (vcoords0 x)))))))

;; The coordinates of a basis element:

(defthm vcomb-funit
  (implies (and (natp n) (natp j) (< j n) (vlistnp l n))
           (equal (vcomb (funit j n) l)
	          (nth j l))))

(defthm vcoords-nth-basis
  (implies (and (vbasisp b) (natp j) (< j (vdim)))
           (equal (vcoords (nth j b) b)
	          (funit j (vdim))))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use ((:instance vcoords-unique (c (funit j (vdim))) (x (nth j b)))))))

;; Given a vbasis b and a list of vectors l, consider the matrix of coordinates of the members of l with respect to b:

(defun vbasis-mat (l b)
  (if (consp l)
      (cons (vcoords (car l) b)
            (vbasis-mat (cdr l) b))
    ()))

(defthmd fmatp-basis-mat
  (implies (and (vbasisp b) (vlistnp l m))
           (fmatp (vbasis-mat l b) m (vdim)))
  :hints (("Goal" :induct (nthcdr m l)
                  :in-theory (enable fmatp))
          ("Subgoal *1/2" :use ((:instance vbasis-spans (x (car l)))))))

;; By functional instantiation of vcoords0-vcomb, for any linear combination (vcomb c l) of l, we have the following 
;; formula for (vcoords (vcomb c l) b):

(defthmd vcoords-vcomb
  (implies (and (vbasisp b) (posp m) (vlistnp l m) (flistnp c m))
	   (equal (vcoords (vcomb c l) b)
		  (car (fmat* (list c) (vbasis-mat l b)))))
  :hints (("Goal" :use ((:functional-instance vcoords0-vcomb
                          (vbasis0 (lambda () (if (and (posp (vdim)) (vbasisp b)) b (vbasis0))))
                          (vcoord-mat (lambda (l) (if (and (posp (vdim)) (vbasisp b)) (vbasis-mat l b) (vcoord-mat l))))
			  (vcoords0 (lambda (x) (if (and (posp (vdim)) (vbasisp b)) (vcoords x b) (vcoords0 x)))))))
	  ("Subgoal 5" :in-theory (enable vbasisp)
	               :use (vbasis0-lin-indep
		             (:instance vindepp-vcomb-v0 (l b) (m (vdim)))))
	  ("Subgoal 4" :in-theory (enable vbasisp)
	               :use (vbasis-spans))
	  ("Subgoal 3" :in-theory (disable flistnp-vcoords0)
	               :use (vbasis-spans flistnp-vcoords0))
	  ("Subgoal 2" :in-theory (enable vbasisp))
	  ("Subgoal 1" :in-theory (enable vdim vbasisp))))

;; Combining vcoords-vcom and vbasis-spans, we have the following formula relating coordinates with respect to
;; 2 vbases:

(defthmd vcoords-convert
  (implies (and (vbasisp b1) (vbasisp b2) (vp x))
           (equal (fmat* (list (vcoords x b1)) (vbasis-mat b1 b2))
	          (list (vcoords x b2))))
  :hints (("Goal" :in-theory (enable vbasis-spans vbasisp)
                  :use ((:instance vcoords-vcomb (m (vdim)) (l b1) (b b2) (c (vcoords x b1)))))))

(defthmd fmatp-basis-basis-mat
  (implies (and (vbasisp b1) (vbasisp b2))
           (fmatp (vbasis-mat b1 b2) (vdim) (vdim)))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use ((:instance fmatp-basis-mat (l b1) (b b2) (m (vdim)))))))

;; Now let p = (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1)).  For all x,

;;    (fmat* (list (vcoords x b1)) p)
;;      = (fmat* (list (vcoords x b1)) (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1)))
;;      = (fmat* (fmat* (list (vcoords x b1)) (vbasis-mat b1 b2)) (vbasis-mat b2 b1))
;;      = (fmat* (list (vcoords x b2)) (vbasis-mat b2 b1))
;;      = (list (vcoords x b1)).

(local-defthmd compose-basis-basis-mats
  (implies (and (vbasisp b1) (vbasisp b2) (vp x))
           (equal (fmat* (list (vcoords x b1)) (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1)))
	          (list (vcoords x b1))))
  :hints (("Goal" :use (fmatp-basis-basis-mat vcoords-convert
                        (:instance vcoords-convert (b1 b2) (b2 b1))
                        (:instance fmatp-basis-basis-mat (b1 b2) (b2 b1))
			(:instance vbasis-spans (b b1))
			(:instance fmat*-assoc (m 1) (n (vdim)) (p (vdim)) (q (vdim))
			                       (a (list (vcoords x b1))) (b (vbasis-mat b1 b2)) (c (vbasis-mat b2 b1)))))))

;; In particular, for i < (vdim),

;;    (row i p) = (car (fmat* (list (funit i (vdim))) p)) = (funit i (vdim)),

(local-defthmd fmat*-funit-1
  (implies (and (fmatp a m n) (posp m) (posp n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry 0 j (fmat* (list (funit i m)) a))
	          (entry i j a)))
  :hints (("Goal" :use (nth-col (:instance fmat*-entry (m 1) (n m) (p n) (a (list (funit i m))) (b a) (i 0))))))

(local-defthmd fmat*-funit
  (implies (and (fmatp a m n) (posp m) (posp n) (natp i) (< i m))
           (equal (car (fmat* (list (funit i m)) a))
	          (row i a)))
  :hints (("Goal" :use (flistnp-row
                        (:instance flistnp-row (a (fmat* (list (funit i m)) a)) (i 0))
			(:instance fmatp-fmat* (a (list (funit i m))) (b a) (m 1) (n m) (p n))
                        (:instance nth-diff-diff (x (car (fmat* (list (funit i m)) a))) (y (row i a)))
                        (:instance fmat*-funit-1 (j (nth-diff (car (fmat* (list (funit i m)) a)) (row i a))))))))

(local-defthmd fmatp-compose-basis-basis-mats
  (implies (and (vbasisp b1) (vbasisp b2))
           (fmatp (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1))
	          (vdim) (vdim)))
  :hints (("Goal" :use (fmatp-basis-basis-mat
                        (:instance fmatp-basis-basis-mat (b1 b2) (b2 b1))
			(:instance fmatp-fmat* (m (vdim)) (n (vdim)) (p (vdim)) (a (vbasis-mat b1 b2)) (b (vbasis-mat b2 b1)))))))

(local-defthmd row-compose-basis-basis-mats
  (implies (and (vbasisp b1) (vbasisp b2) (natp i) (< i (vdim)))
           (equal (row i (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1)))
	          (funit i (vdim))))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use (fmatp-compose-basis-basis-mats
                        (:instance fmat*-funit (a (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1))) (m (vdim)) (n (vdim)))
			(:instance compose-basis-basis-mats (x (nth i b1)))))))

;; and hence p = (id-fmat (vdim)):

(defthmd compose-basis-basis-mats-id-fmat
  (implies (and (vbasisp b1) (vbasisp b2))
           (equal (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1))
	          (id-fmat (vdim))))
  :hints (("Goal" :use (fmatp-compose-basis-basis-mats
                        (:instance fmat-entry-diff-lemma (m (vdim)) (n (vdim))
			                                 (a (id-fmat (vdim))) (b (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1))))
			(:instance row-compose-basis-basis-mats
			            (i (car (entry-diff (id-fmat (vdim)) (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1))))))))))

;; Thus, by invertiblep-inverse, we have the following:

(defthmd vbasis-mat-inverse
  (implies (and (vbasisp b1) (vbasisp b2))
           (and (invertiblep (vbasis-mat b1 b2) (vdim))
	        (equal (inverse-mat (vbasis-mat b1 b2))
		       (vbasis-mat b2 b1))))
  :hints (("Goal" :use (fmatp-basis-basis-mat compose-basis-basis-mats-id-fmat
                        (:instance fmatp-basis-basis-mat (b1 b2) (b2 b1))
			(:instance invertiblep-inverse (a (vbasis-mat b1 b2)) (b (vbasis-mat b2 b1)) (n (vdim)))))))

;; We shall show that any linearly independent list of vectors may be extended to a vbasis.  To this end,
;; given a linearly independent list l with (len l) = m < (vdim),  we shall construct a vector (unspanned l)
;; that is not a linear combination of l.  Once again, let a = (vcoord-mat l), p = (row-reduce-mat a), and
;; r = (row-reduce a).  We may define (vunspanned l) to be a member of vbasis0 that corresponds to any of the
;; indices of (free-inds r (vdim)).  We arbitrarily select the vbasis element corresponding to
;; (car (free-inds r (vdim))):

(defund vunspanned (l)
  (nth (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))
       (vbasis0)))

(local-defthmd row-echelon-p-row-reduce-vcoord-mat
 (implies (vlistnp l m)
          (let ((r (row-reduce (vcoord-mat l))))
	    (and (fmatp r m (vdim))
	         (row-echelon-p r))))
  :hints (("Goal" :use ((:instance row-echelon-p-row-reduce (n (vdim)) (a (vcoord-mat l)))
                        (:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))))))

(local-defthmd car-free-inds
 (implies (and (vlistnp l m) (posp m) (< m (vdim)))
          (let* ((r (row-reduce (vcoord-mat l)))
	         (i (car (free-inds r (vdim)))))
	    (and (natp i)
	         (< i (vdim))
		 (not (member i (lead-inds r))))))
  :hints (("Goal" :use (row-echelon-p-row-reduce-vcoord-mat
                        (:instance consp-free-inds (a (row-reduce (vcoord-mat l))) (n (vdim)))
			(:instance member-free-inds (a (row-reduce (vcoord-mat l))) (n (vdim))
			                            (x (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))))
			(:instance member-ninit (x (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))) (n (vdim)))))))

(defthmd vp-vunspanned
  (implies (and (vlistnp l m) (posp m) (< m (vdim)))
           (vp (vunspanned l)))
  :hints (("Goal" :in-theory (enable vunspanned)
                  :use (car-free-inds))))

;; Let u = (vunspanned l).  Suppose (flistnp c m) and u = (vcomb c l).  Let c' = (car (fmat* (list c) (inverse-mat p))).
;; By fmat*-vcomb-row-reduce and vcoords0-vcomb,

;;     (car (fmat* (list c') r)) = (car (fmat* (list c) a)) = (vcoords0 u). 

;; Let i < m and j = (nth i (lead-inds r)).  Then by entry-fmat*-row-echelon-p,

;;    (nth i c') = (nth j (car (fmat* (list c') r))) = (nth j (vcoords0 u)) = (f0),

;; and hence c' = (flistn0 m), which implies (vcoords0 u) = (flistn0 (vdim)), a contradiction.

(local-defthmd vunspanned-not-vcomb-1
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vunspanned l) (vcomb c l)))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (car (fmat* (list c1) r))
	            (vcoords0 (vunspanned l)))))
  :hints (("Goal" :use (fmat*-vcomb-row-reduce vcoords0-vcomb))))

(local-defthmd vunspanned-not-vcomb-2
  (implies (and (vlistnp l m) (posp m) (< m (vdim)))
           (equal (vcoords0 (vunspanned l))
	          (funit (car (free-inds (row-reduce (vcoord-mat l)) (vdim))) (vdim))))
  :hints (("Goal" :in-theory (e/d (vunspanned) (vcoords-nth-basis))
                  :use (car-free-inds
		        (:instance vcoords-nth-basis (j (car (free-inds (row-reduce (vcoord-mat l)) (vdim))))
		                                    (b (vbasis0)))))))

(local-defthmd vunspanned-not-vcomb-3
  (implies (and (posp m)
                (vlistnp l m)
		(flistnp c m))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
             (flistnp c1 m)))
  :hints (("Goal" :use ((:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l)))))
		        (:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (i 0) (m 1) (n m) (a (fmat* (list c) (inverse-mat (row-reduce-mat (vcoord-mat l))))))))))

(local-defthmd vunspanned-not-vcomb-4
  (implies (and (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vunspanned l) (vcomb c l))
                (natp i) (< i m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (nth i c1)
	            (nth (nth i (lead-inds r))
		         (vcoords0 (vunspanned l))))))
  :hints (("Goal" :in-theory (e/d (vindepp) (row-rank))
                  :use (vunspanned-not-vcomb-1 vunspanned-not-vcomb-3
		        (:instance row-rank-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance row-echelon-p-row-reduce (a (vcoord-mat l)) (n (vdim)))
                        (:instance entry-fmat*-row-echelon-p (n (vdim))
			                                     (r (row-reduce (vcoord-mat l)))
							     (c (car (fmat* (list c) (inverse-mat (row-reduce-mat (vcoord-mat l)))))))))))

(local-defthmd vunspanned-not-vcomb-5
  (implies (and (posp (vdim))
                (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
                (natp i) (< i m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a)))
	     (and (member (nth i (lead-inds r)) (lead-inds r))
	          (natp (nth i (lead-inds r)))
	          (< (nth i (lead-inds r)) (vdim)))))
  :hints (("Goal" :in-theory (enable vindepp)
                  :use ((:instance len-lead-inds-num-nonzero-rows (a (row-reduce (vcoord-mat l))))
		        (:instance row-rank-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance row-echelon-p-row-reduce (a (vcoord-mat l)) (n (vdim)))
                        (:instance nth-lead-inds-bound (n (vdim)) (k i) (a (row-reduce (vcoord-mat l))))))))

(local-defthmd vunspanned-not-vcomb-6
  (implies (and (posp (vdim))
                (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
                (natp i) (< i m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a)))
	     (equal (nth (nth i (lead-inds r))
	                 (funit (car (free-inds r (vdim))) (vdim)))
	            (f0))))
  :hints (("Goal" :in-theory (e/d (vindepp) (row-rank))
                  :use (car-free-inds vunspanned-not-vcomb-5
		        (:instance nth-funit (i (nth i (lead-inds (row-reduce (vcoord-mat l)))))
			                     (j (car (free-inds (row-reduce (vcoord-mat l)) (vdim))))
					     (n (vdim)))))))

(local-defthmd vunspanned-not-vcomb-7
  (implies (and (posp (vdim))
                (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vunspanned l) (vcomb c l))
                (natp i) (< i m))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (nth i c1)
	            (f0))))
  :hints (("Goal" :use (vunspanned-not-vcomb-2 vunspanned-not-vcomb-4 vunspanned-not-vcomb-6))))

(local-defthmd vunspanned-not-vcomb-8
  (implies (and (posp (vdim))
                (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vunspanned l) (vcomb c l)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal c1 (flistn0 m))))
  :hints (("Goal" :use (vunspanned-not-vcomb-3
		        (:instance nth-diff-diff (x (car (fmat* (list c) (inverse-mat (row-reduce-mat (vcoord-mat l))))))
                                                 (y (flistn0 m)))
			(:instance vunspanned-not-vcomb-7 (i (nth-diff (car (fmat* (list c) (inverse-mat (row-reduce-mat (vcoord-mat l)))))
			                                              (flistn0 m))))))))

(local-defthmd vunspanned-not-vcomb-9
  (implies (and (posp m) (posp n) (fmatp r m n))
           (equal (fmat* (list (flistn0 m)) r)
	          (list (flistn0 n))))
  :hints (("Goal" :use ((:instance fmatp-fmat* (m 1) (n m) (p n) (a (list (flistn0 m))) (b r))
                        (:instance fmat-entry-diff-lemma (a (fmat* (list (flistn0 m)) r)) (b (list (flistn0 n))) (m 1))
			(:instance fmat*-entry (a (list (flistn0 m))) (b r) (m 1) (n m) (p n)
			                       (i (car (entry-diff (fmat* (list (flistn0 m)) r) (list (flistn0 n)))))
			                       (j (cdr (entry-diff (fmat* (list (flistn0 m)) r) (list (flistn0 n))))))))))

(local-defthmd vunspanned-not-vcomb-10
  (implies (and (posp (vdim))
                (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vunspanned l) (vcomb c l)))
	   (equal (vcoords0 (vunspanned l))
	          (flistn0 (vdim))))
  :hints (("Goal" :use (vunspanned-not-vcomb-1 vunspanned-not-vcomb-8
		        (:instance vunspanned-not-vcomb-9 (n (vdim)) (r (row-reduce (vcoord-mat l))))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))))))

(defthmd vunspanned-not-vcomb
  (implies (and (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (not (equal (vunspanned l) (vcomb c l))))
  :hints (("Goal" :use (car-free-inds vunspanned-not-vcomb-2 vunspanned-not-vcomb-10
                        (:instance nth-funit (i (car (free-inds (row-reduce (vcoord-mat l)) (vdim))))
			                     (j (car (free-inds (row-reduce (vcoord-mat l)) (vdim))))
					     (n (vdim)))))))

;; We now invoke vdepp-vcomb:

(defthmd vindepp-cons-vunspanned
  (implies (and (vlistnp l m) (vindepp l) (posp m) (< m (vdim)))
           (vindepp (cons (vunspanned l) l)))
  :hints (("Goal" :in-theory (enable vp-vunspanned vdepp)
                  :use ((:instance vdepp-vcomb (x (vunspanned l)) (n m))
                        (:instance vunspanned-not-vcomb (c (vcoords (vunspanned l) l)))))))

;; The extension of l to a vbasis is constructed recursively:

(defun extend-to-basis (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))))
  (if (and (vlistnp l (len l)) (vindepp l) (< (len l) (vdim)))
      (extend-to-basis (cons (vunspanned l) l))
    l))

;; The following is proved by induction

(in-theory (disable (extend-to-basis) (vunspanned)))

(local-defun vbasisp-extend-to-basis-induct (l n)
  (declare (xargs :measure (nfix (- (vdim) (len l)))))
  (if (and (vlistnp l (len l)) (vindepp l) (< (len l) (vdim)))
      (list (vbasisp-extend-to-basis-induct (cons (vunspanned l) l) (1+ n)))
    (list l n)))

(defthmd vbasisp-extend-to-basis
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l)))	   
  :hints (("Goal" :induct (vbasisp-extend-to-basis-induct l n))
          ("Subgoal *1/2" :in-theory (enable vbasisp)
                          :use ((:instance vdep-if->-dim (m n))))
	  ("Subgoal *1/1" :in-theory (enable vp-vunspanned)
	                  :use ((:instance vindepp-cons-vunspanned (m n))))))


;;---------------------------------------------------------------------------------------------------------------------
;;  Linear Transformations
;;---------------------------------------------------------------------------------------------------------------------

(encapsulate (((wp *) => *)        ;vector recognizer
              ((w+ * *) => *)      ;vector addition
	      ((w0) => *)          ;zero vector
	      ((w- *) => *)        ;additive inverse
	      ((w* * *) => *)      ;scalar multiplication
	      ((wbasis0) => *)     ;canonical basis
	      ((wcoords0 *) => *)) ;coordinates relative ro basis
  (local (defun wp (x) (fp x)))
  (local (defun w+ (x y) (f+ x y)))
  (local (defun w0 () (f0)))
  (local (defun w- (x) (f- x)))
  (local (defun w* (c x) (f* c x)))
  (local (defun wbasis0 () (list (f1))))
  (local (defun wcoords0 (x) (list x)))
  (defthm wp-w0
    (wp (w0)))
  (defthm wp-w-
    (implies (wp x) (wp (w- x))))
  ;; Vector addition:
  (defthm w+closed (implies (and (wp x) (wp y)) (wp (w+ x y))))
  (defthmd w+comm
    (implies (and (wp x) (wp y)) (equal (w+ x y) (w+ y x)))
    :hints (("Goal" :use (f+comm))))
  (defthmd w+assoc
    (implies (and (wp x) (wp y) (wp z)) (equal (w+ x (w+ y z)) (w+ (w+ x y) z)))
    :hints (("Goal" :use (f+assoc))))
  (defthm w+id
    (implies (wp x) (equal (w+ x (w0)) x)))
  (defthm w+inv
    (implies (wp x) (equal (w+ x (w- x)) (w0))))
  ;; Scalar multiplication:
  (defthm w*closed
    (implies (and (fp c) (wp x)) (wp (w* c x))))
  (defthm w*id
    (implies (wp x) (equal (w* (f1) x) x)))
  (defthmd w*assoc
    (implies (and (fp c) (fp d) (wp x)) (equal (w* c (w* d x)) (w* (f* c d) x)))
    :hints (("Goal" :use ((:instance f*assoc (x c) (y d) (z x))))))
  (defthmd wdistf
    (implies (and (fp c) (fp d) (wp x)) (equal (w+ (w* c x) (w* d x)) (w* (f+ c d) x)))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y d) (z x))))))
  (defthmd wdistw
    (implies (and (fp c) (wp x) (wp y)) (equal (w+ (w* c x) (w* c y)) (w* c (w+ x y))))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y x) (z y))))))
  ;; List of vectors:
  (defun wlistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (wp (car x))
	   (wlistnp (cdr x) (1- n)))))
  ;; Linear combination of a list of vectors:
  (defun wcomb (flist wlist)
    (if (consp flist)
        (w+ (w* (car flist) (car wlist))
	    (wcomb (cdr flist) (cdr wlist)))
      (w0)))
  ;; Basis and coordinates:
  (defun wdim () (len (wbasis0)))
  (defthmd posp-wdim
    (posp (wdim)))
  (in-theory (disable (wdim) (wlistnp) (wcomb)))
  (defthm wlistnp-basis
    (wlistnp (wbasis0) (wdim)))
  (defthm flistnp-wcoords0
    (implies (wp x) (flistnp (wcoords0 x) (wdim))))
  (defthm wbasis0-spans
    (implies (wp x)
             (equal (wcomb (wcoords0 x) (wbasis0))
		    x)))
  (defthmd wbasis0-lin-indep
    (implies (and (flistnp c (wdim))
                  (equal (wcomb c (wbasis0)) (w0)))
	     (equal (flistn0 (wdim)) c)))
  (in-theory (disable wdim)))

;; All derived properties of V may be attributed to W by functional instantiation:

(defthm w+id-comm
  (implies (wp x) (equal (w+ (w0) x) x))
  :hints (("Goal" :use ((:instance w+comm (y (w0)))))))

(defthm w+inw-comm
  (implies (wp x) (equal (w+ (w- x) x) (w0)))
  :hints (("Goal" :use ((:instance w+comm (y (w- x)))))))

(defthm f0*w0
  (implies (wp x) (equal (w* (f0) x) (w0)))
  :hints (("Goal" :use ((:instance wdistf (c (f1)) (d (f0)))
			(:instance w+assoc (x (w- x)) (y x) (z (w* (f0) x)))))))

(defthm c*w0
  (implies (fp c) (equal (w* c (w0)) (w0)))
  :hints (("Goal" :use ((:instance wdistw (x (w0)) (y (w0)))
			(:instance w+assoc (x (w- (w* c (w0)))) (y (w* c (w0))) (z (w* c (w0))))))))

(defthm wp-wcomb
  (implies (and (flistnp c n) (wlistnp l n))
	   (wp (wcomb c l))))

(defthm len-wlistnp
  (implies (and (natp n) (wlistnp x n))
           (equal (len x) n))
  :hints (("Goal" :induct (nthcdr n x))))

(defun wp-nth-wlistnp-induct (x n j)
  (if (zp j)
      (list x n j)
    (list (wp-nth-wlistnp-induct (cdr x) (1- n) (1- j)))))

(defthm wp-nth-wlistnp
  (implies (and (wlistnp x n) (natp n) (natp j) (< j n))
           (wp (nth j x)))
  :hints (("Goal" :induct (wp-nth-wlistnp-induct x n j))))

(local-defthmd hack-3
  (implies (and (fp x0) (fp y0) (wp l0) (wp lx) (wp ly))
	   (equal (w+ (w* (f+ x0 y0) l0) (w+ lx ly))
		  (w+ (w+ (w* x0 l0) lx) (w+ (w* y0 l0) ly))))
  :hints (("Goal" :use ((:instance w+assoc (x (w+ (w* x0 l0) lx)) (y (w* y0 l0)) (z ly))
			(:instance w+assoc (x (w* x0 l0)) (y lx) (z (w* y0 l0)))
			(:instance w+comm (x lx) (y (w* y0 l0)))
			(:instance w+assoc (x (w* x0 l0)) (y (w* y0 l0)) (z lx))
			(:instance w+assoc (x (w+ (w* x0 l0) (w* y0 l0))) (y lx) (z ly))
			(:instance wdistf (c x0) (d y0) (x l0))))))

(defthmd wcomb-add
  (implies (and (natp n) (wlistnp l n) (flistnp x n) (flistnp y n))
	   (equal (wcomb (flist-add x y) l)
		  (w+ (wcomb x l) (wcomb y l))))
  :hints (("Subgoal *1/6" :use ((:instance hack-3 (x0 (car x)) (y0 (car y)) (l0 (car l))
					   (lx (WCOMB (CDR X) (CDR L))) (ly (WCOMB (CDR y) (CDR L))))))))

(defthmd wcomb-scalar-mul
  (implies (and (natp n) (wlistnp l n) (flistnp x n) (fp c))
	   (equal (wcomb (flist-scalar-mul c x) l)
		  (w* c (wcomb x l))))
  :hints (("Subgoal *1/5" :use ((:instance w*assoc (d (car x)) (x (car l)))
				(:instance wdistw (x (w* (car x) (car l))) (y (WCOMB (CDR X) (CDR L))))))))

;; The list of coordinates of a vector is unique:

(local-defthmd wcoords0-unique-1
  (implies (and (natp n) (flistnp x n) (flistnp y n) (wlistnp l n)
		(= (wcomb x l) (wcomb y l)))
	   (equal (wcomb (flist-add x (flist-scalar-mul (f- (f1)) y)) l)
		  (w0)))
  :hints (("Goal" :in-theory (enable wcomb-add wcomb-scalar-mul)
	          :use ((:instance wdistf (c (f1)) (d (f- (f1))) (x (wcomb x l)))))))

(local-defthmd wcoords0-unique-2
  (implies (and (flistnp x (wdim)) (flistnp y (wdim))
		(= (wcomb x (wbasis0)) (wcomb y (wbasis0))))
	   (equal (flist-add x (flist-scalar-mul (f- (f1)) y))
		  (flistn0 (wdim))))
  :hints (("Goal" :in-theory (enable wdim)
                  :use (wlistnp-basis
		        (:instance wcoords0-unique-1 (n (wdim)) (l (wbasis0)))
                        (:instance wbasis0-lin-indep (c (flist-add x (flist-scalar-mul (f- (f1)) y))))))))

(local-defthm wcoords0-unique-3
  (implies (and (fp x) (fp y) (= (f+ x (f* (f- (f1)) y)) (f0)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance f+assoc (y (f* (f- (f1)) y)) (z y))
                        (:instance fdist-comm (x (f- (f1))) (y (f1)) (z y))))))

(local-defthm wcoords0-unique-4
  (implies (and (natp n) (flistnp x n) (flistnp y n)
	        (equal (flist-add x (flist-scalar-mul (f- (f1)) y))
		       (flistn0 n)))
	   (equal x y))
  :rule-classes ()
  :hints (("Subgoal *1/7" :use ((:instance wcoords0-unique-3 (x (car x)) (y (car y)))))))

(defthmd wcoords0-unique
  (implies (and (wp x) (flistnp c (wdim))
		(equal (wcomb c (wbasis0)) x))
	   (equal (wcoords0 x) c))
  :hints (("Goal" :use ((:instance wcoords0-unique-4 (n (wdim)) (x c) (y (wcoords0 x)))
                        (:instance wcoords0-unique-2 (x c) (y (wcoords0 x)))))))

;; In particular, since (wcomb (flistn0 (wdim)) (wbasis0)) = (w0), (wcoords0 (w0)) = (flistn0 (wdim)):

(defthm wcomb-flistn0
  (implies (wlistnp l n)
           (equal (wcomb (flistn0 n) l)
	          (w0)))
  :hints (("Goal" :induct (nthcdr n l))))

(defthm wcoords0-w0
  (equal (wcoords0 (w0))
         (flistn0 (wdim)))
  :hints (("Goal" :use ((:instance wcoords0-unique (x (w0)) (c (flistn0 (wdim))))))))

;; We define the coordinate matrix of a list of wectors:

(defun wcoord-mat (l)
  (if (consp l)
      (cons (wcoords0 (car l))
	    (wcoord-mat (cdr l)))
    ()))

(in-theory (enable fmatp))

(defthm fmatp-wcoord-mat
  (implies (wlistnp l m)
           (fmatp (wcoord-mat l) m (wdim)))
  :hints (("Goal" :induct (nthcdr m l))))

;; Assume (wlistnp l m) ,where m > 0.  We shall show that the coordinates of any linear combination (wcomb c l) of l
;; may be deriwed by multiplying the row matrix of c by the coordinate matrix of l and extracting the single row of
;; the result:

;;    (wcoords0 (wcomb c l)) = (row 0 (fmat* (row-mat c) (wcoord-mat l))).

;; By wcoords0-unique, it suffices to show that (wcomb (row 0 (fmat* (list c) (wcoord-mat l))) (wbasis0)) = (wcomb c l).
;; We shall prowe this by induction.  If m = 1, then

;;    (wcomb (row 0 (fmat* (list c) (wcoord-mat l))) (wbasis0)
;;      = (wcomb (flist-scalar-mul (car c) (wcoords0 (car l))) (wbasis0))
;;      = (w* (car c) (wcomb (wcoords0 (car l)) (wbasis0)))
;;      = (w* (car c) (car l))
;;      = (wcomb c l).

(local-defthmd wcoords0-wcomb-1
  (implies (and (wlistnp l 1) (flistnp c 1) (natp j) (< j (wdim)))
           (equal (nth j (car (fmat* (list c) (wcoord-mat l))))
	          (f* (car c) (nth j (wcoords0 (car l))))))
  :hints (("Goal" :use ((:instance fmat*-entry (i 0) (m 1) (n 1) (p (wdim)) (a (list c)) (b (wcoord-mat l)))
                        (:instance fp-flistnp (i j) (n (wdim)) (x (wcoords0 (car l)))))
                  :in-theory (disable (fdot))
                  :expand ((flistnp c 1) (wlistnp l 1)))))

(local-defthmd wcoords0-wcomb-2
  (implies (and (wlistnp l 1) (flistnp c 1) (natp j) (< j (wdim)))
           (equal (nth j (flist-scalar-mul (car c) (wcoords0 (car l))))
	          (nth j (car (fmat* (list c) (wcoord-mat l))))))
  :hints (("Goal" :use (wcoords0-wcomb-1
                        (:instance nth-flist-scalar-mul (c (car c)) (x (wcoords0 (car l))) (n (wdim)) (i j))))))

(local-defthmd wcoords0-wcomb-3
  (implies (and (wlistnp l 1) (flistnp c 1))
           (equal (car (fmat* (list c) (wcoord-mat l)))
	          (flist-scalar-mul (car c) (wcoords0 (car l)))))
  :hints (("Goal" :use (posp-wdim
                        (:instance nth-diff-diff (x (car (fmat* (list c) (wcoord-mat l))))
                                                 (y (flist-scalar-mul (car c) (wcoords0 (car l)))))
			(:instance wcoords0-wcomb-2 (j (nth-diff (car (fmat* (list c) (wcoord-mat l)))
			                                        (flist-scalar-mul (car c) (wcoords0 (car l))))))
			(:instance fmatp-fmat* (m 1) (n 1) (p (wdim)) (a (list c)) (b (wcoord-mat l))))
		  :expand ((fmatp (fmat* (list c) (wcoord-mat l)) 1 (wdim))))))

(local-defthmd wcoords0-wcomb-4
  (implies (and (wlistnp l 1) (flistnp c 1))
           (equal (wcomb (car (fmat* (list c) (wcoord-mat l))) (wbasis0))
	          (wcomb c l)))
  :hints (("Goal" :use (posp-wdim) :in-theory (e/d (wcomb-scalar-mul wcoords0-wcomb-3) (fmat*)))))

;; Now suppose m > 1 and assume the claim is true when c and l are repaced by (cdr c) and (cdr l).
;; Let a = (wcoord-mat l).  We shall show first that

;;    (car (fmat* (list c) a) = (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))).

;; To prowe this, it suffices to show that for j < (wdim), the jth members of these lists are equal.  But

;;    (nth j (car (fmat* (list c) a))) = (entry 0 j (fmat* (list c) a))
;;                                     = (fdot c (col j a))
;;                                     = (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a))))

(local-defthmd wcoords0-wcomb-5
  (implies (and (posp m) (wlistnp l m) (flistnp c m) (natp j) (< j (wdim)))
           (let ((a (wcoord-mat l)))
	     (equal (nth j (car (fmat* (list c) a)))
	            (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a)))))))
  :hints (("Goal" :use ((:instance fmat*-entry (i 0) (m 1) (n m) (p (wdim)) (a (list c)) (b (wcoord-mat l)))))))

;; and

;;    (nth j (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))))
;;      = (f+ (f* (car c) (nth j (car a))) (entry 0 j (fmat* (list (cdr c)) (cdr a))))
;;      = (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a)))).

(local-defthmd wcoords0-wcomb-6
  (implies (and (natp m) (> m 1) (wlistnp l m) (flistnp c m) (posp (wdim)) (natp j) (< j (wdim)))
           (let ((a (wcoord-mat l)))
	     (equal (nth j (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a)))))
		    (f+ (f* (car c) (nth j (car a)))
		        (entry 0 j (fmat* (list (cdr c)) (cdr a)))))))
  :hints (("Goal" :in-theory (disable fmatp-wcoord-mat)
                  :expand ((FLISTNP (CAR (WCOORD-MAT L)) (WDIM)))
                  :use (fmatp-wcoord-mat
                        (:instance nth-flist-add (x (flist-scalar-mul (car c) (car (wcoord-mat l))))
                                                 (y (car (fmat* (list (cdr c)) (cdr (wcoord-mat l)))))
						 (i j) (n (wdim)))
			(:instance nth-flist-scalar-mul (i j) (n (wdim)) (c (car c)) (x (wcoords0 (car l))))
                        (:instance flist-scalar-mul (c (car c)) (x (car (wcoord-mat l))))			
			(:instance fmatp-fmat* (m 1) (n (1- m)) (p (wdim)) (a (LIST (CDR C))) (b (CDR (WCOORD-MAT L))))))))

(local-defthmd wcoords0-wcomb-7
  (implies (and (natp m) (> m 1) (wlistnp l m) (flistnp c m) (posp (wdim)) (natp j) (< j (wdim)))
           (let ((a (wcoord-mat l)))
	     (equal (nth j (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a)))))
		    (nth j (car (fmat* (list c) a))))))
  :hints (("Goal" :in-theory (disable fmatp-wcoord-mat)
                  :use (wcoords0-wcomb-5 wcoords0-wcomb-6 fmatp-wcoord-mat
                        (:instance fmat*-entry (m 1) (n (1- m)) (p (wdim))
			                       (a (list (cdr c))) (b (cdr (wcoord-mat l))) (i 0))))))

(local-defthmd wcoords0-wcomb-8
  (implies (and (natp m) (> m 1) (wlistnp l m) (flistnp c m) (posp (wdim)))
           (let ((a (wcoord-mat l)))
	     (equal (flist-add (flist-scalar-mul (car c) (car a))
	                       (car (fmat* (list (cdr c)) (cdr a))))
		    (car (fmat* (list c) a)))))
  :hints (("Goal" :in-theory (disable fmatp-wcoord-mat)
                  :use (fmatp-wcoord-mat
		        (:instance wcoords0-wcomb-7 (j (nth-diff (flist-add (flist-scalar-mul (car c) (car (wcoord-mat l)))
	                                                                   (car (fmat* (list (cdr c)) (cdr (wcoord-mat l)))))
						                (car (fmat* (list c) (wcoord-mat l))))))
			(:instance nth-diff-diff (x (flist-add (flist-scalar-mul (car c) (car (wcoord-mat l)))
	                                                       (car (fmat* (list (cdr c)) (cdr (wcoord-mat l))))))
						 (y (car (fmat* (list c) (wcoord-mat l)))))
			(:instance flistnp-row (a (FMAT* (LIST C) (WCOORD-MAT L))) (i 0) (m 1) (n (wdim)))
			(:instance flistnp-flist-add (x (FLIST-SCALAR-MUL (CAR C) (CAR (WCOORD-MAT L))))
                                                     (y (CAR (FMAT* (LIST (CDR C)) (CDR (WCOORD-MAT L)))))
						     (n (wdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p (wdim)) (a (list c)) (b (wcoord-mat l)))
                        (:instance fmatp-fmat* (m 1) (n (1- m)) (p (wdim)) (a (LIST (CDR C))) (b (CDR (WCOORD-MAT L))))))))

(local-defthmd wcoords0-wcomb-9
  (implies (and (natp m) (> m 1) (wlistnp l m) (flistnp c m) (posp (wdim)))
           (let ((a (wcoord-mat l)))
	     (equal (wcomb (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a))))
			   (wbasis0))
		    (w+ (w* (car c) (wcomb (car a) (wbasis0)))
		        (wcomb (car (fmat* (list (cdr c)) (cdr a))) (wbasis0))))))
  :hints (("Goal" :in-theory (e/d (wcomb-scalar-mul) (fmatp-wcoord-mat))
                  :use (fmatp-wcoord-mat
		        (:instance wcomb-add (x (flist-scalar-mul (car c) (car (wcoord-mat l))))
			                     (y (car (fmat* (list (cdr c)) (cdr (wcoord-mat l)))))
					     (n (wdim)) (l (wbasis0)))
			(:instance flistnp-row (a (FMAT* (LIST C) (WCOORD-MAT L))) (i 0) (m 1) (n (wdim)))
			(:instance flistnp-flist-scalar-mul (c (car c)) (x (car (wcoord-mat l))) (n (wdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p (wdim)) (a (list c)) (b (wcoord-mat l)))
                        (:instance fmatp-fmat* (m 1) (n (1- m)) (p (wdim)) (a (LIST (CDR C))) (b (CDR (WCOORD-MAT L))))))))

(local-defthmd wcoords0-wcomb-10
  (implies (and (natp m) (> m 1) (wlistnp l m) (flistnp c m) (posp (wdim)))
           (let ((a (wcoord-mat l)))
	     (implies (equal (wcomb (car (fmat* (list (cdr c)) (cdr a))) (wbasis0))
	                     (wcomb (cdr c) (cdr l)))
	              (equal (wcomb (flist-add (flist-scalar-mul (car c) (car a))
	                                       (car (fmat* (list (cdr c)) (cdr a))))
			            (wbasis0))
		             (wcomb c l)))))
  :hints (("Goal" :use (wcoords0-wcomb-9))))

(local-defthmd wcoords0-wcomb-11
  (implies (and (natp m) (> m 1) (wlistnp l m) (flistnp c m) (posp (wdim)))
           (let ((a (wcoord-mat l)))
	     (implies (equal (wcomb (car (fmat* (list (cdr c)) (cdr a))) (wbasis0))
	                     (wcomb (cdr c) (cdr l)))
	              (equal (wcomb (car (fmat* (list c) a)) (wbasis0))
		             (wcomb c l)))))
  :hints (("Goal" :use (wcoords0-wcomb-10 wcoords0-wcomb-8))))

(local-defthmd wcoords0-wcomb-12
  (implies (and (posp m) (wlistnp l m) (flistnp c m) (posp (wdim)))
           (equal (wcomb (car (fmat* (list c) (wcoord-mat l))) (wbasis0))
		  (wcomb c l)))
  :hints (("Subgoal *1/5" :use (wcoords0-wcomb-4 wcoords0-wcomb-11))
          ("Subgoal *1/2" :use (wcoords0-wcomb-4))))

(defthmd wcoords0-wcomb
  (implies (and (posp m) (wlistnp l m) (flistnp c m))
	   (equal (wcoords0 (wcomb c l))
		  (car (fmat* (list c) (wcoord-mat l)))))
  :hints (("Goal" :use (posp-wdim wcoords0-wcomb-12
			(:instance fmatp-fmat* (m 1) (n m) (p (wdim)) (a (list c)) (b (wcoord-mat l)))
                        (:instance wcoords0-unique (x (wcomb c l)) (c (car (fmat* (list c) (wcoord-mat l)))))))))

;; This formula is the basis of our definition of linear independence:

(defund windepp (l)
  (equal (row-rank (wcoord-mat l))
         (len l)))

(defund wdepp (l)
  (not (windepp l)))

;; To confirm that the definition has the intended meaning, we must first show that if (wdepp l), then
;; (w0) is a nontriwial linearly combination of l.  The required  coefficients may be constructed as follows:

(defun wdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (wcoord-mat l))))

(in-theory (enable fmat*))

(defthmd fmat*-nth
  (implies (and (fmatp a m n) (fmatp b n p) (posp m) (natp n) (natp p) (natp i) (< i m))
           (equal (car (fmat* (list (nth i a)) b))
	          (nth i (fmat* a b)))))

;; Let m = (len l), a = (wcoord-mat l), c = (wdep-coeffs l), and p = (row-reduce-mat (wcoord-mat l)).  
;; Then c is the last row of p.  Since p is invertible, (wdep-coeffs l) != (flistn0 m).  But

;;   (wcoords0 (wcomb c l)) = (car (fmat* (list c) a))
;;                         = (nth (1- m) (fmat* p a))
;;                         = (nth (1- m) (row-reduce a))
;;                         = (flistn0 (wdim)),

;; which implies (wcomb c l) = (w0):

(local-defthmd wdepp-wcomb-w0-1
  (implies (and (posp m) (wlistnp l m) (wdepp l) (posp (wdim)))
	   (let ((c (wdep-coeffs l)))
             (equal (wcoords0 (wcomb c l))
	            (nth (1- m) (row-reduce (wcoord-mat l))))))
  :hints (("Goal" :in-theory (e/d (row-ops-mat-row-reduce) (fmat* fmatp-wcoord-mat))
                  :use (fmatp-wcoord-mat
                        (:instance wcoords0-wcomb (c (wdep-coeffs l)))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance flistnp-row (a (row-reduce-mat (wcoord-mat l))) (n m) (i (1- m)))
			(:instance fmat*-nth (i (1- m)) (n m) (p (wdim)) (b (wcoord-mat l))
			                     (a (row-reduce-mat (wcoord-mat l))))))))
                        
(local-defthmd wdepp-wcomb-w0-2
  (implies (and (posp m) (wlistnp l m) (wdepp l) (posp (wdim)))
  	   (equal (nth (1- m) (row-reduce (wcoord-mat l)))
	          (flistn0 (wdim))))
  :hints (("Goal" :in-theory (enable windepp wdepp)
                  :use (wdepp-wcomb-w0-1
		        (:instance num-nonzero-rows-nonzero (a (row-reduce (wcoord-mat l))) (n (wdim)) (i (1- m)))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance flistnp-row (a (row-reduce-mat (wcoord-mat l))) (n m) (i (1- m)))
		        (:instance flist0p-flistn0-len (x (wcoords0 (wcomb (wdep-coeffs l) l))))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance row-rank<=m (a (wcoord-mat l)) (n (wdim)))
                        (:instance row-echelon-p-row-reduce (n (wdim)) (a (wcoord-mat l)))))))

(local-defthmd wdepp-wcomb-w0-3
  (implies (and (posp m) (wlistnp l m) (wdepp l) (posp (wdim)))
	   (let ((c (wdep-coeffs l)))
  	     (equal (wcoords0 (wcomb c l))
	            (flistn0 (wdim)))))
  :hints (("Goal" :use (wdepp-wcomb-w0-1 wdepp-wcomb-w0-2))))

(local-defthmd wdepp-wcomb-w0-4
  (implies (and (posp m) (wlistnp l m) (wdepp l) (posp (wdim)))
	   (let ((c (wdep-coeffs l)))
	     (and (flistnp c m)
	          (not (equal c (flistn0 m))))))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance flistnp-row (a (row-reduce-mat (wcoord-mat l))) (n m) (i (1- m)))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance invertiblep-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance invertiblep-fdet-not-zero (a (row-reduce-mat (wcoord-mat l))) (n m))
			(:instance fdet-row-0 (a (row-reduce-mat (wcoord-mat l))) (n m) (k (1- m)))))))

(local-defthmd wdepp-wcomb-w0-5
  (implies (and (natp n) (wlistnp b n))
           (equal (wcomb (flistn0 n) b)
	          (w0))))

(defthmd wdepp-wcomb-w0
  (implies (and (posp m) (wlistnp l m) (wdepp l))
	   (let ((c (wdep-coeffs l)))
	     (and (flistnp c m)
		  (not (= c (flistn0 m)))
		  (equal (wcomb c l) (w0)))))
  :hints (("Goal" :in-theory (disable wbasis0-spans)
                  :use (wdepp-wcomb-w0-3 wdepp-wcomb-w0-4 posp-wdim
                        (:instance wdepp-wcomb-w0-5 (n (wdim)) (b (wbasis0)))
			(:instance wbasis0-spans (x (wcomb (wdep-coeffs l) l)))
		        (:instance flist0p-flistn0-len (x (wcoords0 (wcomb (wdep-coeffs l) l))))))))

;; Note that the axiom wbasis0-lin-indep ensures that wbasis0 is a linearly independent list:

(defthm windepp-wbasis0
  (windepp (wbasis0))
  :hints (("Goal" :use (posp-wdim
                        (:instance wdepp-wcomb-w0 (m (wdim)) (l (wbasis0)))
                        (:instance wbasis0-lin-indep (c (wdep-coeffs (wbasis0))))))))

;; We must also show that if (windepp l), then (w0) is not a nontrivial linearly combination of l.
;; Assume (flistnp c m).  We must show that if (car (fmat* (list c) a)) = (flistn0 (wdim)), then
;; c = (flistn0 m).  We first show that this holds if a is replaced by r = (row-reduce a).
;; Let i < m and j = (nth i (lead-inds r)).  By fmat*-entry,

;;    (nth j (car (fmat* (list c) r))) = (entry 0 j (fmat* (list c) r)) = (fdot c (col j r)),

;; and it follows from  nth-col-lead-inds that (fdot c (col j r)) = (nth i c):

(local-defthmd row-echelon-p-windepp-1
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m)
		(dlistp l)
		(sublistp l (ninit m)))
	   (equal (fdot-select l c (col (nth i (lead-inds r)) r))
	          (if (member i l) (nth i c) (f0))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance nth-col-lead-inds (a r) (k (car l)))
	                        (:instance member-ninit (n m) (x (car l)))))))

(local-defthmd row-echelon-p-windepp-2
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (fdot c (col (nth i (lead-inds r)) r))
	          (nth i c)))
  :hints (("Goal" :in-theory (e/d (row-rank) (member-sublist))
                  :use ((:instance len-lead-inds-num-nonzero-rows (a r))
		        (:instance sublistp-lead-inds-ninit (a r))
		        (:instance row-echelon-p-windepp-1 (l (ninit m)))
			(:instance member-ninit (x i) (n m))
			(:instance row-reduce-row-echelon-p (a r))
			(:instance member-ninit (x (nth i (lead-inds r))))
			(:instance member-sublist (x (nth i (lead-inds r))) (l (lead-inds r)) (m (ninit n)))
                        (:instance fdot-select-ninit (n m) (x c) (y (col (nth i (lead-inds r)) r)))
			(:instance flistnp-col (a r) (j (nth i (lead-inds r))))))))

(defthmd entry-fmat*-row-echelon-p
  (implies (and (posp m) (posp n) (fmatp r m n)
                (row-echelon-p r) (= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (nth (nth i (lead-inds r)) (car (fmat* (list c) r)))
	          (nth i c)))
  :hints (("Goal" :in-theory (e/d (row-rank) (fmat*))
                  :use (row-echelon-p-windepp-2
		        (:instance len-lead-inds-num-nonzero-rows (a r))
			(:instance row-reduce-row-echelon-p (a r))
			(:instance nth-lead-inds-bound (a r) (k i))
                        (:instance fmat*-entry (i 0) (j (nth i (lead-inds r))) (m 1) (n m) (p n) (a (list c)) (b r))))))

;; But since (car (fmat* (list c) a)) = (flistn0 (wdim)), (nth i c) = (f0) for all i, i.e., c = (flistn0 m):

(local-defthmd row-echelon-p-windepp-3
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n))
		(natp j)
		(< j n))
	   (equal (nth j (car (fmat* (list c) r)))
	          (f0))))

(local-defthmd row-echelon-p-windepp-4
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n))
		(natp i)
		(< i m))
	   (equal (nth i c) (f0)))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use (entry-fmat*-row-echelon-p
                        (:instance nth-lead-inds-bound (a r) (k i))
			(:instance row-reduce-row-echelon-p (a r))
                        (:instance row-echelon-p-windepp-3 (j (nth i (lead-inds r))))))))

(defthm row-echelon-p-windepp
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n)))
	   (equal c (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance nth-diff-diff (x c) (y (flistn0 m)))
                        (:instance row-echelon-p-windepp-4 (i (nth-diff c (flistn0 m))))))))

;; Suppose (wcomb c l) = (w0).  Then (car (fmat* (list c) a)) = (wcoords0 (w0)) = (flistn0 (wdim)).
;; Let r = (row-reduce a), p = (row-reduce-mat a), and c' = (car (fmat* (list c) (inwerse-mat p))).
;; Then r = (fmat* p a), which implies a = (fmat* (inwerse-mat p) r) and

;;   (fmat* (list c') r) = (fmat* (fmat* (list c) (inwerse-mat p)) r)
;;                       = (fmat* (list c) (fmat* (inwerse-mat p) r))
;;                       = (fmat* (list c) a):

(local-defthmd windepp-wcomb-w0-1
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wcomb c l) (w0)))
	   (equal (car (fmat* (list c) (wcoord-mat l)))
	          (flistn0 (wdim))))
  :hints (("Goal" :use (wcoords0-wcomb wcoords0-w0))))

(local-defthmd windepp-wcomb-w0-2
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (fmat* (list c) (inverse-mat p)) r)
	            (fmat* (list c) (fmat* (inverse-mat p) r)))))
  :hints (("Goal" :in-theory (e/d (fmatp) (fmatp-wcoord-mat))
                  :use (fmatp-wcoord-mat
		        (:instance fmat*-assoc (m 1) (n m) (p m) (q (wdim)) (a (list c))
                                               (b (inverse-mat (row-reduce-mat (wcoord-mat l))))
					       (c (row-reduce (wcoord-mat l))))
			(:instance invertiblep-sufficient (a (row-reduce-mat (wcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))))))

(local-defthmd windepp-wcomb-w0-3
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (inverse-mat p) r)
	            a)))
  :hints (("Goal" :in-theory (e/d (fmatp) (fmatp-wcoord-mat))
                  :use (fmatp-wcoord-mat
		        (:instance fmat*-assoc (n m) (p m) (q (wdim))
                                               (a (inverse-mat (row-reduce-mat (wcoord-mat l))))
                                               (b (row-reduce-mat (wcoord-mat l)))
					       (c (wcoord-mat l)))
			(:instance id-fmat-left (a (wcoord-mat l)) (n (wdim)))
			(:instance invertiblep-sufficient (a (row-reduce-mat (wcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance row-ops-mat-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))))))

(defthmd fmat*-wcomb-row-reduce
  (implies (and (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (fmat* (list c1) r)
	            (fmat* (list c) a))))
  :hints (("Goal" :use (posp-wdim windepp-wcomb-w0-2 windepp-wcomb-w0-3))))

;; Thus, (car (fmat* (list c') r) = (flistn0 (wdim)).  By row-echelon-p-windepp, c' = (flistn0 m),
;; which implies

;;   (list c) = (fmat* (list (flistn0 m)) p) = (list (flistn0 m))

;; and we hawe the following:

(local-defthmd windepp-wcomb-w0-4
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wcomb c l) (w0)))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (car (fmat* (fmat* (list c) (inverse-mat p)) r))
	            (flistn0 (wdim)))))
  :hints (("Goal" :use (windepp-wcomb-w0-1 windepp-wcomb-w0-2 windepp-wcomb-w0-3))))

(local-defthm windepp-wcomb-w0-5
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wcomb c l) (w0)))
	   (let* ((a (wcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (list (car (fmat* (list c) (inverse-mat p))))
	            (fmat* (list c) (inverse-mat p)))))
  :hints (("Goal" :in-theory (disable fmatp-wcoord-mat)
                  :use (fmatp-wcoord-mat
			(:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (wcoord-mat l)))))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))))))

(local-defthm windepp-wcomb-w0-6
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wcomb c l) (w0)))
	   (let* ((a (wcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (list c) (inverse-mat p))
	            (list (flistn0 m)))))
  :hints (("Goal" :in-theory (e/d (row-echelon-p-row-reduce row-reduce-row-echelon-p windepp) (fmatp-wcoord-mat fmat*))
                  :use (windepp-wcomb-w0-4 windepp-wcomb-w0-5 fmatp-wcoord-mat
                        (:instance row-echelon-p-windepp
			  (c (car (fmat* (list c) (inverse-mat (row-reduce-mat (wcoord-mat l))))))
			  (r (row-reduce (wcoord-mat l)))
                          (n (wdim)))
			(:instance invertiblep-sufficient (a (row-reduce-mat (wcoord-mat l))) (n m))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (wcoord-mat l)))))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))))))

(local-defthm windepp-wcomb-w0-7
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
 		(equal (wcomb c l) (w0)))
	   (let* ((a (wcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (car (fmat* (list (flistn0 m)) p))
	            c)))
  :hints (("Goal" :in-theory (disable fmatp-wcoord-mat fmat*)
                  :use (windepp-wcomb-w0-6 fmatp-wcoord-mat
			(:instance invertiblep-sufficient (a (row-reduce-mat (wcoord-mat l))) (n m))
			(:instance id-fmat-right (m 1) (n m) (a (list c)))
			(:instance fmat*-assoc (m 1) (n m) (p m) (q m)
			                       (a (list c)) (b (inverse-mat (row-reduce-mat (wcoord-mat l))))
					       (c (row-reduce-mat (wcoord-mat l))))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))))))

(local-defthm windepp-wcomb-w0-8
  (implies (and (posp m)
		(flistnp c m)
 		(fmatp p m m)
		(natp j)
		(< j m))
	   (equal (nth j (car (fmat* (list (flistn0 m)) p)))
		  (f0)))
  :hints (("Goal" :use ((:instance fmat*-entry (a (list (flistn0 m))) (b p) (m 1) (n m) (p m) (i 0))))))

(local-defthm windepp-wcomb-w0-9
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
 		(equal (wcomb c l) (w0))
		(natp j)
		(< j m))
	   (equal (nth j c)
		  (f0)))
  :hints (("Goal" :in-theory (disable fmatp-wcoord-mat fmat*)
                  :use (windepp-wcomb-w0-7 fmatp-wcoord-mat
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
                        (:instance windepp-wcomb-w0-8 (p (row-reduce-mat (wcoord-mat l))))))))

(defthm windepp-wcomb-w0
  (implies (and (posp m)
		(wlistnp l m)
		(windepp l)
		(flistnp c m)
		(Equal (wcomb c l) (w0)))
	   (equal c (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use (posp-wdim
                        (:instance nth-diff-diff (x c) (y (flistn0 m)))
                        (:instance windepp-wcomb-w0-9 (j (nth-diff c (flistn0 m))))))))

;; (w0) is not a member of any linearly independent list:

(defthm wcomb-funit
  (implies (and (natp n) (natp j) (< j n) (wlistnp l n))
           (equal (wcomb (funit j n) l)
	          (nth j l))))

(defthm nth-windepp-not-w0
  (implies (and (posp m)
		(wlistnp l m)
		(windepp l)
		(natp j)
		(< j m))
	   (not (equal (nth j l) (w0))))
  :hints (("Goal" :in-theory (enable wdepp)
                  :use (posp-wdim
		        (:instance wcomb-funit (n m))
		        (:instance windepp-wcomb-w0 (c (funit j m)))
			(:instance nth-funit (n m) (i j))))))

(defthm w0-not-member-windepp
  (implies (and (natp m)
		(wlistnp l m)
		(windepp l))
	   (not (member (w0) l)))
  :hints (("Goal" :use (posp-wdim
                        (:instance nth-windepp-not-w0 (j (index (w0) l)))
                        (:instance ind<len (x (w0)))))))

;; If m > (wdim), then since (fmatp a m (wdim)), (row-rank a) <= (wdim) < m, i.e., (wdepp l):

(defthmd wdep-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (wdepp l))
  :hints (("Goal" :in-theory (enable wdepp windepp)
                  :use (posp-wdim (:instance row-rank<=n (a (wcoord-mat l)) (n (wdim)))))))

(defund wcoords (x l)
  (let ((c (wdep-coeffs (cons x l))))
    (flist-scalar-mul (f- (f/ (car c))) (cdr c))))

(in-theory (disable wdep-coeffs))

(defthmd wdepp-wcomb-1
  (implies (and (wlistnp l n) (posp n) (wp x) (windepp l) (wdepp (cons x l)) (posp (wdim)))
           (let ((c (wdep-coeffs (cons x l))))
	     (and (flistnp c (1+ n))
		  (not (= (car c) (f0)))
	          (equal (wcomb c (cons x l)) (w0)))))
  :hints (("Goal" :use ((:instance wdepp-wcomb-w0 (m (1+ n)) (l (cons x l)))
                        (:instance windepp-wcomb-w0 (m n) (c (cdr (wdep-coeffs (cons x l)))))))))

(defthmd hack-4
  (implies (and (wp x) (wp d) (fp c) (not (= c (f0))) (= (w+ (w* c x) d) (w0)))
           (equal (w* (f- (f/ c)) d) x))
  :hints (("Goal" :use ((:instance wdistw (c (f/ c)) (x (w* c x)) (y d))
                        (:instance w*assoc (c (f/ c)) (d c))
			(:instance w+assoc (y (w* (f/ c) d)) (z (w* (f- (f/ c)) d)))
			(:instance wdistf (c (f/ c)) (d (f- (f/ c))) (x d))))))

(defthmd wdepp-wcomb
  (implies (and (wlistnp l n) (posp n) (wp x) (windepp l) (wdepp (cons x l)))
           (and (flistnp (wcoords x l) n)
	        (equal (wcomb (wcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable wcomb-scalar-mul wcoords)
                  :use (wdepp-wcomb-1 posp-wdim
		        (:instance hack-4 (c (CAR (WDEP-COEFFS (CONS X L)))) (d (WCOMB (CDR (WDEP-COEFFS (CONS X L))) L)))))))

;; Conwersely, suppose  x is a linear combination of l, say x = (wcomb c l).  Let c' = (cons (f- (f1)) c).
;; Then (wcomb c' (cons x l)) = (w+ (w* (f- (f1)) x) (wcomb c l)) = (w+ (w- x) x) = (w0), and by windepp-wcomb-w0,
;; (wdepp (cons x l)):

(defthmd wcomb-wdepp
  (implies (and (wlistnp l n) (flistnp c n) (natp n))
           (wdepp (cons (wcomb c l) l)))
  :hints (("Goal" :in-theory (e/d (wdepp) (f-f0))
                  :use (f-f0 posp-wdim
		        (:instance windepp-wcomb-w0 (c (cons (f- (f1)) c)) (l (cons (wcomb c l) l)) (m (1+ n)))
		        (:instance wdistf (c (f- (f1))) (d (f1)) (x (wcomb c l)))))))

;; An equivalent formulation of linear independence using defun-sk:

(defun-sk windepp-sk (l)
  (forall (c)
    (implies (and (flistnp c (len l))
                  (equal (wcomb c l) (w0)))
	     (equal c (flistn0 (len l))))))

(defthmd windepp-sk-lemma
  (implies (and (windepp-sk l)
                (flistnp c (len l))
                (equal (wcomb c l) (w0)))
	   (equal (flistn0 (len l)) c))
  :hints (("Goal" :use (windepp-sk-necc))))

(defthmd windepp-sk-witness-lemma
  (let ((c (windepp-sk-witness l)))
     (implies (implies (and (flistnp c (len l))
                            (equal (wcomb c l) (w0)))
	               (equal (flistn0 (len l)) c))
	      (windepp-sk l))))

(in-theory (disable windepp-sk))

(defthmd windepp-equivalence
  (implies (and (posp m) (wlistnp l m))
           (iff (windepp-sk l)
	        (windepp l)))
  :hints (("Goal" :in-theory (enable wdepp)
                  :use (posp-wdim wdepp-wcomb-w0 windepp-sk-witness-lemma
		        (:instance windepp-sk-lemma (c (wdep-coeffs l)))
			(:instance windepp-wcomb-w0 (c (windepp-sk-witness l)))))))

(defthmd not-windepp-sk-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (not (windepp-sk l)))
  :hints (("Goal" :in-theory (enable wdepp)
                  :use (windepp-equivalence wdep-if->-dim))))


;; We define a wbasis to be a linearly independent list of (wdim) vectors:

(defund wbasisp (l)
  (and (wlistnp l (wdim))
       (windepp l)))

;; Obviously, the canonical basis is a wbasis:

(defthm wbasisp-wbasis0
  (wbasisp (wbasis0))
  :hints (("Goal" :in-theory (enable wbasisp)))) 

;; By wdep-if->-dim, for any vector x, the list (cons x b) is linearly dependent, and therefore, by wdepp-wcomb,
;; b spans the space:

(defthmd wbasis-spans
  (implies (and (wbasisp b) (wp x))
           (and (flistnp (wcoords x b) (wdim))
	        (equal (wcomb (wcoords x b) b)
	               x)))
  :hints (("Goal" :in-theory (enable wbasisp)
                  :use ((:instance wdep-if->-dim (m (1+ (wdim))) (l (cons x b)))
		        (:instance wdepp-wcomb (l b) (n (wdim)))))))

;; By functional instantiation of wcoords0-unique, this representation is unique:

(defthmd wcoords-unique
  (implies (and (wbasisp b) (wp x) (flistnp c (wdim))
		(equal (wcomb c b) x))
	   (equal (wcoords x b) c))
  :hints (("Goal" :use ((:functional-instance wcoords0-unique
                          (wbasis0 (lambda () (if (and (posp (wdim)) (wbasisp b)) b (wbasis0))))
			  (wcoords0 (lambda (x) (if (and (posp (wdim)) (wbasisp b)) (wcoords x b) (wcoords0 x)))))))
	  ("Subgoal 5" :in-theory (enable wbasisp)
	               :use (wbasis0-lin-indep
		             (:instance windepp-wcomb-w0 (l b) (m (wdim)))))
	  ("Subgoal 4" :in-theory (enable wbasisp)
	               :use (wbasis-spans))
	  ("Subgoal 3" :in-theory (disable flistnp-wcoords0)
	               :use (wbasis-spans flistnp-wcoords0))
	  ("Subgoal 2" :in-theory (enable wbasisp))
	  ("Subgoal 1" :in-theory (enable wdim wbasisp))))

;; Consequently,

(defthm wcoords-wcoords0
  (implies (wp x)
           (equal (wcoords x (wbasis0))
	          (wcoords0 x)))
  :hints (("Goal" :use ((:instance wcoords-unique (b (wbasis0)) (c (wcoords0 x)))))))

;; The coordinates of a basis element:

(defthm wcomb-funit
  (implies (and (natp n) (natp j) (< j n) (wlistnp l n))
           (equal (wcomb (funit j n) l)
	          (nth j l))))

(defthm wcoords-nth-basis
  (implies (and (wbasisp b) (natp j) (< j (wdim)))
           (equal (wcoords (nth j b) b)
	          (funit j (wdim))))
  :hints (("Goal" :in-theory (enable wbasisp)
                  :use ((:instance wcoords-unique (c (funit j (wdim))) (x (nth j b)))))))

;; Given a wbasis b and a list of vectors l, consider the matrix of coordinates of the members of l with respect to b:

(defun wbasis-mat (l b)
  (if (consp l)
      (cons (wcoords (car l) b)
            (wbasis-mat (cdr l) b))
    ()))

(defthmd fmatp-wbasis-mat
  (implies (and (wbasisp b) (wlistnp l m))
           (fmatp (wbasis-mat l b) m (wdim)))
  :hints (("Goal" :induct (nthcdr m l)
                  :in-theory (enable fmatp))
          ("Subgoal *1/2" :use ((:instance wbasis-spans (x (car l)))))))

;; By functional instantiation of wcoords0-wcomb, for any linear combination (wcomb c l) of l, we have the following 
;; formula for (wcoords (wcomb c l) b):

(defthmd wcoords-wcomb
  (implies (and (wbasisp b) (posp m) (wlistnp l m) (flistnp c m))
	   (equal (wcoords (wcomb c l) b)
		  (car (fmat* (list c) (wbasis-mat l b)))))
  :hints (("Goal" :use ((:functional-instance wcoords0-wcomb
                          (wbasis0 (lambda () (if (and (posp (wdim)) (wbasisp b)) b (wbasis0))))
                          (wcoord-mat (lambda (l) (if (and (posp (wdim)) (wbasisp b)) (wbasis-mat l b) (wcoord-mat l))))
			  (wcoords0 (lambda (x) (if (and (posp (wdim)) (wbasisp b)) (wcoords x b) (wcoords0 x)))))))
	  ("Subgoal 5" :in-theory (enable wbasisp)
	               :use (wbasis0-lin-indep
		             (:instance windepp-wcomb-w0 (l b) (m (wdim)))))
	  ("Subgoal 4" :in-theory (enable wbasisp)
	               :use (wbasis-spans))
	  ("Subgoal 3" :in-theory (disable flistnp-wcoords0)
	               :use (wbasis-spans flistnp-wcoords0))
	  ("Subgoal 2" :in-theory (enable wbasisp))
	  ("Subgoal 1" :in-theory (enable wdim wbasisp))))

;; Combining wcoords-wcom and wbasis-spans, we have the following formula relating coordinates with respect to
;; 2 wbases:

(defthmd wcoords-convert
  (implies (and (wbasisp b1) (wbasisp b2) (wp x))
           (equal (fmat* (list (wcoords x b1)) (wbasis-mat b1 b2))
	          (list (wcoords x b2))))
  :hints (("Goal" :in-theory (enable wbasis-spans wbasisp)
                  :use ((:instance wcoords-wcomb (m (wdim)) (l b1) (b b2) (c (wcoords x b1)))))))

(defthmd fmatp-wbasis-wbasis-mat
  (implies (and (wbasisp b1) (wbasisp b2))
           (fmatp (wbasis-mat b1 b2) (wdim) (wdim)))
  :hints (("Goal" :in-theory (enable wbasisp)
                  :use ((:instance fmatp-wbasis-mat (l b1) (b b2) (m (wdim)))))))

;; Now let p = (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1)).  For all x,

;;    (fmat* (list (wcoords x b1)) p)
;;      = (fmat* (list (wcoords x b1)) (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1)))
;;      = (fmat* (fmat* (list (wcoords x b1)) (wbasis-mat b1 b2)) (wbasis-mat b2 b1))
;;      = (fmat* (list (wcoords x b2)) (wbasis-mat b2 b1))
;;      = (list (wcoords x b1)).

(local-defthmd compose-wbasis-wbasis-mats
  (implies (and (wbasisp b1) (wbasisp b2) (wp x))
           (equal (fmat* (list (wcoords x b1)) (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1)))
	          (list (wcoords x b1))))
  :hints (("Goal" :use (fmatp-wbasis-wbasis-mat wcoords-convert
                        (:instance wcoords-convert (b1 b2) (b2 b1))
                        (:instance fmatp-wbasis-wbasis-mat (b1 b2) (b2 b1))
			(:instance wbasis-spans (b b1))
			(:instance fmat*-assoc (m 1) (n (wdim)) (p (wdim)) (q (wdim))
			                       (a (list (wcoords x b1))) (b (wbasis-mat b1 b2)) (c (wbasis-mat b2 b1)))))))

;; In particular, for i < (wdim),

;;    (row i p) = (car (fmat* (list (funit i (wdim))) p)) = (funit i (wdim)),

(local-defthmd fmat*-funit-1
  (implies (and (fmatp a m n) (posp m) (posp n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry 0 j (fmat* (list (funit i m)) a))
	          (entry i j a)))
  :hints (("Goal" :use (nth-col (:instance fmat*-entry (m 1) (n m) (p n) (a (list (funit i m))) (b a) (i 0))))))

(local-defthmd fmat*-funit
  (implies (and (fmatp a m n) (posp m) (posp n) (natp i) (< i m))
           (equal (car (fmat* (list (funit i m)) a))
	          (row i a)))
  :hints (("Goal" :use (flistnp-row
                        (:instance flistnp-row (a (fmat* (list (funit i m)) a)) (i 0))
			(:instance fmatp-fmat* (a (list (funit i m))) (b a) (m 1) (n m) (p n))
                        (:instance nth-diff-diff (x (car (fmat* (list (funit i m)) a))) (y (row i a)))
                        (:instance fmat*-funit-1 (j (nth-diff (car (fmat* (list (funit i m)) a)) (row i a))))))))

(local-defthmd fmatp-compose-wbasis-wbasis-mats
  (implies (and (wbasisp b1) (wbasisp b2))
           (fmatp (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1))
	          (wdim) (wdim)))
  :hints (("Goal" :use (fmatp-wbasis-wbasis-mat
                        (:instance fmatp-wbasis-wbasis-mat (b1 b2) (b2 b1))
			(:instance fmatp-fmat* (m (wdim)) (n (wdim)) (p (wdim)) (a (wbasis-mat b1 b2)) (b (wbasis-mat b2 b1)))))))

(local-defthmd row-compose-wbasis-wbasis-mats
  (implies (and (wbasisp b1) (wbasisp b2) (natp i) (< i (wdim)))
           (equal (row i (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1)))
	          (funit i (wdim))))
  :hints (("Goal" :in-theory (enable wbasisp)
                  :use (fmatp-compose-wbasis-wbasis-mats
                        (:instance fmat*-funit (a (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1))) (m (wdim)) (n (wdim)))
			(:instance compose-wbasis-wbasis-mats (x (nth i b1)))))))

;; and hence p = (id-fmat (wdim)):

(defthmd compose-wbasis-wbasis-mats-id-fmat
  (implies (and (wbasisp b1) (wbasisp b2))
           (equal (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1))
	          (id-fmat (wdim))))
  :hints (("Goal" :use (fmatp-compose-wbasis-wbasis-mats
                        (:instance fmat-entry-diff-lemma (m (wdim)) (n (wdim))
			                                 (a (id-fmat (wdim))) (b (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1))))
			(:instance row-compose-wbasis-wbasis-mats
			            (i (car (entry-diff (id-fmat (wdim)) (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1))))))))))

;; Thus, by invertiblep-inverse, we have the following:

(defthmd wbasis-mat-inverse
  (implies (and (wbasisp b1) (wbasisp b2))
           (and (invertiblep (wbasis-mat b1 b2) (wdim))
	        (equal (inverse-mat (wbasis-mat b1 b2))
		       (wbasis-mat b2 b1))))
  :hints (("Goal" :use (fmatp-wbasis-wbasis-mat compose-wbasis-wbasis-mats-id-fmat
                        (:instance fmatp-wbasis-wbasis-mat (b1 b2) (b2 b1))
			(:instance invertiblep-inverse (a (wbasis-mat b1 b2)) (b (wbasis-mat b2 b1)) (n (wdim)))))))

;; We shall show that any linearly independent list of vectors may be extended to a wbasis.  To this end,
;; given a linearly independent list l with (len l) = m < (wdim),  we shall construct a vector (unspanned l)
;; that is not a linear combination of l.  Once again, let a = (wcoord-mat l), p = (row-reduce-mat a), and
;; r = (row-reduce a).  We may define (wunspanned l) to be a member of wbasis0 that corresponds to any of the
;; indices of (free-inds r (wdim)).  We arbitrarily select the wbasis element corresponding to
;; (car (free-inds r (wdim))):

(defund wunspanned (l)
  (nth (car (free-inds (row-reduce (wcoord-mat l)) (wdim)))
       (wbasis0)))

(local-defthmd row-echelon-p-row-reduce-wcoord-mat
 (implies (wlistnp l m)
          (let ((r (row-reduce (wcoord-mat l))))
	    (and (fmatp r m (wdim))
	         (row-echelon-p r))))
  :hints (("Goal" :use ((:instance row-echelon-p-row-reduce (n (wdim)) (a (wcoord-mat l)))
                        (:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))))))

(local-defthmd car-free-inds-w
 (implies (and (wlistnp l m) (posp m) (< m (wdim)))
          (let* ((r (row-reduce (wcoord-mat l)))
	         (i (car (free-inds r (wdim)))))
	    (and (natp i)
	         (< i (wdim))
		 (not (member i (lead-inds r))))))
  :hints (("Goal" :use (row-echelon-p-row-reduce-wcoord-mat
                        (:instance consp-free-inds (a (row-reduce (wcoord-mat l))) (n (wdim)))
			(:instance member-free-inds (a (row-reduce (wcoord-mat l))) (n (wdim))
			                            (x (car (free-inds (row-reduce (wcoord-mat l)) (wdim)))))
			(:instance member-ninit (x (car (free-inds (row-reduce (wcoord-mat l)) (wdim)))) (n (wdim)))))))

(defthmd wp-wunspanned
  (implies (and (wlistnp l m) (posp m) (< m (wdim)))
           (wp (wunspanned l)))
  :hints (("Goal" :in-theory (enable wunspanned)
                  :use (car-free-inds-w))))

;; Let u = (wunspanned l).  Suppose (flistnp c m) and u = (wcomb c l).  Let c' = (car (fmat* (list c) (inverse-mat p))).
;; By fmat*-wcomb-row-reduce and wcoords0-wcomb,

;;     (car (fmat* (list c') r)) = (car (fmat* (list c) a)) = (wcoords0 u). 

;; Let i < m and j = (nth i (lead-inds r)).  Then by entry-fmat*-row-echelon-p,

;;    (nth i c') = (nth j (car (fmat* (list c') r))) = (nth j (wcoords0 u)) = (f0),

;; and hence c' = (flistn0 m), which implies (wcoords0 u) = (flistn0 (wdim)), a contradiction.

(local-defthmd wunspanned-not-wcomb-1
  (implies (and (posp (wdim))
                (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wunspanned l) (wcomb c l)))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (car (fmat* (list c1) r))
	            (wcoords0 (wunspanned l)))))
  :hints (("Goal" :use (fmat*-wcomb-row-reduce wcoords0-wcomb))))

(local-defthmd wunspanned-not-wcomb-2
  (implies (and (wlistnp l m) (posp m) (< m (wdim)))
           (equal (wcoords0 (wunspanned l))
	          (funit (car (free-inds (row-reduce (wcoord-mat l)) (wdim))) (wdim))))
  :hints (("Goal" :in-theory (e/d (wunspanned) (wcoords-nth-basis))
                  :use (car-free-inds-w
		        (:instance wcoords-nth-basis (j (car (free-inds (row-reduce (wcoord-mat l)) (wdim))))
		                                    (b (wbasis0)))))))

(local-defthmd wunspanned-not-wcomb-3
  (implies (and (posp m)
                (wlistnp l m)
		(flistnp c m))
	   (let* ((a (wcoord-mat l))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
             (flistnp c1 m)))
  :hints (("Goal" :use ((:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (wcoord-mat l)))))
		        (:instance invertiblep-sufficient (a (row-reduce-mat (wcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance invertiblep-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance flistnp-row (i 0) (m 1) (n m) (a (fmat* (list c) (inverse-mat (row-reduce-mat (wcoord-mat l))))))))))

(local-defthmd wunspanned-not-wcomb-4
  (implies (and (posp m)
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wunspanned l) (wcomb c l))
                (natp i) (< i m))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (nth i c1)
	            (nth (nth i (lead-inds r))
		         (wcoords0 (wunspanned l))))))
  :hints (("Goal" :in-theory (e/d (windepp) (row-rank))
                  :use (wunspanned-not-wcomb-1 wunspanned-not-wcomb-3
		        (:instance row-rank-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance fmatp-row-reduce-mat (a (wcoord-mat l)) (n (wdim)))
			(:instance row-echelon-p-row-reduce (a (wcoord-mat l)) (n (wdim)))
                        (:instance entry-fmat*-row-echelon-p (n (wdim))
			                                     (r (row-reduce (wcoord-mat l)))
							     (c (car (fmat* (list c) (inverse-mat (row-reduce-mat (wcoord-mat l)))))))))))

(local-defthmd wunspanned-not-wcomb-5
  (implies (and (posp (wdim))
                (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
                (natp i) (< i m))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a)))
	     (and (member (nth i (lead-inds r)) (lead-inds r))
	          (natp (nth i (lead-inds r)))
	          (< (nth i (lead-inds r)) (wdim)))))
  :hints (("Goal" :in-theory (enable windepp)
                  :use ((:instance len-lead-inds-num-nonzero-rows (a (row-reduce (wcoord-mat l))))
		        (:instance row-rank-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))
			(:instance row-echelon-p-row-reduce (a (wcoord-mat l)) (n (wdim)))
                        (:instance nth-lead-inds-bound (n (wdim)) (k i) (a (row-reduce (wcoord-mat l))))))))

(local-defthmd wunspanned-not-wcomb-6
  (implies (and (posp (wdim))
                (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
                (natp i) (< i m))
	   (let* ((a (wcoord-mat l))
	          (r (row-reduce a)))
	     (equal (nth (nth i (lead-inds r))
	                 (funit (car (free-inds r (wdim))) (wdim)))
	            (f0))))
  :hints (("Goal" :in-theory (e/d (windepp) (row-rank))
                  :use (car-free-inds-w wunspanned-not-wcomb-5
		        (:instance nth-funit (i (nth i (lead-inds (row-reduce (wcoord-mat l)))))
			                     (j (car (free-inds (row-reduce (wcoord-mat l)) (wdim))))
					     (n (wdim)))))))

(local-defthmd wunspanned-not-wcomb-7
  (implies (and (posp (wdim))
                (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wunspanned l) (wcomb c l))
                (natp i) (< i m))
	   (let* ((a (wcoord-mat l))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal (nth i c1)
	            (f0))))
  :hints (("Goal" :use (wunspanned-not-wcomb-2 wunspanned-not-wcomb-4 wunspanned-not-wcomb-6))))

(local-defthmd wunspanned-not-wcomb-8
  (implies (and (posp (wdim))
                (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wunspanned l) (wcomb c l)))
	   (let* ((a (wcoord-mat l))
		  (p (row-reduce-mat a))
		  (c1 (car (fmat* (list c) (inverse-mat p)))))
	     (equal c1 (flistn0 m))))
  :hints (("Goal" :use (wunspanned-not-wcomb-3
		        (:instance nth-diff-diff (x (car (fmat* (list c) (inverse-mat (row-reduce-mat (wcoord-mat l))))))
                                                 (y (flistn0 m)))
			(:instance wunspanned-not-wcomb-7 (i (nth-diff (car (fmat* (list c) (inverse-mat (row-reduce-mat (wcoord-mat l)))))
			                                              (flistn0 m))))))))

(local-defthmd wunspanned-not-wcomb-9
  (implies (and (posp m) (posp n) (fmatp r m n))
           (equal (fmat* (list (flistn0 m)) r)
	          (list (flistn0 n))))
  :hints (("Goal" :use ((:instance fmatp-fmat* (m 1) (n m) (p n) (a (list (flistn0 m))) (b r))
                        (:instance fmat-entry-diff-lemma (a (fmat* (list (flistn0 m)) r)) (b (list (flistn0 n))) (m 1))
			(:instance fmat*-entry (a (list (flistn0 m))) (b r) (m 1) (n m) (p n)
			                       (i (car (entry-diff (fmat* (list (flistn0 m)) r) (list (flistn0 n)))))
			                       (j (cdr (entry-diff (fmat* (list (flistn0 m)) r) (list (flistn0 n))))))))))

(local-defthmd wunspanned-not-wcomb-10
  (implies (and (posp (wdim))
                (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
		(flistnp c m)
		(equal (wunspanned l) (wcomb c l)))
	   (equal (wcoords0 (wunspanned l))
	          (flistn0 (wdim))))
  :hints (("Goal" :use (wunspanned-not-wcomb-1 wunspanned-not-wcomb-8
		        (:instance wunspanned-not-wcomb-9 (n (wdim)) (r (row-reduce (wcoord-mat l))))
			(:instance fmatp-row-reduce (a (wcoord-mat l)) (n (wdim)))))))

(defthmd wunspanned-not-wcomb
  (implies (and (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
		(flistnp c m))
	   (not (equal (wunspanned l) (wcomb c l))))
  :hints (("Goal" :use (car-free-inds-w wunspanned-not-wcomb-2 wunspanned-not-wcomb-10
                        (:instance nth-funit (i (car (free-inds (row-reduce (wcoord-mat l)) (wdim))))
			                     (j (car (free-inds (row-reduce (wcoord-mat l)) (wdim))))
					     (n (wdim)))))))

;; We now invoke wdepp-wcomb:

(defthmd windepp-cons-wunspanned
  (implies (and (wlistnp l m) (windepp l) (posp m) (< m (wdim)))
           (windepp (cons (wunspanned l) l)))
  :hints (("Goal" :in-theory (enable wp-wunspanned wdepp)
                  :use ((:instance wdepp-wcomb (x (wunspanned l)) (n m))
                        (:instance wunspanned-not-wcomb (c (wcoords (wunspanned l) l)))))))

;; The extension of l to a wbasis is constructed recursively:

(defun extend-to-wbasis (l)
  (declare (xargs :measure (nfix (- (wdim) (len l)))))
  (if (and (wlistnp l (len l)) (windepp l) (< (len l) (wdim)))
      (extend-to-wbasis (cons (wunspanned l) l))
    l))

;; The following is proved by induction

(in-theory (disable (extend-to-wbasis) (wunspanned)))

(local-defun wbasisp-extend-to-wbasis-induct (l n)
  (declare (xargs :measure (nfix (- (wdim) (len l)))))
  (if (and (wlistnp l (len l)) (windepp l) (< (len l) (wdim)))
      (list (wbasisp-extend-to-wbasis-induct (cons (wunspanned l) l) (1+ n)))
    (list l n)))

(defthmd wbasisp-extend-to-wbasis
  (implies (and (wlistnp l n) (posp n) (windepp l))
           (wbasisp (extend-to-wbasis l)))	   
  :hints (("Goal" :induct (wbasisp-extend-to-wbasis-induct l n))
          ("Subgoal *1/2" :in-theory (enable wbasisp)
                          :use ((:instance wdep-if->-dim (m n))))
	  ("Subgoal *1/1" :in-theory (enable wp-wunspanned)
	                  :use ((:instance windepp-cons-wunspanned (m n))))))


;;---------------------------------------

;; The function lin is constrained to be a linear transformation from V to W:

(encapsulate (((lin *) => *))
  (local (defun lin (x) (declare (ignore x)) (w0)))
  (defthm lin-val
    (implies (vp x) (wp (lin x))))
  (defthm lin-v0
    (equal (lin (v0)) (w0)))
  (defthm lin-v+
    (implies (and (vp x) (vp y))
             (equal (lin (v+ x y))
	            (w+ (lin x) (lin y)))))
  (defthm lin-v*
    (implies (and (fp c) (vp x))
             (equal (lin (v* c x))
	            (w* c (lin x))))))

;; The image under lin of a list of vectors:

(defun lin-list (l)
  (if (consp l)
      (cons (lin (car l))
            (lin-list (cdr l)))
    ()))

(defthm len-lin-list
  (equal (len (lin-list l))
         (len l)))

(defun vlistnp-induct (l n)
  (declare (irrelevant l))
  (if (posp n)
      (vlistnp-induct (cdr l) (1- n))
    ()))

(defthm wlistnp-lin-list
  (implies (and (natp n) (vlistnp l n))
           (wlistnp (lin-list l) n))
  :hints (("Goal" :induct (vlistnp-induct l n)))) 

;; The image under lin of a linear combination:

(defthmd lin-vcomb
  (implies (and (natp n) (vlistnp l n) (flistnp c n))
           (equal (lin (vcomb c l))
	          (wcomb c (lin-list l)))))

;; The matrix representation of lin:

(defund lin-mat ()
  (wcoord-mat (lin-list (vbasis0))))

(defthmd lin-mat-lin
  (implies (and (vp x))
           (equal (wcoords0 (lin x))
	          (car (fmat* (list (vcoords0 x)) (lin-mat)))))
  :hints (("Goal" :in-theory (enable lin-mat)
                  :use (vbasis0-spans vlistnp-basis flistnp-vcoords0 
		        (:instance lin-vcomb (c (vcoords0 x)) (l (vbasis0)) (n (vdim)))
			(:instance wcoords0-wcomb (m (vdim)) (c (vcoords0 x)) (l (lin-list (vbasis0))))))))

;; Proof: Let c = (vcoords0 x). By vbasis0-spans, x = (vcomb c (vbasis0)), and by lin-vcomb,
;; (lin x) = (wcomb c (lin-list (wbasis0))).  Thus, by wcoords0-wcomb,

;;   (wcoords0 (lin x)) = (wcoords0 (wcomb c (wbasis0)))
;;                     = (car (fmat* (list c) (wcoord-mat (wbasis0))))
;; 		       = (car (fmat* (list (vcoords0 x)) (lin-mat)))  

;; lin is injective if the following is true:

(defun-sk lin-injective-p ()
  (forall (x)
    (implies (and (vp x) (equal (lin x) (w0)))
             (equal x (v0)))))

(defthmd lin-injective-p-lemma
  (implies (and (lin-injective-p)
                (vp x) (equal (lin x) (w0)))
           (equal (v0) x))
  :hints (("Goal" :use (lin-injective-p-necc))))

(defthmd lin-injective-p-witness-lemma
  (let ((x (lin-injective-p-witness)))
     (implies (implies (and (vp x) (equal (lin x) (w0)))
                       (equal (v0) x))
              (lin-injective-p))))

;; lin is surjective if the following is true:

(defchoose lin-preimage x (y)
  (and (vp x)
       (equal (lin x) y)))

(defun-sk lin-surjective-p ()
  (forall (y)
    (implies (wp y)
             (and (vp (lin-preimage y))
	          (equal (lin (lin-preimage y))
		         y)))))

(defthmd lin-surjective-p-lemma
  (implies (and (lin-surjective-p) (wp y))
           (and (vp (lin-preimage y))
	        (equal (lin (lin-preimage y))
		       y)))
  :hints (("Goal" :use (lin-surjective-p-necc))))

(defthmd lin-surjective-p-witness-lemma
  (let ((y (lin-surjective-p-witness)))
     (implies (implies (wp y)
                       (and (vp (lin-preimage y))
	                    (equal (lin (lin-preimage y))
		                   y)))
              (lin-surjective-p))))

(in-theory (disable lin-injective-p lin-surjective-p))

;; If lin is injective, (vlistnp l n), and l is linearly independent, then (lin-list l) is linearly independent:

(defthmd lin-injective-vindepp-windepp
  (implies (and (lin-injective-p) (natp n) (vlistnp l n) (vindepp l))
           (windepp (lin-list l)))
  :hints (("Goal" :use ((:instance wdepp-wcomb-w0 (l (lin-list l)) (m n))
                        (:instance lin-vcomb (c (wdep-coeffs (lin-list l))))
			(:instance lin-injective-p-lemma (x (vcomb (wdep-coeffs (lin-list l)) l)))
			(:instance vindepp-vcomb-v0 (m n) (c (wdep-coeffs (lin-list l))))))))

;; Proof: Suppose (wcomb c (lin-list l)) = (w0).  By lin-vcomb, (lin (vcomb c l)) = (w0).  Since lin is injective,
;; (vcomb c l) = (v0), and since l is linearly independent, c = (flistn0 n).

;; If lin is injective, then (dimv) <= (dimw):

(defthmd injection-dim-<=
  (implies (lin-injective-p)
           (<= (vdim) (wdim)))
  :hints (("Goal" :in-theory (enable vdim)
                  :use (vlistnp-basis
		        (:instance wdep-if->-dim (l (lin-list (vbasis0))) (m (vdim)))
                        (:instance lin-injective-vindepp-windepp (n (vdim)) (l (vbasis0)))
			(:instance wlistnp-lin-list (l (vbasis0)) (n (vdim)))))))

;; Proof: Suppose (dimv) > (dimw).  Then (len (lin-list (vbasis0))) = (len (vbasis0)) = (dimv) > (dimw).
;; By wdep-if->-dim, (lin-list (vbasis0)) is linearly dependent, but by lin-injective-vindepp-windepp, this
;; contradicts the linear independence of (vbasis0).

;; If lin is injective and (dimv) = (dimw), then lin is surjective:

(local-defthmd injection-dim-=
  (implies (and (lin-injective-p)
                (equal (vdim) (wdim)))
	   (lin-surjective-p))
  :hints (("Goal" :use (vlistnp-basis lin-surjective-p-witness-lemma
                        (:instance lin-preimage (y (lin-surjective-p-witness))
			                        (x (VCOMB (WCOORDS (LIN-SURJECTIVE-P-WITNESS) (LIN-LIST (VBASIS0))) (VBASIS0))))
                        (:instance wdep-if->-dim (m (1+ (vdim)))(l (cons (lin-surjective-p-witness) (lin-list (vbasis0)))))
		        (:instance lin-injective-vindepp-windepp (n (vdim)) (l (vbasis0)))
		        (:instance wdepp-wcomb (x (lin-surjective-p-witness)) (l (lin-list (vbasis0))) (n (vdim)))
		        (:instance lin-vcomb (n (vdim)) (c (wcoords (lin-surjective-p-witness) (lin-list (vbasis0)))) (l (vbasis0)))))))

(local-defthmd injection-surjection
  (implies (and (lin-injective-p)
                (lin-surjective-p))
	   (equal (vdim) (wdim)))
  :hints (("Goal" :use (vlistnp-basis injection-dim-<=
			(:instance lin-injective-vindepp-windepp (n (vdim)) (l (vbasis0)))
			(:instance wp-wunspanned (m (vdim)) (l (lin-list (vbasis0))))
			(:instance lin-surjective-p-lemma (y (wunspanned (lin-list (vbasis0)))))
			(:instance vbasis-spans (b (vbasis0)) (x (lin-preimage (wunspanned (lin-list (vbasis0))))))
			(:instance wunspanned-not-wcomb (m (vdim)) (l (lin-list (vbasis0)))
				                        (c (vcoords (lin-preimage (wunspanned (lin-list (vbasis0)))) (vbasis0))))
			(:instance lin-vcomb (n (vdim)) (l (vbasis0))
				             (c (vcoords (lin-preimage (wunspanned (lin-list (vbasis0)))) (vbasis0))))))))
									       
(defthmd injection-surjection-dim-=
  (implies (lin-injective-p)
           (iff (lin-surjective-p)
	        (equal (vdim) (wdim))))
  :hints (("Goal" :use (injection-dim-= injection-surjection))))

;; Proof: Let l = (lin-list (vbasis0)).  By lin-injective-vindepp-windepp, l is linearly independent.

;; Suppose vdim = wdim.  Let (wp y).  Since (len (cons y l)) = (vdim) + 1 = (wdim) + 1 > (wdim).  By wdep-if->-dim,
;; (cons y l) is linearly dependent.  By wdepp-wcomb and lin-vcomb,

;;    y = (wcomb (wcoords y l) l) = (lin (vcomb (wcoords y l) (vbasis0))).

;; On the other hand, suppose lin is surjective and vdim < wdim.  Let l = (lin-list (vbasis0)), y = (wunspanned l),
;; x = (lin-preimage y), and c = (vcoords x (vbasis0)).  By wp-wunspanned and lin-surjective-p-lemma, (wp y), (vp x),
;; and (lin x) = y.  By vbasisp-vbasis0 and vbasis-spans, (flistnp c (vdim)) and x = (vcomb c (vbasis0)).  By lin-vcomb,
;; y = (wcomb c l), contradicting wunspanned-not-wcomb.

#|
;;---------------------------------------------------------------------------------------------------------------------
;;  Subspaces
;;---------------------------------------------------------------------------------------------------------------------

;; Informally, a subspace of a vector space V is a subset of V that forms a vector space under the operations of V.
;; In our formalization, in order to specify a subspace, we must define a recognizer that refines the predicate vp and,
;; as usual, prove it is satisfied by (v0) and that the closure properties hold.  But we must also construct a basis,
;; define the corresponding coordinate function, and verify the related axioms.

(encapsulate (((sp *) => *) ((sbasis) => *))
  (local (defun sp (x) (vp x)))
  (local (defun sbasis () (vbasis0)))
  ;; Subset:
  (defthm s-subset
    (implies (sp x) (vp x)))
  ;; Non-empty:
  (defthm sp-v0
    (sp (v0)))
  ;; Closure:
  (defthm s-closed
    (implies (and (fp c) (sp x) (sp y))
             (sp (v+ (v* c x) y))))
  ;; List of s-vectors:
  (defun slistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (sp (car x))
	   (slistnp (cdr x) (1- n)))))
  ;; Basis:
  (defun sdim () (len (sbasis)))
  (in-theory (disable (sdim) (slistnp)))
  (defthm slistnp-basis
    (slistnp (sbasis) (sdim)))
  (defthmd sbasis-lin-indep
    (vindepp (sbasis)))
  (defthm sbasis-spans
    (implies (sp x)
             (vdepp (cons x (sbasis)))))
  (in-theory (disable sdim)))
  

(defthm sp-v- (implies (sp x) (sp (v- x))))
    
(defthm s+closed (implies (and (sp x) (sp y)) (sp (v+ x y))))
  
(defthm s*closed (implies (and (fp c) (sp x)) (sp (v* c x))))


;; Zero subspace


;; Any linearly independent list of vectors l determines a subspace with basis l.  An element
;; of this subspace is recognized by the predicate

(defund spannedp (x l)
  (vdepp (cons x l)))

;; Given any list of vectors l, we may construct a subspace whose elements are the linear
;; combinations of l.  A basis for this subspace may be constructed as a maximal linearly
;; independent sublist of l:

(defun max-indep (l)
  (if (consp l)
      (let ((m (max-indep (cdr l))))
        (if (spannedp (car l) m)
	    m
	  (cons (car l) m)))
    ()))

(defthmd vindepp-max-indep
  (implies (vlistnp l n)
           (vindepp (max-indep l))))

;; We shall show that a vector x is a linear combination of l iff x is a linear combination
;; of l' = (max-indep l).  Given a list of scalars c such that x = (vcomb c l), we construct
;; a list of scalars c' = (contract-vcomb c l) such that x = (vcomb c' l'):

(defun contract-vcomb (c l)
  (if (consp l)
      (if (spannedp (car l) (max-indep (cdr l)))
          (flist-add (flist-scalar-mul (car c) (vcoords (car l) (max-indep (cdr l))))
	             (contract-vcomb (cdr c) (cdr l)))
	(cons (car c) (contract-vcomb (cdr c) (cdr l))))
    ()))

(defthmd vcomb-contract-vcomb
  (implies (and (natp n) (vlistnp l n) (flistnp c n))
           (and (flistnp (contract-vcomb c l) (len (max-indep l)))
	        (equal (vcomb (contract-vcomb c l) (max-indep l))
		       (vcomb x l)))))

;; Given a list of scalars c' such that x = (vcomb c' l'), we construct a list of scalars
;; c = (contract-vcomb c' l) such that x = (vcomb c l):

(defun expand-vcomb (c l)
  (if (consp l)
      (if (spannedp (car l) (max-indep (cdr l)))
          (cons (f0) (expand-vcomb c (cdr l)))
	(cons (car c) (expand-vcomb (cdr c) (cdr l))))
    ()))

(defthmd vcomb-expand-comb
  (implies (and (natp n) (vlistnp l n) (flistnp c (len (max-indep l))))
           (and (flistnp (expand-vcomb c l) n)
	        (equal (vcomb (expand-vcomb c l) l)
	               (vcomb c (max-indep l))))))



;;---------------------------------------------------------------------------------------------------------------------
;;  n-space
;;---------------------------------------------------------------------------------------------------------------------

(defund fnp (x n)
  (flistnp x n))

(defund fn+ (x y)
  (flist-add x y))

(defund fn0 (n)
  (flistn0 n))

(defund fn- (x)
  (flist-scalar-mul (f- (f1)) x))

(defund fn* (c x)
  (flist-scalar-mul c x))

(defund fnbasis (n)
  (id-fmat n))

(defund fncoords (x)
  x)

(defund fnlistmp (x m n)
  (fmatp x m n))

(defund fncomb (c x)
  (fmat* (list c) x))
    




;; Solution space of a homogeneous system of linear equations with mxn coefficient matrix a:

(defun sol-space-basis-elt (a lead-inds free-ind j n)
  (if (and (natp j) (natp n) (< j n))
      (cons (if (= j free-ind)
	        (f1)
	      (if (member-equal j lead-inds)
	          (f- (entry j free-ind a))
		(f0)))
            (sol-space-basis-elt a lead-inds free-ind (1+ j) n))
    ()))

(defun sol-space-basis (a lead-inds free-inds n)
  (if (consp free-inds)
      (cons (sol-space-basis-elt a lead-inds (car free-inds) 0 n)
            (sol-space-basis a lead-inds (cdr free-inds) n)

(defun sol-space-coords (free-inds x)
  (if (consp free-inds)
      (cons (nth (car free-inds) x)
            (sol-space-coords (cdr free-inds) x))
    ()))



;; Row space of a matrix:

Let a be an mxn matrix with row-rank r.  Let b be a basis for the row space of a.
Then b is a list of r vectors in n-space, i.e., an rxn matrix.
Every row of a is a linear combination of b.
For some mxr matrix c, a = (fmat* c b).  Let a', b', and c' be the transposes of a, b,
and c, of dimensions nxm, nxr, and rxm.
Then a' = (fmat* b' c'), and hence every row of a' is a linear combination of c'.
Therefore, (row-rank a') <= r = (row-rank a).
Similarly, (row-rank a) <= (row-rank a').

(defthmd row-column-rank
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (row-rank (transpose-mat a))
	          (row-rank a))))

|#
