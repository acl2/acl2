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
  (defthm vlistnp-basis0
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

(defthmd v-unique
  (implies (and (vp x) (vp y) (equal (v+ x y) (v0)))
           (equal (v- x) y))
  :hints (("Goal" :use ((:instance v+assoc (x (v- x)) (y x) (z y))))))

(defthmd v*f-f1
  (implies (vp x)
           (equal (v* (f- (f1)) x)
	          (v- x)))
  :hints (("Goal" :use ((:instance v-unique (y (v* (f- (f1)) x)))
                        (:instance vdistf (c (f1)) (d (f- (f1))))))))

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

(defthmd vcomb-append
  (implies (and (flistnp c n) (flistnp d m)
                (vlistnp x n) (vlistnp y m)
		(natp n) (natp m))
	   (equal (vcomb (append c d) (append x y))
	          (v+ (vcomb c x) (vcomb d y))))
  :hints (("Subgoal *1/6" :use ((:instance v+assoc (x (V* (CAR C) (CAR X))) (y (VCOMB (CDR C) (CDR X))) (z (VCOMB D Y)))))))

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
                  :use (vlistnp-basis0
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

;; Coordinates of a sum:

(defthmd vcoords0-v+
  (implies (and (vp x) (vp y))
           (equal (vcoords0 (v+ x y))
	          (flist-add (vcoords0 x) (vcoords0 y))))
  :hints (("Goal" :use ((:instance vcoords0-unique (x (v+ x y)) (c (flist-add (vcoords0 x) (vcoords0 y))))
                        (:instance vcomb-add (n (vdim)) (l (vbasis0)) (x (vcoords0 x)) (y (vcoords0 y)))))))

;; Coordinates of a scalar product:

(defthmd vcoords0-v*
  (implies (and (vp x) (fp c))
           (equal (vcoords0 (v* c x))
	          (flist-scalar-mul c (vcoords0 x))))
  :hints (("Goal" :use ((:instance vcoords0-unique (x (v* c x)) (c (flist-scalar-mul c (vcoords0 x))))
                        (:instance vcomb-scalar-mul (n (vdim)) (l (vbasis0)) (x (vcoords0 x)))))))


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
  (or (null l)
      (equal (row-rank (vcoord-mat l))
             (len l))))

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
		  (not (equal c (flistn0 m)))
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
  (implies (and (natp m)
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
  (implies (and (natp m)
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

;; A list of length 1 is linearly dependent iff its member is v0:

(local-defthmd vdepp-v0-1
  (implies (and (vp x) (flistnp c 1) (equal (vcomb c (list x)) (v0)) (not (equal c (flistn0 1))))
           (and (fp (car c))
	        (not (equal (car c) (f0)))
	        (equal (v* (car c) x) (v0)))))

(local-defthmd vdepp-v0-2
  (implies (and (vp x) (flistnp c 1) (equal (vcomb c (list x)) (v0)) (not (equal c (flistn0 1))))
           (and (fp (car c))
	        (not (equal (car c) (f0)))
	        (equal (v0) x)))
  :hints (("Goal" :use (vdepp-v0-1 (:instance v*assoc (c (f/ (car c))) (d (car c)))))))

(local-defthmd vdepp-v0-3
  (implies (and (vp x) (vdepp (list x)))
           (equal (v0) x))
  :hints (("Goal" :use ((:instance vdepp-vcomb-v0 (m 1) (l (list x)))
                        (:instance vdepp-v0-2 (c (vdep-coeffs (list x))))))))

(defthmd vdepp-v0
  (implies (vp x)
           (iff (vdepp (list x))
                (equal (v0) x)))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vdepp-v0-3
                        (:instance v0-not-member-vindepp (m 1) (l (list x)))))))

;; If m > (vdim), then since (fmatp a m (vdim)), (row-rank a) <= (vdim) < m, i.e., (vdepp l):

(defthmd vdepp-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp l))
  :hints (("Goal" :in-theory (enable vdepp vindepp)
                  :use (posp-vdim (:instance row-rank<=n (a (vcoord-mat l)) (n (vdim)))))))

;; Combining vdepp-vcomb-v0 with vdepp-if->-dim, we can construct a linear dependency of a list of more
;; than(vdim) vectors:

(defthmd vcomb-v0-if->-dim
  (implies (and (posp m) (vlistnp l m) (> m (vdim)))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (equal c (flistn0 m)))
		  (equal (vcomb c l) (v0)))))
  :hints (("Goal" :use (vdepp-vcomb-v0 vdepp-if->-dim))))

;; Let l be a list of vectors and let x be a vector.  Suppose l is linearly independent and (cons x l)
;; is linearly dependent.  We shall construct a list of scalars (vcoords x l) such that
;; x = (vcomb (vcoords x l) l).  By vdepp-vcomb-v0,  we have a list c = (vdep-coeffs (cons x b)) such that

;;    (vcomb c (cons x l)) = (v+ (v* (car c) x) (vcomb (cdr c) l)) = (v0).

;; Since l is linearly independent, by vindepp-vcomb-v0, we cannot have (car c) = (f0), and therefore,

;;    x = (vcomb (flist-scalar-mul (f- (f/ (car c))) (cdr c)) l).

;; Thus, we define

(defund vcoords (x l)
  (if (null l)
      ()
    (let ((c (vdep-coeffs (cons x l))))
      (flist-scalar-mul (f- (f/ (car c))) (cdr c)))))

;; and we have

(in-theory (disable vdep-coeffs))

(defthmd vdepp-vcomb-1
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)) (posp (vdim)))
           (let ((c (vdep-coeffs (cons x l))))
	     (and (flistnp c (1+ n))
		  (not (equal (car c) (f0)))
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

(defthmd vdepp-vcomb-2
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)))
           (and (flistnp (vcoords x l) n)
	        (equal (vcomb (vcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable vcomb-scalar-mul vcoords)
                  :use (vdepp-vcomb-1 posp-vdim
		        (:instance hack-2 (c (CAR (VDEP-COEFFS (CONS X L)))) (d (VCOMB (CDR (VDEP-COEFFS (CONS X L))) L)))))))

(defthmd vdepp-vcomb
  (implies (and (vlistnp l n) (natp n) (vp x) (vindepp l) (vdepp (cons x l)))
           (and (flistnp (vcoords x l) n)
	        (equal (vcomb (vcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable vcomb-scalar-mul vcoords)
                  :use (vdepp-v0 vdepp-vcomb-2))))

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

(defund vdepp-sk (l)
  (not (vindepp-sk l)))

(defthmd vindepp-equivalence
  (implies (and (natp m) (vlistnp l m))
           (iff (vindepp-sk l)
	        (vindepp l)))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (posp-vdim vdepp-vcomb-v0 vindepp-sk-witness-lemma
		        (:instance vindepp-sk-lemma (c (vdep-coeffs l)))
			(:instance vindepp-vcomb-v0 (c (vindepp-sk-witness l)))))))

;; The main motivation for this equivalent formulation is that it will facilitate functional instantiation of lemmas
;; pertaining to linear independence.  Functional instantiation of any lemma that refers to a function that depends
;; on vindepp would require definitions analogous to those of vindepp and all of its supporting functions, including
;; those pertaining to row reduction.  Functional instantiation of the following is much simpler (see, for example
;; vdepp-sk-if->-sdim):

(defthmd vdepp-sk-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp-sk l))
  :hints (("Goal" :in-theory (enable vdepp vdepp-sk)
                  :use (vindepp-equivalence vdepp-if->-dim))))


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

;; By vdepp-if->-dim, for any vector x, the list (cons x b) is linearly dependent, and therefore, by vdepp-vcomb,
;; b spans the space:

(defthmd vbasis-spans
  (implies (and (vbasisp b) (vp x))
           (and (flistnp (vcoords x b) (vdim))
	        (equal (vcomb (vcoords x b) b)
	               x)))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use ((:instance vdepp-if->-dim (m (1+ (vdim))) (l (cons x b)))
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
                          :use ((:instance vdepp-if->-dim (m n))))
	  ("Subgoal *1/1" :in-theory (enable vp-vunspanned)
	                  :use ((:instance vindepp-cons-vunspanned (m n))))))

(local-defthmd cdr-nthcdr
  (implies (natp n)
           (equal (cdr (nthcdr n l))
	          (nthcdr (1+ n) l))))

(local-defthmd len-extend-to-basis
  (<= (len l) (len (extend-to-basis l))))

(local-defthmd nthcdr-extend-to-basis-1
  (equal (nthcdr (- (len (extend-to-basis l)) (len l)) (extend-to-basis l))
         l)
  :hints (("Subgoal *1/1" :use ((:instance cdr-nthcdr (l (EXTEND-TO-BASIS (CONS (VUNSPANNED L) L)))
                                                      (n (+ -1 (- (LEN L)) (LEN (EXTEND-TO-BASIS (CONS (VUNSPANNED L) L))))))
				(:instance len-extend-to-basis (l (CONS (VUNSPANNED L) L)))))))

(defthmd nthcdr-extend-to-basis
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (equal (nthcdr (- (vdim) (len l)) (extend-to-basis l))
                  l))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use (vbasisp-extend-to-basis nthcdr-extend-to-basis-1
		        (:instance len-vlistnp (x (extend-to-basis l)) (n (vdim)))))))


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

(defthmd w-unique
  (implies (and (wp x) (wp y) (equal (w+ x y) (w0)))
           (equal (w- x) y))
  :hints (("Goal" :use ((:instance w+assoc (x (w- x)) (y x) (z y))))))

(defthmd w*f-f1
  (implies (wp x)
           (equal (w* (f- (f1)) x)
	          (w- x)))
  :hints (("Goal" :use ((:instance w-unique (y (w* (f- (f1)) x)))
                        (:instance wdistf (c (f1)) (d (f- (f1))))))))

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

;; Coordinates of a sum:

(defthmd wcoords0-w+
  (implies (and (wp x) (wp y))
           (equal (wcoords0 (w+ x y))
	          (flist-add (wcoords0 x) (wcoords0 y))))
  :hints (("Goal" :use ((:instance wcoords0-unique (x (w+ x y)) (c (flist-add (wcoords0 x) (wcoords0 y))))
                        (:instance wcomb-add (n (wdim)) (l (wbasis0)) (x (wcoords0 x)) (y (wcoords0 y)))))))

;; Coordinates of a scalar product:

(defthmd wcoords0-w*
  (implies (and (wp x) (fp c))
           (equal (wcoords0 (w* c x))
	          (flist-scalar-mul c (wcoords0 x))))
  :hints (("Goal" :use ((:instance wcoords0-unique (x (w* c x)) (c (flist-scalar-mul c (wcoords0 x))))
                        (:instance wcomb-scalar-mul (n (wdim)) (l (wbasis0)) (x (wcoords0 x)))))))

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
  (or (null l)
      (equal (row-rank (wcoord-mat l))
             (len l))))

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
		  (not (equal c (flistn0 m)))
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
  (implies (and (natp m)
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
  (implies (and (natp m)
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

;; A list of length 1 is linearly dependent iff its member is v0:

(local-defthmd wdepp-w0-1
  (implies (and (wp x) (flistnp c 1) (equal (wcomb c (list x)) (w0)) (not (equal c (flistn0 1))))
           (and (fp (car c))
	        (not (equal (car c) (f0)))
	        (equal (w* (car c) x) (w0)))))

(local-defthmd wdepp-w0-2
  (implies (and (wp x) (flistnp c 1) (equal (wcomb c (list x)) (w0)) (not (equal c (flistn0 1))))
           (and (fp (car c))
	        (not (equal (car c) (f0)))
	        (equal (w0) x)))
  :hints (("Goal" :use (wdepp-w0-1 (:instance w*assoc (c (f/ (car c))) (d (car c)))))))

(local-defthmd wdepp-w0-3
  (implies (and (wp x) (wdepp (list x)))
           (equal (w0) x))
  :hints (("Goal" :use ((:instance wdepp-wcomb-w0 (m 1) (l (list x)))
                        (:instance wdepp-w0-2 (c (wdep-coeffs (list x))))))))

(defthmd wdepp-w0
  (implies (wp x)
           (iff (wdepp (list x))
                (equal (w0) x)))
  :hints (("Goal" :in-theory (enable wdepp)
                  :use (wdepp-w0-3
                        (:instance w0-not-member-windepp (m 1) (l (list x)))))))

;; If m > (wdim), then since (fmatp a m (wdim)), (row-rank a) <= (wdim) < m, i.e., (wdepp l):

(defthmd wdep-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (wdepp l))
  :hints (("Goal" :in-theory (enable wdepp windepp)
                  :use (posp-wdim (:instance row-rank<=n (a (wcoord-mat l)) (n (wdim)))))))

(defund wcoords (x l)
  (if (null l)
      ()
    (let ((c (wdep-coeffs (cons x l))))
      (flist-scalar-mul (f- (f/ (car c))) (cdr c)))))

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

(defthmd wdepp-wcomb-2
  (implies (and (wlistnp l n) (posp n) (wp x) (windepp l) (wdepp (cons x l)))
           (and (flistnp (wcoords x l) n)
	        (equal (wcomb (wcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable wcomb-scalar-mul wcoords)
                  :use (wdepp-wcomb-1 posp-wdim
		        (:instance hack-4 (c (CAR (WDEP-COEFFS (CONS X L)))) (d (WCOMB (CDR (WDEP-COEFFS (CONS X L))) L)))))))

(defthmd wdepp-wcomb
  (implies (and (wlistnp l n) (natp n) (wp x) (windepp l) (wdepp (cons x l)))
           (and (flistnp (wcoords x l) n)
	        (equal (wcomb (wcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable wcomb-scalar-mul wcoords)
                  :use (wdepp-wcomb-2 wdepp-w0))))

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

(defund wdepp-sk (l)
  (not (windepp-sk l)))

(defthmd windepp-equivalence
  (implies (and (natp m) (wlistnp l m))
           (iff (windepp-sk l)
	        (windepp l)))
  :hints (("Goal" :in-theory (enable wdepp)
                  :use (posp-wdim wdepp-wcomb-w0 windepp-sk-witness-lemma
		        (:instance windepp-sk-lemma (c (wdep-coeffs l)))
			(:instance windepp-wcomb-w0 (c (windepp-sk-witness l)))))))

(defthmd wdepp-sk-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (wdepp-sk l))
  :hints (("Goal" :in-theory (enable wdepp wdepp-sk)
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

(in-theory (disable (lin-mat)))

(defthm fmatp-lin-mat
  (fmatp (lin-mat) (vdim) (wdim))
  :hints (("Goal" :in-theory (enable lin-mat))))
 
;; Proof: Let c = (vcoords0 x). By vbasis0-spans, x = (vcomb c (vbasis0)), and by lin-vcomb,
;; (lin x) = (wcomb c (lin-list (wbasis0))).  Thus, by wcoords0-wcomb,

;;   (wcoords0 (lin x)) = (wcoords0 (wcomb c (wbasis0)))
;;                     = (car (fmat* (list c) (wcoord-mat (wbasis0))))
;; 		       = (car (fmat* (list (vcoords0 x)) (lin-mat)))  

(defthmd lin-mat-lin
  (implies (vp x)
           (equal (wcoords0 (lin x))
                  (car (fmat* (list (vcoords0 x)) (lin-mat)))))
  :hints (("goal" :in-theory (enable lin-mat)
                  :use (vbasis0-spans vlistnp-basis0 flistnp-vcoords0
                        (:instance lin-vcomb (c (vcoords0 x)) (l (vbasis0)) (n (vdim)))
                        (:instance wcoords0-wcomb (m (vdim)) (c (vcoords0 x)) (l (lin-list (vbasis0))))))))

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
                  :use (vlistnp-basis0
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
  :hints (("Goal" :use (vlistnp-basis0 lin-surjective-p-witness-lemma
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
  :hints (("Goal" :use (vlistnp-basis0 injection-dim-<=
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


;; If lin is both injective and surjective, then we can construct an inverse linear transformation from W to V.
;; Unlike the function lin-preimage, this construction is algorithmic, requiring no Skolem functions.
;; This will be important in our formalization of Galois theory, which will involve the functional instantiation
;; of the lemma lin-lin-inv below, resulting in an executable definition of the inverse operator of the Galois group.

;; First we show that if lin is injective, then (row-rank (lin-mat)) = (vdim).
;; Let m = (vdim), n = (wdim), a = (lin-mat), ar = (row-reduce a), and p = (row-reduce-mat a).
;; Let z = (funit (1- m) m) and z' = (car (fmat* (list z) p)).  Then 

;;   (car (fmat* (list z') (inverse-mat p))) = (car (fmat* (list (car (fmat* (list z) p))) (inverse-mat p)))
;;                                           = (car (fmat* (fmat* (list z) p) (inverse-mat p)))
;;                                           = (car (fmat* (list z) (fmat* p (inverse-mat p))))
;;                                           = (car (list z))
;;                                           = z

;; and since z != (flistn0 n), it follows that z' != (flistn0 n).
;; Suppose (row-rank a) < m.  Then the final row of ar is zero: (flist0p (row (1- m) ar)).  It is easily shown that

;;   (car (fmat* (list z) ar)) = (flistn0 n),

;; which implies

;;   (car (fmat* (list z') a)) = (car (fmat* (fmat* (list z) p) a)) = (car (fmat* (list z) ar)) = (flistn0 n).

(local-defund ar% () (row-reduce (lin-mat)))

(local-defund p% () (row-reduce-mat (lin-mat)))

(local-defund z% () (funit (1- (vdim)) (vdim)))

(local-defund z1% () (car (fmat* (list (z%)) (p%))))

(local (in-theory (disable (z%) (z1%) (ar%) (p%))))

(local-defthm fmatp-p%
  (fmatp (p%) (vdim) (vdim))
  :hints (("Goal" :in-theory (enable p%)
                  :use ((:instance fmatp-row-reduce-mat (a (lin-mat)) (m (vdim)) (n (wdim)))))))

(local-defthmd fmatp-ar%
  (fmatp (ar%) (vdim) (wdim))
  :hints (("Goal" :in-theory (enable ar%)
                  :use ((:instance fmatp-row-reduce (a (lin-mat)) (m (vdim)) (n (wdim)))))))

(local-defthm flistnp-z%
  (flistnp (z%) (vdim))
  :hints (("Goal" :in-theory (enable z%))))

(local-defthm fmatp-list-z%
  (fmatp (list (z%)) 1 (vdim))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthmd fmatp-z%-p%
  (fmatp (fmat* (list (z%)) (p%)) 1 (vdim))  
  :hints (("Goal" :use ((:instance fmatp-fmat* (a (list (z%))) (b (p%)) (m 1) (n (vdim)) (p (vdim)))))))

(local-defthm flistnp-z1%
  (flistnp (z1%) (vdim))
  :hints (("Goal" :in-theory (enable z1%)
                  :use (fmatp-z%-p%))))

(local-defthmd fmatp-list-car
  (implies (fmatp a 1 (vdim))
           (equal (list (car a)) a)))

(local-defthmd list-z1%
  (equal (list (z1%)) (fmat* (list (z%)) (p%)))
  :hints (("Goal" :in-theory (enable z1%))))

(in-theory (disable fmat*))

(local-defthmd fmatp-list-z1%-1
  (equal (fmat* (list (z1%)) (inverse-mat (p%)))
         (fmat* (fmat* (list (z%)) (p%)) (inverse-mat (p%))))
  :hints (("Goal" :in-theory (enable list-z1%))))

(in-theory (disable (lin-mat)))

(local-defthm invertiblep-p%
  (invertiblep (p%) (vdim))
  :hints (("Goal" :in-theory (e/d (p%) (fmatp-lin-mat))
                  :use (fmatp-lin-mat
		        (:instance invertiblep-row-reduce-mat (a (lin-mat)) (m (vdim)) (n (wdim)))))))

(local-defthmd fmatp-inverse-p%
  (and (fmatp (inverse-mat (p%)) (vdim) (vdim))
       (equal (fmat* (p%) (inverse-mat (p%)))
              (id-fmat (vdim))))
  :hints (("Goal" :use ((:instance invertiblep-sufficient (a (p%)) (n (vdim)))))))

(local-defthmd fmatp-list-z1%-2
  (equal (fmat* (list (z1%)) (inverse-mat (p%)))
         (fmat* (list (z%)) (id-fmat (vdim))))
  :hints (("Goal" :use (fmatp-list-z1%-1 fmatp-inverse-p%
                        (:instance fmat*-assoc (a (list (z%))) (b (p%)) (c (inverse-mat (p%))) (m 1) (n (vdim)) (p (vdim)) (q (vdim)))))))

(local-defthmd fmatp-list-z1%
  (equal (fmat* (list (z1%)) (inverse-mat (p%)))
         (list (z%)))
  :hints (("Goal" :use (fmatp-list-z1%-2
                        (:instance id-fmat-right (a (list (z%))) (m 1) (n (vdim)))))))

(local-defthmd z1*-nonzero-1
  (equal (entry 0 (1- (vdim)) (fmat* (list (flistn0 (vdim))) (inverse-mat (p%))))
         (fdot (flistn0 (vdim)) (col (1- (vdim)) (inverse-mat (p%)))))
  :hints (("Goal" :use (fmatp-inverse-p%
                        (:instance fmat*-entry (a (list (flistn0 (vdim)))) (b (inverse-mat (p%))) (m 1) (n (vdim)) (p (vdim)) (i 0) (j (1- (vdim))))))))

(local-defthmd z1*-nonzero-2
  (flistnp (col (1- (vdim)) (inverse-mat (p%))) (vdim))
  :hints (("Goal" :use (fmatp-inverse-p%
                        (:instance flistnp-col (a (inverse-mat (p%))) (m (vdim)) (n (vdim)) (j (1- (vdim))))))))

(local-defthmd z1*-nonzero-3
  (equal (entry 0 (1- (vdim)) (fmat* (list (flistn0 (vdim))) (inverse-mat (p%))))
         (f0))
  :hints (("Goal" :use (z1*-nonzero-1 z1*-nonzero-2))))

(local-defthmd z1*-nonzero-4
  (equal (entry 0 (1- (vdim)) (list (z%)))
         (f1))
  :hints (("Goal" :in-theory (enable z%)
                  :use ((:instance nth-funit (i (1- (vdim))) (j (1- (vdim))) (n (vdim)))))))

(local-defthmd z1*-nonzero
  (not (equal (z1%) (flistn0 (vdim))))
  :hints (("Goal" :use (fmatp-list-z1% z1*-nonzero-3 z1*-nonzero-4 f1f0))))

(local-defthmd flist0p-last-row
  (implies (< (row-rank (lin-mat)) (vdim))
           (flist0p (nth (1- (vdim)) (ar%))))
  :hints (("Goal" :in-theory (enable fmatp-row-reduce row-rank ar%)
                  :use ((:instance num-nonzero-rows-nonzero (a (ar%)) (m (vdim)) (n (wdim)) (i (1- (vdim))))
		        (:instance row-echelon-p-row-reduce (a (lin-mat)) (m (vdim)) (n (wdim)))))))

(local-defthmd nth-col-ar%
  (implies (and (< (row-rank (lin-mat)) (vdim))
                (natp j) (< j (wdim)))
	   (equal (nth (1- (vdim)) (col j (ar%)))
	          (f0)))
  :hints (("Goal" :use (flist0p-last-row fmatp-ar%
                        (:instance nth-col (a (ar%)) (i (1- (vdim))))
			(:instance nth-flist0p (x (nth (1- (vdim)) (ar%))) (i j))))))

(local-defthmd entry-fmat*-z%-ar%
  (implies (and (< (row-rank (lin-mat)) (vdim))
                (natp j) (< j (wdim)))
	   (equal (entry 0 j (fmat* (list (z%)) (ar%)))
	          (f0)))
  :hints (("Goal" :in-theory (enable z%)
                  :use (fmatp-ar% nth-col-ar%
                        (:instance fmat*-entry (a (list (z%))) (b (ar%)) (m 1) (n (vdim)) (p (wdim)) (i 0))
			(:instance nth-flist0p (x (nth (1- (vdim)) (ar%))) (i j))))))

(local-defthmd fmat*-z%-ar%
  (implies (< (row-rank (lin-mat)) (vdim))
	   (equal (fmat* (list (z%)) (ar%))
	          (list (flistn0 (wdim)))))
  :hints (("Goal" :use (fmatp-ar%
                        (:instance fmatp-fmat* (a (list (z%))) (b (ar%)) (m 1) (n (vdim)) (p (wdim)))
                        (:instance fmat-entry-diff-lemma (a (list (flistn0 (wdim)))) (b (fmat* (list (z%)) (ar%))) (m 1) (n (wdim)))
			(:instance entry-fmat*-z%-ar% (j (cdr (entry-diff (list (flistn0 (wdim))) (fmat* (list (z%)) (ar%))))))))))

(local-defthmd fmat*-z1%-a-1
  (equal (fmat* (list (z1%)) (lin-mat))
         (fmat* (fmat* (list (z%)) (p%)) (lin-mat)))
  :hints (("Goal" :in-theory (enable z1%)
                  :use ((:instance fmatp-list-car (a (fmat* (list (z%)) (p%))))
		        (:instance fmatp-fmat* (a (list (z%))) (b (p%)) (m 1) (n (vdim)) (p (vdim)))))))

(local-defthmd fmat*-z1%-a-2
  (equal (fmat* (list (z1%)) (lin-mat))
         (fmat* (list (z%)) (fmat* (p%) (lin-mat))))
  :hints (("Goal" :use (fmat*-z1%-a-1
                        (:instance fmat*-assoc (a (list (z%))) (b (p%)) (c (lin-mat)) (m 1) (n (vdim)) (p (vdim)) (q (wdim)))))))

(local-defthmd fmat*-p%-lin-mat
  (equal (fmat* (p%) (lin-mat))
         (ar%))
  :hints (("Goal" :in-theory (enable ar% p%)
                  :use ((:instance row-ops-mat-row-reduce (a (lin-mat)) (m (vdim)) (n (wdim)))))))

(local-defthmd fmat*-z1%-a-3
  (equal (fmat* (list (z1%)) (lin-mat))
         (fmat* (list (z%)) (ar%)))
  :hints (("Goal" :use (fmat*-z1%-a-2 fmat*-p%-lin-mat))))

(local-defthmd fmat*-z1%-a
  (implies (< (row-rank (lin-mat)) (vdim))
           (equal (car (fmat* (list (z1%)) (lin-mat)))
                  (flistn0 (wdim))))
  :hints (("Goal" :use (fmat*-z1%-a-3 fmat*-z%-ar%))))

;; Let x = (vcomb z' (vbasis0)).  Then (vp x) and x != (v0).  By vcoords0-unique, (vcoords0 x) = z'.  By lin-mat-lin,

;;   (wcoords0 (lin x)) = (car (fmat* (list z') a)) = (flistn0 n)

;; and hence, (lin x) = (w0), contradicting injectivity:

(local-defund x% () (vcomb (z1%) (vbasis0)))

(local (in-theory (disable (x%))))

(local-defthm vp-x%
  (vp (x%))
  :hints (("Goal" :in-theory (enable x%))))

(local-defthmd x%-nonzero
  (not (equal (x%) (v0)))
  :hints (("Goal" :in-theory (enable x%)
                  :use (z1*-nonzero
		        (:instance vbasis0-lin-indep (c (z1%)))))))

(local-defthm vcoords0-x%
  (equal (vcoords0 (x%))
         (z1%))
  :hints (("Goal" :in-theory (enable x%)
                  :use (vp-x% (:instance vcoords0-unique (x (x%)) (c (z1%)))))))

(local-defthmd wcoords0-lin-x%
  (implies (< (row-rank (lin-mat)) (vdim))
           (equal (wcoords0 (lin (x%)))
	          (flistn0 (wdim))))
  :hints (("Goal" :use (fmat*-z1%-a (:instance lin-mat-lin (x (x%)))))))

(local-defthmd lin-x%-w0
  (implies (< (row-rank (lin-mat)) (vdim))
           (equal (lin (x%))
	          (w0)))
  :hints (("Goal" :use (wcoords0-lin-x% (:instance wbasis0-spans (x (lin (x%))))))))

(defthmd row-rank-lin-mat
  (implies (lin-injective-p)
           (equal (row-rank (lin-mat))
                  (vdim)))
  :hints (("Goal" :use (lin-x%-w0 x%-nonzero
                        (:instance lin-injective-p-lemma (x (x%)))
			(:instance row-rank<=m (a (lin-mat)) (m (vdim)) (n (wdim)))))))

;; Now suppose lin is both injective and surjective.  Then m = n and a is invertible.  We define

(defund lin-inv (y)
  (vcomb (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))
         (vbasis0)))

;; It is easily verified that lin-inv satisfies the properties of a linear transformation:

(local-defthm lli-1
  (implies (and (lin-injective-p) (= (vdim) (wdim)))
           (invertiblep (lin-mat) (wdim)))
  :hints (("Goal" :in-theory (enable invertiblep)
                  :use (row-rank-lin-mat))))

(local-defthm lli-2
  (implies (and (lin-injective-p) (= (vdim) (wdim)))
           (let ((m (inverse-mat (lin-mat))))
	     (and (fmatp m (wdim) (wdim))
	          (equal (fmat* m (lin-mat)) (id-fmat (wdim))))))
  :hints (("Goal" :in-theory (disable fmatp-lin-mat)
                  :use (lli-1 fmatp-lin-mat
                        (:instance invertiblep-sufficient (a (lin-mat)) (n (wdim)))))))

(local-defthmd lin-inv-w+-1
  (implies (and (posp n) (fmatp b n n) (flistnp x n) (flistnp y n))
           (equal (car (fmat* (list (flist-add x y)) b))
	          (flist-add (car (fmat* (list x) b)) (car (fmat* (list y) b)))))
  :hints (("Goal":in-theory (enable fmat*)
                 :use ((:instance fmat*-dist-1 (m 1) (p n) (a1 (list x)) (a2 (list y)))))))

(local-defthmd lin-inv-w+-2
  (implies (and (fmatp b n n) (posp n) (flistnp x n))
           (flistnp (car (fmat* (list x) b)) n))
  :hints (("Goal":use ((:instance fmatp-fmat* (a (list x)) (m 1) (p n))))))

(defthmd lin-inv-w+
  (implies (and (lin-injective-p) (= (vdim) (wdim))
                (wp x) (wp y))
           (equal (lin-inv (w+ x y))
	          (v+ (lin-inv x) (lin-inv y))))
  :hints (("Goal":in-theory (enable lin-inv)
                 :use (wcoords0-w+ lli-2
		       (:instance vcomb-add (n (vdim)) (l (vbasis0))
		                            (x (car (fmat* (list (wcoords0 x)) (inverse-mat (lin-mat)))))
		                            (y (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))))
		       (:instance lin-inv-w+-2 (n (vdim)) (x (wcoords0 x)) (b (inverse-mat (lin-mat))))
		       (:instance lin-inv-w+-2 (n (vdim)) (x (wcoords0 y)) (b (inverse-mat (lin-mat))))
                       (:instance lin-inv-w+-1 (x (wcoords0 x)) (y (wcoords0 y)) (n (vdim)) (b (inverse-mat (lin-mat))))))))

(local-defthmd lin-inv-w*-1
  (implies (and (posp n) (fmatp b n n) (flistnp x n) (fp c))
           (equal (car (fmat* (list (flist-scalar-mul c x)) b))
	          (flist-scalar-mul c (car (fmat* (list x) b)))))
  :hints (("Goal":in-theory (enable fmat*)
                 :use ((:instance fmat*-fmat-scalar-mul-1 (m 1) (p n) (a (list x)))))))

(defthmd lin-inv-w*
  (implies (and (lin-injective-p) (= (vdim) (wdim))
                (wp x) (fp c))
           (equal (lin-inv (w* c x))
	          (v* c (lin-inv x))))
  :hints (("Goal":in-theory (enable lin-inv)
                 :use (wcoords0-w* lli-2
		       (:instance vcomb-scalar-mul (n (vdim)) (l (vbasis0))
		                                   (x (car (fmat* (list (wcoords0 x)) (inverse-mat (lin-mat))))))
		       (:instance lin-inv-w+-2 (n (vdim)) (x (wcoords0 x)) (b (inverse-mat (lin-mat))))
                       (:instance lin-inv-w*-1 (x (wcoords0 x)) (n (vdim)) (b (inverse-mat (lin-mat))))))))

(local-defthmd fdot-list-flistn0
  (implies (and (fmatp a m n) (natp m) (natp n))
           (equal (fdot-list (flistn0 n) a)
	          (flistn0 m))))

(local-defthmd fmat*-flistn0
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (car (fmat* (list (flistn0 m)) a))
	          (flistn0 n)))
  :hints (("Goal" :expand ((FMAT* (list(FLISTN0 M)) A))
                  :use (fmatp-transpose
                        (:instance fdot-list-flistn0 (a (transpose-mat a)) (m n) (n m))))))

(defthmd lin-inv-w0
  (implies (and (lin-injective-p) (= (vdim) (wdim)))
           (equal (lin-inv (w0)) (v0)))
  :hints (("Goal" :in-theory (enable lin-inv)
                  :use (wcoords0-w0 lli-2
	                (:instance fmat*-flistn0 (m (vdim)) (n (vdim)) (a (inverse-mat (lin-mat))))
	                (:instance vcomb-flistn0 (l (vbasis0)) (n (vdim)))))))

;; Suppose (wp y) and let x = (lin-inv y).  Then (vp x).  We shall show that (lin x) = y.  By vcoords0-unique,

;;   (vcoords0 x) = (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))).

;; By lin-mat-lin,

;;   (wcoords0 (lin x)) = (car (fmat* (list (vcoords0 x)) (lin-mat)))
;;                      = (car (fmat* (list (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))) (lin-mat)))
;;                      = (car (fmat* (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))) (lin-mat)))
;;                      = (car (fmat* (list (wcoords0 y)) (fmat* (inverse-mat (lin-mat)) (lin-mat))))
;;                      = (car (list (wcoords0 y))
;;                      = (wcoords0 y)

;; which implies (lin x) = y.

(local-defthmd lli-3
  (implies (wp y)
           (fmatp (list (wcoords0 y)) 1 (wdim))))

(local-defthm lli-4
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (fmatp (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))) 1 (wdim)))
  :hints (("Goal" :use (lli-2 lli-3
                        (:instance fmatp-fmat* (a (list (wcoords0 y))) (b (inverse-mat (lin-mat))) (m 1) (n (wdim)) (p (wdim)))))))

(local-defthm lli-5
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (flistnp (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat)))) (wdim)))
  :hints (("Goal" :use (lli-4))))

(local-defthm lli-6
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
	          (equal (vcoords0 x)
	                 (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))))))
  :hints (("Goal" :in-theory (enable lin-inv)
                  :use (lli-5
		        (:instance vcoords0-unique (x (lin-inv y)) (c (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))))))))

(defthm vp-lin-inv
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (vp (lin-inv y)))
  :hints (("Goal" :use lli-6)))

(local-defthm lli-7
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
	          (equal (wcoords0 (lin x))
	                 (car (fmat* (list (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))) (lin-mat)))))))
  :hints (("Goal" :use (lli-6
		        (:instance lin-mat-lin (x (lin-inv y)))))))

(local-defthm lli-8
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
	          (equal (wcoords0 (lin x))
	                 (car (fmat* (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))) (lin-mat)))))))
  :hints (("Goal" :use (lli-7 lli-4
		        (:instance fmatp-list-car (a (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat)))))))))

(local-defthm lli-9
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
	          (equal (wcoords0 (lin x))
	                 (car (fmat* (list (wcoords0 y)) (id-fmat (wdim))))))))
  :hints (("Goal" :in-theory (disable fmatp-lin-mat)
                  :use (lli-8 lli-2 lli-3 fmatp-lin-mat
		        (:instance fmat*-assoc (a (list (wcoords0 y))) (b (inverse-mat (lin-mat))) (c (lin-mat)) (m 1) (n (wdim)) (p (wdim)) (q (wdim)))))))

(local-defthm lli-10
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
	          (equal (wcoords0 (lin x))
	                 (wcoords0 y)))))
  :hints (("Goal" :use (lli-9 lli-3
		        (:instance id-fmat-right (a (list (wcoords0 y))) (m 1) (n (wdim)))))))

(defthmd lin-lin-inv
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y))))
  :hints (("Goal" :use (lli-10 injection-surjection-dim-=
                        (:instance wbasis0-spans (x y))
			(:instance wbasis0-spans (x (lin (lin-inv y))))))))


;;---------------------------------------------------------------------------------------------------------------------
;;  Subspaces
;;---------------------------------------------------------------------------------------------------------------------

;; Informally, a subspace of V is a subset of V that forms a vector space under the operations of V. In our
;; formalization, in order to specify a subspace, we must define a recognizer that refines the predicate vp and prove
;; that it is satisfied by v0 and that the closure properties hold.  

;; We constrain a predicate sp that recognizes a subspace of V.  Informally, we shall refer to this subspace as S:

(encapsulate (((sp *) => *))
  (local (defun sp (x) (vp x)))
  ;; Subset:
  (defthm sp-vp (implies (sp x) (vp x)))
  ;; Zero vector:
  (defthm sp-v0 (sp (v0)))
  ;; Closure:
  (defthm sp-v- (implies (sp x) (sp (v- x))))    
  (defthm s+closed (implies (and (sp x) (sp y)) (sp (v+ x y))))  
  (defthm s*closed (implies (and (fp c) (sp x)) (sp (v* c x)))))

;; We define a basis of S and verify the corresponding axioms:

(defun slistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (sp (car x))
         (slistnp (cdr x) (1- n)))))

(defthm slistnp-vlistnp
  (implies (slistnp x n)
           (vlistnp x n)))

(defchoose sunspanned x (l)
  (and (sp x) (vindepp (cons x l))))

(defun sbasis0-aux (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))
                  :hints (("Goal" :in-theory (enable vdepp)
		                  :use ((:instance vdepp-if->-dim
				         (m (1+ (len l)))
				         (l (cons (sunspanned l) l))))))))
  (let ((x (sunspanned l)))
    (if (and (slistnp l (len l)) (sp x) (vindepp (cons x l)))
        (sbasis0-aux (cons x l))
      l)))

(defund sbasis0 ()
  (sbasis0-aux ()))

(defun sdim () (len (sbasis0)))

(in-theory (disable (slistnp) (sbasis0-aux) (sbasis0) (sdim)))

;; It follows from the definitions that sbasis0 is a linearly independent slist:

(local-defthmd slistnp-sbasis0-aux
  (implies (slistnp l (len l))
           (let ((b (sbasis0-aux l)))
	     (slistnp b (len b)))))

(defthmd slistnp-sbasis0
  (slistnp (sbasis0) (sdim))
  :hints (("Goal" :in-theory (enable sbasis0)
                  :use ((:instance slistnp-sbasis0-aux (l ()))))))

(local-defthmd vindepp-sbasis0-aux
  (implies (and (slistnp l (len l)) (vindepp l))
           (let ((b (sbasis0-aux l)))
             (and (slistnp b (len b))
	          (vindepp b)))))

(defthm vindepp-sbasis0
  (and (slistnp (sbasis0) (sdim))
       (vindepp (sbasis0)))
  :hints (("Goal" :in-theory (enable sbasis0)
                  :use ((:instance vindepp-sbasis0-aux (l ()))))))

;; By vdepp-if->-dim, sdim <= vdim:

(defthmd sdim-bound
  (<= (sdim) (vdim))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vindepp-sbasis0
		        (:instance vdepp-if->-dim (l (sbasis0)) (m (sdim)))))))

;; sbasis0 is a maximal linearly independent list:

(local-defthmd vdepp-cons-sbasis0-aux-1
  (implies (and (slistnp l (len l)) (vindepp l))
           (let ((x (sunspanned (sbasis0-aux l))))
	     (not (and (sp x) (vindepp (cons x (sbasis0-aux l))))))))

(local-defthmd vdepp-cons-sbasis0-aux
  (implies (and (slistnp l (len l)) (vindepp l) (sp x))
           (vdepp (cons x (sbasis0-aux l))))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vdepp-cons-sbasis0-aux-1
		        (:instance sunspanned (l (sbasis0-aux l)))))))

(defthmd vdepp-cons-sbasis0
  (implies (sp x)
           (vdepp (cons x (sbasis0))))
  :hints (("Goal" :in-theory (enable sbasis0 vdepp)
                  :use (:instance vdepp-cons-sbasis0-aux (l ())))))

;; S contains a nonzero vector iff sdim > 0:

(local-defthm true-listp-sbasis0-aux
  (implies (true-listp l)
           (true-listp (sbasis0-aux l))))

(local-defthmd true-listp-sbasis0
  (true-listp (sbasis0))
  :hints (("Goal" :in-theory (enable sbasis0))))

(local-defthmd hack-5
  (implies (and (true-listp l) l)
           (> (len l) 0)))

(defthmd sdim-0-nil
  (iff (null (sbasis0))
       (equal (sdim) 0))           
  :hints (("Goal" :use (true-listp-sbasis0
                        (:instance hack-5 (l (sbasis0)))))))

(local-defthmd consp-sbasis0-1
  (implies (consp l)
           (consp (sbasis0-aux l))))

(local-defthmd consp-sbasis0-2
  (iff (consp (sbasis0))
       (let ((x (sunspanned ())))
         (and (sp x) (vindepp (list x)))))
  :hints (("Goal" :in-theory (enable sbasis0)
                  :use ((:instance consp-sbasis0-1 (l (list (sunspanned ()))))))))

(defthmd posp-sdim-not-v0
  (implies (posp (sdim))
           (let ((x (sunspanned ())))
             (and (sp x) (not (equal x (v0))))))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (consp-sbasis0-2 (:instance vdepp-v0 (x (sunspanned ())))))))

(defthmd not-v0-posp-sdim
  (implies (and (sp x) (not (equal x (v0))))
           (posp (sdim)))
  :hints (("Goal" :use (vdepp-v0 sdim-0-nil consp-sbasis0-2
                        (:instance sunspanned (l ()))))))

(in-theory (disable sdim))

;; It follows from vdepp-vcomb that sbasis0 spans the subspace:

(defund scoords0 (x)
  (vcoords x (sbasis0)))

(defthm flistnp-scoords0
  (implies (sp x)
           (flistnp (scoords0 x) (sdim)))
  :hints (("Goal" :in-theory (enable sdim scoords0)
                  :use (vdepp-cons-sbasis0 vindepp-sbasis0
		        (:instance vdepp-vcomb (l (sbasis0)) (n (sdim)))))))

(defthm sbasis0-spans
  (implies (sp x)
           (equal (vcomb (scoords0 x) (sbasis0))
                  x))
  :hints (("Goal" :in-theory (enable sdim scoords0)
                  :use (vdepp-cons-sbasis0 vindepp-sbasis0 not-v0-posp-sdim
		        (:instance vdepp-vcomb (l (sbasis0)) (n (sdim)))))))

;; Apply vindepp-vcomb-v0:

(defthmd sbasis0-lin-indep
  (implies (and (flistnp c (sdim))
                (equal (vcomb c (sbasis0)) (v0)))
           (equal (flistn0 (sdim)) c))
  :hints (("Goal" :use ((:instance vindepp-vcomb-v0 (l (sbasis0)) (m (sdim)))))))

;; Note that we have verified analogs of all of the axioms of V with the exception of sdim > 0.  Thus, any proven
;; result for V may be instantiated for S under this assumption.

;; For example, we shall prove an analog of vdepp-if->-dim: every list of vectors of S of length exceeding sdim is
;; linearly dependent.  To prove this directly by functional instantiation of vdepp-if->-dim would be difficult because
;; of the complicated definition of vindepp.  Instead, we functionally instantiate not-vindepp-sk-if->-dim:

(defthmd vdepp-sk-if->-sdim
  (implies (and (> (sdim) 0) (natp m) (> m (sdim))
		(slistnp l m))
	   (vdepp-sk l))
  :hints (("Goal" :use ((:functional-instance vdepp-sk-if->-dim
                         (vp (lambda (x) (if (> (sdim) 0) (sp x) (vp x))))
			 (vbasis0 (lambda () (if (> (sdim) 0) (sbasis0) (vbasis0))))
			 (vcoords0 (lambda (x) (if (> (sdim) 0) (scoords0 x) (vcoords0 x))))
			 (vdim (lambda () (if (> (sdim) 0) (sdim) (vdim))))
			 (vlistnp (lambda (x n) (if (> (sdim) 0) (slistnp x n) (vlistnp x n)))))))
	  ("Subgoal 16" :use (sbasis0-lin-indep vbasis0-lin-indep))
	  ("Subgoal 12" :use (vdistv))
	  ("Subgoal 11" :use (vdistf))
	  ("Subgoal 10" :use (v*assoc))
	  ("Subgoal 5" :use (v+assoc))
	  ("Subgoal 4" :use (v+comm))
	  ("Subgoal 1" :use (vdim))))

;; Combine this with vindepp-equivalence:

(defthmd vdepp-if->-sdim
  (implies (and (> (sdim) 0) (natp m) (> m (sdim))
		(slistnp l m))
	   (vdepp l))
  :hints (("Goal" :use (vdepp-sk-if->-sdim vindepp-equivalence))))

;; The dimension of a subspace is well-defined.  That is, suppose sbasis1 is another linearly independent spanning
;; set:

(encapsulate (((sbasis1) => *) ((scoords1 *) => *))
  (local (defun sbasis1 () (sbasis0)))
  (local (defun scoords1 (x) (scoords0 x)))
  (defun sdim1 () (len (sbasis1)))
  (defthmd slistnp-sbasis1
    (slistnp (sbasis1) (sdim1))
    :hints (("Goal" :in-theory (enable sdim) :use (slistnp-sbasis0))))
  (defthmd flistnp-scoords1
    (implies (and (posp (sdim)) (sp x)) (flistnp (scoords1 x) (sdim1)))
    :hints (("Goal" :use (flistnp-scoords0))))
  (defthmd sbasis1-spans
    (implies (and (posp (sdim)) (sp x))
             (equal (vcomb (scoords1 x) (sbasis1))
                    x))
    :hints (("Goal" :use (sbasis0-spans))))
  (defthm vindepp-sbasis1
    (vindepp (sbasis1))
    :hints (("Goal" :use (vindepp-sbasis0)))))

;; We shall show that sdim1 = sdim.

;; First, it is easily shown that sdim1 = 0 iff sdim - 0:

(local-defthmd sdim1-0-1
  (implies (and (= (sdim) 0) (> (sdim1) 0))
           (equal (car (sbasis1)) (v0)))
  :hints (("Goal" :use (slistnp-sbasis1
                        (:instance not-v0-posp-sdim (x (car (sbasis1))))))))

(local-defthmd sdim1-0-2
  (implies (and (= (sdim) 0) (> (sdim1) 0))
           (let ((c (cons (f1) (flistn0 (1- (sdim1))))))
	     (and (flistnp c (sdim1))
	          (not (equal (flistn0 (sdim1)) c))
		  (equal (vcomb c (sbasis1)) (v0)))))		  
  :hints (("Goal" :use (slistnp-sbasis1 sdim1-0-1
                        (:instance not-v0-posp-sdim (x (car (sbasis1))))))))

(local-defthmd sdim1-0-3
  (implies (= (sdim) 0) (= (sdim1) 0))
  :hints (("Goal" :use (sdim1-0-2 slistnp-sbasis1
                        (:instance vindepp-vcomb-v0 (l (sbasis1)) (m (sdim1)) (c (cons (f1) (flistn0 (1- (sdim1))))))))))

(defthmd sdim-sdim1-0
  (iff (= (sdim) 0) (= (sdim1) 0))
  :hints (("Goal" :use (sdim1-0-3 posp-sdim-not-v0
                        (:instance sbasis1-spans (x (sunspanned ())))
			(:instance flistnp-scoords1 (x (sunspanned ())))))))

;; We shal prove the analog of vdepp-if->-dim for sdim1 in the same way that we proved vdepp-if->-sdim.
;; First we derive the following from vindepp-sbasis1 and vindepp-vcomb-v0:

(defthmd sbasis1-lin-indep
  (implies (and (flistnp c (sdim1))
                (equal (vcomb c (sbasis1)) (v0)))
           (equal (flistn0 (sdim1)) c))
  :hints (("Goal" :use (slistnp-sbasis1
                        (:instance vindepp-vcomb-v0 (l (sbasis1)) (m (sdim1)))))))

;; Now functionally instantiate not-vindepp-sk-if->-dim:

(defthmd vdepp-sk-if->-sdim1
  (implies (and (> (sdim1) 0) (natp m) (> m (sdim1))
		(slistnp l m))
	   (vdepp-sk l))
  :hints (("Goal" :use ((:functional-instance vdepp-sk-if->-dim
                         (vp (lambda (x) (if (> (sdim1) 0) (sp x) (vp x))))
			 (vbasis0 (lambda () (if (> (sdim1) 0) (sbasis1) (vbasis0))))
			 (vcoords0 (lambda (x) (if (> (sdim1) 0) (scoords1 x) (vcoords0 x))))
			 (vdim (lambda () (if (> (sdim1) 0) (sdim1) (vdim))))
			 (vlistnp (lambda (x n) (if (> (sdim1) 0) (slistnp x n) (vlistnp x n)))))))
	  ("Subgoal 16" :use (sbasis1-lin-indep vbasis0-lin-indep))
	  ("Subgoal 15" :use (sdim-sdim1-0 sbasis1-spans))
	  ("Subgoal 14" :use (sdim-sdim1-0 flistnp-scoords1))
	  ("Subgoal 13" :use (sdim-sdim1-0 slistnp-sbasis1))
	  ("Subgoal 12" :use (vdistv))
	  ("Subgoal 11" :use (vdistf))
	  ("Subgoal 10" :use (v*assoc))
	  ("Subgoal 5" :use (v+assoc))
	  ("Subgoal 4" :use (v+comm))
	  ("Subgoal 1" :use (vdim))))

;; Invoke vindepp-equivalence:

(defthmd vdepp-if->-sdim1
  (implies (and (> (sdim1) 0) (natp m) (> m (sdim1))
		(slistnp l m))
	   (vdepp l))
  :hints (("Goal" :use (vdepp-sk-if->-sdim1 vindepp-equivalence))))

;; Combine vdepp-if->-sdim, vdepp-if->-sdim1, vindepp-sbasis0, and vindepp-sbasis1:

(defthmd sdim-well-defined
  (= (sdim1) (sdim))
  :hints (("Goal" :use (sdim-sdim1-0 slistnp-sbasis1
                        (:instance vdepp-if->-sdim (l (sbasis1)) (m (sdim1)))
                        (:instance vdepp-if->-sdim1 (l (sbasis0)) (m (sdim)))))))

;; Thus, sdim1 <= vdim:

(defthmd sdim1<=vdim
  (<= (sdim1) (vdim))
  :hints (("Goal" :use (sdim-well-defined sdim-bound))))
  

;;---------------------------------------------------------------------------------------------------------------------
;;  Kernel and Image of a Linear Transformation
;;---------------------------------------------------------------------------------------------------------------------

;; The kernel of a linear transformation is the subspace of vectors that are mapped to 0:

(defund in-kernel-p (x)
  (and (vp x)
       (equal (lin x) (w0))))

;; The subspace axioms are easily verified:

(defthm in-kernel-p-vp
  (implies (in-kernel-p x) (vp x))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(defthmd in-kernel-p-v0
  (in-kernel-p (v0))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(defthm in-kernel-p-v+
  (implies (and (in-kernel-p x) (in-kernel-p y))
           (in-kernel-p (v+ x y)))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(defthm in-kernel-p-v*
  (implies (and (fp c) (in-kernel-p x))
           (in-kernel-p (v* c x)))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(defthm in-kernel-p-v-
  (implies (in-kernel-p x) 
           (in-kernel-p (v- x)))
  :hints (("Goal" :in-theory (enable in-kernel-p)  
                  :use (v*f-f1 (:instance in-kernel-p-v* (c (f- (f1))))))))

;; List of kernel elements:

(defun klistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-kernel-p (car x))
         (klistnp (cdr x) (1- n)))))

(defthm klistnp-vlistnp
  (implies (klistnp x n)
           (vlistnp x n)))

(defthm in-kernel-p-vcomb
  (implies (and (klistnp x n) (flistnp c n))
           (in-kernel-p (vcomb c x))))

;; We shall construct a basis for the kernel, kbasis, based on a characterization of the kernel as the solution space
;; of a homogeneous system of linear equations. 

;; Let (vp x).  By lin-mat-lin, (in-kernel-p x) iff the following equation holds:

;;   (fmat* (row-mat (vcoords0 x)) (lin-mat)) = (row-mat (flistn0 (wdim))).

;; Let a = (transpose-mat (lin-mat)).  Taking the transpose of both sides of the above equation yields

;;   (fmat* a (col-mat (vcoords0 x))) = (col-mat (flistn0 (wdim))).

;; Thus, x is in the kernel iff (vcoords0 x) is a solution of the homogeneous system of linear equations with coordinate 
;; matrix a.  See the discussion of the function sol0p at the end of the book "reduction".

(local-defthmd in-kernel-p-sol0p-1
  (implies (vp x)
           (fmatp (fmat* (row-mat (vcoords0 x)) (lin-mat)) 1 (wdim)))
  :hints (("Goal" :use ((:instance fmatp-fmat* (a (row-mat (vcoords0 x))) (b (lin-mat)) (m 1) (n (vdim)) (p (wdim)))
                        (:instance fmatp-row-mat (x (vcoords0 x)) (n (vdim)))))))

(local-defthmd in-kernel-p-sol0p-2
  (implies (fmatp a 1 n)
           (equal (list (car a)) a)))

                  
(local-defthmd in-kernel-p-sol0p-3
  (implies (vp x)
           (iff (in-kernel-p x)
	        (equal (fmat* (row-mat (vcoords0 x)) (lin-mat))
		       (row-mat (flistn0 (wdim))))))
  :hints (("Goal" :in-theory (e/d (fmatp row-mat lin-mat-lin in-kernel-p) (wbasis0-spans))
                  :use (in-kernel-p-sol0p-1
		        (:instance in-kernel-p-sol0p-2 (a (fmat* (row-mat (vcoords0 x)) (lin-mat))) (n (wdim)))
		        (:instance wcoords0-unique (x (lin x)) (c (flistn0 (wdim))))
		        (:instance wbasis0-spans (x (lin x)))))))

(local-defthmd in-kernel-p-sol0p-4
  (implies (and (fmatp a 1 n) (fmatp b 1 n) (posp n))
           (iff (equal (transpose-mat a) (transpose-mat b))
	        (equal a b)))
  :hints (("Goal" :use ((:instance transpose-fmat-2 (m 1))
                        (:instance transpose-fmat-2 (m 1) (a b))))))

(local-defthmd in-kernel-p-sol0p-5
  (implies (vp x)
           (equal (transpose-mat (fmat* (row-mat (vcoords0 x)) (lin-mat)))
	          (fmat* (transpose-mat (lin-mat)) (col-mat (vcoords0 x)))))
  :hints (("Goal" :in-theory (enable col-mat row-mat)
                  :use (fmatp-lin-mat
		        (:instance fmatp-row-mat (x (vcoords0 x)) (n (vdim)))
                        (:instance transpose-fmat* (a (row-mat (vcoords0 x))) (b (lin-mat)) (m 1) (n (vdim)) (p (wdim)))))))

(local-defthmd in-kernel-p-sol0p-6
  (implies (vp x)
           (iff (in-kernel-p x)
	        (equal (fmat* (transpose-mat (lin-mat)) (col-mat (vcoords0 x)))
		       (col-mat (flistn0 (wdim))))))
  :hints (("Goal" :in-theory (enable col-mat)
                  :use (in-kernel-p-sol0p-5 in-kernel-p-sol0p-1 in-kernel-p-sol0p-3
		        (:instance in-kernel-p-sol0p-4 (a (fmat* (row-mat (vcoords0 x)) (lin-mat))) (b (row-mat (flistn0 (wdim)))) (n (wdim)))))))

(defthmd fmatp-transpose-mat-lin-mat
  (fmatp (transpose-mat (lin-mat)) (wdim) (vdim))
  :hints (("Goal" :use (fmatp-lin-mat (:instance fmatp-transpose (a (lin-mat)) (m (vdim)) (n (wdim)))))))

(local-defthmd in-kernel-p-sol0p-7
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (len (car a)) n)))

(defthmd in-kernel-p-sol0p
  (implies (vp x)
           (iff (in-kernel-p x)
                (sol0p (vcoords0 x) (transpose-mat (lin-mat)))))
  :hints (("Goal" :in-theory (enable sol0p solutionp)
                  :use (fmatp-transpose-mat-lin-mat in-kernel-p-sol0p-6
		        (:instance in-kernel-p-sol0p-7 (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
		        (:instance len-fmatp (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))))))

;; Let ar = (row-reduce a), q = (num-nonzero-rows ar) = (row-rank a), l = (lead-inds ar) and f = (free-inds ar n).
;; Then (len l) = q and (len f) = vdim - q.  The basis kbasis will be a list of length (len f), each member of which
;; corresponds to a member of f.

;; Given j in f, we first define the coordinate list c with respect to vbasis0 of the kbasis element corresponding to j.
;; For 0 <= i < vdim, (nth i c) = (kbasis-coord i j), which is defined as follows:

;; (a) If i is in l, let k = (index i l), i.e., i = (nth k l).  Then (nth i c)) = (f- (entry k j ar)).
;; (b) If i = j, then (nth i c) = (f1).
;; (c) If i is in f and i !+ j, then (nth i c) = (f0).

(defund kbasis-coord (i j)
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
	 (l (lead-inds ar)))
    (if (member i l)
        (f- (entry (index i l) j ar))
      (if (= i j)
          (f1)
        (f0)))))

(local-defthmd fp-kbasis-coord-1
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
	 (l (lead-inds ar)))
    (implies (member i l)
             (and (natp (index i l))
                  (< (index i l) (wdim)))))
  :hints (("Goal" :in-theory (disable ind<len)
                  :use (fmatp-transpose-mat-lin-mat
                        (:instance fmatp-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
			(:instance len-lead-inds-bound (a (row-reduce (transpose-mat (lin-mat)))) (m (wdim)) (n (vdim)))			
			(:instance ind<len (x i) (l (lead-inds (row-reduce (transpose-mat (lin-mat))))))))))

(defthmd fp-kbasis-coord
  (implies (and (natp j) (< j (vdim)))
           (fp (kbasis-coord i j)))
  :hints (("Goal" :in-theory (enable kbasis-coord)
                  :use (fp-kbasis-coord-1 fmatp-transpose-mat-lin-mat
                        (:instance fmatp-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
                        (:instance fp-entry (a (row-reduce (transpose-mat (lin-mat))))
			                    (i (index i (lead-inds (row-reduce (transpose-mat (lin-mat))))))
					    (m (wdim)) (n (vdim)))))))

;; Thus, c = (kbasis-elt-coords j), defined as follows:

(defun kbasis-coords-aux (i j)
  (if (posp i)
      (append (kbasis-coords-aux (1- i) j)
              (list (kbasis-coord (1- i) j)))
    ()))

(defund kbasis-coords (j) (kbasis-coords-aux (vdim) j))

(local-defthm nth-append
  (implies (natp k)
           (equal (nth k (append l m))
	          (if (< k (len l))
		      (nth k l)
		    (nth (- k (len l)) m)))))

(local-defthm len-kbasis-coords-aux
  (equal (len (kbasis-coords-aux i j))
         (nfix i)))

(local-defthm nth-kbasis-coords-aux
  (implies (and (natp i) (<= i (vdim))
                (natp k) (< k i))
	   (equal (nth k (kbasis-coords-aux i j))
	          (kbasis-coord k j))))

(defthmd nth-kbasis-coords
  (implies (and (natp k) (< k (vdim)))
           (equal (nth k (kbasis-coords j))
	          (kbasis-coord k j)))
  :hints (("Goal" :in-theory (enable kbasis-coords))))

(defthm len-kbasis-coords
  (equal (len (kbasis-coords j))
         (vdim))
  :hints (("Goal" :in-theory (enable kbasis-coords))))

(local-defthmd fp-member-kbasis-coords
  (implies (and (member x (kbasis-coords j)) (natp j) (< j (vdim)))
           (fp x))
  :hints (("Goal" :in-theory (e/d (fp-kbasis-coord) (ind<len))
                  :use (len-kbasis-coords
		        (:instance nth-kbasis-coords (k (index x (kbasis-coords j))))
			(:instance ind<len (l (kbasis-coords j)))))))

(local-defun non-fp-member (l)
  (if (consp l)
      (if (fp (car l))
          (non-fp-member (cdr l))
	(car l))
    ()))

(local-defthmd non-fp-member-or-flistnp
  (implies (true-listp l)
           (let ((x (non-fp-member l)))
	     (or (and (member x l) (not (fp x)))
	         (flistnp l (len l))))))

(local-defthm true-listp-kbasis-coords-aux
  (true-listp (kbasis-coords-aux i j)))

(local-defthm true-listp-kbasis-coords
  (true-listp (kbasis-coords j))
  :hints (("Goal" :in-theory (enable kbasis-coords))))

(defthm flistnp-kbasis-coords
  (implies (and (natp j) (< j (vdim)))
           (flistnp (kbasis-coords j) (vdim)))
  :hints (("Goal" :use ((:instance non-fp-member-or-flistnp (l (kbasis-coords j)))
                        (:instance fp-member-kbasis-coords (x (non-fp-member (kbasis-coords j))))))))

;; The kbasis element corresponding to j is the vector (vcomb c (vbasis0)).  Thus, kbasis is defined as follows:

(defun kbasis-aux (f)
  (if (consp f)
      (cons (vcomb (kbasis-coords (car f)) (vbasis0))
            (kbasis-aux (cdr f)))
    ()))

(defund kbasis ()
  (let ((ar (row-reduce (transpose-mat (lin-mat)))))
    (kbasis-aux (free-inds ar (vdim)))))

(local-defthm true-listnp-kbasis-aux
  (true-listp (kbasis-aux f)))

(local-defthm true-listnp-kbasis
  (true-listp (kbasis))
  :hints (("Goal" :in-theory (enable kbasis))))

(in-theory (disable (kbasis)))

(defund kdim () (len (kbasis)))

(in-theory (disable (kdim)))

(local-defthm len-kbasis-aux
  (equal (len (kbasis-aux f))
         (len f)))

(defthmd kdim-val
  (equal (kdim)
         (len (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim))))
  :hints (("Goal" :in-theory (enable kdim kbasis))))

;; We must show that kbasis is a linearly independent list of kernel vectors that spans the kernel.

;; If i < kdim and j = (nth i f), then

;;   (nth i (kbasis)) =  (vcomb (kbasis-coords j) (vbasis0)),

(local-defun ar$ () (row-reduce (transpose-mat (lin-mat))))

(local-defun f$ () (free-inds (ar$) (vdim)))

(local-defun l$ () (lead-inds (ar$)))

(local-defun q$ () (num-nonzero-rows (ar$)))

(local-defun aq$ () (first-rows (q$) (ar$)))

(local-defthmd fmatp-ar
  (fmatp (ar$) (wdim) (vdim))
  :hints (("Goal" :use (fmatp-transpose-mat-lin-mat
                        (:instance fmatp-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))))))

(local-defthmd row-echelon-p-ar
  (row-echelon-p (ar$))
  :hints (("Goal" :use (fmatp-transpose-mat-lin-mat
                        (:instance row-echelon-p-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))))))

(local-defthmd q<=wdim
  (<= (q$) (wdim))
  :hints (("Goal" :use (fmatp-ar
                        (:instance num-nonzero-rows<=m (a (row-reduce (transpose-mat (lin-mat)))) (m (wdim)) (n (vdim)))))))

(local-defthmd len-l
  (equal (len (l$)) (q$))
  :hints (("Goal" :use ((:instance len-lead-inds-num-nonzero-rows (a (ar$)))))))

(local-defthmd dlistp-f
  (dlistp (f$))
  :hints (("Goal" :use (fmatp-ar row-echelon-p-ar
                        (:instance dlistp-free-inds (a (ar$)) (m (wdim)) (n (vdim)))))))

(local-defthmd dlistp-l
  (dlistp (l$))
  :hints (("Goal" :use (fmatp-ar row-echelon-p-ar
                        (:instance dlistp-lead-inds (a (ar$)) (m (wdim)) (n (vdim)))))))

(local-defthmd lead-inds-aq
  (equal (lead-inds (aq$))
         (l$))
  :hints (("Goal" :use (fmatp-ar
                        (:instance lead-inds-first-nonzero-rows (a (row-reduce (transpose-mat (lin-mat)))) (m (wdim)) (n (vdim)))))))

(local-defthmd free-inds-aq
  (equal (free-inds (aq$) (vdim))
         (f$))
  :hints (("Goal" :in-theory (enable free-inds)
                  :use (lead-inds-aq))))

(local-defthm nth-kbasis-aux
  (implies (and (natp i) (< i (len f)))
           (equal (nth i (kbasis-aux f))
	          (vcomb (kbasis-coords (nth i f)) (vbasis0)))))

(local-defthmd nth-kbasis
  (implies (and (natp i) (< i (len (f$))))
           (equal (nth i (kbasis))
                  (vcomb (kbasis-coords (nth i (f$))) (vbasis0))))
  :hints (("Goal" :in-theory (enable kbasis))))

;; which implies (vp (nth i (kbasis))) and (vcoords0 (nth i (kbasis))) = (kbasis-coords j).

(local-defthmd member-f
  (iff (member x (f$))
       (and (natp x)
            (< x (vdim))
            (not (member x (l$)))))
  :hints (("Goal" :use (fmatp-transpose-mat-lin-mat
                        (:instance member-free-inds (a (row-reduce (transpose-mat (lin-mat)))) (m (wdim)) (n (vdim)))
			(:instance fmatp-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
			(:instance member-ninit (n (vdim)))
			(:instance row-echelon-p-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))))))

(local-defthmd vp-nth-kbasis
  (implies (and (natp i) (< i (len (f$))))
           (vp (nth i (kbasis))))
  :hints (("Goal" :in-theory (disable FLISTNP-KBASIS-COORDS)
                  :use (nth-kbasis
                        (:instance member-f (x (nth i (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))))
			(:instance flistnp-kbasis-coords (j (nth i (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))))))))

(local-defthmd vcoords-nth-kbasis
  (implies (and (natp i) (< i (len (f$))))
           (equal (vcoords0 (nth i (kbasis)))
                  (kbasis-coords (nth i (f$)))))
  :hints (("Goal" :in-theory (disable FLISTNP-KBASIS-COORDS)
                  :use (nth-kbasis vp-nth-kbasis
                        (:instance member-f (x (nth i (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))))
			(:instance vcoords0-unique (c (kbasis-coords (nth i (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))))
			                           (x (nth i (kbasis))))
			(:instance flistnp-kbasis-coords (j (nth i (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))))))))

;; Thus, to prove that every member of kbasis is in the kernel, it suffices to show that for all j in f,

;;   (sol0p (kbasis-coords j) a).

;; Let x = (kbasis-coords j).  According to the lemma sol0p-suff, it suffices to prove that for all k < q,

;;   (nth (nth k l) x) = (f- (fdot-select f (nth k ar) x).

;; But according to the definition of kbasis-coords, both sides of this equation reduce to (f- (entry k j ar)).
;; Thus, we have

(local-defthm nth-free-index-kbasis-coords
  (implies (and (member j (f$)) (member k (f$)))
           (equal (nth k (kbasis-coords j))
	          (if (equal k j)
		      (f1)
		    (f0))))
  :hints (("Goal" :in-theory (enable kbasis-coord)
                  :use (nth-kbasis-coords
                        (:instance member-f (x j))
                        (:instance member-f (x k))))))

(local-defthmd fp-nth-flistnp
  (implies (and (natp n) (flistnp x n) (natp j) (< j n))
           (fp (nth j x))))

(local-defthmd fp-nth-free-flistnp
  (implies (and (flistnp r (vdim)) (member j (f$)))
           (fp (nth j r)))
  :hints (("Goal" :use ((:instance member-f (x j))
                        (:instance fp-nth-flistnp (n (vdim)) (x r))))))

(local-defthmd fdot-select-sublist-f
  (implies (and (dlistp f) (sublistp f (f$)) (member j (f$))
                (flistnp r (vdim)))
           (equal (fdot-select f r (kbasis-coords j))
	          (if (member j f)
		      (nth j r)
		    (f0))))
  :hints (("Goal" :induct (len f))
          ("Subgoal *1/1" :use (fp-nth-free-flistnp (:instance fp-nth-free-flistnp (j (car f)))))))

(local-defthmd flistnp-nth-ar
  (implies (and (natp k) (< k (q$)))
           (flistnp (nth k (ar$)) (vdim)))
  :hints (("Goal" :use (fmatp-ar q<=wdim
                        (:instance flistnp-row (a (ar$)) (i k) (m (wdim)) (n (vdim)))))))

(local-defthmd fdot-select-f
  (implies (and (member j (f$)) (natp k) (< k (q$)))
           (equal (fdot-select (f$) (nth k (ar$)) (kbasis-coords j))
	          (entry k j (ar$))))
  :hints (("Goal" :use (flistnp-nth-ar dlistp-f
                        (:instance fdot-select-sublist-f (r (nth k (ar$))) (f (f$)))))))

(local-defthmd nth-lead-ind-kbasis-coords
  (implies (and (member j (f$)) (natp k) (< k (q$)))
           (equal (nth (nth k (l$)) (kbasis-coords j))
                  (f- (entry k j (ar$)))))
  :hints (("Goal" :in-theory (enable kbasis-coord)
                  :use (len-l fmatp-ar row-echelon-p-ar dlistp-l
		        (:instance nth-lead-inds-bound (a (ar$)) (m (wdim)) (n (vdim)))
			(:instance ind-nth (i k) (l (l$)))
		        (:instance nth-kbasis-coords (k (nth k (l$))))))))

(local-defthmd nth-lead-ind-kbasis-coords-fdot-select
  (implies (and (member j (f$)) (natp k) (< k (q$)))
           (equal (nth (nth k (l$)) (kbasis-coords j))
	          (f- (fdot-select (f$) (nth k (ar$)) (kbasis-coords j)))))
  :hints (("Goal" :use (fdot-select-f nth-lead-ind-kbasis-coords))))

(defthmd sol0p-kbasis-coords
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (member j f)
             (sol0p (kbasis-coords j) (transpose-mat (lin-mat)))))
  :hints (("Goal" :use (lead-inds-aq free-inds-aq flistnp-kbasis-coords fmatp-transpose-mat-lin-mat fmatp-ar q<=wdim
                        (:instance sol0p-suff (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)) (x (kbasis-coords j)))
			(:instance member-f (x j))
			(:instance nth-first-rows (a (ar$)) (m (wdim)) (n (vdim)) (q (q$)) (i (sol0p-witness (kbasis-coords j) (transpose-mat (lin-mat)) (vdim))))
			(:instance nth-lead-ind-kbasis-coords-fdot-select (k (sol0p-witness (kbasis-coords j) (transpose-mat (lin-mat)) (vdim))))))))

(local-defthmd in-kernel-p-nth-kbasis
  (implies (and (natp i) (< i (len (f$))))
           (in-kernel-p (nth i (kbasis))))
  :hints (("Goal" :use (vp-nth-kbasis vcoords-nth-kbasis
                        (:instance in-kernel-p-sol0p (x (nth i (kbasis))))
			(:instance sol0p-kbasis-coords (j (nth i (f$))))))))

(local-defthmd in-kernel-p-member-kbasis
  (implies (member x (kbasis))
           (in-kernel-p x))
  :hints (("Goal" :in-theory (e/d (kdim) (kdim-val))
                  :use (kdim-val
		        (:instance in-kernel-p-nth-kbasis (i (index x (kbasis))))))))

(local-defthm klistnp-kbasis-1
  (implies (and (true-listp l) (sublistp l (kbasis)))
           (klistnp l (len l)))
  :hints (("Subgoal *1/5" :use ((:instance in-kernel-p-member-kbasis (x (car l)))))))

(defthm klistnp-kbasis
  (klistnp (kbasis) (kdim))
  :hints (("Goal" :in-theory (enable kdim))))

(defthmd kbasis-nil
  (implies (= (kdim) 0)
           (null (kbasis)))
  :hints (("Goal" :in-theory (e/d (kdim) (len-vlistnp))
                  :use ((:instance len-vlistnp (x (kbasis)) (n 0))))))

#|
;; The kernel is trivial iff lin is injective:

(defthm in-kernel-p-nontrivial
  (iff (lin-injective-p)
       (= (kdim) 0)))
|#

;; Next, we prove that kbasis is linearly independent.

;; Given (flistnp c n), (vlistnp l n), and i < vdim, we derive a formula for (nth i (vcoords0 (vcomb c l))):

(defun nth-vcomb (j c l)
  (if (consp c)
      (f+ (f* (car c) (nth j (vcoords0 (car l))))
	  (nth-vcomb j (cdr c) (cdr l)))
      (f0)))

(defthmd nth-vcomb-val
  (implies (and (flistnp c n) (vlistnp l n)
                (natp j) (< j (vdim)))
	   (equal (nth j (vcoords0 (vcomb c l)))
	          (nth-vcomb j c l)))
  :hints (("Subgoal *1/3" :in-theory (enable vcoords0-v+ vcoords0-v*)  
                          :use ((:instance nth-flist-add (n (vdim)) (i j) (x (FLIST-SCALAR-MUL (CAR C) (VCOORDS0 (CAR L)))) (y (VCOORDS0 (VCOMB (CDR C) (CDR L)))))
			        (:instance nth-flist-scalar-mul (n (vdim)) (i j) (c (car c)) (x (VCOORDS0 (CAR L))))))))

;; We apply this result to the case l = (kbasis), n = kdim, and j = (nth i f), where i < kdim.  By construction of
;; kbasis, (nth-vcomb j c (kbasis)) = (nth i c):

(local-defthmd nth-nth-kbasis
  (implies (and (natp i) (< i (len (f$))) (member j (f$)))
           (equal (nth j (vcoords0 (nth i (kbasis))))
	          (if (equal (nth i (f$)) j)
		      (f1)
		    (f0))))
  :hints (("Goal" :use (vcoords-nth-kbasis
                        (:instance nth-free-index-kbasis-coords (k (nth i (f$))))))))

(local-defthmd nth-kbasis-distinct
  (implies (and (natp i) (< i (len (f$))) (natp j) (< j (len (f$))) (not (= i j)))
           (not (equal (nth i (kbasis)) (nth j (kbasis)))))
  :hints (("Goal" :use (dlistp-f
                        (:instance nth-nth-kbasis (j (nth i (f$))))
                        (:instance nth-nth-kbasis (i j) (j (nth i (f$))))))))

(defthm dlistp-kbasis
  (dlistp (kbasis))
  :hints (("Goal" :in-theory (disable dcex-lemma)
                  :use (kdim-val kdim
                        (:instance dcex-lemma (l (kbasis)))
                        (:instance nth-kbasis-distinct (i (dcex1 (kbasis))) (j (dcex2 (kbasis))))))))

(local-defthmd nth-vcomb-nth-c-1
  (implies (and (true-listp l) (dlistp l) (sublistp l (kbasis)) (flistnp c (len l))
                (natp i) (< i (len (f$))))
           (equal (nth-vcomb (nth i (f$)) c l)
	          (if (member (nth i (kbasis)) l)
		      (nth (index (nth i (kbasis)) l) c)
		    (f0))))
  :hints (("Goal" :induct (vcomb c l))  
          ("Subgoal *1/1.2" :use ((:instance nth-nth-kbasis (j (nth i (f$))))))	  
	  ("Subgoal *1/1.1" :in-theory (disable ind<len)
	                    :use (kdim kdim-val dlistp-f
	                          (:instance nth-nth-kbasis (j (nth i (f$))) (i (index (car l) (kbasis))))	  
	                          (:instance nth-dlist-distinct (l (f$)) (j (index (car l) (kbasis))))
 			  	  (:instance ind<len (x (car l)) (l (kbasis)))))
	  ("Subgoal *1/1.4" ;:in-theory (disable ind<len)
	                    :use (kdim kdim-val dlistp-f
	                          (:instance nth-nth-kbasis (j (nth i (f$))) (i (index (car l) (kbasis))))	  
	                          (:instance nth-dlist-distinct (l (f$)) (j (index (car l) (kbasis))))
 			  	  (:instance ind<len (x (car l)) (l (kbasis)))))))

(defthmd nth-vcomb-nth-c
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (and (flistnp c (len f)) (natp i) (< i (len f)))
             (equal (nth-vcomb (nth i f) c (kbasis))
	            (nth i c))))
  :hints (("Goal" :use (kdim-val (:instance nth-vcomb-nth-c-1 (l (kbasis)))))))

;; Combine nth-vcomb-val and nth-vcomb-val:

(defthmd nth-vcomb-kbasis 
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (implies (and (flistnp c (kdim)) (natp i) (< i (kdim)))
              (equal (nth (nth i f) (vcoords0 (vcomb c (kbasis))))
	             (nth i c))))
  :hints (("Goal" :use (kdim kdim-val nth-vcomb-nth-c klistnp-kbasis
                        (:instance nth-vcomb-val (j (nth i (f$))) (l (kbasis)) (n (kdim)))
			(:instance member-f (x (nth i (f$))))))))

;; Now suppose (vcomb c (kbasis)) = 0. Then (vcoords0 (vcomb c (kbasis))) = (flistn0 (kbasis)).  It follows that
;; (nth i c) = 0 for all i < kdim, and therefore c = (flistn0 (kdim):

(local-defthmd vcomb-kbasis-v0-1
  (implies (and (flistnp c (kdim)) (equal (vcomb c (kbasis)) (v0))
                (natp i) (< i (kdim)))
	   (equal (nth i c) (f0)))
  :hints (("Goal" :use (kdim kdim-val nth-vcomb-kbasis
			(:instance member-f (x (nth i (f$))))))))

(local-defthmd vcomb-kbasis-v0-2
  (implies (and (flistnp c (kdim)) (equal (vcomb c (kbasis)) (v0))
                (true-listp l) (sublistp l c))
	   (equal (flistn0 (len l)) l))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (disable ind<len)
	                  :use ((:instance vcomb-kbasis-v0-1 (i (index (car l) c)))
	                        (:instance ind<len (x (car l)) (l c))))))
  
(defthmd vcomb-kbasis-v0
  (implies (and (flistnp c (kdim)) (equal (vcomb c (kbasis)) (v0)))
	   (equal (flistn0 (kdim)) c))
  :hints (("Goal" :use ((:instance vcomb-kbasis-v0-2 (l c))
                        (:instance len-flist (x c) (n (kdim)))))))

;; Thus, kbasis is linearly independent:

(local-defthmd vindepp-kbasis-0
  (implies (= (kdim) 0)
           (vindepp (kbasis)))
  :hints (("Goal" :in-theory (e/d (vindepp) (klistnp-kbasis))
                  :use (klistnp-kbasis))))

(defthmd vindepp-kbasis
  (vindepp (kbasis))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vindepp-kbasis-0
		        (:instance vdepp-vcomb-v0 (l (kbasis)) (m (kdim)))
		        (:instance vcomb-kbasis-v0 (c (vdep-coeffs (kbasis))))))))

;; To prove that kbasis spans the kernel, we define the following coordinate function:

(defun kcoords-aux (x f)
  (if (consp f)
      (cons (nth (car f) (vcoords0 x))
            (kcoords-aux x (cdr f)))
    ()))

(defund kcoords (x)
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (kcoords-aux x f)))

;; The first requirement of this function is trivial:

(local-defthm flistnp-kcoords-1
  (implies (and (vp x) (sublistp f (ninit (vdim))))
           (flistnp (kcoords-aux x f) (len f)))
  :hints (("Goal" :induct (len f))
          ("Subgoal *1/1" :use ((:instance member-ninit (x (car f)) (n (vdim)))
	                        (:instance fp-flistnp (n (vdim)) (x (vcoords0 x)) (i (car f)))))))

(local-defthm sublistp-set-difference-equal
  (sublistp (set-difference-equal l m) l))

(local-defthmd sublistp-f
  (sublistp (f$) (ninit (vdim)))
  :hints (("Goal" :in-theory (enable free-inds))))

(defthmd kdim-bound
  (<= (kdim) (vdim))
  :hints (("Goal" :use (sublistp-f dlistp-f kdim-val
                        (:instance sublistp-<=-len (l (f$)) (m (ninit (vdim))))))))

(defthm flistnp-kcoords
  (implies (in-kernel-p x) (flistnp (kcoords x) (kdim)))
  :hints (("Goal" :in-theory (enable in-kernel-p kdim kcoords)
                  :use (kdim-val sublistp-f))))

;; Another immediate consequence of the definition:

(local-defthm nth-kcoords-aux
  (implies (and (natp i) (< i (len f)))
           (equal (nth i (kcoords-aux x f))
	          (nth (nth i f) (vcoords0 x)))))

(defthmd nth-kcoords
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (and (natp i) (< i (kdim)))
             (equal (nth i (kcoords x))
	            (nth (nth i f) (vcoords0 x)))))
  :hints (("Goal" :in-theory (enable kcoords kdim)
                  :use (kdim-val))))

;; We must show that if (in-kernel-p x), then (vcomb (kcoords x) (kbasis)) = x.  Let y = (vcomb (kcoords x) (kbasis).
;; By vbasis0-spans, it suffices to show that (vcoords0 y) = (vcoords0 x).  But since (sol0p x a) and (sol0p y a), it
;; follows from sol0p-necc that each leading index coordinate of a kernel element is determined by the free index
;; coordinates, and therefore it suffices to show that for all j in f, (nth j (vcoords0 y)) = (nth j (vcoords0 x)).
;; To prove this, we instantiate nth-vcomb-kbasis with i = (index j f) and c = (kcoords x):

;;    (nth j (vcoords0 y)) = (nth (nth i f) (vcoords0 (vcomb (kcoords x) (kbasis))))
;;                         = (nth i (kcoords x))
;;                         = (nth j (vcoords0 x)).

(local-defthmd kbasis-spans-1
  (implies (in-kernel-p x)
           (in-kernel-p (vcomb (kcoords x) (kbasis)))))

(local-defthmd kbasis-spans-2
  (implies (in-kernel-p x)
           (and (vp x)
	        (vp (vcomb (kcoords x) (kbasis)))))
  :hints (("Goal" :in-theory (enable in-kernel-p)
                  :use (kbasis-spans-1))))

(local-defthmd kbasis-spans-3
  (implies (and (in-kernel-p x)
                (equal (vcoords0 (vcomb (kcoords x) (kbasis))) (vcoords0 x)))
           (equal (vcomb (kcoords x) (kbasis))
	          x))
  :hints (("Goal" :use (kbasis-spans-2  
                        (:instance vbasis0-spans (x (vcomb (kcoords x) (kbasis))))))))

(local-defthmd kbasis-spans-4
  (implies (in-kernel-p x)
           (and (sol0p (vcoords0 x) (transpose-mat (lin-mat)))
	        (sol0p (vcoords0 (vcomb (kcoords x) (kbasis))) (transpose-mat (lin-mat)))))
  :hints (("Goal" :use (kbasis-spans-1 in-kernel-p-sol0p
                        (:instance in-kernel-p-sol0p (x (vcomb (kcoords x) (kbasis))))))))

(local-defthmd kbasis-spans-5
  (implies (and (in-kernel-p x) (member j (f$)))
           (equal (nth j (vcoords0 x))
	          (nth j (vcoords0 (vcomb (kcoords x) (kbasis))))))
  :hints (("Goal" :in-theory (disable ind<len)
                  :use (kdim kdim-val
                        (:instance nth-vcomb-kbasis (i (index j (f$))) (c (kcoords x)))
                        (:instance nth-kcoords (i (index j (f$))))
			(:instance ind<len (x j) (l (f$)))))))

(local-defthmd kbasis-spans-6
  (implies (and (in-kernel-p x) (sublistp l (f$)))
           (equal (fdot-select l r (vcoords0 x))
	          (fdot-select l r (vcoords0 (vcomb (kcoords x) (kbasis))))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance kbasis-spans-5 (j (car l)))))))

(local-defthmd kbasis-spans-7
  (implies (in-kernel-p x)
           (equal (fdot-select (f$) r (vcoords0 x))
	          (fdot-select (f$) r (vcoords0 (vcomb (kcoords x) (kbasis))))))
  :hints (("Goal" :use ((:instance kbasis-spans-6 (l (f$)))))))

(local-defthmd kbasis-spans-8
  (implies (and (in-kernel-p x) (natp k) (< k (q$)))
           (equal (nth (nth k (l$)) (vcoords0 x))
	          (nth (nth k (l$)) (vcoords0 (vcomb (kcoords x) (kbasis))))))
  :hints (("Goal" :use (fmatp-transpose-mat-lin-mat kbasis-spans-2 kbasis-spans-4 lead-inds-aq free-inds-aq
                        (:instance sol0p-necc (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)) (x (vcoords0 x)))
                        (:instance sol0p-necc (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)) (x (vcoords0 (vcomb (kcoords x) (kbasis)))))
			(:instance kbasis-spans-7 (r (nth k (aq$))))))))

(local-defthmd kbasis-spans-9
  (implies (and (in-kernel-p x) (member j (l$)))
           (equal (nth j (vcoords0 x))
	          (nth j (vcoords0 (vcomb (kcoords x) (kbasis))))))
  :hints (("Goal" :use (len-l
                        (:instance kbasis-spans-8 (k (index j (l$))))))))

(local-defthmd kbasis-spans-10
  (implies (and (in-kernel-p x) (natp j) (< j (vdim)))
           (equal (nth j (vcoords0 x))
	          (nth j (vcoords0 (vcomb (kcoords x) (kbasis))))))
  :hints (("Goal" :use (len-l kbasis-spans-5 kbasis-spans-9
                        (:instance member-f (x j))))))

(local-defthmd kbasis-spans-11
  (implies (in-kernel-p x)
           (equal (vcoords0 x)
	          (vcoords0 (vcomb (kcoords x) (kbasis)))))
  :hints (("Goal" :in-theory (disable len-flist flistnp-vcoords0)
                  :use (kbasis-spans-2 flistnp-vcoords0
		        (:instance len-flist (x (vcoords0 x)) (n (vdim)))
		        (:instance len-flist (x (vcoords0 (vcomb (kcoords x) (kbasis)))) (n (vdim)))
                        (:instance flistnp-vcoords0 (x (vcomb (kcoords x) (kbasis))))
                        (:instance nth-diff-diff (x (vcoords0 x)) (y (vcoords0 (vcomb (kcoords x) (kbasis)))))
			(:instance kbasis-spans-10 (j (nth-diff (vcoords0 x) (vcoords0 (vcomb (kcoords x) (kbasis))))))))))

(defthm kbasis-spans
  (implies (in-kernel-p x)
           (equal (vcomb (kcoords x) (kbasis))
                  x))
  :hints (("Goal" :use (kbasis-spans-3 kbasis-spans-11))))


#|
;; This is an alternative non-constructive definition of a kernel basis that I did before I did the above.
;; I no longer need it, but here it is.

;; A basis of the kernel may be defined by emulating the definition of sbasis0:

(defchoose kunspanned x (l)
  (and (in-kernel-p x) (vindepp (cons x l))))

(defthmd kunspanned-lemma
  (implies (and (in-kernel-p x) (vindepp (cons x l)))
           (let ((y (kunspanned l)))
	     (and (in-kernel-p y) (vindepp (cons y l)))))
  :hints (("Goal" :use (kunspanned))))

(defun kbasis-aux (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))
                  :hints (("Goal" :in-theory (enable vdepp)
		                  :use ((:instance vdepp-if->-dim
				         (m (1+ (len l)))
				         (l (cons (kunspanned l) l))))))))
  (let ((x (kunspanned l)))
    (if (and (klistnp l (len l)) (in-kernel-p x) (vindepp (cons x l)))
        (kbasis-aux (cons x l))
      l)))

(defun kbasis ()
  (kbasis-aux ()))

(defun kdim () (len (kbasis)))

(in-theory (disable (kdim) (kbasis-aux) (kbasis)))

(defun kcoords (x)
  (vcoords x (kbasis)))

;; The next 5 results are derived by functional instantiation of the properties of sbasis0:

(defthm klistnp-kbasis
  (klistnp (kbasis) (kdim))
  :hints (("Goal" :use ((:functional-instance slistnp-sbasis0
                         (sp in-kernel-p)
			 (slistnp klistnp)
			 (sunspanned kunspanned)
			 (sbasis0-aux kbasis-aux)
			 (sbasis0 kbasis)
			 (sdim kdim))))
	  ("Subgoal 4" :use (kunspanned))
	  ("Subgoal 3" :use (kunspanned))))

(defthmd vindepp-kbasis
  (vindepp (kbasis))
  :hints (("Goal" :use ((:functional-instance vindepp-sbasis0
                         (sp in-kernel-p)
			 (slistnp klistnp)
			 (sunspanned kunspanned)
			 (sbasis0-aux kbasis-aux)
			 (sbasis0 kbasis)
			 (sdim kdim))))
	  ("Subgoal 4" :use (kunspanned))
	  ("Subgoal 3" :use (kunspanned))))

(defthm flistnp-kcoords
  (implies (in-kernel-p x) (flistnp (kcoords x) (kdim)))
  :hints (("Goal" :use ((:functional-instance flistnp-scoords0
                         (sp in-kernel-p)
			 (slistnp klistnp)
			 (sunspanned kunspanned)
			 (sbasis0-aux kbasis-aux)
			 (sbasis0 kbasis)
			 (sdim kdim)
			 (scoords0 kcoords))))
	  ("Subgoal 4" :use (kunspanned))
	  ("Subgoal 3" :use (kunspanned))))

(defthm kbasis-spans
  (implies (in-kernel-p x)
           (equal (vcomb (kcoords x) (kbasis))
                  x))
  :hints (("Goal" :use ((:functional-instance sbasis0-spans
                         (sp in-kernel-p)
			 (slistnp klistnp)
			 (sunspanned kunspanned)
			 (sbasis0-aux kbasis-aux)
			 (sbasis0 kbasis)
			 (sdim kdim)
			 (scoords0 kcoords))))
	  ("Subgoal 4" :use (kunspanned))
	  ("Subgoal 3" :use (kunspanned))))

(defthmd kdim-bound
  (<= (kdim) (vdim))  
  :hints (("Goal" :use ((:functional-instance sdim-bound
                         (sp in-kernel-p)
			 (slistnp klistnp)
			 (sunspanned kunspanned)
			 (sbasis0-aux kbasis-aux)
			 (sbasis0 kbasis)
			 (sdim kdim)
			 (scoords0 kcoords))))))
|#	  

;; The image of lin is recognized by the predicate in-image-p:

(defund in-image-p (x)
  (let ((p (lin-preimage x)))
    (and (vp p) (equal (lin p) x))))

(defthmd in-image-p-lemma
  (implies (and (vp p) (equal (lin p) x))
           (in-image-p x))
  :hints (("Goal" :in-theory (enable in-image-p)
                  :use ((:instance lin-preimage (x p) (y x))))))
  
(defthm in-image-p-lin
  (implies (vp x)
           (in-image-p (lin x)))
  :hints (("Goal" :use ((:instance in-image-p-lemma (p x) (x (lin x)))))))

;; The subspace axioms are easily verified:

(defthm in-image-p-wp
  (implies (in-image-p x) (wp x))
  :hints (("Goal" :in-theory (enable in-image-p)
                  :use ((:instance lin-val (x (lin-preimage x)))))))

(defthmd in-image-p-w0
  (in-image-p (w0))
  :hints (("Goal" :use ((:instance in-image-p-lemma (x (w0)) (p (v0)))))))

(defthm in-image-p-w+
  (implies (and (in-image-p x) (in-image-p y))
           (in-image-p (w+ x y)))
  :hints (("Goal" :in-theory (enable in-image-p)
                  :use ((:instance in-image-p-lemma (x (w+ x y)) (p (v+ (lin-preimage x) (lin-preimage y))))))))

(defthm in-image-p-w*
  (implies (and (in-image-p x) (fp c))
           (in-image-p (w* c x)))
  :hints (("Goal" :in-theory (enable in-image-p)
                  :use ((:instance in-image-p-lemma (x (w* c x)) (p (v* c (lin-preimage x))))))))

(defthm in-image-p-w-
  (implies (in-image-p x)
           (in-image-p (w- x)))
  :hints (("Goal" :use (w*f-f1 (:instance in-image-p-w* (c (f- (f1))))))))

;; We shall show that the dimension of the image is the difference vdim - kdim:

(defun idim () (- (vdim) (kdim)))

(defthmd idim+kdim
  (equal (+ (idim) (kdim))
         (vdim))
  :hints (("Goal" :in-theory (enable idim))))

;; We must construct a basis for the image of length idim.  First we extend kbasis to a basis for V:
;; First we extend kbasis to a basis of V:

(defund extend-kbasis ()
  (if (posp (kdim))
      (extend-to-basis (kbasis))
    (vbasis0)))

(in-theory (disable (extend-kbasis)))

(in-theory (disable kbasis))

(defthmd vbasisp-extend-kbasis
  (vbasisp (extend-kbasis))
  :hints (("Goal" :in-theory (enable extend-kbasis kdim)
                  :use (vindepp-kbasis klistnp-kbasis
		        (:instance vbasisp-extend-to-basis (l (kbasis)) (n (kdim)))))))

;; The image basis consists of the first idim members of the extended basis:

(defun firstn (n l)
  (if (zp n)
      ()
    (cons (car l) (firstn (1- n) (cdr l)))))

(defthmd firstn-append
  (implies (true-listp l)
           (equal (firstn (len l) (append l m))
	          l)))

(defthmd append-firstn-nthcdr
  (implies (and (natp n) (<= n (len l)))
           (equal (append (firstn n l) (nthcdr n l))
	          l)))

(local-defun vlistnp-firstn-induct (k l n)
  (declare (irrelevant k l))
  (if (zp n)
      t
    (vlistnp-firstn-induct (1- k) (cdr l) (1- n))))

(defthm vlistnp-firstn
  (implies (and (natp n) (natp k) (<= k n) (vlistnp l n))
           (vlistnp (firstn k l) k))
  :hints (("Goal" :induct (vlistnp-firstn-induct k l n))))

(defthm vlistnp-nthcdr
  (implies (and (natp n) (natp k) (<= k n) (vlistnp l n))
           (vlistnp (nthcdr k l) (- n k)))
  :hints (("Goal" :induct (vlistnp-firstn-induct k l n))))

(defthm flistnp-firstn
  (implies (and (natp n) (natp k) (<= k n) (flistnp l n))
           (flistnp (firstn k l) k))
  :hints (("Goal" :induct (vlistnp-firstn-induct k l n))))

(defthm flistnp-nthcdr
  (implies (and (natp n) (natp k) (<= k n) (flistnp l n))
           (flistnp (nthcdr k l) (- n k)))
  :hints (("Goal" :induct (vlistnp-firstn-induct k l n))))

(defund ibasis ()
  (lin-list (firstn (idim) (extend-kbasis))))

(in-theory (disable (ibasis)))

;; We must show that ibasis is a linearly independent list of length idim that spans the image.
;; We first note that the members of ibasis are in the image:

(defun ilistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-image-p (car x))
         (ilistnp (cdr x) (1- n)))))

(defthmd ilistnp-wlistnp
  (implies (ilistnp x n)
           (wlistnp x n)))

(local-defthm ilistnp-lin-list
  (implies (vlistnp l n)
           (ilistnp (lin-list l) n))
  :hints (("Goal" :induct (vlistnp-induct l n))))

(defthm ilistnp-ibasis
  (ilistnp (ibasis) (idim))
  :hints (("Goal" :in-theory (enable kdim idim ibasis vbasisp)
                  :use (kdim-bound vbasisp-extend-kbasis
		        (:instance vlistnp-firstn (n (vdim)) (k (idim)) (l (extend-kbasis)))))))

;; To show that ibasis is linearly dependent, suppose (flistnp c (idim)) and (wcomb c (ibasis)) = w0.
;; Let l = (firstn (idim) (extend-kbasis)).  Then

;;   (lin (vcomb c l)) = (wcomb c (lin-list l)) = (wcomb c (ibasis)) = w0,

;; i.e., (in-kernel-p (vcomb c l).  Let d = (kcoords (vcomb c l)).  By kbasis-spans,

;; (vcomb c l) = (vcomb d (kbasis)).  It follows that

;;   (vcomb (append c (flist-minus d)) (extend-kbasis))
;;     = (vcomb (append c (flist-minus d)) (append l (kbasis))
;;     = (v+ (vcomb c l) (vcomb (flist-minus d) (kbasis)))
;;     = (v+ (vcomb d (kbasis)) (vcomb (flist-minus d) (kbasis)))
;;     = (vcomb (flist-add d (flist-minus d)) (kbasis))
;;     = (vcomb (flistn0 kdim) (kbasis))
;;     = v0.

(local-defthmd ili-1
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (vlistnp (firstn (idim) (extend-kbasis)) (idim)))
  :hints (("Goal" :in-theory (enable kdim idim ibasis vbasisp)
                  :use (kdim-bound vbasisp-extend-kbasis
		        (:instance vlistnp-firstn (k (idim)) (n (vdim)) (l (extend-kbasis)))))))

(local-defthmd ili-2
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (equal (lin (vcomb c (firstn (idim) (extend-kbasis))))
	          (w0)))
  :hints (("Goal" :in-theory (enable kdim idim ibasis vbasisp)
                  :use (kdim-bound vbasisp-extend-kbasis
		        (:instance lin-vcomb (l (firstn (idim) (extend-kbasis))) (n (idim)))
		        (:instance vlistnp-firstn (k (idim)) (n (vdim)) (l (extend-kbasis)))))))

(local-defthmd ili-3
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (in-kernel-p (vcomb c (firstn (idim) (extend-kbasis)))))
  :hints (("Goal" :in-theory (enable in-kernel-p)
                  :use (ili-1 ili-2))))

(local-defthmd ili-4
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (let* ((l (firstn (idim) (extend-kbasis)))
	          (d (kcoords (vcomb c l))))
             (and (flistnp d (kdim))
	          (equal (vcomb c l)
	                 (vcomb d (kbasis))))))
  :hints (("Goal" :use (ili-3
                        (:instance kbasis-spans (x (vcomb c (firstn (idim) (extend-kbasis)))))
                        (:instance flistnp-kcoords (x (vcomb c (firstn (idim) (extend-kbasis)))))))))

(local-defthmd true-listp-vlistnp
  (implies (vlistnp l n)
           (true-listp l))
  :hints (("Goal" :induct (vlistnp-induct l n))))

(local-defthmd ili-5
  (equal (extend-kbasis)
         (append (firstn (idim) (extend-kbasis))
	         (kbasis)))
  :hints (("Goal" :in-theory (enable vbasisp vdim idim extend-kbasis)
                  :use (klistnp-kbasis vlistnp-basis0 kdim-bound vbasisp-extend-kbasis
		        (:instance nthcdr-extend-to-basis (l (kbasis)) (n (kdim)))
			(:instance firstn-append (l (vbasis0)) (m ()))
			(:instance true-listp-vlistnp (l (vbasis0)) (n (vdim)))
			(:instance len-vlistnp (x (extend-kbasis)) (n (vdim)))
		        (:instance append-firstn-nthcdr (l (extend-kbasis)) (n (idim)))))
	  ("Subgoal 1''" :use (kbasis-nil))))

(local-defthmd ili-6
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (let* ((l (firstn (idim) (extend-kbasis)))
	          (d (kcoords (vcomb c l))))
             (equal (vcomb (append c (flist-minus d)) (extend-kbasis))
	            (v+ (vcomb d (kbasis)) (vcomb (flist-minus d) (kbasis))))))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use (ili-3 ili-4 ili-5 klistnp-kbasis kdim-bound vbasisp-extend-kbasis
                        (:instance flistnp-kcoords (x (vcomb c (firstn (idim) (extend-kbasis)))))
			(:instance vlistnp-firstn (n (vdim)) (k (idim)) (l (extend-kbasis)))
                        (:instance vcomb-append (n (idim)) (m (kdim))
			                        (d (flist-minus (kcoords (vcomb c (firstn (idim) (extend-kbasis))))))
						(x (firstn (idim) (extend-kbasis)))
						(y (kbasis)))))))

(local-defthmd ili-7
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (let* ((l (firstn (idim) (extend-kbasis)))
	          (d (kcoords (vcomb c l))))
             (equal (v+ (vcomb d (kbasis)) (vcomb (flist-minus d) (kbasis)))
	            (vcomb (flistn0 (kdim)) (kbasis)))))
  :hints (("Goal" :use (ili-4 klistnp-kbasis
                        (:instance vcomb-add (x (kcoords (vcomb c (firstn (idim) (extend-kbasis)))))
			                     (y (flist-minus (kcoords (vcomb c (firstn (idim) (extend-kbasis))))))
					     (n (kdim))
					     (l (kbasis)))))))

(local-defthmd ili-8
  (equal (vcomb (flistn0 (kdim)) (kbasis))
         (v0))
  :hints (("Goal" :use (klistnp-kbasis
                        (:instance vcomb-flistn0 (n (kdim)) (l (kbasis)))))))

(local-defthmd ili-9
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (let* ((l (firstn (idim) (extend-kbasis)))
	          (d (kcoords (vcomb c l))))
             (equal (vcomb (append c (flist-minus d)) (extend-kbasis))
	            (v0))))
  :hints (("Goal" :use (ili-6 ili-7 ili-8))))

;; Since kbasis is linearly independent, (append c (flist-minus d)) = (flistn0 (vdim)), which implies
;; c = (flistn0 (idim)).  Thus, ibasis is linearly independent:

(local-defthmd ili-10
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (let* ((l (firstn (idim) (extend-kbasis)))
	          (d (kcoords (vcomb c l))))
             (flistnp (append c (flist-minus d)) (vdim))))
  :hints (("Goal" :in-theory (enable idim)
                  :use (ili-4 kdim-bound
		        (:instance flistnp-append (x c) (y (flist-minus (kcoords (vcomb c (firstn (idim) (extend-kbasis))))))
			                          (n (idim)) (m (kdim)))))))

(local-defthmd ili-11
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (let* ((l (firstn (idim) (extend-kbasis)))
	          (d (kcoords (vcomb c l))))
             (equal (append c (flist-minus d))
	            (flistn0 (vdim)))))
  :hints (("Goal" :in-theory (enable vbasisp)
                  :use (ili-9 ili-10 vbasisp-extend-kbasis
		        (:instance vindepp-vcomb-v0 (c (append c (flist-minus (kcoords (vcomb c (firstn (idim) (extend-kbasis)))))))
			                            (l (extend-kbasis))
						    (m (vdim)))))))

(local-defthmd ili-12
  (implies (and (flistnp c n) (flist0p (append c d)))
           (equal (flistn0 n) c)))

(local-defthmd ili-13
  (implies (and (flistnp c (idim)) (equal (wcomb c (ibasis)) (w0)))
           (equal (flistn0 (idim))
	          c))
  :hints (("Goal" :use (ili-11
                        (:instance ili-12 (n (idim)) (d (flist-minus (kcoords (vcomb c (firstn (idim) (extend-kbasis)))))))))))

(in-theory (disable idim (idim)))

(local-defthmd ili-14
  (implies (posp (idim))
           (windepp (ibasis)))
  :hints (("Goal" :use ((:instance ili-13 (c (wdep-coeffs (ibasis))))
                        (:instance ilistnp-wlistnp (x (ibasis)) (n (idim)))
                        (:instance wdepp-wcomb-w0 (l (ibasis)) (m (idim)))))))

(local-defthmd ili-15
  (implies (zp (idim))
           (null (ibasis)))
  :hints (("Goal" :in-theory (disable ilistnp-ibasis)
                  :use (ilistnp-ibasis))))

(defthmd ibasis-lin-indep
  (windepp (ibasis))
  :hints (("Goal" :in-theory (enable windepp)
                  :use (ili-14 ili-15))))

;; It remains to show that ibasis spans the image.  We define the coordinate function as follows:

(defund icoords (x)
  (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis))))

(local-defthmd flistnp-icoords-1
  (implies (in-image-p x)
           (flistnp (vcoords (lin-preimage x) (extend-kbasis)) (vdim)))
  :hints (("Goal" :in-theory (enable in-image-p)
                  :use (vbasisp-extend-kbasis
		        (:instance vbasis-spans (b (extend-kbasis)) (x (lin-preimage x)))))))

(local-defthm flistnp-icoords-2
  (implies (and (flistnp l n) (natp n) (natp k) (<= k n))
           (flistnp (firstn k l) k)))

(defthm flistnp-icoords
  (implies (in-image-p x)
           (flistnp (icoords x) (idim)))
  :hints (("Goal" :in-theory (enable icoords idim)
                  :use (kdim-bound flistnp-icoords-1
			 (:instance flistnp-icoords-2 (l (vcoords (lin-preimage x) (extend-kbasis))) (n (vdim)) (k (idim)))))))

;; If (in-image-p x), then

;;   x = (lin (lin-preimage x))
;;     = (lin (vcomb (vcoords (lin-preimage x) (extend-kbasis)) (kbasis)))
;;     = (lin (v+ (vcomb (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;                       (firstn (idim) (extend-kbasis)))
;;                (vcomb (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;                       (nthcdr (idim) (extend-kbasis)))))
;;     = (w+ (lin (vcomb (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;                       (firstn (idim) (extend-kbasis))))
;;           (lin (vcomb (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;                       (nthcdr (idim) (extend-kbasis))))).

;; The first term is

;;   (lin (vcomb (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;                       (firstn (idim) (extend-kbasis))))
;;     = (lin (vcomb (icoords x) (firstn (idim) (extend-kbasis))))
;;     = (wcomb (icoords x) (lin-list (firstn (idim) (extend-kbasis))))
;;     = (wcomb (icoords x) (ibasis))

;; and the second is

;;   (lin (vcomb (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;               (nthcdr (idim) (extend-kbasis))))
;;     = (lin (vcomb (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))
;;                   (kbasis)))
;;     = w0.

;; Thus, x = (w+ (wcomb (icoords x) (ibasis)) (w0)) = (wcomb (icoords x) (ibasis)).

(local-defthm len-flistnp
  (implies (and (natp n) (flistnp x n))
           (equal (len x) n))
  :hints (("goal" :induct (nthcdr n x))))

(local-defthmd is-1
  (implies (in-image-p x)
           (let* ((p (lin-preimage x)) (c (vcoords p (extend-kbasis))))
	     (and (vp p)
	          (flistnp c (vdim))
		  (flistnp (firstn (idim) c) (idim))
		  (flistnp (nthcdr (idim) c) (kdim))
		  (vlistnp (firstn (idim) (extend-kbasis)) (idim))
		  (vlistnp (nthcdr (idim) (extend-kbasis)) (kdim))
		  (equal (lin (v+ (vcomb (firstn (idim) c) (firstn (idim) (extend-kbasis)))
		                  (vcomb (nthcdr (idim) c) (nthcdr (idim) (extend-kbasis)))))
		         x))))
  :hints (("Goal" :in-theory (enable vbasisp idim in-image-p)
                  :use (vbasisp-extend-kbasis kdim-bound
		        (:instance vbasis-spans (b (extend-kbasis)) (x (lin-preimage x)))
			(:instance vcomb-append (c (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis))))
			                        (d (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis))))
			                        (x (firstn (idim) (extend-kbasis)))
						(y (nthcdr (idim) (extend-kbasis)))
						(n (idim))
						(m (kdim)))
		        (:instance append-firstn-nthcdr (n (idim)) (l (extend-kbasis)))
		        (:instance append-firstn-nthcdr (n (idim)) (l (vcoords (lin-preimage x) (extend-kbasis))))
			(:instance len-vlistnp (n (vdim)) (x (extend-kbasis)))
			(:instance len-flistnp (n (vdim)) (x (vcoords (lin-preimage x) (extend-kbasis))))
			(:instance flistnp-firstn (k (idim)) (n (vdim)) (l (vcoords (lin-preimage x) (extend-kbasis))))
			(:instance flistnp-nthcdr (k (idim)) (n (vdim)) (l (vcoords (lin-preimage x) (extend-kbasis))))
			(:instance vlistnp-firstn (k (idim)) (n (vdim)) (l (extend-kbasis)))
			(:instance vlistnp-nthcdr (k (idim)) (n (vdim)) (l (extend-kbasis)))))))

(local-defthmd is-2
  (implies (in-image-p x)
           (let* ((p (lin-preimage x)) (c (vcoords p (extend-kbasis))))
	     (and (vp p)
	          (flistnp c (vdim))
		  (flistnp (firstn (idim) c) (idim))
		  (flistnp (nthcdr (idim) c) (kdim))
		  (vlistnp (firstn (idim) (extend-kbasis)) (idim))
		  (vlistnp (nthcdr (idim) (extend-kbasis)) (kdim))
		  (equal (w+ (lin (vcomb (firstn (idim) c) (firstn (idim) (extend-kbasis))))
		             (lin (vcomb (nthcdr (idim) c) (nthcdr (idim) (extend-kbasis)))))
		         x))))
  :hints (("Goal" :in-theory (enable idim)
                  :use (kdim-bound is-1
		        (:instance vp-vcomb (n (idim)) (c (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis)))) (l (firstn (idim) (extend-kbasis))))
		        (:instance vp-vcomb (n (idim)) (c (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))) (l (nthcdr (idim) (extend-kbasis))))
		        (:instance lin-v+ (x (vcomb (firstn (idim) c) (firstn (idim) (extend-kbasis))))
			                  (y (vcomb (nthcdr (idim) c) (nthcdr (idim) (extend-kbasis)))))))))

(local-defthmd is-3
  (implies (in-image-p x)
           (let* ((p (lin-preimage x)) (c (vcoords p (extend-kbasis))))
             (equal (lin (vcomb (firstn (idim) c) (firstn (idim) (extend-kbasis))))
	            (wcomb (icoords x) (ibasis)))))
  :hints (("Goal" :in-theory (enable idim icoords ibasis)
                  :use (is-2 flistnp-icoords kdim-bound		  
		        (:instance lin-vcomb (n (idim)) (c (icoords x)) (l (firstn (idim) (extend-kbasis))))))))

(local-defthmd nthcdr-append
  (equal (nthcdr (len x) (append x y))
         y))

(local-defthmd is-4
  (equal (nthcdr (len (firstn (idim) (extend-kbasis))) (extend-kbasis))
         (kbasis))
  :hints (("Goal" :in-theory (enable vbasisp idim)
                  :use (kdim-bound ili-5 vbasisp-extend-kbasis
		        (:instance nthcdr-append (x (firstn (idim) (extend-kbasis))) (y (kbasis)))))))

(local-defthmd is-5
  (equal (len (firstn (idim) (extend-kbasis)))
         (idim))
  :hints (("Goal" :in-theory (enable vbasisp idim)
                  :use (kdim-bound is-4 vbasisp-extend-kbasis
			(:instance len-vlistnp (x (firstn (idim) (extend-kbasis))) (n (idim)))
			(:instance vlistnp-firstn (l (extend-kbasis)) (n (vdim)) (k (idim)))
			(:instance len-vlistnp (n (idim)) (x (firstn (idim) (extend-kbasis))))))))

(local-defthmd is-6
  (equal (nthcdr (idim) (extend-kbasis))
         (kbasis))
  :hints (("Goal" :use (is-4 is-5))))

(local-defthmd is-7
  (implies (in-image-p x)
           (let* ((p (lin-preimage x)) (c (vcoords p (extend-kbasis))))
	     (and (flistnp (nthcdr (idim) c) (kdim))
                  (equal (lin (vcomb (nthcdr (idim) c) (nthcdr (idim) (extend-kbasis))))
	                 (lin (vcomb (nthcdr (idim) c) (kbasis)))))))
  :hints (("Goal" :use (is-2 is-6))))

(local-defthmd is-8
  (implies (and (klistnp x n) (flistnp c n))
           (equal (lin (vcomb c x))
	          (w0)))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(local-defthmd is-9
  (implies (in-image-p x)
           (let* ((p (lin-preimage x)) (c (vcoords p (extend-kbasis))))
             (equal (lin (vcomb (nthcdr (idim) c) (nthcdr (idim) (extend-kbasis))))
	            (w0))))
  :hints (("Goal" :use (is-7 klistnp-kbasis
                        (:instance is-8 (n (kdim)) (c (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))) (x (kbasis)))))))

(defthm ibasis-spans
  (implies (in-image-p x)
           (equal (wcomb (icoords x) (ibasis))
                  x))
  :hints (("Goal" :use (is-2 is-3 is-9))))



#|
;;-----------------------------------------------------

;; A subspace may be specified as the span of a given list of vectors.  The subspace spanned by 
;; a list l is recognized by the following predicate:

(defun-sk spannedp (x l)
  (exists (c)
    (and (flistnp c (len l))
         (equal (vcomb c l) x))))

(defthmd spannedp-lemma
  (implies (and (flistnp c (len l))
                (equal (vcomb c l) x))
	   (spannedp x l)))

(defthmd spannedp-witness-lemma
  (implies (spannedp x l)
           (let ((c (spannedp-witness x l)))
	     (and (flistnp c (len l))
                  (equal (vcomb c l) x)))))

(defun vlistnp-len-induct (l n)
  (if (zp n)
      l
    (vlistnp-len-induct (cdr l) (1- n))))

(defthm vlistnp-len
  (implies (vlistnp l n)
           (vlistnp l (len l)))
  :hints (("Goal" :induct (vlistnp-len-induct l n))))

(defthm spannedp-vp
  (implies (and (vlistnp l n) (spannedp x l))
           (vp x))
  :hints (("Goal" :use (spannedp-witness-lemma
                        (:instance vp-vcomb (n (len l)) (c (spannedp-witness x l)))))))

(defthm spannedp-v0
  (implies (vlistnp l n)
           (spannedp (v0) l))
  :hints (("Goal" :use ((:instance spannedp-lemma (x (v0)) (c (flistn0 (len l))))))))

(defthm spannedp-v-
  (implies (and (vlistnp l n) (spannedp x l))
           (spannedp (v- x) l))
  :hints (("Goal" :use (spannedp-witness-lemma v*f-f1
                        (:instance spannedp-lemma (x (v- x)) (c (flist-scalar-mul (f- (f1)) (spannedp-witness x l))))
			(:instance vcomb-scalar-mul (x (spannedp-witness x l)) (c (f- (f1))) (n (len l)))))))

(defthm spannedp-v+
  (implies (and (vlistnp l n) (spannedp x l) (spannedp y l))
           (spannedp (v+ x y) l))
  :hints (("Goal" :use (spannedp-witness-lemma
                        (:instance spannedp-witness-lemma (x y))
			(:instance spannedp-lemma (x (v+ x y))
			                          (c (flist-add (spannedp-witness x l) (spannedp-witness y l))))
			(:instance vcomb-add (x (spannedp-witness x l)) (y (spannedp-witness y l)) (n (len l)))))))

(defthm spannedp-v*
  (implies (and (vlistnp l n) (spannedp x l) (fp c))
           (spannedp (v* c x) l))
  :hints (("Goal" :use (spannedp-witness-lemma
                        (:instance spannedp-lemma (x (v* c x)) (c (flist-scalar-mul c (spannedp-witness x l))))
			(:instance vcomb-scalar-mul (x (spannedp-witness x l)) (n (len l)))))))

(defthmd spannedp-spannedp
  (implies (spannedp x l)
           (let ((c (spannedp-witness x l)))
             (and (flistnp c (len l))
	          (equal (vcomb c l)
	                 x)))))

;; Thus, if l is linearly independent, then l is a basis for the span of l.

;; A basis of the span of an arbitrary list of vectors l may be constructed as a sublist of l:

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
		       (vcomb c l)))))

;; Given a list of scalars c' such that x = (vcomb c' l'), we construct a list of scalars
;; c = (expand-vcomb c' l) such that x = (vcomb c l):

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

;; The claim follows:

(defthmd vindepp-max-indep
  (implies (and (vlistnp l n) (vp x))
           (iff (spannedp x l)
	        (spannedp x (max-indep l)))))


;;---------------------------------------------------------------------------------------------------------------------
;;  n-space
;;---------------------------------------------------------------------------------------------------------------------

;; The vector space Fn consists of all lists of field elements of length n:

(defund fnp (x n) (flistnp x n))

;; The zero vector:

(defund fn0 (n) (flistn0 n))

;; Vector addition:

(defund fn+ (x y) (flist-add x y))

;; Additive inverse:

(defund fn- (x) (flist-minus x))

;; Scalar multiplication:

(defund fn* (c x) (flist-scalar-mul c x))

;; A list of l of m vectors is recognized by (fmatp l m n).

(defun fnlistp (x m n) (fmatp x m n))

;; The canonical basis is the identity matrix:

(defund fnbasis0 (n) (id-fmat n))

;; A vector is its own coordinate list:

(defun fncoords0 (x) x)

;; Consequently, a list of vectors is its own coordinate matrix:

(defun fncoord-mat (l)
  (if (consp l)
      (cons (fncoords0 (car l))
	    (fncoord-mat (cdr l)))
    ()))
  
(defthmd fncoord-mat-id
  (implies (fnlistp x m n)
           (equal (fncoord-mat x)
	          x)))

;; Linear combination:

(defun fncomb (c l n)
    (if (consp c)
        (fn+ (fn* (car c) (car l))
	     (fncomb (cdr c) (cdr l) n))
      (fn0 n)))


vp          fnp
v+          fn+
v0          fn0
v-          fn-
v*          fn*
vbasis0     fnbasis0
vcoords0    fncoords0
vdim        n
vlistnp     fmatp   
vcomb       fncomb


vp-v0       flistnp-flistn0
vp-v-       flistnp-flist-minus
v+closed    flistnp-flist-add
v+comm      flist-add-comm
v+assoc     flist-add-assoc
v+id        flist-add-flistn0
v+inv       flist-minus-inv
v*closed    flistnp-flist-scalar-mul
v*id        flist-scalar-mul-f1
v*assoc     flist-scalar-mul-assoc
vdistf      flist-scalar-mul-dist-1
vdistv      flist-scalar-mul-dist-2

posp-vdim           (posp n)
vlistnp-basis0      fmatp-id-fmat
flistnp-vcoords0    (fnp x n)
vbasis0-spans
vbasis0-lin-indep

??		  
;;-----------------------------------------------------

;; An mxn matrix a is a list of m elements of Fn.  The row space of a is its span, which is
;; recognized by the following predicate:

(defun-sk fnspannedp (x a n)
  (exists (c)
    (and (flistnp c (len a))
         (equal (fncomb c a n) x))))

(defthm fnspannedp-fnp
  (implies (and (fnlistp a m n) (fnspannedp x a n))
           (fnp x n)))

(defthm fnspannedp-fn0
  (implies (fnlistp a m n)
           (fnspannedp (fn0) a n)))

(defthm fnspannedp-fn-
  (implies (and (fnlistp a m n) (fnspannedp x a n))
           (fnspannedp (fn- x n) a n)))

(defthm fnspannedp-fn+
  (implies (and (fnlistp a m n) (fnspannedp x a n) (fnspannedp y a n))
           (fnspannedp (fn+ x y n) a n)))

(defthm fnspannedp-fn*
  (implies (and (fnlistp a m n) (fnspannedp x a n) (fp c))
           (fnspannedp (fn* c x n) a n)))

;; The nonzero rows of (row-reduce a) form a basis of the row space:

(defun rbasis (a)
  (firstn (row-rank a) (row-reduce a)))
         
(defund rdim (a)
  (len (rbasis a)))

(defthmd rdim-row-rank
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (rdim a)
	          (row-rank a))))

(defthmd fnlistp-rbasis
  (implies (and (fmatp a m n) (posp m) (posp n))
           (fnlistp (rbasis a) (row-rank a))))


(defthmd fnspannedp-rbasis
  (implies (and (fmatp a m n) (posp m) (posp n) (fnp x n))
           (iff (spannedp x a n)
	        (spannedp x (rnasis a) n))))

(defund rbasis-coords (x a n)
  (fnspannedp-witness x (rbasis a) n))

(defthmd fnspannedp-fnspannedp
  (implies (and (fmatp a mn) (posp m) (posp n) (fnspanned x a n))
           (let ((c (rbasis-coords x a n)))
             (and (flistnp c (rdim a))
	          (equal (fncomb c (rbasis a))
	                 x)))))

(defthmd rbasis-lin-indep
  (implies (and (fmatp a mn) (posp m) (posp n)
                (fnlistp c (rdim a) n)
                (equal (fncomb c (rbasis a)) (fn0 n)))
           (equal (flistn0 (rdim a)) c)))

;; Thus, the dimension of the row space of a is the row rank of a.

;; The column rank of a is defined as the row rank of (transpose-mat a).  We shall show that the row rank and the
;; column rank of a are equal.

;; Let b = (rbasis a).  Every row of a is a linear combination of b.  Consequently, for some m x rdim matrix p,
;; a = (fmat* p b).  Let a', b', and p' be the transposes of a, b, and p, of dimensions n x m, n x rdim, and rdim x m.
;; Then a' = (fmat* b' p').  we shall show that p' spans the row space of a'.  Let x be in the row space of a', i.e.,
;; (spannedp x a').  Thenb for some c, (flistnp c rdim) and x = (fncomb c a'), which may be expressed as

;;     x = (fncomb c a')
;;       = (car (fmat* (list c) a'))
;;       = (car (fmat* (list c) (fmat* b' p')))
;;       = (car (fmat* (fmat* (list c) b') p'))
;;       = (car (fmat* (list (car (fmat* (list c) b'))) p'))
;;       = (fncomb (car (fmat* (list c) b')) p').

;; Thus, (fnspannedp x p').  By exists-unspanned-len<vdim, since (rbasis a') is a basis of the row space of a' of length
;; (row-rank a'), (row-rank a') <= (row-rank a).  Similarly, (row-rank a) <= (row-rank a').

(defthmd row-column-rank
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (row-rank (transpose-mat a))
	          (row-rank a))))

;;-----------------------------------------------------

;; We have shown that the solutions of a homogeneous system of linear equations with mxn coefficient matrix a form a 
;; subspace of Fn recognized by the predicate esol0.  We shall show that the dimension of this subspace is the 
;; difference n - (row-rank a).

;; This subspace may be viewed as the kernel of the linear transformation from Fn to Fm defined by a, the image of
;; which is the subspace of Fm recognized by the following predicate:

(defun-sk exists-solution (a b)
  (exists (x)
    (and (fnp x n)
         (solutionp x a b))))

;; This is the same subspace as the row space of the transpose of a:

(defthmd exists-solution-spannedp
  (implies (and (fmatp a m n) (posp m) (posp n))
           (iff (exists-solution a b)
	        (fnspannedp b (transpose-mat a)))))

;; Thus, the dimension of the image is (row-rank a).  One way to compute the dimension of the kernel is by functional
;; instantiation of idim+kdim.  We shall take a different approach, explicitly deriving a natural basis for the
;; solution space.

;; Let ar = (row-reduce a), q = (row-rank a), aq = (first-rows q ar), l = (lead-inds aq) and f = (free-inds aq n).
;; Corresponding to each member j of f, we construct a basis element (c_0 ... c_n-1). The kth entry c_k is defined as
;; follows:

;;   (1) If k = j, then c_k = 1;
;;   (2) If k is in f and k != j, then c_k = 0;
;;   (3) If k is the ith member of l, then c_k = (f- (entry i j aq)):

(defun solbasis-elt-aux (j l aq k n)
  (if (and (natp k) (natp n) (< k n))
      (cons (if (member-equal k l)
		(f- (entry (index k l) j aq))
	      (if (= k j)
	          (f1)
	        (f0)))		
            (solbasis-elt-aux j l aq (1+ k) n))
    ()))

(defun solbasis-elt (j l aq n)
  (solbasis-elt-aux j l aq 0 n))

(defun solbasis-aux (a f l n)
  (if (consp f)
      (cons (solbasis-elt (car f) l a n)
            (solbasis a (cdr f) l n))))

(defund solbasis (a)
  (let* ((ar (row-reduce a))
         (q (num-nonzero-rows ar))
         (aq (first-rows q ar))
         (l (lead-inds aq))
         (f (free-inds aq n)))
    (solbasis-aux aq f l (len (car a)))))

(defund soldim (a)
  (len (solbasis a)))

(defthmd soldim-val
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (soldim a)
	          (- (len (car a)) (row-rank a)))))

;; We shall prove that (solbasis a) is a basis of the solution space.  First we show that each basis element is indeed
;; a solution:

(defthmd sol0p-solbasis-elt
  (let* ((ar (row-reduce a))
         (q (num-nonzero-rows ar))
         (aq (first-rows q ar))
         (l (lead-inds aq))
         (f (free-inds aq n)))
    (implies (and (fmatp a m n) (posp m) (posp n)
                  (member j f))
	     (sol0p (solbasis-elt j l aq k n) a))))

;; Therefore, (solbasis a) is a list of solutions:

(defun sol0listp (l n a)
  (if (zp n)
      (null l)
    (and (consp l)
         (sol0p (car l) a)
	 (sol0listp (cdr l) (1- n) a))))

(defthmd sol0listp-solbasis
  (implies (and (fmatp a m n) (posp m) (posp n))
           (sol0listp (solbasis a) (soldim a) a)))

;; The ith entry of a linear combination of (solbasis a) is the coefficient of the ith free index: 

(defthmd nth-fncomb-solbasis
  (implies (and (fmatp a m n) (posp m) (posp n)
                (flistnp c (soldim a))
		(nat i) (< i n))
	   (equal (nth (nth i (free-inds a n)) (fncomb c (solbasis a)))
	          (nth i c))))

;; It follows that (solbasis a) is linearly independent:

(defthmd solbasis-lin-indep
  (implies (and (fmatp a m n) (posp m) (posp n)
                (flistnp c (soldim a))
                (equal (fncomb c (solbasis a)) (fn0 n)))
	   (equal (flistn0 (soldim a)) c)))
 
;; The coordinates of a solution with respect to (solbasis a):

(defun solcoords-aux (x f)
  (if (consp f)
      (cons (nth (car f) x)
            (solcoords x (cdr f)))
    ()))

(defund solcoords (x a)
  (let* ((ar (row-reduce a))
         (q (num-nonzero-rows ar))
         (aq (first-rows q ar))
         (f (free-inds aq (len (car a)))))
    (solcoords-aux x d)))

(defthmd nth-fncomb-solbasis
  (implies (and (fmatp a m n) (posp m) (posp n)
                (sol0p x a))
	   (flistnp (solcoords x a) (soldim a))))

;; Let x' = (fncomb (solcoords x a) (solbasis a)).  By nth-fncomb-solbasis, x and x' agree at every free index,
;; and it follows that x' = x.  Thus, (solbasis a) spans the solution space:

(defthmd solbasis-spans
 (implies (and (fmatp a m n) (posp m) (posp n)
               (sol0p x a))
	  (equal (fncomb (solcoords x a) (solbasis a))
	         x)))


;;---------------------------------------------------------------------------------------------------------------------

;; Let's try this again:

;; Let (vp x).  By lin-mat-lin, (in-kernel-p x) iff the following equation holds:

;;   (fmat* (row-mat (vcoords0 x)) (lin-mat)) = (row-mat (flistn0 (wdim))).

;; Let a = (transpose-mat (lin-mat)).  Taking the transpose of both sides of the above equation yields

;;   (fmat* a (col-mat (vcoords0 x))) = (col-mat (flistn0 (wdim))).

;; Thus, x is in the kernel iff (vcoords0 x) is a solution of the homogeneous system of linear equations with coordinate 
;; matrix a.  See the discussion of the function sol0p at the end of the book "reduction".

(defthmd in-kernel-p-sol0p
  (iff (in-kernel-p x)
       (sol0p (vcoords0 x) (transpose-mat (lin-mat)))))

;; We shall use this characterization to construct a basis of the kernel, kbasis.  Let ar = (row-reduce a),
;; q = (num-nonzero-rows ar) = (row-rank a), l = (lead-inds ar) and f = (free-inds ar n).  Then (len l) = q and
;; (len f) = vdim - q.  Each member of kbasis corresponds to a member of f.

;; Given j in f, we first define the coordinate list c with respect to vbasis0 of the kbasis element corresponding to j.
;; For 0 <= i < vdim, (nth i c) = (kbasis-coord i j), which is defined as follows:

;; (a) If i is in l, let k = (index i l), i.e., i = (nth k l).  Then (nth i c)) = (f- (entry k j ar)).
;; (b) If i = j, then (nth i c) = (f1).
;; (c) If i is in f and i !+ j, then (nth i c) = (f0).

(defun kbasis-coord (i j)
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
	 (l (lead-inds ar)))
    (if (member i l)
        (f- (entry (index i l) j ar))
      (if (= i j)
          (f1)
        (f0)))))

;; Thus, c = (kbasis-elt-coords j), defined as follows:

(defun kbasis-coords-aux (i j)
  (declare (xargs :measure (nfix (- (vdim) i))))
  (if (and (natp i) (< i (vdim)))
      (cons (kbasis-coord i j)
            (kbasis-coords-aux (1+ i) j))
    ()))

(defund kbasis-coords (j) (kbasis-coords-aux 0 j))

;; The kbasis element corresponding to j is the vector (vcomb c (vbasis0)).  Thus, kbasis is defined as follows:

(defun kbasis-aux (f)
  (if (consp f)
      (cons (vcomb (kbasis-coords (car f)) (vbasis0))
            (kbasis-aux (cdr f)))
    ()))

(defund kbasis ()
  (let ((ar (row-reduce (transpose-mat (lin-mat)))))
    (kbasis-aux (free-inds ar (vdim)))))

(defund kdim () (len (kbasis)))

;; We must show that kbasis is a linearly independent list of kernel vectors that spans the kernel.

;; Given i < kdim, let j = (nth i f).  Then

;;   (nth i (kbasis)) =  (vcomb (kbasis-coords j) (vbasis0)),

;; which implies

;;   (vcoords0 (nth i (kbasis))) = (kbasis-coords j).

;; Thus, to prove that every member of kbasis is in the kernel, it suffices to show that for all j in f,

;;   (sol0p (kbasis-coords j) a).

;; Let x = (kbasis-coords j).  According to the lemma sol0p-suff, it suffices to prove that for all k < q,

;;   (nth (nth k l) x) = (f- (fdot-select f (nth k aq) x).

;; But according to the definition of kbasis-coords, both sides of this equation reduce to (f- (entry k j ar)).
;; Thus, we have

(defthm klistnp-kbasis
  (klistnp (kbasis) (kdim)))

;; Next, we prove that kbasis is linearly independent.

;; Given (flistnp c n), (vlistnp l n), and i < vdim, we derive a formula for (nth i (vcoords0 (vcomb c l))):

(defun nth-vcomb (j c l)
  (if (consp c)
      (v+ (v* (car c) (nth j (vcoords0 (car l))))
	  (nth-vcomb j (cdr c) (cdr l)))
      (f0)))

(defthmd nth-vcomb-val
  (implise (and (flistnp c n) (vlistnp l n)
                (natp i) (< j (vdim)))
	   (equal (nth j (vcoords0 (vcomb c l)))
	          (nth-vcomb j c l))))

;; We apply this result to the case l = (kbasis), n = kdim, and j = (nth i f), where i < kdim.  By construction of
;; kbasis, (nth-vcomb j c (kbasis)) = (nth i c).  Instantiating nth-vcomb-val, we have

(defthmd nth-vcomb-kbasis
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (implies (and (flistnp c (kdim)) (natp i) (< i (kdim)))
              (equal (nth (nth i f) (vcoords0 (vcomb c (kbasis))))
	             (nth i c)))))

;; Now suppose (vcomb c (kbasis)) = 0. Then (vcoords0 (vcomb c (kbasis))) = (flistn0 (kbasis)).  It follows that
;; (nth i c) = 0 for all i < kdim, and therefore c = (flistn0 (kdim):

(defthmd vcomb-kbasis-v0
  (implies (and (flistnp c (kdim)) (equal (vcomb c (kbasis)) (v0))
                (natp i) (< i (kdim)))
	   (equal (nth i c) (f0))))

(defthmd vcomb-kbasis-v0
  (implies (and (flistnp c (kdim)) (equal (vcomb c (kbasis)) (v0)))
	   (equal (flistn0 (kdim)) c)))

;; Thus, kbasis is linearly independent:

(defthmd vindepp-kbasis
  (vindepp (kbasis)))

;; To prove that kbasis spans the kernel, we define the following coordinate function:

(defun kcoords-aux (x f)
  (if (consp f)
      (cons (nth (car f) (vcoords0 x))
            (kcoords-aux x (cdr f)))
    ()))

(defund kcoords (x)
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (kcoords-aux x f)))

;; The first requirement of this function is trivial:

(defthm flistnp-kcoords
  (implies (in-kernel-p x) (flistnp (kcoords x) (kdim))))

;; Another immediate consequence of the definition:

(defthmd nth-kcoords
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (and (natp i) (< i (kdim)))
             (equal (nth i (kcoords x))
	            (nth (nth i f) (vcoords0 x))))))

;; We must show that if (in-kernel-p x), then (vcomb (kcoords x) (kbasis)) = x.  Let y = (vcomb (kcoords x) (kbasis).
;; By vbasis0-spans, it suffices to show that (vcoords0 y) = (vcoords0 x).  But since (sol0p x a) and (sol0p y a), it
;; follows from sol0p-necc that it suffices to show that for all j in f, (nth j (vcoords0 y)) = (nth j (vcoords0 x)).
;; Instantiating nth-vcomb-kbasis with i = (index j f) and c = (kcoords x), we have

;;    (nth j (vcoords0 y)) = (nth (nth i f) (vcoords0 (vcomb (kcoords x) (kbasis))))
;;                         = (nth i (kcoords x))
;;                         = (nth j (vcoords0 x)).

(defthm kbasis-spans
  (implies (in-kernel-p x)
           (equal (vcomb (kcoords x) (kbasis))
                  x)))






;; Given k < kdim, let j = (nth k f).  Then

;;   (nth k (kbasis)) =  (vcomb (kbasis-coords j) (vbasis0)),

;; which implies

;;   (vcoords0 (nth k (kbasis))) = (kbasis-coords j).

;; To prove that (nth k (kbasis)) is in the kernel, we must show that for i < q,

;;   (fdot (row i aq) (kbasis-coords j) = 0.

;; Let r = (row i aq) and c = (kbasis-coords j).  There is only 1 leading index at which r is nonzero, nasmely

;;   (nth (nth i l) r) = 1,

;; and only 1 free index at which c is nonzero, namly

;;   (nth j c) = 1.

;; Therefore, (fdot r c) has at most 2 nonzero terms, the sum of which is

;;   (nth (nth i l) r) * (nth (nth i l) c) + (nth j r) * (nth j c) = (nth (nth i l) c) + (nth j r).

;; But according to the definition of kbasis-coords, (nth (nth i l) c) = (f- (nth j r)), and hence (fdot r c) = 0.
;; Thus, every element of kbasis is in the kernel:


|#
