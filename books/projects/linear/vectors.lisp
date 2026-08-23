(in-package "DM")

(include-book "projects/linear/support/reduction" :dir :system)
(local (include-book "support/vectors"))

;; This formalization of vector spaces is not complete, but currently meets our first objective of providing the results
;; required for our development of Galois theory (lemmas vdepp-if->-dim, injection-dim-<=, and injection-dim-=).

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
  (implies (vp x) (equal (v+ (v0) x) x)))

(defthm v+inv-comm
  (implies (vp x) (equal (v+ (v- x) x) (v0))))

(defthm f0*v0
  (implies (vp x) (equal (v* (f0) x) (v0))))

(defthm c*v0
  (implies (fp c) (equal (v* c (v0)) (v0))))

(defthmd v-unique
  (implies (and (vp x) (vp y) (equal (v+ x y) (v0)))
           (equal (v- x) y)))

(defthmd v*f-f1
  (implies (vp x)
           (equal (v* (f- (f1)) x)
	          (v- x))))

(defthm vp-vcomb
  (implies (and (flistnp c n) (vlistnp l n))
	   (vp (vcomb c l))))

(defthm len-vlistnp
  (implies (and (natp n) (vlistnp x n))
           (equal (len x) n)))

(defthm vp-nth-vlistnp
  (implies (and (vlistnp x n) (natp n) (natp j) (< j n))
           (vp (nth j x))))

(defthmd vcomb-add
  (implies (and (natp n) (vlistnp l n) (flistnp x n) (flistnp y n))
	   (equal (vcomb (flist-add x y) l)
		  (v+ (vcomb x l) (vcomb y l)))))

(defthmd vcomb-scalar-mul
  (implies (and (natp n) (vlistnp l n) (flistnp x n) (fp c))
	   (equal (vcomb (flist-scalar-mul c x) l)
		  (v* c (vcomb x l)))))

(defthm vcomb-flistn0
  (implies (vlistnp l n)
           (equal (vcomb (flistn0 n) l)
	          (v0))))

(defthmd vcomb-append
  (implies (and (flistnp c n) (flistnp d m)
                (vlistnp x n) (vlistnp y m)
		(natp n) (natp m))
	   (equal (vcomb (append c d) (append x y))
	          (v+ (vcomb c x) (vcomb d y)))))

;; The list of coordinates of a vector is unique:

(defthmd vcoords0-unique
  (implies (and (vp x) (flistnp c (vdim))
		(equal (vcomb c (vbasis0)) x))
	   (equal (vcoords0 x) c)))

;; In particular, since (vcomb (flistn0 (vdim)) (vbasis0)) = (v0), (vcoords0 (v0)) = (flistn0 (vdim)):

(defthm vcoords0-v0
  (equal (vcoords0 (v0))
         (flistn0 (vdim))))

;; Coordinates of a sum:

(defthmd vcoords0-v+
  (implies (and (vp x) (vp y))
           (equal (vcoords0 (v+ x y))
	          (flist-add (vcoords0 x) (vcoords0 y)))))

;; Coordinates of a scalar product:

(defthmd vcoords0-v*
  (implies (and (vp x) (fp c))
           (equal (vcoords0 (v* c x))
	          (flist-scalar-mul c (vcoords0 x)))))


;;---------------------------------------------------------------------------------------------------------------------
;;  Linear Dependence
;;---------------------------------------------------------------------------------------------------------------------

;; A list of vectors l is linearly dependent if v0 is a nontrivial linear combination of l.  Our objective is an
;; algorithmic definition of this property.

;; We first define the coordinate matrix of a list of vectors:

(defun vcoord-mat (l)
  (if (consp l)
      (cons (vcoords0 (car l))
	    (vcoord-mat (cdr l)))
    ()))

(defthm fmatp-vcoord-mat
  (implies (vlistnp l m)
           (fmatp (vcoord-mat l) m (vdim))))

;; Assume (vlistnp l m), where m > 0.  We shall show that the coordinates of any linear combination (vcomb c l) of l
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

;; Now suppose m > 1 and assume the claim is true when c and l are repaced by (cdr c) and (cdr l).
;; Let a = (vcoord-mat l).  We shall show first that

;;    (car (fmat* (list c) a) = (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))).

;; To prove this, it suffices to show that for j < vdim, the jth members of these lists are equal.  But

;;    (nth j (car (fmat* (list c) a))) = (entry 0 j (fmat* (list c) a))
;;                                     = (fdot c (col j a))
;;                                     = (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a))))

;; and

;;    (nth j (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))))
;;      = (f+ (f* (car c) (nth j (car a))) (entry 0 j (fmat* (list (cdr c)) (cdr a))))
;;      = (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a)))).

;; Now complete the proof:

;;   (vcomb (car (fmat* (list c) a)) (vbasis0))
;;     = (vcomb (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))) (vbasis0))
;;     = (v+ (v* (car c) (vcomb (car a) (vbasis0)))
;;           (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0)))
;;     = (v+ (v* (car c) (car l))
;;           (vcomb (cdr c) (cdr l)))
;;     = (vcomb c l).

(defthmd vcoords0-vcomb
  (implies (and (posp m) (vlistnp l m) (flistnp c m))
	   (equal (vcoords0 (vcomb c l))
		  (car (fmat* (list c) (vcoord-mat l))))))

;; This formula is the basis of our definition of linear independence.  Note that the null list is vacuously linearly 
;; independent.  A non-null list is defined to be linearly independent if the row-rank of its coordinate matrix is its
;; length:

(defund vindepp (l)
  (or (null l)
      (equal (row-rank (vcoord-mat l))
             (len l))))

(defund vdepp (l)
  (not (vindepp l)))

;; To confirm that the definition has the intended meaning, we first show that if (vdepp l), then (v0) is a nontrivial
;; linear combination of l.  The required coefficients may be constructed as follows:

(defun vdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (vcoord-mat l))))

(defthmd fmat*-nth
  (implies (and (fmatp a m n) (fmatp b n p) (posp m) (natp n) (natp p) (natp i) (< i m))
           (equal (car (fmat* (list (nth i a)) b))
	          (nth i (fmat* a b)))))

;; Let m = (len l), a = (vcoord-mat l), c = (vdep-coeffs l), and p = (row-reduce-mat (vcoord-mat l)).  Then c is the last
;; row of p.  Since p is invertible, (vdep-coeffs l) != (flistn0 m).  But

;;   (vcoords0 (vcomb c l)) = (car (fmat* (list c) a))
;;                         = (nth (1- m) (fmat* p a))
;;                         = (nth (1- m) (row-reduce a))
;;                         = (flistn0 (vdim)),

;; which implies (vcomb c l) = (v0):

(defthmd vdepp-vcomb-v0
  (implies (and (posp m) (vlistnp l m) (vdepp l))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (equal c (flistn0 m)))
		  (equal (vcomb c l) (v0))))))

;; Note that the axiom vbasis0-lin-indep ensures that vbasis0 is a linearly independent list:

(defthm vindepp-vbasis0
  (vindepp (vbasis0)))

;; We must also show that if (vindepp l), then (v0) is not a nontrivial linearly combination of l.  Assume (flistnp c m).
;; We must show that if (car (fmat* (list c) a)) = (flistn0 (vdim)), then c = (flistn0 m).  We first show that this holds
;; if a is replaced by r = (row-reduce a).  Let i < m and j = (nth i (lead-inds r)).  By fmat*-entry,

;;    (nth j (car (fmat* (list c) r))) = (entry 0 j (fmat* (list c) r)) = (fdot c (col j r)),

;; and it follows from  nth-col-lead-inds that (fdot c (col j r)) = (nth i c):

(defthmd entry-fmat*-row-echelon-p
  (implies (and (posp m) (posp n) (fmatp r m n)
                (row-echelon-p r) (= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (nth (nth i (lead-inds r)) (car (fmat* (list c) r)))
	          (nth i c))))

;; But since (car (fmat* (list c) a)) = (flistn0 (vdim)), (nth i c) = (f0) for all i, i.e., c = (flistn0 m):

(defthm row-echelon-p-vindepp
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n)))
	   (equal c (flistn0 m)))
  :rule-classes ())

;; Suppose (vcomb c l) = (v0).  Then (car (fmat* (list c) a)) = (vcoords0 (v0)) = (flistn0 (vdim)).  Let r = (row-reduce a),
;; p = (row-reduce-mat a), and c' = (car (fmat* (list c) (inverse-mat p))). Then r = (fmat* p a), which implies
;; a = (fmat* (inverse-mat p) r) and

;;   (fmat* (list c') r) = (fmat* (fmat* (list c) (inverse-mat p)) r)
;;                       = (fmat* (list c) (fmat* (inverse-mat p) r))
;;                       = (fmat* (list c) a):

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
	            (fmat* (list c) a)))))

;; Thus, (car (fmat* (list c') r) = (flistn0 (vdim)).  By row-echelon-p-vindepp, c' = (flistn0 m), which implies

;;   (list c) = (fmat* (list (flistn0 m)) p) = (list (flistn0 m))

;; and we have the following:

(defthm vindepp-vcomb-v0
  (implies (and (natp m)
		(vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (equal c (flistn0 m)))
  :rule-classes ())

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
	   (not (equal (nth j l) (v0)))))

(defthm v0-not-member-vindepp
  (implies (and (natp m)
		(vlistnp l m)
		(vindepp l))
	   (not (member (v0) l))))

;; A list of length 1 is linearly dependent iff its member is v0:

(defthmd vdepp-v0
  (implies (vp x)
           (iff (vdepp (list x))
                (equal (v0) x))))

;; If m > vdim, then since (fmatp a m (vdim)), (row-rank a) <= vdim < m, i.e., (vdepp l):

(defthmd vdepp-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp l)))

;; Combining vdepp-vcomb-v0 with vdepp-if->-dim, we construct a linear dependency of any list of more than vdim vectors:

(defthmd vcomb-v0-if->-dim
  (implies (and (posp m) (vlistnp l m) (> m (vdim)))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (equal c (flistn0 m)))
		  (equal (vcomb c l) (v0))))))

;; Let l be a list of vectors and let x be a vector.  Suppose l is linearly independent and (cons x l) is linearly
;; dependent.  We shall construct a list of scalars (vcoords x l) such that x = (vcomb (vcoords x l) l).  By
;; vdepp-vcomb-v0,  we have a list c = (vdep-coeffs (cons x b)) such that

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

(defthmd vdepp-vcomb
  (implies (and (vlistnp l n) (natp n) (vp x) (vindepp l) (vdepp (cons x l)))
           (and (flistnp (vcoords x l) n)
	        (equal (vcomb (vcoords x l) l) x))))

;; Conversely, suppose  x is a linear combination of l, say x = (vcomb c l).  Let c' = (cons (f- (f1)) c).
;; Then (vcomb c' (cons x l)) = (v+ (v* (f- (f1)) x) (vcomb c l)) = (v+ (v- x) x) = (v0), and by vindepp-vcomb-v0,
;; (vdepp (cons x l)):

(defthmd vcomb-vdepp
  (implies (and (vlistnp l n) (flistnp c n) (natp n))
           (vdepp (cons (vcomb c l) l))))

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
	   (equal (flistn0 (len l)) c)))

(defthmd vindepp-sk-witness-lemma
  (let ((c (vindepp-sk-witness l)))
     (implies (implies (and (flistnp c (len l))
                            (equal (vcomb c l) (v0)))
	               (equal (flistn0 (len l)) c))
	      (vindepp-sk l))))

(defthmd vindepp-equivalence
  (implies (and (natp m) (vlistnp l m))
           (iff (vindepp-sk l)
	        (vindepp l))))

(defund vdepp-sk (l)
  (not (vindepp-sk l)))

;; The main motivation for this equivalent formulation is that it will facilitate functional instantiation of lemmas
;; pertaining to linear independence.  Functional instantiation of any lemma that refers to a function that depends
;; on vindepp would require definitions analogous to those of vindepp and all of its supporting functions, including
;; those pertaining to row reduction.  Functional instantiation of the following is much simpler (see, for example
;; vdepp-sk-if->-sdim):

(defthmd vdepp-sk-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp-sk l)))


;;---------------------------------------------------------------------------------------------------------------------
;;  Bases
;;---------------------------------------------------------------------------------------------------------------------

;; We define a vbasis to be a linearly independent list of vdim vectors:

(defund vbasisp (l)
  (and (vlistnp l (vdim))
       (vindepp l)))

;; Obviously, the canonical basis is a vbasis:

(defthm vbasisp-vbasis0
  (vbasisp (vbasis0)))

;; Let b  be a vbasis.  By vdepp-if->-dim, for any vector x, the list (cons x b) is linearly dependent, and therefore, 
;; by vdepp-vcomb, b spans the space:

(defthmd vbasis-spans
  (implies (and (vbasisp b) (vp x))
           (and (flistnp (vcoords x b) (vdim))
	        (equal (vcomb (vcoords x b) b)
	               x))))

;; By functional instantiation of vcoords0-unique, this representation is unique:

(defthmd vcoords-unique
  (implies (and (vbasisp b) (vp x) (flistnp c (vdim))
		(equal (vcomb c b) x))
	   (equal (vcoords x b) c)))

;; Consequently,

(defthm vcoords-vcoords0
  (implies (vp x)
           (equal (vcoords x (vbasis0))
	          (vcoords0 x))))

;; The coordinates of a basis element:

(defthm vcomb-funit
  (implies (and (natp n) (natp j) (< j n) (vlistnp l n))
           (equal (vcomb (funit j n) l)
	          (nth j l))))

(defthm vcoords-nth-basis
  (implies (and (vbasisp b) (natp j) (< j (vdim)))
           (equal (vcoords (nth j b) b)
	          (funit j (vdim)))))

;; Given a vbasis b and a list of vectors l, consider the matrix of coordinates of the members of l with respect to b:

(defun vbasis-mat (l b)
  (if (consp l)
      (cons (vcoords (car l) b)
            (vbasis-mat (cdr l) b))
    ()))

(defthmd fmatp-basis-mat
  (implies (and (vbasisp b) (vlistnp l m))
           (fmatp (vbasis-mat l b) m (vdim))))

;; By functional instantiation of vcoords0-vcomb, for any linear combination (vcomb c l) of l, we have the following 
;; formula for (vcoords (vcomb c l) b):

(defthmd vcoords-vcomb
  (implies (and (vbasisp b) (posp m) (vlistnp l m) (flistnp c m))
	   (equal (vcoords (vcomb c l) b)
		  (car (fmat* (list c) (vbasis-mat l b))))))

;; Combining vcoords-vcom and vbasis-spans, we have the following formula relating coordinates with respect to
;; 2 vbases:

(defthmd vcoords-convert
  (implies (and (vbasisp b1) (vbasisp b2) (vp x))
           (equal (fmat* (list (vcoords x b1)) (vbasis-mat b1 b2))
	          (list (vcoords x b2)))))

(defthmd fmatp-basis-basis-mat
  (implies (and (vbasisp b1) (vbasisp b2))
           (fmatp (vbasis-mat b1 b2) (vdim) (vdim))))

;; Now let p = (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1)).  For all x,

;;    (fmat* (list (vcoords x b1)) p)
;;      = (fmat* (list (vcoords x b1)) (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1)))
;;      = (fmat* (fmat* (list (vcoords x b1)) (vbasis-mat b1 b2)) (vbasis-mat b2 b1))
;;      = (fmat* (list (vcoords x b2)) (vbasis-mat b2 b1))
;;      = (list (vcoords x b1)).

;; In particular, for i < vdim,

;;    (row i p) = (car (fmat* (list (funit i (vdim))) p)) = (funit i (vdim)),

;; and hence p = (id-fmat (vdim)):

(defthmd compose-basis-basis-mats-id-fmat
  (implies (and (vbasisp b1) (vbasisp b2))
           (equal (fmat* (vbasis-mat b1 b2) (vbasis-mat b2 b1))
	          (id-fmat (vdim)))))

;; Thus, by invertiblep-inverse, we have the following:

(defthmd vbasis-mat-inverse
  (implies (and (vbasisp b1) (vbasisp b2))
           (and (invertiblep (vbasis-mat b1 b2) (vdim))
	        (equal (inverse-mat (vbasis-mat b1 b2))
		       (vbasis-mat b2 b1)))))
;;---------------------------------------------------------------------------------------------------------------------

;; We shall show that any linearly independent list of vectors may be extended to a vbasis.  To this end, given a
;; linearly independent list l with (len l) = m < vdim,  we shall construct a vector (vunspanned l) that is not a linear
;; combination of l.  Once again, let a = (vcoord-mat l), p = (row-reduce-mat a), and r = (row-reduce a).  We may define
;; (vunspanned l) to be a member of vbasis0 that corresponds to any of the indices of (free-inds r (vdim)).  We
;; arbitrarily select the vbasis element corresponding to (car (free-inds r (vdim))):

(defund vunspanned (l)
  (nth (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))
       (vbasis0)))

(defthmd vp-vunspanned
  (implies (and (vlistnp l m) (posp m) (< m (vdim)))
           (vp (vunspanned l))))

;; Let u = (vunspanned l).  Suppose (flistnp c m) and u = (vcomb c l).  Let c' = (car (fmat* (list c) (inverse-mat p))).
;; By fmat*-vcomb-row-reduce and vcoords0-vcomb,

;;     (car (fmat* (list c') r)) = (car (fmat* (list c) a)) = (vcoords0 u). 

;; Let i < m and j = (nth i (lead-inds r)).  Then by entry-fmat*-row-echelon-p,

;;    (nth i c') = (nth j (car (fmat* (list c') r))) = (nth j (vcoords0 u)) = (f0),

;; and hence c' = (flistn0 m), which implies (vcoords0 u) = (flistn0 (vdim)), a contradiction.

(defthmd vunspanned-not-vcomb
  (implies (and (posp m)
		(< m (vdim))
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (not (equal (vunspanned l) (vcomb c l)))))

;; We now invoke vdepp-vcomb:

(defthmd vindepp-cons-vunspanned
  (implies (and (vlistnp l m) (vindepp l) (posp m) (< m (vdim)))
           (vindepp (cons (vunspanned l) l))))

;; The extension of l to a vbasis is constructed recursively:

(defun extend-to-basis (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))))
  (if (and (vlistnp l (len l)) (vindepp l) (< (len l) (vdim)))
      (extend-to-basis (cons (vunspanned l) l))
    l))

;; The following is proved by induction:

(defthmd vbasisp-extend-to-basis
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l))))

(defthmd nthcdr-extend-to-basis
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (equal (nthcdr (- (vdim) (len l)) (extend-to-basis l))
                  l)))


;;---------------------------------------------------------------------------------------------------------------------
;;  Linear Transformations
;;---------------------------------------------------------------------------------------------------------------------

;; In order to formalize the notion of a linear transformation, we shall require a second vector space, W:

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
  (implies (wp x) (equal (w+ (w0) x) x)))

(defthm w+inw-comm
    (implies (wp x) (equal (w+ (w- x) x) (w0))))

(defthm f0*w0
  (implies (wp x) (equal (w* (f0) x) (w0))))

(defthm c*w0
  (implies (fp c) (equal (w* c (w0)) (w0))))

(defthmd w-unique
  (implies (and (wp x) (wp y) (equal (w+ x y) (w0)))
           (equal (w- x) y)))

(defthmd w*f-f1
  (implies (wp x)
           (equal (w* (f- (f1)) x)
	          (w- x))))

(defthm wp-wcomb
  (implies (and (flistnp c n) (wlistnp l n))
	   (wp (wcomb c l))))

(defthm len-wlistnp
  (implies (and (natp n) (wlistnp x n))
           (equal (len x) n)))

(defthm wp-nth-wlistnp
  (implies (and (wlistnp x n) (natp n) (natp j) (< j n))
           (wp (nth j x))))

(defthmd wcomb-add
  (implies (and (natp n) (wlistnp l n) (flistnp x n) (flistnp y n))
	   (equal (wcomb (flist-add x y) l)
		  (w+ (wcomb x l) (wcomb y l)))))

(defthmd wcomb-scalar-mul
  (implies (and (natp n) (wlistnp l n) (flistnp x n) (fp c))
	   (equal (wcomb (flist-scalar-mul c x) l)
		  (w* c (wcomb x l)))))

(defthmd wcoords0-unique
  (implies (and (wp x) (flistnp c (wdim))
		(equal (wcomb c (wbasis0)) x))
	   (equal (wcoords0 x) c)))

(defthm wcomb-flistn0
  (implies (wlistnp l n)
           (equal (wcomb (flistn0 n) l)
	          (w0))))

(defthm wcoords0-w0
  (equal (wcoords0 (w0))
         (flistn0 (wdim))))


(defthmd wcoords0-w+
  (implies (and (wp x) (wp y))
           (equal (wcoords0 (w+ x y))
	          (flist-add (wcoords0 x) (wcoords0 y)))))

(defthmd wcoords0-w*
  (implies (and (wp x) (fp c))
           (equal (wcoords0 (w* c x))
	          (flist-scalar-mul c (wcoords0 x)))))

;;  Linear Dependence

(defun wcoord-mat (l)
  (if (consp l)
      (cons (wcoords0 (car l))
	    (wcoord-mat (cdr l)))
    ()))

(defthm fmatp-wcoord-mat
  (implies (wlistnp l m)
           (fmatp (wcoord-mat l) m (wdim))))

(defthmd wcoords0-wcomb
  (implies (and (posp m) (wlistnp l m) (flistnp c m))
	   (equal (wcoords0 (wcomb c l))
		  (car (fmat* (list c) (wcoord-mat l))))))

(defund windepp (l)
  (or (null l)
      (equal (row-rank (wcoord-mat l))
             (len l))))

(defund wdepp (l)
  (not (windepp l)))

(defun wdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (wcoord-mat l))))

(defthmd wdepp-wcomb-w0
  (implies (and (posp m) (wlistnp l m) (wdepp l))
	   (let ((c (wdep-coeffs l)))
	     (and (flistnp c m)
		  (not (equal c (flistn0 m)))
		  (equal (wcomb c l) (w0))))))

(defthm windepp-wbasis0
  (windepp (wbasis0)))

(defthm windepp-wcomb-w0
  (implies (and (natp m)
		(wlistnp l m)
		(windepp l)
		(flistnp c m)
		(Equal (wcomb c l) (w0)))
	   (equal c (flistn0 m)))
  :rule-classes ())

(defthmd wdep-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (wdepp l)))

(defund wcoords (x l)
  (if (null l)
      ()
    (let ((c (wdep-coeffs (cons x l))))
      (flist-scalar-mul (f- (f/ (car c))) (cdr c)))))

(defthmd wdepp-wcomb
  (implies (and (wlistnp l n) (natp n) (wp x) (windepp l) (wdepp (cons x l)))
           (and (flistnp (wcoords x l) n)
	        (equal (wcomb (wcoords x l) l) x))))

(defthmd wcomb-wdepp
  (implies (and (wlistnp l n) (flistnp c n) (natp n))
           (wdepp (cons (wcomb c l) l))))

(defun-sk windepp-sk (l)
  (forall (c)
    (implies (and (flistnp c (len l))
                  (equal (wcomb c l) (w0)))
	     (equal c (flistn0 (len l))))))

(defthmd windepp-sk-lemma
  (implies (and (windepp-sk l)
                (flistnp c (len l))
                (equal (wcomb c l) (w0)))
	   (equal (flistn0 (len l)) c)))

(defthmd windepp-sk-witness-lemma
  (let ((c (windepp-sk-witness l)))
     (implies (implies (and (flistnp c (len l))
                            (equal (wcomb c l) (w0)))
	               (equal (flistn0 (len l)) c))
	      (windepp-sk l))))

(defund wdepp-sk (l)
  (not (windepp-sk l)))

(defthmd windepp-equivalence
  (implies (and (natp m) (wlistnp l m))
           (iff (windepp-sk l)
	        (windepp l))))

(defthmd wdepp-sk-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (wdepp-sk l)))

;; Bases


(defund wbasisp (l)
  (and (wlistnp l (wdim))
       (windepp l)))

(defthm wbasisp-wbasis0
  (wbasisp (wbasis0)))

(defthmd wbasis-spans
  (implies (and (wbasisp b) (wp x))
           (and (flistnp (wcoords x b) (wdim))
	        (equal (wcomb (wcoords x b) b)
	               x))))

(defthmd wcoords-unique
  (implies (and (wbasisp b) (wp x) (flistnp c (wdim))
		(equal (wcomb c b) x))
	   (equal (wcoords x b) c)))

(defthm wcoords-wcoords0
  (implies (wp x)
           (equal (wcoords x (wbasis0))
	          (wcoords0 x))))

(defthm wcomb-funit
  (implies (and (natp n) (natp j) (< j n) (wlistnp l n))
           (equal (wcomb (funit j n) l)
	          (nth j l))))

(defthm wcoords-nth-basis
  (implies (and (wbasisp b) (natp j) (< j (wdim)))
           (equal (wcoords (nth j b) b)
	          (funit j (wdim)))))

(defun wbasis-mat (l b)
  (if (consp l)
      (cons (wcoords (car l) b)
            (wbasis-mat (cdr l) b))
    ()))

(defthmd fmatp-wbasis-mat
  (implies (and (wbasisp b) (wlistnp l m))
           (fmatp (wbasis-mat l b) m (wdim))))

(defthmd wcoords-wcomb
  (implies (and (wbasisp b) (posp m) (wlistnp l m) (flistnp c m))
	   (equal (wcoords (wcomb c l) b)
		  (car (fmat* (list c) (wbasis-mat l b))))))

(defthmd wcoords-convert
  (implies (and (wbasisp b1) (wbasisp b2) (wp x))
           (equal (fmat* (list (wcoords x b1)) (wbasis-mat b1 b2))
	          (list (wcoords x b2)))))

(defthmd fmatp-wbasis-wbasis-mat
  (implies (and (wbasisp b1) (wbasisp b2))
           (fmatp (wbasis-mat b1 b2) (wdim) (wdim))))

(defthmd compose-wbasis-wbasis-mats-id-fmat
  (implies (and (wbasisp b1) (wbasisp b2))
           (equal (fmat* (wbasis-mat b1 b2) (wbasis-mat b2 b1))
	          (id-fmat (wdim)))))

(defthmd wbasis-mat-inverse
  (implies (and (wbasisp b1) (wbasisp b2))
           (and (invertiblep (wbasis-mat b1 b2) (wdim))
	        (equal (inverse-mat (wbasis-mat b1 b2))
		       (wbasis-mat b2 b1)))))

(defund wunspanned (l)
  (nth (car (free-inds (row-reduce (wcoord-mat l)) (wdim)))
       (wbasis0)))

(defthmd wp-wunspanned
  (implies (and (wlistnp l m) (posp m) (< m (wdim)))
           (wp (wunspanned l))))

(defthmd wunspanned-not-wcomb
  (implies (and (posp m)
		(< m (wdim))
                (wlistnp l m)
		(windepp l)
		(flistnp c m))
	   (not (equal (wunspanned l) (wcomb c l)))))

(defthmd windepp-cons-wunspanned
  (implies (and (wlistnp l m) (windepp l) (posp m) (< m (wdim)))
           (windepp (cons (wunspanned l) l))))

(defun extend-to-wbasis (l)
  (declare (xargs :measure (nfix (- (wdim) (len l)))))
  (if (and (wlistnp l (len l)) (windepp l) (< (len l) (wdim)))
      (extend-to-wbasis (cons (wunspanned l) l))
    l))

(defthmd wbasisp-extend-to-wbasis
  (implies (and (wlistnp l n) (posp n) (windepp l))
           (wbasisp (extend-to-wbasis l))))

;;-------------------------------------------------------------------------------------------------

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

(defthm wlistnp-lin-list
  (implies (and (natp n) (vlistnp l n))
           (wlistnp (lin-list l) n)))

;; The image under lin of a linear combination:

(defthmd lin-vcomb
  (implies (and (natp n) (vlistnp l n) (flistnp c n))
           (equal (lin (vcomb c l))
	          (wcomb c (lin-list l)))))

;; It is easily shown that any linear transformation may be computed by matrix multiplication.  The matrix corresponding
;; to lin is defined as follows:

(defund lin-mat ()
  (wcoord-mat (lin-list (vbasis0))))

(in-theory (disable (lin-mat)))

(defthm fmatp-lin-mat
  (fmatp (lin-mat) (vdim) (wdim)))

;; If (vp x), then (wcoords0 (lin x)) = (car (fmat* (list (vcoords0 x)) (lin-mat)).

;; Proof: Let c = (vcoords0 x). By vbasis0-spans, x = (vcomb c (vbasis0)), and by lin-vcomb,
;; (lin x) = (wcomb c (lin-list (wbasis0))).  Thus, by wcoords0-wcomb,

;;   (wcoords0 (lin x)) = (wcoords0 (wcomb c (wbasis0)))
;;                     = (car (fmat* (list c) (wcoord-mat (wbasis0))))
;; 		       = (car (fmat* (list (vcoords0 x)) (lin-mat)))

(defthmd lin-mat-lin
  (implies (and (vp x))
           (equal (wcoords0 (lin x))
	          (car (fmat* (list (vcoords0 x)) (lin-mat))))))

;; lin is injective if the following is true:

(defun-sk lin-injective-p ()
  (forall (x)
    (implies (and (vp x) (equal (lin x) (w0)))
             (equal x (v0)))))

(defthmd lin-injective-p-lemma
  (implies (and (lin-injective-p)
                (vp x) (equal (lin x) (w0)))
           (equal (v0) x)))

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
		       y))))

(defthmd lin-surjective-p-witness-lemma
  (let ((y (lin-surjective-p-witness)))
     (implies (implies (wp y)
                       (and (vp (lin-preimage y))
	                    (equal (lin (lin-preimage y))
		                   y)))
              (lin-surjective-p))))

(in-theory (disable lin-injective-p lin-surjective-p))

;; If lin is injective, (vlistnp l n), and l is linearly independent, then (lin-list l) is linearly independent.

;; Proof: Suppose (wcomb c (lin-list l)) = (w0).  By lin-vcomb, (lin (vcomb c l)) = (w0).  Since lin is injective,
;; (vcomb c l) = (v0), and since l is linearly independent, c = (flistn0 n).

(defthmd lin-injective-vindepp-windepp
  (implies (and (lin-injective-p) (natp n) (vlistnp l n) (vindepp l))
           (windepp (lin-list l))))

;; If lin is injective, then (dimv) <= (dimw).

;; Proof: Suppose (dimv) > (dimw).  Then (len (lin-list (vbasis0))) = (len (vbasis0)) = (dimv) > (dimw).
;; By wdep-if->-dim, (lin-list (vbasis0)) is linearly dependent, but by lin-injective-vindepp-windepp, this
;; contradicts the linear independence of (vbasis0).

(defthmd injection-dim-<=
  (implies (lin-injective-p)
           (<= (vdim) (wdim))))

;; If lin is injective, then lin is surjective iff (dimv) = (dimw).

;; Proof: Let l = (lin-list (vbasis0)).  By lin-injective-vindepp-windepp, l is linearly independent.
;; Suppose vdim = wdim.  Let (wp y).  Since (len (cons y l)) = vdim + 1 = wdim + 1 > wdim.  By wdep-if->-dim,
;; (cons y l) is linearly dependent.  By wdepp-wcomb and lin-vcomb,

;;    y = (wcomb (wcoords y l) l) = (lin (vcomb (wcoords y l) (vbasis0))).

;; On the other hand, suppose lin is surjective and vdim < wdim.  Let l = (lin-list (vbasis0)), y = (wunspanned l),
;; x = (lin-preimage y), and c = (vcoords x (vbasis0)).  By wp-wunspanned and lin-surjective-p-lemma, (wp y), (vp x),
;; and (lin x) = y.  By vbasisp-vbasis0 and vbasis-spans, (flistnp c (vdim)) and x = (vcomb c (vbasis0)).  By lin-vcomb,
;; y = (wcomb c l), contradicting wunspanned-not-wcomb.

(defthmd injection-surjection-dim-=
  (implies (lin-injective-p)
           (iff (lin-surjective-p)
	        (equal (vdim) (wdim)))))

;; If lin is both injective and surjective, then we can define an inverse linear transformation from W to V.
;; Unlike the function lin-preimage, this definition is constructive, requiring no Skolem functions.
;; This will be important in our formalization of Galois theory, which will involve the functional instantiation
;; of the lemma lin-lin-inv below, resulting in an executable definition of the inverse operator of the Galois group.

;; First we show that if lin is injective, then (row-rank (lin-mat)) = vdim.
;; Let m = vdim, n = wdim, a = lin-mat, ar = (row-reduce a), and p = (row-reduce-mat a).
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

;; Let x = (vcomb z' (vbasis0)).  Then (vp x) and x != (v0).  By vcoords0-unique, (vcoords0 x) = z'.  By lin-mat-lin,

;;   (wcoords0 (lin x)) = (car (fmat* (list z') a)) = (flistn0 n)

;; and hence, (lin x) = (w0), contradicting injectivity:

(defthmd row-rank-lin-mat
  (implies (lin-injective-p)
           (equal (row-rank (lin-mat))
                  (vdim))))

;; Now suppose lin is both injective and surjective.  Then m = n and a is invertible.  We define

(defund lin-inv (y)
  (vcomb (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))
         (vbasis0)))

;; It is easily verified that lin-inv satisfies the properties of a linear transformation:

(defthm vp-lin-inv
  (implies (and (lin-injective-p) (= (vdim) (wdim)) (wp y))
           (vp (lin-inv y))))

(defthmd lin-inv-w0
  (implies (and (lin-injective-p) (= (vdim) (wdim)))
           (equal (lin-inv (w0)) (v0))))

(defthmd lin-inv-w+
  (implies (and (lin-injective-p) (= (vdim) (wdim))
                (wp x) (wp y))
           (equal (lin-inv (w+ x y))
	          (v+ (lin-inv x) (lin-inv y)))))

(defthmd lin-inv-w*
  (implies (and (lin-injective-p) (= (vdim) (wdim))
                (wp x) (fp c))
           (equal (lin-inv (w* c x))
	          (v* c (lin-inv x)))))

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

(defthmd lin-lin-inv
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y)))))


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

(defthmd slistnp-sbasis0
  (slistnp (sbasis0) (sdim)))

(defthm vindepp-sbasis0
  (and (slistnp (sbasis0) (sdim))
       (vindepp (sbasis0))))

;; By vdepp-if->-dim, sdim <= vdim:

(defthmd sdim-bound
  (<= (sdim) (vdim)))

;; sbasis0 is a maximal linearly independent list:

(defthmd vdepp-cons-sbasis0
  (implies (sp x)
           (vdepp (cons x (sbasis0)))))

;; S contains a nonzero vector iff sdim > 0:

(defthmd sdim-0-nil
  (iff (null (sbasis0))
       (equal (sdim) 0)))

(defthmd posp-sdim-not-v0
  (implies (posp (sdim))
           (let ((x (sunspanned ())))
             (and (sp x) (not (equal x (v0)))))))

(defthmd not-v0-posp-sdim
  (implies (and (sp x) (not (equal x (v0))))
           (posp (sdim))))

;; It follows from vdepp-vcomb that sbasis0 spans the subspace:

(defund scoords0 (x)
  (vcoords x (sbasis0)))

(defthm flistnp-scoords0
  (implies (sp x)
           (flistnp (scoords0 x) (sdim))))

(defthm sbasis0-spans
  (implies (sp x)
           (equal (vcomb (scoords0 x) (sbasis0))
                  x)))

;; Apply vindepp-vcomb-v0:

(defthmd sbasis0-lin-indep
  (implies (and (flistnp c (sdim))
                (equal (vcomb c (sbasis0)) (v0)))
           (equal (flistn0 (sdim)) c)))

;; Note that we have verified analogs of all of the axioms of V with the exception of sdim > 0.  Thus, any proven
;; result for V may be instantiated for S under this assumption.

;; For example, we shall prove an analog of vdepp-if->-dim: every list of vectors of S of length exceeding sdim is
;; linearly dependent.  To prove this directly by functional instantiation of vdepp-if->-dim would be difficult
;; because of the complicated definition of vindepp.  Instead, we functionally instantiate not-vindepp-sk-if->-dim:

(defthmd vdepp-sk-if->-sdim
  (implies (and (> (sdim) 0) (natp m) (> m (sdim))
		(slistnp l m))
	   (vdepp-sk l)))

;; Combine this with vindepp-equivalence:

(defthmd vdepp-if->-sdim
  (implies (and (> (sdim) 0) (natp m) (> m (sdim))
		(slistnp l m))
	   (vdepp l)))

;; The dimension of a subspace is well-defined.  That is, suppose sbasis1 is another linearly independent spanning set:

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

(defthmd sdim-sdim1-0
  (iff (= (sdim) 0) (= (sdim1) 0)))

;; We shall prove the analog of vdepp-if->-dim for sdim1 in the same way that we proved vdepp-if->-sdim. First we
;; derive the following from vindepp-sbasis1 and vindepp-vcomb-v0:

(defthmd sbasis1-lin-indep
  (implies (and (flistnp c (sdim1))
                (equal (vcomb c (sbasis1)) (v0)))
           (equal (flistn0 (sdim1)) c)))

;; Now functionally instantiate not-vindepp-sk-if->-dim:

(defthmd vdepp-sk-if->-sdim1
  (implies (and (> (sdim1) 0) (natp m) (> m (sdim1))
		(slistnp l m))
	   (vdepp-sk l)))

;; Invoke vindepp-equivalence:

(defthmd vdepp-if->-sdim1
  (implies (and (> (sdim1) 0) (natp m) (> m (sdim1))
		(slistnp l m))
	   (vdepp l)))

;; Combine vdepp-if->-sdim, vdepp-if->-sdim1, vindepp-sbasis0, and vindepp-sbasis1:

(defthmd sdim-well-defined
  (= (sdim1) (sdim)))
  
;; It is also worth noting that sdim1 <= vdim:

(defthmd sdim1<=vdim
  (<= (sdim1) (vdim)))


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

(defthmd fmatp-transpose-mat-lin-mat
  (fmatp (transpose-mat (lin-mat)) (wdim) (vdim)))

(defthmd in-kernel-p-sol0p
  (implies (vp x)
           (iff (in-kernel-p x)
                (sol0p (vcoords0 x) (transpose-mat (lin-mat))))))

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

(defthmd fp-kbasis-coord
  (implies (and (natp j) (< j (vdim)))
           (fp (kbasis-coord i j))))

;; Thus, c = (kbasis-elt-coords j), defined as follows:

(defun kbasis-coords-aux (i j)
  (if (posp i)
      (append (kbasis-coords-aux (1- i) j)
              (list (kbasis-coord (1- i) j)))
    ()))

(defund kbasis-coords (j) (kbasis-coords-aux (vdim) j))

(defthmd nth-kbasis-coords
  (implies (and (natp k) (< k (vdim)))
           (equal (nth k (kbasis-coords j))
	          (kbasis-coord k j))))

(defthm len-kbasis-coords
  (equal (len (kbasis-coords j))
         (vdim)))

(defthm flistnp-kbasis-coords
  (implies (and (natp j) (< j (vdim)))
           (flistnp (kbasis-coords j) (vdim))))

;; The kbasis element corresponding to j is the vector (vcomb c (vbasis0)).  Thus, kbasis is defined as follows:

(defun kbasis-aux (f)
  (if (consp f)
      (cons (vcomb (kbasis-coords (car f)) (vbasis0))
            (kbasis-aux (cdr f)))
    ()))

(defund kbasis ()
  (let ((ar (row-reduce (transpose-mat (lin-mat)))))
    (kbasis-aux (free-inds ar (vdim)))))

(in-theory (disable (kbasis)))

(defund kdim () (len (kbasis)))

(in-theory (disable (kdim)))

(defthmd kdim-val
  (equal (kdim)
         (len (free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))))

(defthmd kdim-bound
  (<= (kdim) (vdim)))

;; We must show that kbasis is a linearly independent list of kernel vectors that spans the kernel.

;; If i < kdim and j = (nth i f), then

;;   (nth i (kbasis)) =  (vcomb (kbasis-coords j) (vbasis0)),

;; which implies (vp (nth i (kbasis))) and (vcoords0 (nth i (kbasis))) = (kbasis-coords j).

;; Thus, to prove that every member of kbasis is in the kernel, it suffices to show that for all j in f,

;;   (sol0p (kbasis-coords j) a).

;; Let x = (kbasis-coords j).  According to the lemma sol0p-suff, it suffices to prove that for all k < q,

;;   (nth (nth k l) x) = (f- (fdot-select f (nth k ar) x).

;; But according to the definition of kbasis-coords, both sides of this equation reduce to (f- (entry k j ar)).
;; Thus, we have

(defthmd sol0p-kbasis-coords
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (member j f)
             (sol0p (kbasis-coords j) (transpose-mat (lin-mat))))))

(defthm klistnp-kbasis
  (klistnp (kbasis) (kdim)))

(defthm dlistp-kbasis
  (dlistp (kbasis)))

(defthmd kbasis-nil
  (implies (= (kdim) 0)
           (null (kbasis))))

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
	          (nth-vcomb j c l))))

;; We apply this result to the case l = (kbasis), n = kdim, and j = (nth i f), where i < kdim.  By construction of
;; kbasis, (nth-vcomb j c (kbasis)) = (nth i c):

(defthmd nth-vcomb-nth-c
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (and (flistnp c (len f)) (natp i) (< i (len f)))
             (equal (nth-vcomb (nth i f) c (kbasis))
	            (nth i c)))))

;; Combine nth-vcomb-val and nth-vcomb-val:

(defthmd nth-vcomb-kbasis 
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (implies (and (flistnp c (kdim)) (natp i) (< i (kdim)))
              (equal (nth (nth i f) (vcoords0 (vcomb c (kbasis))))
	             (nth i c)))))

;; Now suppose (vcomb c (kbasis)) = 0. Then (vcoords0 (vcomb c (kbasis))) = (flistn0 (kbasis)).  It follows that
;; (nth i c) = 0 for all i < kdim, and therefore c = (flistn0 (kdim):
  
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
  (implies (in-kernel-p x) (flistnp (kcoords x) (kdim)))
  :hints (("Goal" :in-theory (enable in-kernel-p kdim kcoords)
                  :use (kdim-val sublistp-f))))

;; Another immediate consequence of the definition:

(defthmd nth-kcoords
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
    (implies (and (natp i) (< i (kdim)))
             (equal (nth i (kcoords x))
	            (nth (nth i f) (vcoords0 x))))))

;; We must show that if (in-kernel-p x), then (vcomb (kcoords x) (kbasis)) = x.  Let y = (vcomb (kcoords x) (kbasis).
;; By vbasis0-spans, it suffices to show that (vcoords0 y) = (vcoords0 x).  But since (sol0p x a) and (sol0p y a), it
;; follows from sol0p-necc that each leading index coordinate of a kernel element is determined by the free index
;; coordinates, and therefore it suffices to show that for all j in f, (nth j (vcoords0 y)) = (nth j (vcoords0 x)).
;; To prove this, we instantiate nth-vcomb-kbasis with i = (index j f) and c = (kcoords x):

;;    (nth j (vcoords0 y)) = (nth (nth i f) (vcoords0 (vcomb (kcoords x) (kbasis))))
;;                         = (nth i (kcoords x))
;;                         = (nth j (vcoords0 x)).

(defthm kbasis-spans
  (implies (in-kernel-p x)
           (equal (vcomb (kcoords x) (kbasis))
                  x)))

;;-------------------------------------------------------

;; The image of lin is recognized by the predicate in-image-p:

(defund in-image-p (x)
  (let ((p (lin-preimage x)))
    (and (vp p) (equal (lin p) x))))

;; The subspace axioms are easily verified:

(defthm in-image-p-wp
  (implies (in-image-p x) (wp x)))

(defthmd in-image-p-w0
  (in-image-p (w0)))

(defthm in-image-p-w+
  (implies (and (in-image-p x) (in-image-p y))
           (in-image-p (w+ x y))))

(defthm in-image-p-w*
  (implies (and (in-image-p x) (fp c))
           (in-image-p (w* c x))))

(defthm in-image-p-w-
  (implies (in-image-p x)
           (in-image-p (w- x))))

;; We shall show that the dimension of the image is the difference vdim - kdim:

(defun idim () (- (vdim) (kdim)))

(defthmd idim+kdim
  (equal (+ (idim) (kdim))
         (vdim)))

;; We must construct a basis for the image of length idim.  First we extend kbasis to a basis for V:

(defund extend-kbasis ()
  (if (posp (kdim))
      (extend-to-basis (kbasis))
    (vbasis0)))

(in-theory (disable (extend-kbasis)))

(defthmd vbasisp-extend-kbasis
  (vbasisp (extend-kbasis)))

;; The image basis consists of the first idim members of the extended basis:

(defun firstn (n l)
  (if (zp n)
      ()
    (cons (car l) (firstn (1- n) (cdr l)))))

(defund ibasis ()
  (lin-list (firstn (idim) (extend-kbasis))))

(in-theory (disable (ibasis)))

;; We must show that ibasis is a linearly independent list of length idim that spans the image.  We first note that the
;; members of ibasis are in the image:

(defun ilistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-image-p (car x))
         (ilistnp (cdr x) (1- n)))))

(defthm ilistnp-ibasis
  (ilistnp (ibasis) (idim)))

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

;; Since kbasis is linearly independent, (append c (flist-minus d)) = (flistn0 (vdim)), which implies
;; c = (flistn0 (idim)).  Thus, ibasis is linearly independent:

(defthmd ibasis-lin-indep
  (windepp (ibasis)))

;; It remains to show that ibasis spans the image.  We define the coordinate function as follows:

(defund icoords (x)
  (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis))))

(defthm flistnp-icoords
  (implies (in-image-p x)
           (flistnp (icoords x) (idim))))

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

(defthm ibasis-spans
  (implies (in-image-p x)
           (equal (wcomb (icoords x) (ibasis))
                  x)))
