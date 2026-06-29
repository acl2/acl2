(in-package "DM")

(include-book "projects/linear/support/reduction" :dir :system)
(local (include-book "support/vectors"))

;; This formalization of vector spaces is not complete, but currently meets our first objective of providing the results
;; required for our development of Galois theory.  (se the lemmas not-vindepp-sk-if->-dim, injection-dim-<=, and
;; injection-dim-=.)

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
  (implies (vp x) (equal (v+ (v0) x) x)))

(defthm v+inv-comm
  (implies (vp x) (equal (v+ (v- x) x) (v0))))

(defthm f0*v0
  (implies (vp x) (equal (v* (f0) x) (v0))))

(defthm c*v0
  (implies (fp c) (equal (v* c (v0)) (v0))))

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

;; The list of coordinates of a vector is unique:

(defthmd vcoords0-unique
  (implies (and (vp x) (flistnp c (vdim))
		(equal (vcomb c (vbasis0)) x))
	   (equal (vcoords0 x) c)))

;; In particular, since (vcomb (flistn0 (vdim)) (vbasis0)) = (v0), (vcoords0 (v0)) = (flistn0 (vdim)):

(defthm vcomb-flistn0
  (implies (vlistnp l n)
           (equal (vcomb (flistn0 n) l)
	          (v0))))

(defthm vcoords0-v0
  (equal (vcoords0 (v0))
         (flistn0 (vdim))))


;;---------------------------------------------------------------------------------------------------------------------
;;  Linear Dependence
;;---------------------------------------------------------------------------------------------------------------------

;; We define the coordinate matrix of a list of vectors:

(defun vcoord-mat (l)
  (if (consp l)
      (cons (vcoords0 (car l))
	    (vcoord-mat (cdr l)))
    ()))

(defthm fmatp-vcoord-mat
  (implies (vlistnp l m)
           (fmatp (vcoord-mat l) m (vdim))))

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

;; Now suppose m > 1 and assume the claim is true when c and l are repaced by (cdr c) and (cdr l).
;; Let a = (vcoord-mat l).  We shall show first that

;;    (car (fmat* (list c) a) = (flist-add (flist-scalar-mul (car c) (car a)) (car (fmat* (list (cdr c)) (cdr a)))).

;; To prove this, it suffices to show that for j < (vdim), the jth members of these lists are equal.  But

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

(defthmd vdepp-vcomb-v0
  (implies (and (posp m) (vlistnp l m) (vdepp l))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (= c (flistn0 m)))
		  (equal (vcomb c l) (v0))))))

;; Note that the axiom vbasis0-lin-indep ensures that vbasis0 is a linearly independent list:

(defthm vindepp-vbasis0
  (vindepp (vbasis0)))

;; We must also show that if (vindepp l), then (v0) is not a nontrivial linearly combination of l.
;; Assume (flistnp c m).  We must show that if (car (fmat* (list c) a)) = (flistn0 (vdim)), then
;; c = (flistn0 m).  We first show that this holds if a is replaced by r = (row-reduce a).
;; Let i < m and j = (nth i (lead-inds r)).  By fmat*-entry,

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

;; Suppose (vcomb c l) = (v0).  Then (car (fmat* (list c) a)) = (vcoords0 (v0)) = (flistn0 (vdim)).
;; Let r = (row-reduce a), p = (row-reduce-mat a), and c' = (car (fmat* (list c) (inverse-mat p))).
;; Then r = (fmat* p a), which implies a = (fmat* (inverse-mat p) r) and

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

;; Thus, (car (fmat* (list c') r) = (flistn0 (vdim)).  By row-echelon-p-vindepp, c' = (flistn0 m),
;; which implies

;;   (list c) = (fmat* (list (flistn0 m)) p) = (list (flistn0 m))

;; and we have the following:

(defthm vindepp-vcomb-v0
  (implies (and (posp m)
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
  (implies (and (posp m)
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

;; If m > (vdim), then since (fmatp a m (vdim)), (row-rank a) <= (vdim) < m, i.e., (vdepp l):

(defthmd vdep-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp l)))

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

(defthmd vdepp-vcomb
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)))
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

;; The main motivation for this equivalent formulation is that it will facilitate functional instantiation of lemmas
;; pertaining to linear independence.  In particular, in our development of field theory, we shall show that is a field
;; e is a finite extension of a field f, then e satisfies axioms of for vector space over f, the dimension of which is
;; the degree of the extension.  We would like to conclude, by functional instantiation of vdep-if->-dim, that if l is
;; a list of elements of e of length exceeding the degree of the extension, then 0 may be expressed as a linear combination
;; of the elements of l with coefficients in f.  (This result will be critial in proiving that every finite extension is
;; algebraic.  To do this directly would require defining a notion of linear independence that mirrors the definition of
;; vindepp, which is based on matrix algebra, row reduction, etc.  All of this may be avoided by applying functional
;; instantiation to the following result instead:

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

;; In particular, for i < (vdim),

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

;; We shall show that any linearly independent list of vectors may be extended to a vbasis.  To this end,
;; given a linearly independent list l with (len l) = m < (vdim),  we shall construct a vector (vunspanned l)
;; that is not a linear combination of l.  Once again, let a = (vcoord-mat l), p = (row-reduce-mat a), and
;; r = (row-reduce a).  We may define (vunspanned l) to be a member of vbasis0 that corresponds to any of the
;; indices of (free-inds r (vdim)).  We arbitrarily select the vbasis element corresponding to
;; (car (free-inds r (vdim))):

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
  (equal (row-rank (wcoord-mat l))
         (len l)))

(defund wdepp (l)
  (not (windepp l)))

(defun wdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (wcoord-mat l))))

(defthmd wdepp-wcomb-w0
  (implies (and (posp m) (wlistnp l m) (wdepp l))
	   (let ((c (wdep-coeffs l)))
	     (and (flistnp c m)
		  (not (= c (flistn0 m)))
		  (equal (wcomb c l) (w0))))))

(defthm windepp-wbasis0
  (windepp (wbasis0)))

(defthm windepp-wcomb-w0
  (implies (and (posp m)
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
  (let ((c (wdep-coeffs (cons x l))))
    (flist-scalar-mul (f- (f/ (car c))) (cdr c))))

(defthmd wdepp-wcomb
  (implies (and (wlistnp l n) (posp n) (wp x) (windepp l) (wdepp (cons x l)))
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

(defthmd windepp-equivalence
  (implies (and (posp m) (wlistnp l m))
           (iff (windepp-sk l)
	        (windepp l))))

(defthmd not-windepp-sk-if->-dim
  (implies (and (natp m) (> m (wdim))
		(wlistnp l m))
	   (not (windepp-sk l))))


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

(defthmd lin-mat-lin
  (implies (and (vp x))
           (equal (wcoords0 (lin x))
	          (car (fmat* (list (vcoords0 x)) (lin-mat))))))

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
           (windepp (lin-list l))))

;; Proof: Suppose (wcomb c (lin-list l)) = (w0).  By lin-vcomb, (lin (vcomb c l)) = (w0).  Since lin is injective,
;; (vcomb c l) = (v0), and since l is linearly independent, c = (flistn0 n).

;; Our final 2 results will be critical (along with the lemma not-vindepp-sk-if->-dim) to our formalization of
;; Galois theory.

;; If lin is injective, then (dimv) <= (dimw):

(defthmd injection-dim-<=
  (implies (lin-injective-p)
           (<= (vdim) (wdim))))

;; Proof: Suppose (dimv) > (dimw).  Then (len (lin-list (vbasis0))) = (len (vbasis0)) = (dimv) > (dimw).
;; By wdep-if->-dim, (lin-list (vbasis0)) is linearly dependent, but by lin-injective-vindepp-windepp, this
;; contradicts the linear independence of (vbasis0).

;; If lin is injective, then lin is surjective iff (dimv) = (dimw):

(defthmd injection-surjection-dim-=
  (implies (lin-injective-p)
           (iff (lin-surjective-p)
	        (equal (vdim) (wdim)))))

;; Proof: Let l = (lin-list (vbasis0)).  By lin-injective-vindepp-windepp, l is linearly independent.

;; Suppose vdim = wdim.  Let (wp y).  Since (len (cons y l)) = (vdim) + 1 = (wdim) + 1 > (wdim).  By wdep-if->-dim,
;; (cons y l) is linearly dependent.  By wdepp-wcomb and lin-vcomb,

;;    y = (wcomb (wcoords y l) l) = (lin (vcomb (wcoords y l) (vbasis0))).

;; On the other hand, suppose lin is surjective and vdim < wdim.  Let l = (lin-list (vbasis0)), y = (wunspanned l),
;; x = (lin-preimage y), and c = (vcoords x (vbasis0)).  By wp-wunspanned and lin-surjective-p-lemma, (wp y), (vp x),
;; and (lin x) = y.  By vbasisp-vbasis0 and vbasis-spans, (flistnp c (vdim)) and x = (vcomb c (vbasis0)).  By lin-vcomb,
;; y = (wcomb c l), contradicting wunspanned-not-wcomb.
