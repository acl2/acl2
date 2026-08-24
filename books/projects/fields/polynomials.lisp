(in-package "DM")

(include-book "vectors")
(local (include-book "support/embeddings"))

;; In this book, we define and analyze polynomial evaluation, the primitive element of a simple extension,
;; polynomial factorization, and the minimal polynomial of a field element.  Factorization is based on thr
;; Skolem function pfactor of the book "extensions" and is therefore not executable.  (The implementation
;; of a constructive factorization algorithm for finite fields and number fields is project for the future.)

;; The first step in the definition of the minimal polynomial is the (zero-poly x e f), which computes, for
;; a given element x of an extension e of f, a polynomial over f of which x is a root.  The definition of
;; this function, which is based on the linear dependence of the powers of x, is constructive, but the
;; definition of the minimal polynomial of x, which involves the fasctorization of (zero-poly x e f), is not.

;;----------------------------------------------------------------------------------------------------------
;;                                          Polynomial Evaluation
;;----------------------------------------------------------------------------------------------------------

;; Power of a field element:

(defun fpower (x n f)
  (if (zp n)
      (fone f)
    (fmul x (fpower x (1- n) f) f)))

(defthm feltp-fpower
  (implies (and (fieldp f) (feltp x f))
           (feltp (fpower x n f) f)))

(defthmd fpower-nonzero
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (fpower x n f) (fzero f)))))

;; Power of a polynomial:

(defun ppower (p n f)
  (if (zp n)
      (pone f)
    (pmul p (ppower p (1- n) f) f)))

(defthm polyp-ppower
  (implies (and (fieldp f) (polyp x f))
           (polyp (ppower x n f) f)))

;; If f is a non-base field, then (fpower x n f) and (ppower x n (cdr f)) are related as follows:

;;    (fpower x n f) = (fmul x (fpower x (1- n) f) f)
;;                   = (fmul x (prem (ppower x (1- n) (cdr f)) (car f) (cdr f)) f)
;;		     = (prem (pmul x (prem (ppower x (1- n) (cdr f)) (car f) (cdr f)) (cdr f)) (car f))
;;		     = (prem (pmul x (ppower x (1- n) (cdr f)) (cdr f)) (car f) (cdr f))
;;		     = (prem (ppower x n (cdr f)) (car f) (cdr f))

(defthmd fpower-ppower
  (implies (and (fieldp f) (consp f)
                (feltp x f) (natp n))
	   (equal (fpower x n f)
	          (prem (ppower x n (cdr f)) (car f) (cdr f)))))

;; Evaluation of a polynomial:

(defun peval (p x f)
  (declare (xargs :measure (len p) :hints (("Goal" :use ((:instance len-pstrip (x (cdr p))))))))
  (if (consp p)
      (if (pconstp p)
          (car p)
	(fadd (fmul (car p) (fpower x (degree p) f) f)
	      (peval (pstrip (cdr p) f) x f)
	      f))
    ()))

(defthm feltp-peval
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (feltp (peval p x f) f)))

;; A homomorphism commutes with polynomial evaluation:

(defthmd hom-fpower
  (implies (and (feltp x (fld1)) (natp n))
           (equal (hom (fpower x n (fld1)))
	          (fpower (hom x) n (fld2)))))

(defthmd pconstp-phom
  (iff (pconstp (phom p))
       (pconstp p)))

(defthmd hom-peval
  (implies (and (polyp p (fld1)) (feltp x (fld1)))
           (equal (hom (peval p x (fld1)))
	          (peval (phom p) (hom x) (fld2)))))

;; By functional instantiation of hom-peval, lifting commutes with polynomial evaluation:

(defthmd flift-peval
  (implies (and (extensionp e f)
                (polyp p f) (feltp x f))
	   (equal (flift (peval p x f) f e)
	          (peval (plift p f e) (flift x f e) e))))

;; Evaluation of constants:

(defthmd peval-pconstp
  (implies (and (fieldp f) (polyp p f) (pconstp p) (feltp x f))
           (equal (peval p x f) (car p))))

;; Evaluation of sums and products:

(defun feval (p x f)
  (if (consp p)
      (fadd (fmul (car p) (fpower x (degree p) f) f)
            (feval (cdr p) x f)
	    f)
    (fzero f)))

(defthm feltp-feval
  (implies (and (fieldp f) (feltsp p f) (feltp x f))
           (feltp (feval p x f) f)))

(defthmd feval-pstrip
  (implies (and (fieldp f) (feltsp p f) (feltp x f))
           (equal (feval (pstrip p f) x f)
	          (feval p x f))))

(defthmd feval-peval
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (equal (feval p x f)
	          (peval p x f))))

(defthmd feval-faddl
  (implies (and (fieldp f) (feltsp p f) (feltsp q f) (feltp x f))
           (equal (feval (faddl p q f) x f)
	          (fadd (feval p x f) (feval q x f) f))))

(defthmd peval-padd
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (equal (peval (padd p q f) x f)
	          (fadd (peval p x f) (peval q x f) f))))

(defthmd feval-cmul
  (implies (and (fieldp f) (feltp c f) (feltsp q f) (feltp x f))
           (equal (feval (cmul c q f) x f)
	          (fmul c (feval q x f) f))))

(defthmd peval-cmul
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (polyp q f) (feltp x f))
           (equal (peval (cmul c q f) x f)
	          (fmul c (peval q x f) f))))

(defthmd peval-pshift
  (implies (and (fieldp f) (polyp q f) (not (equal q (pzero f))) (natp k) (feltp x f))
           (equal (peval (pshift q k f) x f)
	          (fmul (fpower x k f) (peval q x f) f))))

(defthmd peval-pmul
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (equal (peval (pmul p q f) x f)
	          (fmul (peval p x f) (peval q x f) f))))
  
;; The identity polynomial is the monic monomial of degree 1.  We may think of this as the polynomial X:

(defund pid (f)
  (list (fone f) (fzero f)))

(defthmd polyp-pid
  (implies (fieldp f)
           (polyp (pid f) f)))

(defthmd peval-pid
  (implies (and (fieldp f) (feltp x f))
           (equal (peval (pid f) x f) x)))

;; Root of a polynomial:

(defund prootp (x p f)
  (and (feltp x f)
       (equal (peval p x f) (fzero f))))


;;----------------------------------------------------------------------------------------------------------
;;                                    Primitive Element of an Extension 
;;----------------------------------------------------------------------------------------------------------

;; The primitive element of a non-base field f is the identity polynomial of (cdr f):

(defund primitive (f)
  (pid (cdr f)))

(defthm feltp-primitive
  (implies (and (fieldp f) (consp f))
           (feltp (primitive f) f)))

(defthmd primitive-nonzero
  (implies (and (fieldp f) (consp f))
           (not (equal (primitive f) (fzero f)))))

;; A power of the primitive element:

(defthmd fpower-primitive
  (implies (and (fieldp f) (consp f) (natp n))
           (equal (fpower (primitive f) n f)
	          (prem (monomial (fone (cdr f)) n (cdr f))
		        (car f)
			(cdr f)))))

;; We shall show that (primitive f) is a root of (plift (car f) (cdr f) f), the lifted generating polynomial.

;; Let p be any polynomial over (cdr f).  if we lift p to f and evaluate it on the primitive element, we get 
;; the remainder of p modulo (car f):

;;   (peval (plift p (cdr f) f) (primitive f) f)
;;     = (peval (cons (list (car p)) (plift (cdr p) (cdr f) f)) (primitive f) f)
;;     = (fadd (fmul (list (car p))
;;                   (fpower (primitive f) (degree p) f)
;;		     f)
;;             (peval (pstrip (plift (cdr p) (cdr f) f) f) (primitive f) f)
;;             f)
;;     = (fadd (fmul (list (car p))
;;                   (fpower (primitive f) (degree p) f)
;;		     f)
;;             (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
;;             f)
;;     = (fadd (fmul (list (car p))
;;                   (fpower (primitive f) (degree p) f)
;;		     f)
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             f)
;;     = (padd (prem (pmul (list (car p))
;;                         (fpower (primitive f) (degree p) f)
;;			   (cdr f))
;;                   (car f)
;;		     (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (padd (prem (pmul (list (car p))
;;                         (prem (monomial (fone (cdr f)) (degree p) (cdr f)) (car f) (cdr f))
;;			   (cdr f))
;;                   (car f)
;;		     (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (padd (prem (pmul (list (car p))
;;                         (monomial (fone (cdr f)) (degree p) (cdr f))
;;			   (cdr f))
;;                   (car f)
;;		     (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (padd (prem (monomial (car p) (degree p) (cdr f)) (car f) (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (prem (padd (monomial (car p) (degree p) (cdr f))
;;                   (pstrip (cdr p) (cdr f))
;;                   (cdr f))
;;             (car f)
;;             (cdr f))
;;     = (prem (padd (head p (cdr f))
;;                   (tail p (cdr f))
;;                   (cdr f))
;;             (car f)
;;             (cdr f))
;;     = (prem p (car f) (cdr f))

(defthmd peval-primitive
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
	          (prem p (car f) (cdr f)))))

;; The claim follows by substituting (car f) for p:

(defthmd prootp-primitive
  (implies (and (fieldp f) (consp f))
           (prootp (primitive f) (plift (car f) (cdr f) f) f)))
  

;;----------------------------------------------------------------------------------------------------------
;;                                        Polynomial Factorization
;;----------------------------------------------------------------------------------------------------------

;; If p is monic and reducible, then p is a product of 2 monic polynomials of lesser degree:

(defthmd reduciblep-product
  (implies (and (fieldp f) (polyp p f) (monicp p f) (reduciblep p f))
           (let* ((d (pfactor p f)) (q (pquot p d f)))
	     (and (polyp d f) (monicp d f) (> (degree d) 0) (< (degree d) (degree p))
	          (polyp q f) (monicp q f) (> (degree q) 0) (< (degree q) (degree p))
		  (equal (pmul d q f) p)))))

;; Factorization of a polynomial as a product of irreducible polynomials:

(defun factorization (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :use (reduciblep-product)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 2) (reduciblep p f))
      (let ((d (pfactor p f)))
        (append (factorization d f)
                (factorization (pquot p d f) f)))
    (list p)))

;; The following predicate recognizes a list of non-constant monic irreducible polynomials:

(defun monicp-irreduciblep-listp (l f)
  (if (consp l)
      (and (polyp (car l) f)
           (irreduciblep (car l) f)
           (monicp (car l) f)
	   (>= (degree (car l)) 1)
	   (monicp-irreduciblep-listp (cdr l) f))
    (null l)))

(defthmd member-monicp-irreduciblep-listp
  (implies (and (monicp-irreduciblep-listp l f)
                (member p l))
	   (and (polyp p f)
                (irreduciblep p f)
                (monicp p f)
	        (>= (degree p) 1))))

(defthmd monicp-irreduciblep-append
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (monicp-irreduciblep-listp m f))
           (monicp-irreduciblep-listp (append l m) f)))

;; The product of such a list:

(defun pmul-list (l f)
  (if (consp l)
      (pmul (car l) (pmul-list (cdr l) f) f)
    (pone f)))

(defthm polyp-pmul-list
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (polyp (pmul-list l f) f)))

(defthm monicp-pmul-list
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (monicp (pmul-list l f) f)))

(defthm pmul-list-append
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (monicp-irreduciblep-listp m f))
           (equal (pmul-list (append l m) f)
	          (pmul (pmul-list l f) (pmul-list m f) f))))

;; The factorization of a non-constant monic polynomial is a list of monic irreducible polynomials with
;; product p:

(defthmd pmul-list-irreduciblep-factorization
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
	   (and (monicp-irreduciblep-listp (factorization p f) f)
	        (equal (pmul-list (factorization p f) f)
	               p))))

(defthmd len-factorization-bound
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (<= (len (factorization p f))
	       (degree p))))

;; A root of the product of polynomials p and q must be a root of either p or q:

(defthmd prootp-pmul
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (iff (prootp x (pmul p q f) f)
	        (or (prootp x p f) (prootp x q f)))))

;; Every element of f is a root of a unique monic polynomial of degree 1 over f:

(defun root-poly (x f)
  (list (fone f) (fneg x f)))

(defthmd peval-root-poly
  (implies (and (fieldp f) (feltp x f))
           (equal (peval (root-poly x f) x f)
	          (fzero f))))

(defthmd polyp-root-poly
  (implies (and (fieldp f) (feltp x f))
           (polyp (root-poly x f) f)))

(defthmd degree-root-poly
  (implies (and (fieldp f) (feltp x f))
           (equal (degree (root-poly x f))
	          1)))

(defthm root-poly-nonzero
  (implies (and (fieldp f) (feltp x f))
           (not (equal (root-poly x f) (pzero f)))))

(defthmd monicp-irreduciblep-root-poly
  (implies (and (fieldp f) (feltp x f))
           (let ((p (root-poly x f)))
	     (and (polyp p f)
	          (monicp p f)
		  (irreduciblep p f)
		  (equal (degree p) 1)))))

;; x is a root of a polynomial p iff p is divisible by (root-poly x f):

(defthmd prootp-pdivides
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (iff (prootp x p f)
	        (pdivides (root-poly x f) p f))))

(defthmd prootp-not-pconstp
  (implies (and (fieldp f) (feltp x f) (polyp p f) (not (equal p (pzero f)))
                (prootp x p f))
	   (>= (degree p) 1)))

(defthm irreduciblep-pdivides-equal
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (>= (degree q) 1)
		(pdivides p q f))
	   (equal p q))
  :rule-classes ())

(defthmd pdivides-pmul-listp
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1))
	   (iff (pdivides p (pmul-list l f) f)
	        (member p l))))

(defthmd pdivides-member-factorization
  (implies (and (fieldp f)
		(polyp q f) (monicp q f) (>= (degree q) 1)
		(polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1))
	   (iff (pdivides p q f)
	        (member p (factorization q f)))))

(defthmd member-factorization
  (implies (and (fieldp f)
                (polyp q f) (monicp q f) (>= (degree q) 1)
		(member p (factorization q f)))
	   (and (polyp p f)
                (irreduciblep p f)
                (monicp p f)
	        (>= (degree p) 1)
	        (<= (degree p) (degree q))
		(pdivides p q f))))

(defthmd prootp-pmul-listp
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(feltp x f))
	   (iff (prootp x (pmul-list l f) f)
	        (member (root-poly x f) l))))

(defthmd prootp-member-factorization
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(feltp x f))
	   (iff (prootp x p f)
	        (member (root-poly x f)
		        (factorization p f)))))

;; If p is irreducible and (degree p) > 1, then p has no roots, for if (prootp x p f), then since 
;; (factorization p f) = (list p), prootp-member-factorization implies p = (root-poly x f), which
;; has degree 1:

(defthmd irreduciblep-no-root
  (implies (and (fieldp f)
                (polyp p f) (irreduciblep p f) (monicp p f) (> (degree p) 1)
		(feltp x f))
	   (not (prootp x p f))))

;; List of the distinct roots of p:

(defun proots-aux (l f)
  (if (consp l)
      (let ((d (proots-aux (cdr l) f))
            (r (fneg (cadar l) f)))
        (if (and (= (degree (car l)) 1)
	         (not (member r d)))
            (cons r d)
	  d))
    ()))

(defund proots (p f)
  (proots-aux (factorization p f) f))

(defthmd len-proots-<=-len-factorization
  (<= (len (proots p f))
      (len (factorization p f))))

(defthmd len-proots-bound
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
	   (<= (len (proots p f))
	       (degree p))))

(defthmd feltsp-proots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (feltsp (proots p f) f)))

(defthmd feltp-member-proots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (member x (proots p f)))
           (feltp x f)))

(defthmd dlistp-proots
  (dlistp (proots p f)))

(defthmd member-proots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (iff (member x (proots p f))
	        (prootp x p f))))

;; To do:
#|
(defthmd polyp-factorization-unique
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1)
                (monicp-irreduciblep-listp l f)
		(equal (pmul-list l f) p))
	   (permutationp l (factorization p f))))
|#

;;----------------------------------------------------------------------------------------------------------
;;                     Algebraic Nature of Finite Field Extensions: Minimal Polynomials
;;----------------------------------------------------------------------------------------------------------

;; We shall show that every extension e of f (under our definition) is algebraic over f, i.e, every element
;; of e is a root of (the fifting of) some polynomial over f, and consequently of a unique irreducible
;; polynomial, over f.  The degree of this irreducible polynomial is at most the degree of the extension.

;; We have proved that in a vector space of dimension d, given a list l of vectors with (len l) > d, we can
;; construct a linear dependence of l:

(include-book "projects/linear/vectors" :dir :system)

(defun vcoord-mat (l)
  (if (consp l)
      (cons (vcoords0 (car l))
	    (vcoord-mat (cdr l)))
    ()))

(defun vdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (vcoord-mat l))))

(defthmd vcomb-v0-if->-dim
  (implies (and (posp m) (vlistnp l m) (> m (vdim)))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (equal c (flistn0 m)))
		  (equal (vcomb c l) (v0))))))

;; Let d = (edegree e f).  Since e is a vector space over f of dimension d, functional instantiation of the 
;; above result yields the following:

(defun ecoord-mat (l e f)
  (if (consp l)
      (cons (ecoords0 (car l) e f)
	    (ecoord-mat (cdr l) e f))
    ()))

(defun edep-coeffs (l e f)
  (nth (1- (len l)) (row-reduction-emat (ecoord-mat l e f) f)))

(defthmd ecomb-fzero-if->-dim
  (implies (and (extensionp e f) (not (equal e f))
                (posp m) (elistnp l m e) (> m (edegree e f)))
	   (let ((c (edep-coeffs l e f)))
	     (and (elistnp c m f)
		  (not (equal c (elistn0 m f)))
		  (equal (ecomb c l e f) (fzero e))))))

;; Thus, any list of elements of e of length exceeding d is linearly dependent over f.
;; In particular, the first d + 1 powers of any element x of e are linearly dependent over f:

(defun fpowers (x n e)
  (if (zp n)
      ()
    (cons (fpower x (1- n) e)
          (fpowers x (1- n) e))))

(defthm len-fpowers
  (implies (natp n)
           (equal (len (fpowers x n e))
	          n)))

(defthmd elistnp-fpowers
  (implies (and (fieldp e) (feltp x e) (natp n))
           (elistnp (fpowers x n e) n e)))

;; A linear combination of (fpowers x n e) may be expressed as the value of a polynomial:

(defthmd ecomb-peval
  (implies (and (extensionp e f)
                (posp n)
		(elistnp c n f)
		(feltp x e))
	   (let ((p (pstrip c f)))
	     (and (polyp p f)
	          (equal (ecomb c (fpowers x n e) e f)
	                 (peval (plift p f e) x e))))))

;; This produces a nonzero polynomial over f of degree at most d of which x is a root.  We multiply this
;; polynomial by the reciprocal of its leading coefficient to produce a monic polynomial with the same
;; property:

(defund zero-poly (x e f)
  (if (equal e f)
      (root-poly x f)
    (let ((p (pstrip (edep-coeffs (fpowers x (1+ (edegree e f)) e) e f) f)))
      (cmul (frecip (car p) f) p f))))

(defthmd prootp-zero-poly
  (implies (and (extensionp e f) (feltp x e))
           (let ((p (zero-poly x e f)))
             (and (polyp p f)
	          (monicp p f)
	          (<= (degree p) (edegree e f))
	          (prootp x (plift p f e) e)))))

(defthmd zero-poly-not-pconstp
  (implies (and (extensionp e f) (feltp x e))
           (>= (degree (zero-poly x e f)) 1)))

;; The minimal polynomial of x is computed by factoring (zero-poly x e f) and selecting an irreducible
;; factor of which x is a root:

(defun min-poly-aux (x l e f)
  (if (consp l)
      (if (prootp x (plift (car l) f e) e)
          (car l)
	(min-poly-aux x (cdr l) e f))
    ()))

(defund min-poly (x e f)
  (min-poly-aux x (factorization (zero-poly x e f) f) e f))

(defthmd prootp-min-poly
  (implies (and (extensionp e f)
                (feltp x e))
	   (let ((p (min-poly x e f)))
	     (and (polyp p f)
	          (monicp p f)
		  (irreduciblep p f)
	          (>= (degree p) 1)
	          (<= (degree p) (edegree e f))
		  (prootp x (plift p f e) e)))))

;; The trivial case:

(defthmd min-poly-trivial
  (implies (and (fieldp f) (feltp x f))
           (equal (min-poly x f f)
	          (root-poly x f))))
;;----------------------------------------------------------------------------------------------------------

;; Let q be a polynomial over f.  If q is divisible by (min-poly x e f), then clearly x is a root of q.  
;; The converse is also true.  The proof requires the following deceptively simple property of the greatest
;; common divisor:

(defthmd plift-pgcd
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
           (equal (pgcd (plift p f e) (plift q f e) e)
	          (plift (pgcd p q f) f e))))

;; If p is a polynomial over f, let p' denote (plift p f e).  Thus, if p = (min-poly x e f), then x is a
;; root of p'.  Let q be another polynomial over f such that x is a root of q' and suppose p does not
;; divide q.  Then (pgcd p q f) = 1, which implies (pgcd p' q' e) = 1.  Thus, we can find r and s such 
;; that rp' + sq' = 1.  Since x is not a root of 1, we have a contradiction:

(defthmd min-poly-pdivides
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f))
	   (iff (prootp x (plift q f e) e)
	        (pdivides (min-poly x e f) q f))))

;; If d is an intermediate field between e and f, and x is an element of d, then since

;;    (peval (plift (plift (min-poly x e f) f d) d e) x e) = (peval (plift (min-poly x e f) f e) x e) = 0,

;; the following is a consequence of prootp-min-poly and min-poly-pdivides:

(defthmd min-poly-divides-min-poly-plift
  (implies (and (extensionp e d) (extensionp d f) (feltp x e))
           (pdivides (min-poly x e d)
	             (plift (min-poly x e f) f d)
		     d)))

;; On the other hand, if x is an element of d, then

;;    (min-poly (flift x d e) e f) = (min-poly x d f).

;; To prove this, note that

;;    (peval (plift (min-poly x d f) f e) (flift x d e) e)
;;      = (peval (plift (plift (min-poly x d f) f d) d e) (flift x d e) e)  [plift-comp] 
;;      = (flift (peval (plift (min-poly x d f) f d) x d) d e)              [flift-peval]
;;      = (flift (fzero d) d e)                                             [prootp-min-poly, def of prootp]
;;      = (fzero e)                                                         [flift-id]

;; Thus, (flift x d e) is a root of (plift (min-poly x d f) f e) e), and by min-poly-pdivides, (min-poly 
;; (flift x d e) e f) divides (min-poly x d f).  Since both polynomials are monic and irreducible, they are 
;; equal according to irreduciblep-no-factor, pdivides-monic-equal, and pdivides-degree:

(defthmd min-poly-flift-min-poly
  (implies (and (extensionp e d) (extensionp d f) (feltp x d))
           (equal (min-poly (flift x d e) e f)
	          (min-poly x d f))))

;; Since (primitive e) is a root of (car e), (car e) must be divisible by (min-poly (primitive e) e (cdr e)), 
;; and since both of these polynomials are irreducible, they must be equal:

(defthmd min-poly-primitive
  (implies (and (fieldp f) (consp f))
           (equal (min-poly (primitive f) f (cdr f))
	          (car f))))

;; We define an element of e to be lifted from f if the degree of its minimal polynomial is 1:

(defund fliftedp (x f e)
  (= (degree (min-poly x e f)) 1))

(defthmd min-poly-flift
  (implies (and (extensionp e f)
                (feltp x f))
	   (equal (min-poly (flift x f e) e f)
	          (root-poly x f))))
                        
(defthm fliftedp-flift
  (implies (and (extensionp e f)
                (feltp x f))
	   (fliftedp (flift x f e) f e)))

;; If (fliftedp x f e), then this function returns the element of f that lifts to x:

(defund fdrop (x e f)
  (fneg (cadr (min-poly x e f)) f))

(defthmd flift-fdrop
  (implies (and (extensionp e f)
                (feltp x e) (fliftedp x f e))
	   (let ((y (fdrop x e f)))
	     (and (feltp y f)
	           (equal (flift y f e) x)))))

(defthmd fdrop-flift
  (implies (and (extensionp e f) (feltp x f))
           (equal (fdrop (flift x f e) e f)
	          x)))

;; The notion of a lifted polynomial will also be important:

(defun pliftedp (p f e)
  (if (consp p)
      (and (fliftedp (car p) f e)
           (pliftedp (cdr p) f e))
    t))

(defthmd plifted-plift
  (implies (and (extensionp e f)
                (polyp p f))
	   (pliftedp (plift p f e) f e)))

(defun pdrop (p e f)
  (if (consp p)
      (cons (fdrop (car p) e f)
            (pdrop (cdr p) e f))
    ()))

(defthmd plift-pdrop-feltsp
  (implies (and (extensionp e f)
                (feltsp p e) (pliftedp p f e))
	   (let ((q (pdrop p e f)))
	     (and (feltsp q f)
	          (equal (plift q f e) p)))))

(defthmd plift-pdrop
  (implies (and (extensionp e f)
                (polyp p e) (pliftedp p f e))
	   (let ((q (pdrop p e f)))
	     (and (polyp q f)
	          (equal (plift q f e) p)))))
