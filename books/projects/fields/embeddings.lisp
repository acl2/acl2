(in-package "DM")

(include-book "extensions")
(local (include-book "support/embeddings"))

;; The theme of the book "extensions" is the reification of the metalogical notion of a field.  Similarly, 
;; a major theme of this book is the reification of the notion of a field homomomorphism.  That is, given 
;; extensions e and k of a field f, we shall define the homomorphic embeddings of e in k over f as ACL2 
;; objects.  We shall consider field extensions as vector spaces and embeddings as linear transformations,
;; applying our earlier results on linear algebra ("../linear/").  Related topics covered include polynomial
;; evaluation, roots, and factorization, minimal polynomials, and algebraic extensions.  

;;----------------------------------------------------------------------------------------------------------
;;                                          Field Homomorphisms
;;----------------------------------------------------------------------------------------------------------

;; The following encapsulation axiomatizes the notion of a field homomorphism:

(encapsulate (((fld1) => *) ((fld2) => *) ((hom *) => *))
  (local (defun fld1 () 0))
  (local (defun fld2 () 0))
  (local (defun hom (x) x))
  (defthm fieldp-fld1-fld2
    (and (fieldp (fld1)) (fieldp (fld2))))
  (defthm hom-fld1-fld2
    (implies (feltp x (fld1)) (feltp (hom x) (fld2))))
  (defthm hom-id
    (and (equal (hom (fzero (fld1))) (fzero (fld2)))
	 (equal (hom (fone (fld1))) (fone (fld2)))))
  (defthm hom-fadd
    (implies (and (feltp x (fld1)) (feltp y (fld1)))
             (equal (hom (fadd x y (fld1))) (fadd (hom x) (hom y) (fld2)))))
  (defthm hom-fmul
    (implies (and (feltp x (fld1)) (feltp y (fld1)))
             (equal (hom (fmul x y (fld1))) (fmul (hom x) (hom y) (fld2))))))

;; The derived properties of the constrained function hom may be attributed to any function that satisfies 
;; the above axioms by functional instantiation.  We begin with some trivial consequences of the axioms:

(defthmd hom-fneg
  (implies (feltp x (fld1))
           (equal (hom (fneg x (fld1)))
	          (fneg (hom x) (fld2)))))

(defthmd hom-frecip
  (implies (and (feltp x (fld1)) (not (equal x (fzero (fld1)))))
           (equal (hom (frecip x (fld1)))
	          (frecip (hom x) (fld2)))))

(defthm hom-fzero
  (implies (and (feltp x (fld1)) (equal (hom x) (fzero (fld2))))
           (equal x (fzero (fld1))))
  :rule-classes ())

(defthm hom-1-1
  (implies (and (feltp x (fld1)) (feltp y (fld1)) (equal (hom x) (hom y)))
           (equal x y))
  :rule-classes ())

(defthm hom-fone
  (implies (and (feltp x (fld1)) (equal (hom x) (fone (fld2))))
           (equal x (fone (fld1))))
  :rule-classes ())

;; A field homomorphism induces a homomorphism of polynomial rings:

(defun phom (p)
  (if (consp p)
      (cons (hom (car p)) (phom (cdr p)))
    ()))

(defthmd feltsp-phom
  (implies (feltsp p (fld1))
           (feltsp (phom p) (fld2))))

(defthmd polyp-phom
  (implies (polyp p (fld1))
           (polyp (phom p) (fld2))))

(defthmd monicp-phom
  (implies (and (polyp p (fld1)) (monicp p (fld1)))
           (monicp (phom p) (fld2))))

(defthmd phom-id
  (and (equal (phom (pzero (fld1))) (pzero (fld2)))
       (equal (phom (pone (fld1))) (pone (fld2)))))

(defthmd phom-pzero
  (implies (and (polyp p (fld1))
                (not (equal p (pzero (fld1)))))
	   (not (equal (phom p) (pzero (fld2))))))

(defthm len-phom
  (equal (len (phom p))
         (len p)))

(defthmd phom-faddl
  (implies (and (feltsp p (fld1)) (feltsp q (fld1)))
           (equal (phom (faddl p q (fld1)))
	          (faddl (phom p) (phom q) (fld2)))))

(defthmd phom-pstrip
  (implies (feltsp p (fld1))
           (equal (phom (pstrip p (fld1)))
	          (pstrip (phom p) (fld2)))))

(defthmd phom-padd
  (implies (and (polyp p (fld1)) (polyp q (fld1)))
           (equal (phom (padd p q (fld1)))
	          (padd (phom p) (phom q) (fld2)))))

(defthmd phom-cmul
  (implies (and (feltsp q (fld1)) (feltp c (fld1)) (not (equal c (fzero (fld1)))))
           (equal (phom (cmul c q (fld1)))
	          (cmul (hom c) (phom q) (fld2)))))

(defthmd phom-append
  (implies (and (feltsp p (fld1)) (feltsp q (fld1)))
           (equal (phom (append p q))
	          (append (phom p) (phom q)))))

(defthm phom-fzero-list
  (implies (natp k)
           (equal (phom (fzero-list k (fld1)))
	          (fzero-list k (fld2)))))

(defthmd phom-pshift
  (implies (and (polyp p (fld1)) (natp k))
           (equal (phom (pshift p k (fld1)))
	          (pshift (phom p) k (fld2)))))

(defthmd phom-pmul
  (implies (and (polyp p (fld1)) (polyp q (fld1)))
           (equal (phom (pmul p q (fld1)))
	          (pmul (phom p) (phom q) (fld2)))))
	  
(defthmd phom-pquot-prem
  (implies (and (polyp x (fld1)) (polyp y (fld1)) (not (equal y (pzero (fld1)))))
           (and (polyp (phom (pquot x y (fld1))) (fld2))
	        (polyp (phom (prem x y (fld1))) (fld2))
                (equal (phom  (pquot x y (fld1)))
		       (pquot (phom x) (phom y) (fld2)))
                (equal (phom  (prem x y (fld1)))
		       (prem (phom x) (phom y) (fld2))))))

(defthmd pdivides-phom
  (implies (and (polyp x (fld1)) (polyp y (fld1)) (not (equal y (pzero (fld1)))))
           (iff (pdivides (phom y) (phom x) (fld2))
	        (pdivides y x (fld1)))))
		

;;----------------------------------------------------------------------------------------------------------
;;                             The Embedding of a Field in an Extension Field
;;----------------------------------------------------------------------------------------------------------

;; Definition of a field extension:

(defun extends (e f)
  (or (equal e f)
      (and (consp e)
           (extends (cdr e) f))))

(defun extensionp (e f)
  (and (fieldp f) (fieldp e) (extends e f)))

(defthmd extends-trans
  (implies (and (extends e d) (extends d f))
           (extends e f)))

(defthmd len-extends
  (implies (extends e f)
           (<= (len f) (len e))))

;; Let e be an extension of f.  We may think of f as a subfield of e, but this is not strictly true -- the 
;; elements of f are not elements of e.  However, there is a natural embedding of f in e:

(defun fliftn (x n)
  (if (zp n)
      x
    (list (fliftn x (1- n)))))

(defund flift (x f e)
  (fliftn x (- (len e) (len f))))

;; flift satisfies the axioms of a field homomorphism:

(defthm feltp-flift
  (implies (and (extensionp e f)
                (feltp x f))
	   (feltp (flift x f e) e)))

(defthm flift-id
  (implies (extensionp e f)
           (and (equal (flift (fzero f) f e) (fzero e))
	        (equal (flift (fone f) f e) (fone e)))))

(defthm flift-fadd
  (implies (and (extensionp e f)
                (feltp x f) (feltp y f))
           (equal (flift (fadd x y f) f e)
	          (fadd (flift x f e) (flift y f e) e))))

(defthm flift-fmul
  (implies (and (extensionp e f)
                (feltp x f) (feltp y f))
           (equal (flift (fmul x y f) f e)
	          (fmul (flift x f e) (flift y f e) e))))

;; Some trivial consequences of the axioms:

(defthmd flift-fneg
  (implies (and (extensionp e f)
                (feltp x f))
           (equal (flift (fneg x f) f e)
	          (fneg (flift x f e) e))))

(defthmd flift-frecip
  (implies (and (extensionp e f)
                (feltp x f) (not (equal x (fzero f))))
           (equal (flift (frecip x f) f e)
	          (frecip (flift x f e) e))))

(defthm flift-fzero
  (implies (and (extensionp e f)
                (feltp x f) (equal (flift x f e) (fzero e)))
           (equal x (fzero f)))
  :rule-classes ())

(defthmd flift-1-1
  (implies (and (extensionp e f)
                (feltp x f) (feltp y f) (not (equal x y)))
	   (not (equal (flift x f e) (flift y f e)))))

(defthm flift-fone
  (implies (and (extensionp e f)
                (feltp x f) (equal (flift x f e) (fone e)))
           (equal x (fone f)))
  :rule-classes ())

;; Additional properties:

(defthm flift-noop
  (equal (flift x f f) x))

(local-defthmd fliftn-plus
  (implies (and (natp n) (natp m))
           (equal (fliftn (fliftn x n) m)
	          (fliftn x (+ n m)))))

(defthm flift-comp
  (implies (and (extensionp e d) (extensionp d f))
           (equal (flift (flift x f d) d e)
	          (flift x f e))))

;; flift induces a homomorphism of polynomial rings:

(defun plift (p f e)
  (if (consp p)
      (cons (flift (car p) f e) (plift (cdr p) f e))
    ()))

(defthmd feltsp-plift
  (implies (and (extensionp e f) (feltsp p f))
           (feltsp (plift p f e) e)))

(defthm len-plift
  (equal (len (plift p f e))
         (len p)))

(defthmd polyp-plift
  (implies (and (extensionp e f) (polyp p f))
	   (polyp (plift p f e) e)))

(defthm monicp-plift
  (implies (and (extensionp e f) (polyp p f) (monicp p f))
           (monicp (plift p f e) e)))

(defthmd pstrip-plift
  (implies (and (extensionp e f) (feltsp p f))
           (equal (pstrip (plift p f e) e)
	          (plift (pstrip p f) f e))))

(defthmd plift-id
  (implies (extensionp e f)
           (and (equal (plift (pzero f) f e) (pzero e))
	        (equal (plift (pone f) f e) (pone e)))))

(defthmd plift-pzero
  (implies (and (extensionp e f)
                (polyp p f) (not (equal p (pzero f))))
           (not (equal (plift p f e) (pzero e)))))
		  
(defthmd plift-padd
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f))
           (equal (plift (padd p q f) f e)
	          (padd (plift p f e) (plift q f e) e))))
		  
(defthmd plift-cmul
  (implies (and (extensionp e f) (feltsp p f)
                (feltp c f) (not (equal c (fzero f))))
           (equal (plift (cmul c p f) f e)
	          (cmul (flift c f e) (plift p f e) e))))

(defthmd plift-pmul
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f))
	   (equal (plift (pmul p q f) f e)
	          (pmul (plift p f e) (plift q f e) e))))

(defthmd pdivides-plift
  (implies (and (extensionp e f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (iff (pdivides (plift y f e) (plift x f e) e)
	        (pdivides y x f))))

(defthm plift-noop
  (implies (polyp p f)
           (equal (plift p f f) p)))

(defthm plift-comp
  (implies (and (extensionp e d) (extensionp d f))
           (equal (plift (plift x f d) d e)
	          (plift x f e))))

(defthmd plift-pshift
  (implies (and (extensionp e f)
                (polyp p f) (natp k))
	   (equal (plift (pshift p k f) f e)
	          (pshift (plift p f e) k e))))

;; We have informally referred to a simple extension e of f as adjoining a root of the irreducible polynomial
;; (car e) to f.  We shall show that (car e) -- or more precisely, (plift (car e) f e) -- does indeed have a
;; root in e.  We must first define the notion of a root.


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

;; The factorization of a non-constant monic polynomial is a list of monic irreducible 
;; polynomials with product p:

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
;;                                     Field Extensions as Vector Spaces
;;----------------------------------------------------------------------------------------------------------

;; We shall show that an extension e of f is a finite-dimensional vector space over f.  That is, we
;; shall define functions corresponding to the functions that are constrained by the encapsulation of
;; "../linear/vectors", which characterize a vector space, and prove the theorems that correspond to the vector
;; space axioms.  Once this is done, the properties of vector spaces may be attributed to field extensions
;; by functional instantiation.  Two such properties are derived in the next section of this book, 
;; "Embeddings of an Extension Field", and another in the section "Minimal Polynomials" of the book "galois".

;; The first 5 of the functions corresponding to the constrained vector space functions are easily defined,
;; and their required properties are readily verified:

;;  vp        (lambda (x) (feltp x e))
;;  v+        (lambda (x y) (fadd x y e))
;;  v0        (lambda () (fzero e))
;;  v-        (lambda (x) (fneg x e))
;;  v*        (lambda (c x) (fmul (flift c f e) x e))

;; The remaining 5 functions are defined below:

;;  vlistnp   (lambda (x n) (elistnp x n e))
;;  vcomb     (lambda (flist elist) (ecomb flist elist e))
;;  vdim      (lambda () (edegree e f))
;;  vbasis0   (lambda () (ebasis0 e f))
;;  vcoords0  (lambda (x) (ecoords0 x e f))

;; List of n vectors::

(defun elistnp (x n e)
  (if (zp n)
      (null x)
    (and (consp x)
         (feltp (car x) e)
	 (elistnp (cdr x) (1- n) e))))

;; List of zeroes:

(defun elist0p (x e)
  (if (consp x)
      (and (= (car x) (fzero e))
           (elist0p (cdr x) e))
    (null x)))

;; List of n zeroes:

(defun elistn0 (n e)
  (if (zp n)
      ()
    (cons (fzero e) (elistn0 (1- n) e))))
	 
;; Linear combination of a list of vectors:

(defun ecomb (flist elist e f)
  (if (consp flist)
      (fadd (fmul (flift (car flist) f e)
                  (car elist)
		  e)
            (ecomb (cdr flist) (cdr elist) e f)
	    e)
    (fzero e)))

;; The dimension of the space is the degree of the extension, defined as follows:

(defun edegree (e f)
  (if (equal e f)
      1
    (and (consp e)
         (* (degree (car e)) (edegree (cdr e) f)))))

;; Note that edegree is multiplicative in the following sense:

(defthmd edegree-mult
  (implies (and (extensionp e k) (extensionp k f))
           (equal (edegree e f)
	          (* (edegree e k) (edegree k f)))))

;; A lower bound on the degree of an extension:

(defthmd edegree-lower-bound
  (implies (extensionp e f)
           (>= (edegree e f) (expt 2 (- (len e) (len f))))))

;; The canonical basis is defined recursively.  First we define the canonical basis of
;; a simple extension:

(defun pid-powers (n f)
  (if (zp n)
      ()
    (cons (pshift (pone f) (1- n) f)
          (pid-powers (1- n) f))))

(defund simple-extension-basis (e)
  (pid-powers (degree (car e)) (cdr e)))

;; Multiply a field element x by each of a list of field elements l:

(defun fmul-list (x l e)
  (if (consp l)
      (cons (fmul x (car l) e)
            (fmul-list x (cdr l) e))
    ()))

;; Multiply each of a list of field elements l by each of a list of field elements m:

(defun fmul-lists (l m e)
  (if (consp l)
      (append (fmul-list (car l) m e)
              (fmul-lists (cdr l) m e))
    ()))

;; The canonical basis of an arbitrary extension:

(defun ebasis0 (e f)
  (if (equal e f)
      (list (fone f))
    (and (consp e)
         (fmul-lists (simple-extension-basis e)
                     (plift (ebasis0 (cdr e) f) (cdr e) e)
		     e))))

;; Given a polynomial x over f, extend it with zeroes to a generalized polynomial of length n:

(defun zpad (x n f)
  (if (and (natp n) (> n (len x)))
      (cons (fzero f) (zpad x (1- n) f))
    x))

;; The coordinates of x with respect to the canonical basis:

(mutual-recursion

  (defun ecoords0 (x e f)
    (declare (xargs :measure (list (len e) (acl2-count x))))
    (if (equal e f)
        (list x)
      (and (consp e)
           (ecoords0-list (zpad x (degree (car e)) (cdr e))
	                  (cdr e)
			  f))))

  (defun ecoords0-list (x e f)
    (declare (xargs :measure (list (len e) (acl2-count x))))
    (if (consp x)
        (append (ecoords0 (car x) e f)
	        (ecoords0-list (cdr x) e f))
      ()))
)

;;------------------------------------------

;; Basic properties of the functions defined above:

(defthmd elistnp-append
  (implies (and (natp m) (natp n) (elistnp x m f) (elistnp y n f))
           (elistnp (append x y) (+ m n) f)))

(defthmd feltsp-elistnp
  (implies (and (fieldp e) (feltsp l e))
           (elistnp l (len l) e)))

(defthmd elistnp-feltsp
  (implies (and (fieldp e) (elistnp l k e))
           (feltsp l e)))

(defthmd len-elistnp
  (implies (and (elistnp l k e) (natp k))
           (equal (len l) k)))

(defthm elistnp-plift-2
  (implies (and (extensionp e f)
                (natp n) (elistnp x n f))
	   (elistnp (plift x f e) n e)))

(defthm elistnp-plift
  (implies (and (fieldp e) (consp e)
                (natp n) (elistnp x n (cdr e)))
	   (elistnp (plift x (cdr e) e) n e)))

(defthmd feltp-ecomb
  (implies (and (extensionp e f) (natp n)
                (elistnp c n f) (elistnp l n e))
	   (feltp (ecomb c l e f) e)))

(defthmd ecomb-append
  (implies (and (extensionp e f) (natp m) (natp n)
                (elistnp c1 m f) (elistnp c2 n f)
		(elistnp b1 m e) (elistnp b2 n e))
	   (equal (ecomb (append c1 c2) (append b1 b2) e f)
	          (fadd (ecomb c1 b1 e f) (ecomb c2 b2 e f) e))))

(defthm len-pid-powers
  (implies (natp n)
           (equal (len (pid-powers n f))
	          n)))

(defthm feltp-pid-power
  (implies (and (fieldp e) (consp e) (natp k) (< k (degree (car e))))
           (feltp (pshift (pone (cdr e)) k (cdr e)) e)))

(defthmd feltsp-pid-powers
  (implies (and (fieldp e) (consp e) (natp k) (<= k (degree (car e))))
           (feltsp (pid-powers k (cdr e)) e)))

(defthmd feltsp-zpad
  (implies (and (fieldp f) (feltsp x f) (natp n) (< (degree x) n))
           (feltsp (zpad x n f) f)))

(defthmd len-zpad
  (implies (and (natp n) (feltsp x f) (<= (len x) n))
           (equal (len (zpad x n f)) n)))

(defthmd pstrip-zpad
  (implies (and (polyp x f) (natp n) (< (degree x) n))
           (equal (pstrip (zpad x n f) f)
	          x)))

(defthmd elistnp-zpad
  (implies (and (fieldp f) (polyp x f) (natp n) (< (degree x) n))
           (elistnp (zpad x n f) n f)))

(defthm len-fmul-list
  (equal (len (fmul-list x l e))
         (len l)))

(defthm len-fmul-lists
  (equal (len (fmul-lists l m e))
         (* (len l) (len m))))

(defthm feltsp-fmul-list
  (implies (and (fieldp e) (feltp x e) (feltsp l e))
           (feltsp (fmul-list x l e) e)))

(defthm feltsp-fmul-lists
  (implies (and (fieldp e) (feltsp l e) (feltsp m e))
           (feltsp (fmul-lists l m e) e)))

(defthmd elistnp-fmul-list
  (implies (and (fieldp f) (natp n) (feltp x f) (elistnp y n f))
           (elistnp (fmul-list x y f) n f)))

(defthmd elistnp-fmul-lists
  (implies (and (fieldp f) (natp m) (natp n) (elistnp x m f) (elistnp y n f))
           (elistnp (fmul-lists x y f) (* m n) f)))

;;------------------------------------------

;; Length of (ebasis0 e):

(defthm len-simple-extension-basis
  (implies (and (fieldp e) (consp e))
           (equal (len (simple-extension-basis e))
                  (degree (car e)))))

(defthm len-ebasis0
  (implies (extensionp e f)
           (equal (edegree e f)
	          (len (ebasis0 e f)))))

;; (ebasis0 e) is a list of elements of e:

(defthmd feltsp-simple-extension-basis
  (implies (and (fieldp e) (consp e))
           (feltsp (simple-extension-basis e) e)))

(defthmd feltsp-ebasis0
  (implies (extensionp e f)
           (feltsp (ebasis0 e f) e)))

(defthmd elistnp-simple-extension-basis
  (implies (and (fieldp e) (consp e))
           (elistnp (simple-extension-basis e) (degree (car e)) e)))

(defthmd elistnp-ebasis0
  (implies (extensionp e f)
           (elistnp (ebasis0 e f) (edegree e f) e)))

;;-----------------------------------------------

;; Linear independence of simple-extension-basis

(defthm flift-cdr
  (implies (and (fieldp e) (consp e))
           (equal (flift x (cdr e) e)
	          (list x))))

(defthmd ecomb-pstrip
  (implies (and (fieldp e) (consp e) (posp k) (<= k (degree (car e)))
                (elistnp c k (cdr e)))
	   (equal (ecomb c (pid-powers k (cdr e)) e (cdr e))
	          (pstrip c (cdr e)))))

(defthmd ecomb-simple-extension-basis
  (implies (and (fieldp e) (consp e)
                (elistnp c (degree (car e)) (cdr e)))
	   (equal (ecomb c (simple-extension-basis e) e (cdr e))
	          (pstrip c (cdr e)))))

(defthmd pstrip-elistn0
  (implies (and (fieldp e) (consp e) (posp n)
                (elistnp c n (cdr e))
		(equal (pstrip c (cdr e)) (fzero e)))
	   (equal (elistn0 n (cdr e)) c)))

(defthmd simple-extension-basis-lin-indep
  (implies (and (fieldp e) (consp e)
                (elistnp c (degree (car e)) (cdr e))
	        (equal (ecomb c (simple-extension-basis e) e (cdr e))
	               (fzero e)))
	   (equal (elistn0 (degree (car e)) (cdr e))
	          c)))

(defthmd ebasis0-simple-extension-1
  (implies (and (fieldp e) (consp e))
           (equal (plift (list (fone (cdr e))) (cdr e) e)
	          (list (fone e)))))

(defthmd ebasis0-simple-extension-2
  (implies (and (fieldp e) (consp e))
           (equal (ebasis0 e (cdr e))
	          (fmul-lists (simple-extension-basis e)
		              (list (fone e))
			      e))))

(defthmd ebasis0-simple-extension-3
  (implies (and (fieldp e) (feltsp l e))
           (equal (fmul-lists l (list (fone e)) e)
	          l)))

(defthmd ebasis0-simple-extension
  (implies (and (fieldp e) (consp e))
           (equal (ebasis0 e (cdr e))
	          (simple-extension-basis e))))

;;--------------------------------

;; Linear independence of ebasis0:

;; The proof requires an alternative formulation of linear independence:

(defun-sk eindepp-sk (l e f)
  (forall (c)
    (implies (and (elistnp c (len l) f)
                  (equal (ecomb c l e f) (fzero e)))
	     (equal c (elistn0 (len l) f)))))

(defthmd eindepp-sk-lemma
  (implies (and (eindepp-sk l e f)
                (elistnp c (len l) f)
                (equal (ecomb c l e f) (fzero e)))
	   (equal (elistn0 (len l) f) c)))

(defthmd eindepp-sk-witness-lemma
  (let ((c (eindepp-sk-witness l e f)))
     (implies (implies (and (elistnp c (len l) f)
                            (equal (ecomb c l e f) (fzero e)))
	               (equal c (elistn0 (len l) f)))
              (eindepp-sk l e f))))


;; Sum of a list of field elements:

(defun fadd-list (l e)
  (if (consp l)
      (fadd (car l) (fadd-list (cdr l) e) e)
    (fzero e)))

;; A list of m lists of field elements, each of length n:

(defun elistn-listp (x n m e)
  (if (zp m)
      (null x)
    (and (consp x)
         (elistnp (car x) n e)
	 (elistn-listp (cdr x) n (1- m) e))))

;; A list of m lists of zeroes, each of length n:

(defun elistn0-list (n m e)
  (if (zp m)
      ()
    (cons (elistn0 n e)
          (elistn0-list n (1- m) e))))

;; Partition a list of length m * n into m lists of length n:

(defun firstn (n l)
  (if (zp n)
      ()
    (cons (car l) (firstn (1- n) (cdr l)))))

(defun split (n l)
  (if (and (posp n) (>= (len l) n))
      (cons (firstn n l) (split n (nthcdr n l)))
    ()))

(defthmd append-firstn-nthcdr
  (implies (and (natp n) (<= n (len l)))
           (equal (append (firstn n l) (nthcdr n l))
	          l)))

(defthmd elistnp-nthcdr
  (implies (and (natp n) (natp k) (<= n k) (elistnp x k f))
           (elistnp (nthcdr n x) (- k n) f)))

(defthmd elistnp-firstn
  (implies (and (natp n) (natp k) (<= n k) (elistnp x k f))
           (elistnp (firstn n x) n f)))

(defthmd split-elistnp
  (implies (and (fieldp f) (natp m) (posp n) (elistnp x (* m n) f))
           (elistn-listp (split n x) n m f)))

;; List of linear combinations of b:

(defun ecomb-list (c b e f)
  (if (consp c)
      (cons (ecomb (car c) b e f)
            (ecomb-list (cdr c) b e f))
    ()))

(defthmd elistnp-ecomb-list
  (implies (and (extensionp e f)
                (elistn-listp c n m f)
		(elistnp b n e))
	   (elistnp (ecomb-list c b e f) m e)))
	 
;; Decomposition of a linear combination:

(defun ecomb-lists (c b e f)
  (if (consp c)
      (cons (ecomb (car c) (car b) e f)
            (ecomb-lists (cdr c) (cdr b) e f))
    ()))

(defthmd ecomb-decomp
  (implies (and (extensionp e f) (natp m) (natp n)
                (elistnp c (* m n) f)
		(elistnp b (* m n) e))
	   (equal (ecomb c b e f)
	          (fadd-list (ecomb-lists (split n c) (split n b) e f) e))))

(defthm firstn-append
  (implies (true-listp x)
           (equal (firstn (len x) (append x y))
	          x)))

(defthm nthcdr-append
  (equal (nthcdr (len x) (append x y))
	 y))

(defthmd split-append
  (implies (and (true-listp x) (consp x))
           (equal (split (len x) (append x y))
	          (cons x (split (len x) y)))))

(defthm consp-fmul-list
  (implies (consp b)
           (consp (fmul-list a (plift b f e) e))))

(defthm flift-flift
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (feltp x f))
           (equal (flift (flift x f (cdr e)) (cdr e) e)
	          (flift x f e))))

(defthmd flift-ecomb
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (natp n)
                (elistnp c n f)
		(elistnp b2 n (cdr e)))
	   (equal (flift (ecomb c b2 (cdr e) f) (cdr e) e)
                  (ecomb c (plift b2 (cdr e) e) e f))))

(defthmd fmul-ecomb
  (implies (and (extensionp e f) (natp n)
                (feltp x e)
                (elistnp c n f)
		(elistnp b n e))
	   (equal (ecomb c (fmul-list x b e) e f)
	          (fmul (ecomb c b e f) x e))))

(defthmd fadd-list-ecomb-step
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (natp m) (natp n)
                (elistn-listp c n m f)
		(elistnp b1 m e) (consp b1)
		(elistnp b2 n (cdr e)) (consp b2)
		(equal (fadd-list (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
		       (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))))
	   (equal (fadd-list (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
	          (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e)))))
			
;; Proof:

;; (fadd-list (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
;;   = (fadd (ecomb (car c) (firstn n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f)
;;           (fadd-list (ecomb-lists (cdr c) (split n (nthcdr n (fmul-lists b1 (plift b2 (cdr e) e) e))) e f) e)
;; 	     e)
;;   = (fadd (ecomb (car c) (fmul-list (car b1) (plift b2 (cdr e) e) e) e f)
;;           (fadd-list (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
;; 	     e)
;;   = (fadd (ecomb (car c) (fmul-list (car b1) (plift b2 (cdr e) e) e) e f)
;;           (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (ecomb (car c) (plift b2 (cdr e) e) e f) (car b1) e)
;;           (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (flift (ecomb (car c) b2 (cdr e) f) (cdr e) e) (car b1) e)
;;           (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
;; 	     e)
;;   = (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e))

(defthmd ecomb-list-elistn0-listp
  (implies (and (extensionp e f)
                (elistnp b n e)
                (elistn-listp c (len b) m f)
		(eindepp-sk b e f)
		(equal (ecomb-list c b e f)
		       (elistn0 m e)))
	   (equal (elistn0-list (len b) m f)
	          c)))

;; Proof:

;; (ecomb-list c b e f) = (cons (ecomb (car c) b e f) (ecomb-list (cdr c) b e f))
;;                      = (elistn0 m e)

;; => (ecomb (car c) b e f) = (fzero e)
;;    (ecomb-list (cdr c) b e f) = (elistn0 (1- m) e)

;; => (car c) = (elistn0 (len b) e)                [eindepp-sk-lemma]
;;    (cdr c) = (elistn0-list (len b) (1- m) f)    [induction]

;; => c = (elistn0-list (len b) m f)


(defthmd append-firstn-nthcdr
  (implies (and (natp n) (<= n (len l)))
           (equal (append (firstn n l) (nthcdr n l))
	          l)))

(defthmd append-elistn0
  (implies (and (natp m) (natp n))
           (equal (append (elistn0 m f) (elistn0 n f))
	          (elistn0 (+ m n) f))))

(defthmd split-elistn0
  (implies (and (fieldp f) (posp n) (natp m) (elistnp c (* m n) f)
                (equal (elistn0-list n m f) (split n c)))
	   (equal (elistn0 (* m n) f)
	          c)))

(defthmd elindepp-ebasis0
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (eindepp-sk (ebasis0 (cdr e) f) (cdr e) f)
                (elistnp c (edegree e f) f)
		(equal (ecomb c (ebasis0 e f) e f) (fzero e)))
	   (equal (elistn0 (edegree e f) f)
	          c)))

;; Proof:

;; Let m = (degree (car e), n = (edegree (cdr e) f), b1 = (simple-extension-basis e), b2 = (ebasis0 (cdr e) f).

;; (fzero e) = (ecomb c (ebasis0 e f) e f)                                                [hypothesis]
;;           = (fadd-list (ecomb-lists (split n c) (split n (ebasis0 e f)) e f) e)        [ecomb-decomp]
;;           = (fadd-list (ecomb-lists (split n c)                                        [definition of ebasis0]
;; 	                               (split n (fmul-lists b1 (plift b2 (cdr e) e) e))
;; 				       e f)
;; 		          e)
;;           = (ecomb (ecomb-list (split n c) b2 (cdr e) f) b1 e (cdr e))                 [fadd-list-ecomb]

;; => (ecomb-list (split n c) b2 (cdr e) f) = (elist0n m (cdr e))                         [simple-extension-basis-lin-indep]

;; => (split n c) = (elistn0-list n m f)                                                  [ecomb-list-elistn0-listp]

;; => c = (elistn0 (* m n) f))


(defthmd eindepp-sk-inductive-case
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (eindepp-sk (ebasis0 (cdr e) f) (cdr e) f))
	   (eindepp-sk (ebasis0 e f) e f)))

(defthmd eindepp-sk-base-case
  (implies (and (fieldp e) (consp e))
           (eindepp-sk (ebasis0 e (cdr e)) e (cdr e))))

(defthmd eindepp-sk-ebasis0
  (implies (and (extensionp e f) (not (equal e f)))
           (eindepp-sk (ebasis0 e f) e f)))

(defthmd ebasis0-lin-indep
  (implies (and (extensionp e f) (not (equal e f))
                (elistnp c (edegree e f) f)
	        (equal (ecomb c (ebasis0 e f) e f)
	               (fzero e)))
	   (equal (elistn0 (edegree e f) f)
	          c)))

;;--------------------------------

;; Properties of ecoords0:

;; Two lemmas pertaining to ecoords0 remain to be proved:

;; (defthmd elistnp-ecoords0
;;   (implies (and (extensionp e f) (not (equal e f)) (feltp x e))
;;            (elistnp (ecoords0 x e f) (edegree e f) f))
;;   :hints (("Goal" :use ((:instance elistnp-ecoords0-gen (flg ()))))))


;; (defthmd ebasis0-spans
;;   (implies (and (extensionp e f) (not (equal e f))
;;                 (feltp x e))
;; 	      (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
;; 	             x)))

;; The proofs are facilitated by an alternative formulation of ebasis0-spans:

(defun-sk ebasis0-spans-sk (e f)
  (forall (x)
    (implies (feltp x e)
	     (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	            x))))

(defthmd ebasis0-spans-sk-lemma
  (implies (and (ebasis0-spans-sk e f)
                (feltp x e))
	   (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	          x)))

(defthmd ebasis0-spans-sk-witness-lemma
  (let ((x (ebasis0-spans-sk-witness e f)))
     (implies (implies (feltp x e)
	               (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	                      x))
              (ebasis0-spans-sk e f))))

;; First we consider the case of a simple extension, f = (cdr e).

;; In this case, (ecoords0 x e f) reduces to (zpad x (degree (car e)) (cdr e))):

(defthmd ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (equal (ecoords0 x e (cdr e))
	          (zpad x (degree (car e)) (cdr e)))))

(defthmd elistnp-ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (elistnp (ecoords0 x e (cdr e)) (degree (car e)) (cdr e))))

;; In the case f = (cdr e), (ecoords0 x e f) reduces to (zpad x (degree (car e)) (cdr e))
;; and the following is a consequence of ecomb-simple-extension-basis:

(defthmd ecomb-ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (equal (ecomb (ecoords0 x e (cdr e))
	                 (simple-extension-basis e)
			 e (cdr e))
		  x)))

(defthmd ebasis0-spans-sk-simple
  (implies (and (fieldp e) (consp e))
           (ebasis0-spans-sk e (cdr e))))

;; For the general case, we use the following induction scheme:

(defun elistnp-ecoords0-induct (flg x e f)
  (declare (xargs :measure (list (len e) (if flg 1 0) (len x))))
  (if flg
      (if (consp x)
          (list (elistnp-ecoords0-induct () (car x) e f)
	        (elistnp-ecoords0-induct t (cdr x) e f))
	())
    (if (equal e f)
        ()
      (and (consp e)
           (elistnp-ecoords0-induct t (zpad x (degree (car e)) (cdr e)) (cdr e) f)))))

;; The desired theorem elistnp-ecoords0 is generalized as follows:

(defthmd elistnp-ecoords0-gen
  (implies (and (extensionp e f) (not (equal e f)))
           (if flg
	       (implies (feltsp x e)
	                (elistnp (ecoords0-list x e f) (* (edegree e f) (len x)) f))
	     (implies (and (not (equal e f)) (feltp x e))
	              (elistnp (ecoords0 x e f) (edegree e f) f)))))

;; We instantiate the above lemma twice, with flg = NIL and flg = T:

(defthmd elistnp-ecoords0
  (implies (and (extensionp e f) (not (equal e f)) (feltp x e))
           (elistnp (ecoords0 x e f) (edegree e f) f)))

(defthmd elistnp-ecoords0-list
  (implies (and (extensionp e f) (not (equal e f)) (feltsp x e))
           (elistnp (ecoords0-list x e f) (* (edegree e f) (len x)) f)))

;; The main lemma:

(defthmd ecomb-ecoords0-list
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
                (natp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (equal (ecomb d a e (cdr e))
	          (ecomb (ecoords0-list d (cdr e) f)
		         (fmul-lists a (plift (ebasis0 (cdr e) f) (cdr e) e) e)
			 e f))))

;; Proof by induction:

;; (ecomb (ecoords0-list d (cdr e) f)
;;        (fmul-lists a (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;;        e f)
;;   = (fadd (ecomb (ecoords0 (car d) (cdr e) f)                                  [ecomb-append]
;;                  (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;; 		    e f)
;; 	     (ecomb (ecoords0-list (cdr d) (cdr e) f)
;;                  (fmul-lists (cdr a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;;                  e f)
;; 	     e)
;;   = (fadd (ecomb (ecoords0 (car d) (cdr e) f)                                  [induction]
;;                  (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;; 		    e f)
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (ecomb (ecoords0 (car d) (cdr e) f)                            [fmul-ecomb]
;;                        (plift (ebasis0 (cdr e) f) (cdr e) e)
;; 		          e f)
;; 		   (car a)
;; 	   	   e)		
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (flift (ecomb (ecoords0 (car d) (cdr e) f)                     [flift-ecomb]
;;                               (ebasis0 (cdr e) f)
;; 		                 (cdr e) f)
;; 		          (cdr e) e)
;; 		   (car a)
;; 	  	   e)		
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (flift (car d) (cdr e) e)                                      [ebasis0-spans-sk-lemma]
;; 		   (car a)
;; 		   e)		
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (ecomb d a e (cdr e))                                                      [definition of ecomb]
		         
;; We instantiate ecomb-ecoords0-list with

;;    m = (degree (car e))
;;    a = (simple-extension-basis e)
;;    d = (zpad x (degree (car e)) (cdr e))

;; where (feltp x e), and combine this result with elistnp-simple-extension-basis, ecomb-ecoords0-simple,
;; ecoords0-simple, and elistnp-ecoords0-simple:

(defthmd ecomb-ecoords0
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
		(feltp x e))
	   (equal (ecomb (ecoords0 x e f)
		         (ebasis0 e f)
			 e f)
	          x)))

;; Apply ebasis0-spans-sk-witness-lemma:

(defthmd ebasis-spans-step
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f))
	   (ebasis0-spans-sk e f)))

;; Apply induction:

(defthmd ebasis0-spans-lemma
  (implies (and (extensionp e f) (not (equal e f)))
	   (ebasis0-spans-sk e f)))

;; Apply ebasis0-spans-sk-lemma:

(defthmd ebasis0-spans
  (implies (and (extensionp e f) (not (equal e f))
                (feltp x e))
	   (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	          x)))


;;----------------------------------------------------------------------------------------------------------
;;                                           Minimal Polynomials
;;----------------------------------------------------------------------------------------------------------

;; We shall show that every extension e of f (according to our definition) is algebraic over f, i.e, every 
;; element of e is a root of (the fifting of) some polynomial over f, and consequently of a unique monic
;; irreducible polynomial over f.  The degree of this irreducible polynomial is at most the degree of the
;; extension.

;; We have proved that in a vector space of degree d, any list l of vectors with (len l) > d is linearly
;; dependent:

(include-book "projects/linear/vectors" :dir :system)

(defthmd not-vindepp-sk-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (not (vindepp-sk l))))

;; Let d = (edegree e f).  Since e is a vector space over f of dimension d, functional instantiation of the 
;; above result yields the following:

(defthmd not-eindepp-sk-if->-edegree
  (implies (and (extensionp e f) (not (equal e f))
                (natp m) (> m (edegree e f))
		(elistnp l m e))
	   (not (eindepp-sk l e f))))

;; According to the definition of eindepp-sk (see embeddings.lisp), this may be restated as follows:

(defthmd ecomb-eindepp-sk-witness
  (implies (and (extensionp e f) (not (equal e f))
                (natp m) (> m (edegree e f))
		(elistnp l m e))
           (let ((c (eindepp-sk-witness l e f)))
	     (and (elistnp c m f)
	          (not (equal c (elistn0 m f)))
		  (equal (ecomb c l e f) (fzero e))))))

;; In particular, the first d + 1 powers of x are linearly dependent over f:

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

;; This produces a nonzero polynomial over f of degree at most d of which x is a root.  We multiply 
;; this polynomial by the reciprocal of its leading coefficient to produce a monic polynomial with
;; the same property:

(defund zero-poly (x e f)
  (if (equal e f)
      (root-poly x f)
    (let ((p (pstrip (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f) f)))
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

;; Let q be a polynomial over f.  If q is divisible by (min-poly x e f), then clearly x is a root of q.  
;; The converse is also true.  The proof requires the following deceptively simple property of the 
;; greatest common divisor:

(defthmd plift-pgcd
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
           (equal (pgcd (plift p f e) (plift q f e) e)
	          (plift (pgcd p q f) f e))))

;; If p is a polynomial over f, let p' denote (plift p f e).  Thus, if p = (min-poly x e f), then x is 
;; a root of p'.  Let q be another polynomial over f such that x is a root of q' and suppose p does not 
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


;;----------------------------------------------------------------------------------------------------------
;;                                      Embeddings of an Extension Field
;;----------------------------------------------------------------------------------------------------------

;; Let e and k be extensions of a field f.  An embedding of e in k over f is conceptually a field homomorphism
;; from e into k that fixes f, i.e., for each element x of f, the image of (flift x f e) is (flift x f k).
;; To formalize this notion, We shall define 3 functions:

;; (1) (embed x phi k f): If x is an element of e and phi is an embedding of e in k over f, then this is the
;;     image of x in k under phi.

;; (2) (pembed p phi k f): If p is a generalized polynomial over e, then this is the image of p under phi, 
;;     i.e, the generalized polynomial over k constructed by replacing each coefficient of p with its image
;;     under phi.

;; (3) (embeddingp phi e k f): This is the predicate that recognizes phi as a well-formed embedding of e in k
;;     over f.

;; Such an embedding phi is represented by a list of elements of k of length (len e) - (len f), constructed
;; recursively as follows:

;;     (a) If e = f, then phi = () and (embed x phi k f) = (flift x k f).

;;     (b) Otherwise, let phi' be an embedding of (cdr e) in k over f.  Then phi may be constructed as an 
;;         extension of phi' by specifying the image of (primitive e) under phi, which must be a root of the 
;;         image of the polynomial (car e) under phi'.  If this root is b, then phi = (b . phi').

;; These 3 functions are formally defined as follows.  Note that the first 2 are mutually recursive:

(mutual-recursion

  (defund embed (x phi k f)
    (declare (xargs :measure (list (len phi) (acl2-count x))))
    (if (consp phi)
        (peval (pembed x (cdr phi) k f) (car phi) k)
      (flift x f k)))

  (defun pembed (p phi k f)
    (declare (xargs :measure (list (len phi) (acl2-count p))))
    (if (consp p)
        (cons (embed (car p) phi k f)
              (pembed (cdr p) phi k f))
      ()))
)

(defund embeddingp (phi e k f)
  (if (equal e f)
      (null phi)
    (and (consp phi)
	 (prootp (car phi) (pembed (car e) (cdr phi) k f) k)
	 (embeddingp (cdr phi) (cdr e) k f))))

;; Our objective is to prove the following 5 essential properties of an embedding:

;; (defthmd embed-image
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x e))
;;            (feltp (embed x phi k f) k)))

;; (defthmd embed-fixes
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x f))
;;            (equal (embed (flift x f e) phi k f)
;;                   (flift x f k))))

;; (defthmd embed-fadd
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x e) (feltp y e))
;;            (equal (embed (fadd x y e) phi k f)
;;                   (fadd (embed x phi k f) (embed y phi k f) k))))

;; (defthmd embed-fmul
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x e) (feltp y e))
;;            (equal (embed (fmul x y e) phi k f)
;;                   (fmul (embed x phi k f) (embed y phi k f) k))))

;; (defthmd embed-fzero-fone
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
;;            (and (equal (embed (fzero e) phi k f) (fzero k))
;;                 (equal (embed (fone e) phi k f) (fone k)))))

;; To this end, we shall prove by induction that every embedding satisfies the
;; predicate embed-props, defined as follows:

(defun-sk embed-prop-1 (phi e k f)
  (forall (x)
    (implies (feltp x e)
             (feltp (embed x phi k f) k))))

(defun-sk embed-prop-2 (phi e k f)
  (forall (x)
    (implies (feltp x f)
             (equal (embed (flift x f e) phi k f)
	            (flift x f k)))))

(defun-sk embed-prop-3 (phi e k f)
  (forall (x1 x2)
    (implies (and (feltp x1 e) (feltp x2 e))
             (let ((y1 (embed x1 phi k f)) (y2 (embed x2 phi k f)))
	       (and (equal (embed (fadd x1 x2 e) phi k f)
	                   (fadd y1 y2 k))
		    (equal (embed (fmul x1 x2 e) phi k f)
	                   (fmul y1 y2 k)))))))

(defun embed-prop-4 (phi e k f)
  (and (equal (embed (fzero e) phi k f) (fzero k))
       (equal (embed (fone e) phi k f) (fone k))))

(defund embed-props (phi e k f)
  (and (embed-prop-1 phi e k f)
       (embed-prop-2 phi e k f)
       (embed-prop-3 phi e k f)
       (embed-prop-4 phi e k f)))

;; The usual lemmas corresponding to the above definitions:

(defthm embed-prop-1-lemma
  (implies (and (embed-props phi e k f) (feltp x e))
           (feltp (embed x phi k f) k)))

(defthmd embed-prop-1-witness-lemma
  (let ((x (embed-prop-1-witness phi e k f)))
    (implies (implies (feltp x e) (feltp (embed x phi k f) k))
	     (embed-prop-1 phi e k f))))

(defthm embed-prop-2-lemma
  (implies (and (embed-props phi e k f) (feltp x f))
           (equal (embed (flift x f e) phi k f)
	                 (flift x f k))))

(defthmd embed-prop-2-witness-lemma
  (let ((x (embed-prop-2-witness phi e k f)))
    (implies (implies (feltp x f)
                      (equal (embed (flift x f e) phi k f)
	                     (flift x f k)))
	     (embed-prop-2 phi e k f))))

(defthm embed-prop-3-lemma
  (implies (and (embed-props phi e k f) (feltp x1 e) (feltp x2 e))
           (let ((y1 (embed x1 phi k f)) (y2 (embed x2 phi k f)))
	     (and (equal (embed (fadd x1 x2 e) phi k f)
	                 (fadd y1 y2 k))
		  (equal (embed (fmul x1 x2 e) phi k f)
	                 (fmul y1 y2 k))))))

(defthmd embed-prop-3-witness-lemma
  (mv-let (x1 x2) (embed-prop-3-witness phi e k f)
    (implies (implies (and (feltp x1 e) (feltp x2 e))
                      (let ((y1 (embed x1 phi k f)) (y2 (embed x2 phi k f)))
	                (and (equal (embed (fadd x1 x2 e) phi k f)
	                            (fadd y1 y2 k))
		             (equal (embed (fmul x1 x2 e) phi k f)
	                            (fmul y1 y2 k)))))
	     (embed-prop-3 phi e k f))))

(defthm embed-prop-4-lemma
  (implies (embed-props phi e k f)
           (and (equal (embed (fzero e) phi k f)
	               (fzero k))
		(equal (embed (fone e) phi k f)
	               (fone k)))))

;; If an embedding phi satistfies the above properties, then it is a homomorphism and inherits
;; the properties of hom, e.g.,

(defthmd embed-fzero-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (feltp x e) (equal (embed x phi k f) (fzero k)))
	   (equal (fzero e) x)))

;; Simiarly, pembed inherits the properties of phom:

(defthmd polyp-pembed-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e))
	   (polyp (pembed p phi k f) k)))

(defthm len-pembed
  (equal (len (pembed p phi k f))
         (len p)))

(defthmd monicp-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (monicp p e))
	   (monicp (pembed p phi k f) k)))

(defthmd pembed-id-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f))
	   (and (equal (pembed (pzero e) phi k f) (pzero k))
	        (equal (pembed (pone e) phi k f) (pone k)))))

(defthmd pembed-pzero-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (not (equal p (pzero e))))
	   (not (equal (pembed p phi k f) (pzero k)))))

(defthmd pembed-padd-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (padd p q e) phi k f)
	          (padd (pembed p phi k f) (pembed q phi k f) k))))

(defthmd pembed-pmul-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (pmul p q e) phi k f)
	          (pmul (pembed p phi k f) (pembed q phi k f) k))))

;;----------------------

;; Base case of the induction:

(defthmd embed-prop-1-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-1 phi f k f)))

(defthmd embed-prop-2-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-2 phi f k f)))

(defthmd embed-prop-3-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-3 phi f k f)))

(defthmd embed-prop-4-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-4 phi f k f)))

(defthmd embed-props-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-props phi f k f)))

;;-----------------------------------------------------------

;; Inductive step:

;; Let e' = (cdr e) and phi' = (cdr phi).  We must prove that if the properties hold for
;; e' and phi', then they hold for e and phi.

(defthmd embed-image-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x e))
	   (feltp (embed x phi k f) k)))

(defthmd embed-fzero-fone-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f))
	   (and (equal (embed (fzero e) phi k f) (fzero k))
	        (equal (embed (fone e) phi k f) (fone k)))))

(defthmd embed-fixes-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x f))
	   (equal (embed (flift x f e) phi k f)
	          (flift x f k))))
		  
;; Proof:
	   
;;   (flift x f e) = (fliftn x (- (len e) (len f))))             [definition of flift]
;;                 = (list (fliftn x (1- (- (len e) (len f)))))  [definition of fliftn]
;;                 = (list (fliftn x (- (len e') (len f))))
;;                 = (list (flift x f e'))                       [definition of flift]
	      
;;   (pembed (flift x f e) phi' k f) = (pembed (list (flift x f e')) phi' k f)
;;                                   = (list (embed (flift x f e')) phi' k f)   [definition of pembed]
;;                                   = (list (flift x f k))                     [induction]

;;   (embed (flift x f e) phi k f) = (peval (list (flift x f k)) (car phi) k)   [definition of embed]
;;                                 = (flift x f k)                              [peval-pconstp]

(defthmd peval-pembed-prem
  (implies (and (extensionp e f) (extensionp k f) (embed-props phi e k f)
                (polyp x e) (polyp y e) (not (equal y (pzero e)))
		(feltp a k) (prootp a (pembed y phi k f) k))
	   (equal (peval (pembed x phi k f) a k)
	          (peval (pembed (prem x y e) phi k f) a k))))

;; Proof: Let q = (pquot x y e) and r = (prem x y e).

;;   (peval (pembed x phi k f) a k) = (peval (pembed (padd (pmul y q e) r e)        [pquot-prem]
;;                                                   phi k f)
;;                                           a k)                             
;;                                  = (peval (padd (pembed (pmul y q e) phi k f)    [pembed-padd-*]                            
;;                                                 (pembed r phi k f)                             
;;                                                 k)                             
;;                                           a k)                             
;;                                  = (peval (padd (pmul (pembed y phi k f)         [pembed-pmul-*]
;;                                                       (pembed q phi k f)
;;                                                       k)
;;                                                 (pembed r phi k f)
;;                                                 k)
;;                                           a k)
;;                                  = (fadd (peval (pmul (pembed y phi k f)         [peval-padd]
;;                                                       (pembed q phi k f)
;;                                                       e)
;;                                                 a k)
;;                                          (peval (pembed r phi k f) a k)
;;                                          k)
;;                                  = (fadd (fmul (peval (pembed y phi k f) a k)    [peval-pmul]
;;                                                (peval (pembed q phi k f) a k)
;;                                                k)
;;                                          (peval (pembed r phi k f) a k)
;;                                          k)
;;                                  = (fadd (fmul (fzero k)                         [hypothesis]
;;                                                (peval (pembed q phi k f) a k)
;;                                                k)
;;                                          (peval (pembed r phi k f) a k)
;;                                          k)
;;                                  = (peval (pembed r phi k f) a k)

(defthmd embad-fadd-fmul-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (embed-props (cdr phi) (cdr e) k f)
                (feltp x e) (feltp y e))
           (and (equal (embed (fadd x y e) phi k f)
                       (fadd (embed x phi k f) (embed y phi k f) k))
                (equal (embed (fmul x y e) phi k f)
                       (fmul (embed x phi k f) (embed y phi k f) k)))))

;; Proof:

;;   (pembed (fadd x y e) phi k f) = (pembed (padd x y e') phi k f)                      [definition of fadd]
;;                                   (padd (pembed x phi k f) (pembed y phi k f) k)      [pembed-padd-*]
;; 
;;   (embed (fadd x y e) phi k f) = (peval (pembed (fadd x y e) phi' k f) (car phi) k)   [definition of embed]
;;                                = (peval (padd (pembed x phi k f)                      [proved above]   
;;                                               (pembed y phi k f)
;;                                               k)
;;                                         (car phi) k)
;;                                = (fadd (peval (pembed x phi' k f) (car phi) k)        [peval-padd, polyp-pembed-*]
;;                                        (peval (pembed y phi' k f) (car phi) k)
;;                                        k)
;;                                = (fadd (embed x phi k f) (embed y phi k f) k)         [definition of embed]

;; For the second equation, we invoke peval-pembed-prem with e <- e', phi <- phi',
;; x <- (pmul x y e'), y <- (car e), and a <- (car phi):

;;   (embed (fmul x y e) phi k f) = (peval (pembed (fmul x y e) phi k f) (car phi) k)    [definition of embed]
;;                                = (peval (pembed (prem (pmul x y e') (car e) e')       [definition of fmul]
;;                                                 phi' k f)
;;                                         (car phi) k)
;;                                = (peval (pembed (pmul x y e') phi' k f) (car phi) k)  [peval-pembed-prem]
;;                                = (peval (pmul (pembed x phi' k f)                     [pembed-pmul-*]
;;                                               (pembed y phi' k f)
;;                                               k)
;;                                         (car phi) k)
;;                                = (fmul (peval (pembed x phi' k f) (car phi) k)        [peval-pmul, polyp-pembed-*]
;;                                        (peval (pembed y phi' k f) (car phi) k)
;;                                        k)
;;                                = (fmul (embed x phi k f)                              [definition of embed]
;;                                        (embed y phi k f)
;;                                        y)

;; Collect the above results:

(defthmd embed-props-induct
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (embed-props (cdr phi) (cdr e) k f))
           (embed-props phi e k f)))

;; Now apply induction:

(defthm embed-props-lemma
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f))
           (embed-props phi e k f)))

;; The required properties follow:
                        
(defthm embed-image
  (implies (and (embeddingp phi e k f) (extensionp e f) (extensionp k f) 
                (feltp x e))
           (feltp (embed x phi k f) k)))

(defthm embed-fixes
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x f))
           (equal (embed (flift x f e) phi k f)
                  (flift x f k))))

(defthm embed-fadd
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (feltp y e))
           (equal (embed (fadd x y e) phi k f)
                  (fadd (embed x phi k f) (embed y phi k f) k))))

(defthm embed-fmul
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (feltp y e))
           (equal (embed (fmul x y e) phi k f)
                  (fmul (embed x phi k f) (embed y phi k f) k))))

(defthmd embed-fzero-fone
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
           (and (equal (embed (fzero e) phi k f) (fzero k))
                (equal (embed (fone e) phi k f) (fone k)))))

;;-------------------------------------------------------

;; The derived properties of hom and phom follow by functional instantiation:

(defthmd embed-fneg
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
	   (equal (embed (fneg x e) phi k f)
	          (fneg (embed x phi k f) k))))

(defthmd embed-frecip
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (not (equal x (fzero e))))
	   (equal (embed (frecip x e) phi k f)
	          (frecip (embed x phi k f) k))))

(defthmd embed-fzero
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (equal (embed x phi k f) (fzero k)))
	   (equal (fzero e) x)))

(defthm embedding-1-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (feltp y e)
		(equal (embed x phi k f) (embed y phi k f)))
           (equal x y))
  :rule-classes ())

(defthmd polyp-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e))
	   (polyp (pembed p phi k f) k)))

(defthmd pembed-id
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
	   (and (equal (pembed (pzero e) phi k f) (pzero k))
	        (equal (pembed (pone e) phi k f) (pone k)))))

(defthmd pembed-pzero
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (not (equal p (pzero e))))
	   (not (equal (pembed p phi k f) (pzero k)))))

(defthmd pembed-padd
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (padd p q e) phi k f)
	          (padd (pembed p phi k f) (pembed q phi k f) k))))

(defthmd pembed-pmul
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (pmul p q e) phi k f)
	          (pmul (pembed p phi k f) (pembed q phi k f) k))))

(defthmd peval-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (polyp p e))
	   (equal (peval (pembed p phi k f) (embed x phi k f) k)
	          (embed (peval p x e) phi k f))))

(defthmd pdivides-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp x e) (polyp y e) (not (equal y (pzero e))))
	   (iff (pdivides (pembed y phi k f) (pembed x phi k f) k)
	        (pdivides y x e))))

(defthmd reduciblep-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp x e) (reduciblep x e))
	   (reduciblep (pembed x phi k f) k)))

;; We also have the following consequence of embed-fixes:

(defthmd pembed-fixes
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f))
           (equal (pembed (plift p f e) phi k f)
                  (plift p f k))))


;;-------------------------------------------------------;

; Embedding commutes with lifting in the following sense:

(defthm embed-flift
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (feltp x (cdr e)))
	   (equal (embed (flift x (cdr e) e) phi k f)
	          (embed x (cdr phi) k f))))

;; Proof: Let e' = (cdr e) and phi' = (cdr phi).

;;   (embed (flift x e' e) phi k f) = (embed (list x) phi k f)
;;                                  = (peval (pembed (list x) phi' k f) (car e) k)
;; 				    = (peval (list (embed x phi' k f)) (car e) k)
;; 				    = (embed x phi' k f)

;; Consequently, the same is true of polynomials:

(defthmd pembed-plift
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (polyp p (cdr e)))
	   (equal (pembed (plift p (cdr e) e) phi k f)
	          (pembed p (cdr phi) k f))))

;; By induction, we have the following generalization of embed-flift:

(defund restrict-embedding (phi e d)
  (nthcdr (- (len e) (len d)) phi))

(defthmd embeddingp-restrict-embedding
  (implies (and (extensionp e d) (extensionp d f) (extensionp k f) (embeddingp phi e k f))                
	   (embeddingp (restrict-embedding phi e d) d k f)))

(defthmd embed-flift-gen
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (extensionp e d) (extensionp d f) (feltp x d))
	   (equal (embed (flift x d e) phi k f)
	          (embed x (restrict-embedding phi e d) k f))))

;;-------------------------------------------------------

;; Let x be in e, m = (min-poly x e), and x' = (embed x phi k f).  Then m = (min-poly x' k).

;;    (peval (plift m f k) x' k) = (peval (pembed (plift m f k) phi k f) x' k)  [pembed-fixes]
;;                               = (embed (peval (plift m f k) x e) phi k f)    [peval-pembed]
;;                               = (embed (fzero e) phi k f)                    [prootp-min-poly]
;;                               = (fzero k)                                    [embed-fzero-fone]

;; By min-poly-pdivides, (min-poly x' k f) divides m, and by pdivides-monic-equal, (min-poly x' k f) = m.

(defthmd pembed-min-poly
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
	   (equal (min-poly (embed x phi k f) k f)
	          (min-poly x e f))))

;;-------------------------------------------------------

;; If e != f, there is no embedding of e in f over f.  First suppose e is a simple extension of f.
;; If phi is an embedding of e in f over f, then (prootp (car phi) (pembed (car e) () f f) f), where
;; (pembed (car e) () f f) = (car e), contradicting irreduciblep-no-root.  The general case follows by
;; induction:

(defthmd no-embedding-in-f
  (implies (and (extensionp e f) (not (equal e f)))
           (not (embeddingp phi e f f))))

;;-------------------------------------------------------

;; The car of an embedding phi of an extension field e is the image under phi of (primitive e).
;; Thus an embedding is constructed by specifying the image of the primitive element of each of the
;; simple extensions that compose the extension:

(defthmd embed-primitive
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f))
           (equal (embed (primitive e) phi k f)
	          (car phi))))

;; Proof:

;; (embed (primitive e) phi k f)
;;   = (peval (pembed (primitive e) (cdr phi) k f) (car phi) k)  [def of embed]
;;   = (peval (pembed (pid (cdr e)) (cdr phi) k f) (car phi) k)  [def of primitive]
;;   = (peval (pid k) (car phi) k)                               [defs of pid and pembed, fembed-id]
;;   = (car phi)                                                 [peval-pid]

;;-------------------------------------------------------

;; Let phi and psi be embeddings of e in k over f.  If (embed x phi k f) = (embed x psi k f) for all
;; x in e, then phi = psi:

(defun embed-cex (phi psi e f)
  (if (and (extensionp e f) (not (equal e f)) (consp phi))
      (if (equal (car phi) (car psi))
          (flift (embed-cex (cdr phi) (cdr psi) (cdr e) f) (cdr e) e)
        (primitive e))
    ()))

(defthmd embed-cex-lemma
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (embeddingp psi e k f)
		(not (equal phi psi)))
	   (let ((x (embed-cex phi psi e f)))
	     (and (feltp x e)
	          (not (equal (embed x phi k f) (embed x psi k f)))))))

;;-------------------------------------------------------

;; We shall construct a list of all embeddings of e in k over f.
;; First, given an embedding phi of (cdr e) in k over f, construct a list of all embeddings of e in
;; k that extend phi:

(defun consl (l x)
  (if (consp l)
      (cons (cons (car l) x)
            (consl (cdr l) x))
    ()))

(defun simple-embedding-extensions (phi e k f)
  (consl (proots (pembed (car e) phi k f) k)
         phi))

;; Given a list l of embeddings of (cdr e) in k over f, construct a list of all embeddings of e in
;; k that extend a member of l:

(defun simple-embeddings-extensions (l e k f)
  (if (consp l)
      (append (simple-embedding-extensions (car l) e k f)
              (simple-embeddings-extensions (cdr l) e k f))
    ()))

;; A list of all embeddings of e in k over f:

(defun embeddings (e k f)
  (if (and (consp e) (not (equal e f)))
      (simple-embeddings-extensions (embeddings (cdr e) k f) e k f)
    (list ())))

;; (embeddings e k f) is a dlist of all embeddings of e in k over f:

(defthmd dlistp-embeddings
  (dlistp (embeddings e k f)))

(defthmd all-embeddings
  (implies (and (extensionp e f) (extensionp k f))
	   (iff (member phi (embeddings e k f))
	        (embeddingp phi e k f))))

;; The number of embeddings of e in k over f that extend a given embedding of phi of (cdr e) is 
;; the number of roots of (pembed (car e) phi k f) in k, which is bounded by (degree (car e)).
;; By induction, the number of embeddings of e in k over f is at most the degree of e over f:

(defthmd len-embeddings
  (implies (and (extensionp e f) (extensionp k f))
	   (<= (len (embeddings e k f))
	       (edegree e f))))

;;----------------------------------------------------------------------------------------------------------
;;                                      Embeddings and Meta-Embeddings
;;----------------------------------------------------------------------------------------------------------

;; The following encapsulation introduces 2 arbitrary extensions, e0 and k0, of a field b0 and a function
;; phi0 that satisfies each of the essential properties of an embedding of e0 in k0 over b0.  Such a function
;; might be termed a "meta-embedding" of e0 in k0 over b0.  Our objective is to define an embedding phi1 of
;; e0 in k0 over b0 that reifies phi0, i.e., with the following property:

;; (defthmd phi1-phi0
;;   (and (embeddingp (phi1) (e0) (k0) (b0))
;;        (implies (feltp x (e0))
;;                 (equal (embed x (phi1) (k0) (b0))
;;                        (phi0 x)))))

;; Subsequently, given any such meta-embedding, we can construct the corresponding embedding by functional
;; instantiation.  Thus, in a real sense, for any extensions e and k of a field f, the embeddings of e in k
;; over f are the only homomorphisms of e into k that fix f.
;; [Note: I wanted to call the base field f0, but it seems we already have a function with that name.]

(encapsulate (((b0) => *) ((e0) => *) ((k0) => *) ((phi0 *) => *))
  (local (defun b0 () 0))
  (local (defun e0 () 0))
  (local (defun k0 () 0))
  (local (defun phi0 (x) x))
  (defthmd extensionp-e0-k0-b0
    (and (extensionp (e0) (b0)) (extensionp (k0) (b0))))
  (defthm phi0-image
    (implies (feltp x (e0)) (feltp (phi0 x) (k0))))
  (defthm phi0-fzero-fone
    (and (equal (phi0 (fzero (e0))) (fzero (k0)))
         (equal (phi0 (fone (e0))) (fone (k0)))))
  (defthm phi0-fadd
    (implies (and (feltp x (e0)) (feltp y (e0)))
	     (equal (phi0 (fadd x y (e0)))
		    (fadd (phi0 x) (phi0 y) (k0)))))
  (defthm phi0-fmul
    (implies (and (feltp x (e0)) (feltp y (e0)))
	     (equal (phi0 (fmul x y (e0)))
		    (fmul (phi0 x) (phi0 y) (k0)))))
  (defthm phi0-fixes
    (implies (feltp x (b0)) (equal (phi0 (flift x (b0) (e0))) (flift x (b0) (k0))))))

;; phi1 is defined as follows:

(defun phi1-aux (d)
  (if (and (extensionp (e0) d) (extensionp d (b0)) (not (equal d (b0))))
      (cons (phi0 (flift (primitive d) d (e0)))
            (phi1-aux (cdr d)))
    ()))

(defund phi1 () (phi1-aux (e0)))

;; We shall derive phi1-phi0 as a corollary of the following generalization:

(defun-sk phi1-aux-phi0 (d)
  (forall (x)
    (implies (feltp x d)
             (equal (embed x (phi1-aux d) (k0) (b0))
	            (phi0 (flift x d (e0)))))))

;; (defthmd phi1-aux-lemma
;;   (implies (and (extensionp d (b0)) (extensionp (e0) d))
;; 	      (and (embeddingp (phi1-aux d) d (k0) (b0))
;; 	           (phi1-aux-phi0 d))))

;; The case d = (b0) of phi1-aux-lemma is trivial:

(defthmd phi1-aux-base
  (and (embeddingp (phi1-aux (b0)) (b0) (k0) (b0))
       (phi1-aux-phi0 (b0))))

;; Assume d != b0 and that the lemma holds for d' = (cdr d).
;; Let phi = (phi1-aux d) and phi' = (cdr phi) = (phi1-aux d').  We must show that it also holds for d.
;; Note that (car phi) = (phi0 (flift (primitive d) d (e0))).  Clearly, (feltp (car phi) (k0)).
;; To show (embeddingp phi d (k0) (b0)), we must show

;;   (prootp (car phi) (pembed (car d) (cdr phi' (k0) (b0)) (k0)),

;; i.e,

;;   (peval (pembed (car d) phi' (k0) (b0))
;;          (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (fzero (k0)).

;; We define

(defun pphi0 (p)
  (if (consp p)
      (cons (phi0 (car p))
            (pphi0 (cdr p)))
    ()))

;; Then

(defthmd pembed-pphi0
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (phi1-aux-phi0 d)
                (polyp p d))
           (equal (pembed p (phi1-aux d) (k0) (b0))
                  (pphi0 (plift p d (e0)))))
  :hints (("Goal" :use (pembed-pphi0-1))))

;; By functional instantiation of hom-peval,

(defthmd phi0-peval
  (implies (and (polyp p (e0)) (feltp x (e0)))
           (equal (phi0 (peval p x (e0)))
                  (peval (pphi0 p) (phi0 x) (k0)))))
 
;;   (peval (pembed (car d) phi' (k0) (b0))
;;          (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (peval (pphi0 (plift (car d) d' (e0)))            [pembed-pphi0]
;;              (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (phi0 (peval (plift (car d) d' (e0))              [phi0-peval]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (peval (plift (plift (car d) d' d) d (e0))  [plift-comp]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (flift (peval (plift (car d) d' d)          [flift-peval]
;;                    (primitive d) d)
;;                    d (e0)))
;;     = (phi0 (flift (prem (car d) (car d) (cdr d))       [peval-primitive] 
;;                    d (e0)))
;;     = (phi0 (flift (fzero d) d (e0)))                   [prem-self]
;;     = (phi0 (fzero (e0)))
;;     = (fzero (k0))

;; Thus, we have

(defthmd encodingp-phi1-aux
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (embeddingp (phi1-aux d) d (k0) (b0))))

;; We must also show (phi1-aux-phi0 d), i.e., if (feltp x d), then

;;   (embed x phi (k0) (b0)) = (phi0 (flift x d (e0))):

;;   (embed x phi (k0) (b0))
;;     = (peval (pembed x phi' (k0) (b0)) (car phi) (k0))   [definition of embed]
;;     = (peval (pphi0 (plift x d' (e0))) (car phi) (k0))   [pembed-pphi0]
;;     = (peval (pphi0 (plift x d' (e0)))                   [def of phi1-aux]
;;              (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (phi0 (peval (plift x d' (e0))                     [phi0-peval]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (peval (plift (plift x d' d) d (e0))         [plift-comp]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (flift (peval (plift x d' d)                 [flift-peval]
;;                           (primitive d)
;;                           d)
;;                    d (e0)))
;;     = (phi0 (flift d (e0)))                              [peval-primitive]

(defthmd embed-phi0
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (embed x (phi1-aux d) (k0) (b0))
                  (phi0 (flift x d (e0))))))

;; A simple restatement:

(defthmd embed-phi1-aux
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (phi1-aux-phi0 d)))

;; Combine this with encodingp-phi1-aux:

(defthmd phi1-aux-step
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (and (embeddingp (phi1-aux d) d (k0) (b0))
                (phi1-aux-phi0 d))))

;; Apply induction:

(defthmd phi1-aux-lemma
  (implies (and (extensionp d (b0)) (extensionp (e0) d))
           (and (embeddingp (phi1-aux d) d (k0) (b0))
                (phi1-aux-phi0 d))))

;; Instantiating phi1-aux-lemma with d = (e0) yields the desired properties of phi1:

(defthmd phi1-phi0
  (and (embeddingp (phi1) (e0) (k0) (b0))
       (implies (feltp x (e0))
                (equal (embed x (phi1) (k0) (b0))
                       (phi0 x)))))
			

;;----------------------------------------------------------------------------------------------------------
;;                               Composition of Embeddings and Isomorphisms
;;----------------------------------------------------------------------------------------------------------

;; We shall present 3 applications of phi1-phi0 through functional instantiation:
;;   (1) The identity embedding of e in e
;;   (2) The composition of 2 embeddings
;;   (3) The inverse of an embedding

;; If k is an extension of e and e is an extension of f, then the trivial embedding of e in k 
;; over f is defined as follows:

(defun trivial-embedding (e k f)
  (if (and (extensionp e f) (not (equal e f)))
      (cons (flift (primitive e) e k)
            (trivial-embedding (cdr e) k f))
    ()))

;; We shall show that this is indeed an embedding and that for all x in e,

;;    (embed x (trivial-embedding e k f) k f) = (flift x e k).

;; To that end, we define a generalization of trivial-embedding that emulates phi1-aux:

(defun trivial-embedding-aux (e d k f)
  (if (and (extensionp e d) (extensionp d f) (not (equal d f)))
      (cons (flift (primitive d) d k)
            (trivial-embedding-aux e (cdr d) k f))
    ()))

(defthmd trivial-embedding-aux-rewrite
  (implies (extensionp e d)
           (equal (trivial-embedding-aux e d k f)
                  (trivial-embedding d k f))))

;; The following is proved by functional instantiation of phi1-phi0, substituting (flift x e k) for (phi0 x):

(defthmd trivial-embedding-aux-flift
  (implies (and (extensionp k e) (extensionp e f))
           (and (embeddingp (trivial-embedding-aux e e k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (trivial-embedding-aux e e k f) k f)
			        (flift x e k))))))

;; The desired result follows from trivial-embedding-aux-flift and trivial-embedding-aux-rewrite:

(defthmd trivial-embedding-flift
  (implies (and (extensionp k e) (extensionp e f))
           (and (embeddingp (trivial-embedding e k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (trivial-embedding e k f) k f)
			        (flift x e k))))))

;; The case e = k is the identity embedding of e in e over f:

(defund id-embedding (e f)
  (trivial-embedding e e f))

(defthmd id-embedding-id
  (implies (extensionp e f)
           (and (embeddingp (id-embedding e f) e e f)
	        (implies (feltp x e)
                         (equal (embed x (id-embedding e f) e f)
	                        x)))))
(defthmd pembed-id-embedding-feltsp
  (implies (and (extensionp e f) (feltsp p e))
           (equal (pembed p (id-embedding e f) e f)
	          p)))

(defthm pembed-id-embedding
  (implies (and (extensionp e f) (polyp p e))
           (equal (pembed p (id-embedding e f) e f)
	          p)))
		  
;;--------------------------------------------------------

;; If phi embeds e in g and psi embeds g in k, then the composition embeds e in k:

(defun comp-embedding (psi phi e k f)
  (if (and (extensionp e f) (not (equal e f)))
      (cons (embed (car phi) psi k f)
            (comp-embedding psi (cdr phi) (cdr e) k f))
    ()))

;; We shall show that

;;    (embed x (comp-embedding psi phi e k f) k f) = (embed (embed x phi g f) psi k f).

;; One again, we define a generalization of comp-embedding that emulates phi1-aux:

(defun comp-embedding-aux (psi phi e d g k f)
  (if (and (extensionp e d) (extensionp d f) (not (equal d f)))
      (cons (embed (embed (primitive d) phi g f) psi k f)
            (comp-embedding-aux psi (cdr phi) e (cdr d) g k f))
    ()))

(defthmd comp-embedding-aux-rewrite
  (implies (and (extensionp e d) (extensionp d f) (extensionp g f) (embeddingp phi d g f))
           (equal (comp-embedding-aux psi phi e d g k f)
	          (comp-embedding psi phi d k f))))

;; The following is proved by functional instantiation of phi1-phi0:

(defthmd embeddingp-comp-embedding-aux
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
		(embeddingp phi e g f) (embeddingp psi g k f))
	   (and (embeddingp (comp-embedding-aux psi phi e e g k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (comp-embedding-aux psi phi e e g k f) k f)
			        (embed (embed x phi g f) psi k f))))))

;; The desired result follows from embeddingp-comp-embedding-aux and comp-embedding-aux-rewrite:

(defthmd embeddingp-comp-embedding
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
                (embeddingp phi e g f) (embeddingp psi g k f))
	   (and (embeddingp (comp-embedding psi phi e k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (comp-embedding psi phi e k f) k f)
			        (embed (embed x phi g f) psi k f))))))

;; Composed embedding of a polynomial:

(defthmd pembed-comp-embedding-feltsp
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
                (embeddingp phi e g f) (embeddingp psi g k f)
		(feltsp p e))
	   (equal (pembed p (comp-embedding psi phi e k f) k f)
	          (pembed (pembed p phi g f) psi k f))))

  (defthmd pembed-comp-embedding
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
                (embeddingp phi e g f) (embeddingp psi g k f)
		(polyp p e))
	   (equal (pembed p (comp-embedding psi phi e k f) k f)
	          (pembed (pembed p phi g f) psi k f))))
			
;; Composition with the identity embedding:

(defthmd comp-id-embedding
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
           (and (equal (comp-embedding (id-embedding k f) phi e k f) phi)
	        (equal (comp-embedding phi (id-embedding e f) e k f) phi))))

;; Associativity of composition:

(defthmd comp-embedding-assoc
  (implies (and (extensionp e1 f) (extensionp e2 f) (extensionp e3 f) (extensionp e4 f)
                (embeddingp phi1 e1 e2 f) (embeddingp phi2 e2 e3 f) (embeddingp phi3 e3 e4 f))
	   (equal (comp-embedding phi3 (comp-embedding phi2 phi1 e1 e3 f) e1 e4 f)
	          (comp-embedding (comp-embedding phi3 phi2 e2 e4 f) phi1 e1 e4 f))))

;;--------------------------------------------------------

;; It is a consequence of the essential properties of embeddings that an embedding of e in k over f is an 
;; injective linear transformation from;; e into k, viewed as vector spaces over f.  It follows by functional
;; instantiation of injection-dim-<= ("../linear/vectors") that the degree of k over f is at least the degree
;; of e over f:

(defthmd embedding-degree-<=
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
	   (<= (edegree e f)
	       (edegree k f))))

;; It similarly follows from injection-surjection-dim-= this linear transformation is surjective iff e and
;; k have the same degree over f:

(defchoose preembed x (y phi e k f)
  (and (feltp x e)
       (equal (embed x phi k f) y)))

(defun-sk surjective-embedding-p (phi e k f)
  (forall (y)
    (implies (feltp y k)
             (let ((x (preembed y phi e k f)))
	       (and (feltp x e)
                    (equal (embed x phi k f) y))))))

(defthm embedding-surjective
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
           (iff (equal (edegree e f) (edegree k f))		
	        (surjective-embedding-p phi e k f))))

;; In this case, we shall say that e and k are isomorphic over f and that phi is an isomorphism from e to
;; k over f:

(defun iso-embeddingp (phi e k f)
  (and (embeddingp phi e k f)
       (equal (edegree e f) (edegree k f))))

;; Suppose phi is an isomorphism from e to k over f.  Given an element y of k, we may define an element
;; x = (preembed y phi e k f) such that (embed x phi k f) = y:

(defchoose preembed x (y phi e k f)
  (and (feltp x e)
       (equal (embed x phi k f) y)))

(defthm embed-preembed
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
                (feltp y k))
	   (let ((x (preembed y phi e k f)))
	     (and (feltp x e)
	          (equal (embed x phi k f) y)))))

;; We shall construct the inverse of an isomorphism, based on the the function preembed.

;; First we observe that preembed is a meta-homorphism:

(defthm preembed-embed
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
                (feltp x e))
	   (let ((y (embed x phi k f)))
	     (and (feltp y k)
	          (equal (preembed y phi e k f) x))))
  :hints (("Goal" :use ((:instance embed-preembed (y (embed x phi k f)))
                        (:instance embedding-1-1 (y (preembed (embed x phi k f) phi e k f)))))))

(defthm preembed-fzero-fone
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
	   (and (equal (preembed (fzero k) phi e k f)
	               (fzero e))
	        (equal (preembed (fone k) phi e k f)
	               (fone e)))))

(defthm preembed-fadd-fmul
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
		(feltp x k) (feltp y k))
	   (and (equal (preembed (fadd x y k) phi e k f)
	               (fadd (preembed x phi e k f) (preembed y phi e k f) e))
		(equal (preembed (fmul x y k) phi e k f)
	               (fmul (preembed x phi e k f) (preembed y phi e k f) e)))))

(defthm preembed-fixes
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
		(feltp x f))
	   (equal (preembed (flift x f k) phi e k f)
	          (flift x f e))))

;; The definition of the inverse isomorphism emulates the definition of phi1:
          
(defun inv-embedding-aux (phi e k d f)
  (and (extensionp k d) (extensionp d f) (not (equal d f))
       (cons (preembed (flift (primitive d) d k) phi e k f)
             (inv-embedding-aux phi e k (cdr d) f))))

(defun inv-embedding (phi e k f)
  (inv-embedding-aux phi e k k f))

;; The following is proved by functional instantiantion of phi1-phi0:

(defthmd embeddingp-inv-embedding-aux
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
           (and (embeddingp (inv-embedding-aux phi e k k f) k e f)
	        (implies (feltp x k)
                         (equal (embed x (inv-embedding-aux phi e k k f) e f)
	                        (preembed x phi e k f))))))

;; Instantiate embeddingp-inv-embedding-aux:

(defthmd embeddingp-inv-embedding
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
           (and (embeddingp (inv-embedding phi e k f) k e f)
	        (implies (feltp x k)
                         (equal (embed x (inv-embedding phi e k f) e f)
	                        (preembed x phi e k f))))))

;; The following are simple consequences of the preceding results:

(defthmd comp-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (let ((inv (inv-embedding phi e k f)))
	     (and (embeddingp inv k e f)
	          (equal (comp-embedding inv phi e e f)
		         (id-embedding e f))
                  (equal (comp-embedding phi inv k k f)
		         (id-embedding k f))))))

(defthmd inv-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (equal (inv-embedding (inv-embedding phi e k f) k e f)
	          phi)))

(defthmd embed-embedding-inv
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(feltp x e))
	   (equal (embed (embed x phi k f) (inv-embedding phi e k f) e f)
	          x)))

(defthmd embed-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(feltp x k))
	   (equal (embed (embed x (inv-embedding phi e k f) e f) phi k f)
	          x)))

(defthmd pembed-embedding-inv
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(polyp p e))
	   (equal (pembed (pembed p phi k f) (inv-embedding phi e k f) e f)
	          p)))

(defthmd pembed-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(polyp p k))
	   (equal (pembed (pembed p (inv-embedding phi e k f) e f) phi k f)
	          p)))


;;----------------------------------------------------------------------------------------------------------
;;                                           Fields and Metafields
;;----------------------------------------------------------------------------------------------------------

;; We introduce a constrained field extension e$ over f$ and a unary predicate constrained to recognize a
;; subset of e$ that includes all elements that are lifted from f$ and is closed under the field operations:

(local (in-theory (enable feltp beltp bmul badd)))

(encapsulate (((e$) => *) ((f$) => *) ((m$ *) => *))
   (local (defun e$ () 0))
   (local (defun f$ () 0))
   (local (defun m$ (x) (feltp x 0)))
   (defthmd extensionp-e$-f$
     (extensionp (e$) (f$)))
   (defthm e$-includes-m$
     (implies (m$ x) (feltp x (e$))))
   (defthm m$-includes-f$
     (implies (feltp x (f$)) (m$ (flift x (f$) (e$)))))
   (defthm m$-closed
     (implies (and (m$ x) (m$ y))
              (and (m$ (fadd x y (e$))) (m$ (fmul x y (e$)))))))

;; Informally, we shall refer to m$ as an intermediate metafield between e$ and f$. We would like to identify 
;; an intermediate field k$ between e$ and f$ that corresponds to m$, i.e., that satisfies

;;     (iff (m$ x) (fliftedp x (k$) (e$))).

;; In general, no such intermediate field k exists.  However, there exists an extension of f$ that is
;; isomorphic to e$ and does contain an intermediate field corresponding to m$.  That is, we can construct
;; an extension d$ of f$ with an intermediate field k$ and an isomorphism phi$ from d$ to e$ over f$ such
;; that the image of k$ under phi$ is the metafield defined by m$.  Thus, our objective is the following:

;;     (defthmd metafield-field
;;       (and (extensionp (d$) (k$)) (extensionp (k$) (f$))
;;            (iso-embeddingp (phi$) (d$) (e$) (f$))
;;            (implies (feltp x (d$))
;;                     (iff (m$ (embed x (phi$) (e$) (f$)))
;;                          (fliftedp x (k$) (d$))))))

;; An important application of this result is a functional instantiation in the context of the Fundamental 
;; Theorem of Galois Theory (see galois.lisp).

;; Let d be an extension of f$ and phi an embedding of d in e$ over f$. The following predicate holds iff
;; y is in the range of phi:

(defund in-range-p (y phi d e f)
  (let ((x (preembed y phi d e f)))
    (and (feltp x d)
         (equal (embed x phi e f)
                y))))

(defthmd in-range-p-lemma
  (implies (and (feltp x d)
                (equal (embed x phi e f)
                       y))
	   (in-range-p y phi d e f)))

;; The following predicate holds when the range of phi is included in m$:

(defun-sk m$-includes-range (phi d)
  (forall (y)
    (implies (in-range-p y phi d (e$) (f$))
             (m$ y))))             

;; The following predicate holds when m$ is included in the range of phi:

(defun-sk range-includes-m$ (phi d)
  (forall (y)
    (implies (m$ y)
             (in-range-p y phi d (e$) (f$)))))

;; Suppose y is an element of e$ outside of the range of phi.  Let p = (min-poly y (e$) (f$)) and let
;; p' = (plift p (f$) d).  Since y is a root of (plift p (f$) (e$)) = (pembed p' phi (e$) (f$)), there
;; exists an irreducible monic factor q of p' such that y is a root of (pembed q phi (e$) (f$)).  Since
;; y is not in the range of phi, (degree q) > 1.  Such a polynomial q is identified by the function
;; extension-poly:

(defun extension-poly-aux (l y phi e f)
  (if (consp l)
      (if (prootp y (pembed (car l) phi e f) e)
          (car l)
	(extension-poly-aux (cdr l) y phi e f))
    ()))

(defun extension-poly (y phi d e f)
  (extension-poly-aux (factorization (plift (min-poly y e f) f d) d) y phi e f))

;; An extension d' of d may be constructed by adjoining a root of this polynomial, and phi may be
;; extended to an embedding of d' in e$:

(defthmd extensionp-extension-poly
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
           (let* ((q (extension-poly y phi d (e$) (f$)))
	          (d1 (cons q d))
		  (phi1 (cons y phi)))
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))))))

;; Now suppose m$ includes the range of phi.  We shall show that m$ also includes the range of phi'.  
;; Let x be an element of d1.  Then (polyp x d) and

;;    (embed x phi' (e$) (f$)) = (peval (pembed x phi (e$) (f$)) y (e$)).

;; Since m$ includes the range of phi, m$ includes the coefficients of (pembed x phi (e$) (f$)), and 
;; it follows that m$ contains (embed x phi' (e$) (f$)):

(defthmd m$-peval-pembed
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(m$ y)
		(polyp x d))
	   (m$ (peval (pembed x phi (e$) (f$)) y (e$)))))

;; Thus, m$ includes the range of phi':

(defthmd extension-poly-extends
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let* ((p (extension-poly y phi d (e$) (f$)))
	          (d1 (cons p d))
		  (phi1 (cons y phi)))
	     (and (extensionp d1 d)
	          (embeddingp phi1 d1 (e$) (f$))
		  (m$-includes-range phi1 d1)))))

;; The function extend-embedding recursively extends phi to an embedding of an extension of d in e$ 
;; with range m$. Note that in the context of the recursive call, according to the above lemma, 
;; (cons y phi) is an embedding of (cons p d) in e$ over f$.  By embedding-degree-<=,
;; (edegree (cons p d) (f$)) <= (edegree (e$) (f$)), and therefore the declared measure decreases.

(defthm extend-range-to-m$-measure-decreases
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (and (posp (edegree d (f$)))
	        (posp (edegree (e$) (f$)))
	        (< (edegree d (f$))
	           (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$)))
	        (<= (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$))
	            (edegree (e$) (f$))))))

(defun extend-range-to-m$ (d phi)
  (declare (xargs :measure (nfix (- (edegree (e$) (f$)) (edegree d (f$))))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-range-to-m$-measure-decreases
				         (y (range-includes-m$-witness phi d))))))))
  (let* ((y (range-includes-m$-witness phi d))
         (q (extension-poly y phi d (e$) (f$))))
    (if (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (m$ y) (not (in-range-p y phi d (e$) (f$))))
        (extend-range-to-m$ (cons q d) (cons y phi))
      (mv d phi))))

(defthmd range-extended-to-m$
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (m$-includes-range phi d))
           (mv-let (d1 phi1) (extend-range-to-m$ d phi)
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))
		  (iff (in-range-p y phi1 d1 (e$) (f$)) (m$ y))
		  (equal (restrict-embedding phi1 d1 d) phi)))))

;; By functional instantiation, with (feltp x (e0)) substituted for (m$ x), d may be extended to to 
;; an isomorph of e$.  This requires defining functions analogous to m$-includes-range,
;; range-includes-m$, and extend-range-to-m$:

(defun-sk e-includes-range (phi d e f)
  (forall (y)
    (implies (in-range-p y phi d e f)
             (feltp y e))))

(defun-sk range-includes-e (phi d e f)
  (forall (y)
    (implies (feltp y e)
             (in-range-p y phi d e f))))

;; The third definition requires the following, which is proved by functional instantiation of
;; extend-range-to-m$-measure-decreases:

(defthm extend-to-isomorphism-measure-decreases
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(feltp y (e$))
		(not (in-range-p y phi d (e$) (f$))))
	   (and (posp (edegree d (f$)))
	        (posp (edegree (e$) (f$)))
	        (< (edegree d (f$))
	           (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$)))
	        (<= (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$))
	            (edegree (e$) (f$))))))

(defun extend-to-isomorphism (d phi)
  (declare (xargs :measure (nfix (- (edegree (e$) (f$)) (edegree d (f$))))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-to-isomorphism-measure-decreases
					  (y (range-includes-e-witness phi d (e$) (f$)))))))))
  (let* ((y (range-includes-e-witness phi d (e$) (f$)))
         (q (extension-poly y phi d (e$) (f$))))
    (if (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (feltp y (e$))
	     (not (in-range-p y phi d (e$) (f$))))
        (extend-to-isomorphism (cons q d) (cons y phi))
      (mv d phi))))

;; Note that e$-includes-range holds trivially:

(defthm e-includes-range-rewrite
  (implies (and (embeddingp phi d e f) (extensionp e f) (extensionp d f))
           (e-includes-range phi d e f)))

;; Thus, functional instantiation of range-extended-to-m$ yields the following:

(defthmd range-extended-to-m$-instance
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)))
           (mv-let (d1 phi1) (extend-to-isomorphism d phi)
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))
		  (iff (in-range-p y phi1 d1 (e$) (f$)) (feltp y (e$)))
		  (equal (restrict-embedding phi1 d1 d) phi)))))

;; Combine this with embedding-surjective:

(defthmd extended-to-isomorphism
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)))
           (mv-let (d1 phi1) (extend-to-isomorphism d phi)
	     (and (extensionp d1 d)
		  (iso-embeddingp phi1 d1 (e$) (f$))
		  (equal (restrict-embedding phi1 d1 d) phi)))))

;; The desired extension and isomorphism are constructed in 2 steps.  First, the intermediate 
;; field is constructed by applying extend-range-to-m$ to f$ and the null embedding:

(defund k$ () (mv-nth 0 (mv-list 2 (extend-range-to-m$ (f$) ()))))

;; Let psi$ be the resulting embedding of k$ in e$:

(defund psi$ () (mv-nth 1 (mv-list 2 (extend-range-to-m$ (f$) ()))))

;; The following is an instance of range-extended-to-m$:

(defthmd k$-psi$-lemma
  (and (extensionp (k$) (f$))
       (embeddingp (psi$) (k$) (e$) (f$))
       (iff (in-range-p y (psi$) (k$) (e$) (f$)) (m$ y))))

;; Next we construct the extension d$ and the isomorphism phi$ by applying extend-to-isomorphism to
;; k$ and psi$:

(defund d$ () (mv-nth 0 (mv-list 2 (extend-to-isomorphism (k$) (psi$)))))

(defund phi$ () (mv-nth 1 (mv-list 2 (extend-to-isomorphism (k$) (psi$)))))

(in-theory (disable (d$) (phi$) (k$) (psi$)))

;; The following is an instance of extended-to-isomorphism:

(defthmd d$-phi$-lemma
  (and (extensionp (d$) (k$))
       (iso-embeddingp (phi$) (d$) (e$) (f$))
       (equal (restrict-embedding (phi$) (d$) (k$)) (psi$))))

;; Let x be an element of d$ and let y = (embed x (phi$) (e$) (f$)).  We must show (m$ y) iff x is lifted from k$.
;; Suppose x is lifted from k$.  Let z = (fdrop x (d$) (k$)).  By fdrop-flift, embed-flift-gen, and d$-phi$-lemma,

;;     y = (embed (flift z (k$) (d$)) (phi$) (e$) (f$))
;;       = (embed z (restrict-embedding (phi$) (d$) (k$)) (e$) (f$))
;;       = (embed z (psi$) (e$) (f$)).

;; Thus, (in-range-p y (psi$) (k$) (e$) (f$)) and by k$-psi$-lemma, (m$ y).
;; On the other hand, suppose (m$ y).  Let x' = (preembed y (psi$) (k$) (e$) (f$)).  By k$-psi$-lemma,
;; (feltp x' (k$)) and y = (embed x' (psi$) (e$) (f$)).  By embed-flift-gen and d$-phi$-lemma,

;;   (embed (flift x' (k$) (d$)) (phi$) (e$) (f$)) = (embed x' (restrict-embedding (phi$) (d$) (k$)) (e$) (f$))
;;                                                 = (embed x' (psi$) (e$) (f$))
;;                                                 = y
;;                                                 = (embed x (phi$) (e$) (f$))

;; and by embedding-1-1, x = (flift x' (k$) (d$)).

;; Thus, we have the desired result:

(defthmd metafield-field
  (and (extensionp (d$) (k$)) (extensionp (k$) (f$))
       (iso-embeddingp (phi$) (d$) (e$) (f$))
       (implies (feltp x (d$))
                (iff (m$ (embed x (phi$) (e$) (f$)))
                     (fliftedp x (k$) (d$))))))
