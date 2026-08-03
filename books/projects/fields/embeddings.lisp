(in-package "DM")

(include-book "polynomials")
(local (include-book "support/embeddings"))

;; The theme of the book "extensions" is the reification of the metalogical notion of a field.  Similarly, 
;; the theme of this book is the reification of the notion of a field homomomorphism.  That is, given 
;; extensions e and k of a field f, we shall define the homomorphic embeddings of e in k over f as ACL2 
;; objects.  We shall consider field extensions as vector spaces and embeddings as linear transformations,
;; applying our earlier results on linear algebra ("../linear/").

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
  (if (and (extends e f) (not (equal e f)))
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
  (implies (and (extensionp e d) (extensionp d f))
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
  (if (and (extends e f) (not (equal e f)))
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

;; In the book "../linear/vectors", we constructively define the inverse of a generic injective surjective 
;; linear transformation:

(defund lin-mat ()
  (wcoord-mat (lin-list (vbasis0))))

(defund lin-inv (y)
  (vcomb (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))
         (vbasis0)))

(defthmd lin-lin-inv
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y)))))

;; The following defining emulates that of lin-inv and is similarly constructive:

(defun embedding-mat (phi e k f)
  (ecoord-mat (pembed (ebasis0 e f) phi k f) k f))

(defun embedding-inv (y phi e k f)
  (ecomb (car (emat* (list (ecoords0 y k f)) (inverse-emat (embedding-mat phi e k f) f) f))
	 (ebasis0 e f)
	 e
	 f))

;; The following is a functional instantance of lin-lin-inv:

(defthm embed-embedding-inv
  (implies (and (extensionp e f) (extensionp k f)
                (iso-embeddingp phi e k f)
		(feltp y k))
           (let ((x (embedding-inv y phi e k f)))
             (and (feltp x e)
                  (equal (embed x phi k f) y)))))

;; A trivial consequence:

(defthm embedding-inv-embed
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
                (feltp x e))
	   (let ((y (embed x phi k f)))
	     (and (feltp y k)
	          (equal (embedding-inv y phi e k f) x)))))

;; We shall construct the inverse of an isomorphism, based on the the function embedding-inv.

;; First we observe that embedding-inv is a meta-homorphism:

(defthm embedding-inv-fzero-fone
  (Implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
	   (and (equal (embedding-inv (fzero k) phi e k f)
	               (fzero e))
	        (equal (embedding-inv (fone k) phi e k f)
	               (fone e)))))

(defthm embedding-inv-fadd-fmul
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
		(feltp x k) (feltp y k))
	   (and (equal (embedding-inv (fadd x y k) phi e k f)
	               (fadd (embedding-inv x phi e k f) (embedding-inv y phi e k f) e))
		(equal (embedding-inv (fmul x y k) phi e k f)
	               (fmul (embedding-inv x phi e k f) (embedding-inv y phi e k f) e)))))

(defthm embedding-inv-fixes
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
		(feltp x f))
	   (equal (embedding-inv (flift x f k) phi e k f)
	          (flift x f e))))

;; The definition of the inverse isomorphism emulates the definition of phi1:
          
(defun inv-embedding-aux (phi e k d f)
  (and (extends k d) (extends d f) (not (equal d f))
       (cons (embedding-inv (flift (primitive d) d k) phi e k f)
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
	                        (embedding-inv x phi e k f))))))

;; Instantiate embeddingp-inv-embedding-aux:

(defthmd embeddingp-inv-embedding
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
           (and (embeddingp (inv-embedding phi e k f) k e f)
	        (implies (feltp x k)
                         (equal (embed x (inv-embedding phi e k f) e f)
	                        (embedding-inv x phi e k f))))))

;; The following are simple consequences of the preceding results:

(defthmd comp-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (let ((inv (inv-embedding phi e k f)))
	     (and (embeddingp inv k e f)
	          (equal (comp-embedding inv phi e e f)
		         (id-embedding e f))
                  (equal (comp-embedding phi inv k k f)
		         (id-embedding k f))))))

(defthmd inv-embed-embedding
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
;; Theorem of Galois Theory (see the book "galois").

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
