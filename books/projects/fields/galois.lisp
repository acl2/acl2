(in-package "DM")

(include-book "embeddings")
(include-book "projects/groups/actions" :dir :system)
(local (include-book "support/galois"))

;; In this book, we investigate the automorphism group of a field extension, the characteristic of a field,
;; the formal derivative of a polynomial, separable polynomials, splitting fields, and Galois extensions.
;; The culmination of the book is a formal version of the Fundamental Theorem of Galois Theory.  The proof
;; depends on a variety of previously formalized results in finite group theory ("../groups/") and linear
;; algebra ("../linear/").

;;----------------------------------------------------------------------------------------------------------
;;                                   Automorphism Group of an Extension Field
;;----------------------------------------------------------------------------------------------------------

;; An automorphism of e over f is an embedding of e in itself over f:

(defund autop (a e f)
  (embeddingp a e e f))

(defthm autop-embeddingp
  (implies (autop a e f)
           (embeddingp a e e f)))

(defthm auto-image
  (implies (and (autop a e f) (extensionp e f)
                (feltp x e))
           (feltp (embed x a e f) e)))

;; A handy version of embed-cex-lemma:

(defthmd auto-cex-lemma
  (implies (and (extensionp e f)
                (autop a e f) (autop b e f)
		(not (equal a b)))
	   (let ((x (embed-cex a b e f)))
	     (and (feltp x e)
	          (not (equal (embed x a e f) (embed x b e f)))))))

;; Identity automorphism:

(defund id-auto (e f)
  (id-embedding e f))

(defthm autop-id-auto
  (implies (and (fieldp f) (fieldp e) (extensionp e f))
           (autop (id-auto e f) e f)))

(defthm embed-auto-id
  (implies (and (fieldp f) (fieldp e) (extensionp e f)
                (feltp x e))
	   (equal (embed x (id-auto e f) e f)
	          x)))

;; Composition of automorphisms:

(defund comp-auto (a b e f)
  (comp-embedding a b e e f))

(defthm autop-comp-auto
  (implies (and (extensionp e f) (autop a e f) (autop b e f))
           (autop (comp-auto a b e f) e f)))

(defthm embed-comp-auto
  (implies (and (extensionp e f) (autop a e f) (autop b e f) (feltp x e))
           (equal (embed x (comp-auto a b e f) e f)
	          (embed (embed x b e f) a e f))))

;; Associativity:

(defthm comp-auto-assoc
  (implies (and (extensionp e f)
                (autop a e f) (autop b e f) (autop c e f))
	   (equal (comp-auto (comp-auto a b e f) c e f)
	          (comp-auto a (comp-auto b c e f) e f))))

;; id-auto is a left identity:

(defthm id-auto-id
  (implies (and (extensionp e f)
                (autop a e f))
	   (equal (comp-auto (id-auto e f) a e f)
	          a)))

;; The inverse of an automorphism:
          
(defund inv-auto (a e f)
  (inv-embedding a e e f))

(defthm autop-inv-auto
  (implies (and (extensionp e f)
                (autop a e f))
	   (autop (inv-auto a e f) e f)))

(defthm comp-inv-auto
  (implies (and (extensionp e f)
                (autop a e f))
	   (equal (comp-auto (inv-auto a e f) a e f)
	          (id-auto e f))))

;; The automorphisms of e over f form a group, but we must reorder its elements so that the identity 
;; is the car:

(defund auto-list (e f)
  (cons (id-auto e f)
        (remove1 (id-auto e f) (embeddings e e f))))

(defthm dlistp-auto-list
  (implies (extensionp e f)
           (dlistp (auto-list e f))))

(defthm member-auto-list
  (implies (extensionp e f)
           (iff (member a (auto-list e f))
	        (autop a e f))))

(defthm car-auto-list
  (equal (car (auto-list e f))
         (id-auto e f)))

(defthm len-auto-list
  (implies (extensionp e f)
           (equal (len (auto-list e f))
	          (len (embeddings e e f)))))
    
(defgroup autos (e f)
  (extensionp e f)
  (auto-list e f)
  (comp-auto x y e f)
  (inv-auto x e f))

;; The order of the group is bounded by the degree of the extension (this is an instance of len-embeddings):

(defthmd ord-autos-bound
  (implies (extensionp e f)
           (<= (order (autos e f))
	       (edegree e f))))

;; An isomorphism from e to k over f induces a group isomorphism from (autos e f) to (autos k f):

(defun auto-map-image (x phi e k f)
  (comp-embedding phi (comp-embedding x (inv-embedding phi e k f) k e f) k k f))
  
(defmap auto-map (phi e k f)
  (auto-list e f)
  (auto-map-image x phi e k f))

(defthmd isomorphismp-auto-map
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f)))
	   (isomorphismp (auto-map phi e k f) (autos e f) (autos k f))))

;; The inverse of (auto-map phi e k f) is the isomorphism induced by the inverse of phi:

(defthmd inv-auto-map
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)))
	   (equal (mapply (auto-map (inv-embedding phi e k f) k e f)
	                  (mapply (auto-map phi e k f)
			          x))
	          x)))

;;---------------------------

;; Let e be an extension of d and d an extension of f.  Let phi be a automorphism of e over f.
;; If the restriction of phi to d is the trivial embedding of d in e, then phi naturally corresponds 
;; to an automorphism of e over d:

(defun trunc-embedding (phi e d)
  (firstn (- (len e) (len d)) phi))

;; We shall require the following generalization of this claim:

(defthmd embeddingp-trunc-embedding
  (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                (equal (restrict-embedding phi e d) (trivial-embedding d k f)))
           (let ((psi (trunc-embedding phi e d)))
	     (and (embeddingp psi e k d)
	          (implies (feltp x e)
		           (equal (embed x psi k d)
			          (embed x phi k f)))))))

;; An obvious consequence of the above:

(defthmd pembed-trunc-embedding
  (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                (equal (restrict-embedding phi e d) (trivial-embedding d k f))
		(polyp p e))
           (equal (pembed p (trunc-embedding phi e d) k d)
	          (pembed p phi k f))))

;; The case k = e:

(defthmd autop-trunc-embedding
  (implies (and (extensionp e d) (extensionp d f) (autop phi e f)
                (equal (restrict-embedding phi e d) (trivial-embedding d e f)))
           (let ((psi (trunc-embedding phi e d)))
	     (and (autop psi e d)
	          (implies (feltp x e)
		           (equal (embed x psi e d)
			          (embed x phi e f)))))))


;;----------------------------------------------------------------------------------------------------------
;;                                              Artin's Lemma
;;----------------------------------------------------------------------------------------------------------

;; This is an important lemma for the fundamental theorem.

;; Artin's Lemma: Let e be an extension of f with intermediate field k.  Let h be a subgroup of (autos e f)
;; such that for all x in e, x is fixed by h iff x is lifted from k.  Then (edegree e k) <= (order h).

;; The predicate fixedp recognizes elements of e that are fixed by a subgroup h of (galois e f):

(defun fixedp-aux (x l e f)
  (if (consp l)
      (and (equal x (embed x (car l) e f))
           (fixedp-aux x (cdr l) e f))
    t))

(defund fixedp (x h e f)
  (fixedp-aux x (elts h) e f))

(defthm fixedp-embed
  (implies (and (fixedp x h e f) (in phi h))
           (equal (embed x phi e f) x))
  :hints (("Goal" :in-theory (enable fixedp))))

;; If x is not fixed by h, then we can find an element of h that does not fix x:

(defun fixedp-aux-cex (x l e f)
  (if (consp l)
      (if (equal x (embed x (car l) e f))
          (fixedp-aux-cex x (cdr l) e f)
	(car l))
    ()))

(defund fixedp-cex (x h e f)
  (fixedp-aux-cex x (elts h) e f))

(defthmd fixedp-cex-lemma
  (implies (not (fixedp x h e f))
           (let ((phi (fixedp-cex x h e f)))
	     (and (in phi h)
                  (not (equal x (embed x phi e f)))))))

;; The hypothesis of Artin's Lemma is that k satisfies the following predicate:

(defun-sk fixed-field-p (k h e f)
  (forall (x)
    (implies (feltp x e)
             (iff (fixedp x h e f)
	          (fliftedp x k e)))))

;;-------------------------------------------

;; For the proof, we need some results from linear algebra pertaining to the solutions of a homogeneous
;; system of linear equations.  These results are proved in "../linear/reduction.lisp" for the generic
;; field f0.  We can easily prove by functional instantiation that they hold for an arbitrary field e.

;; In embeddings.lisp, we define several functions pertaining to lists of elements of a field e.  We
;; shall require some additional definitions.

;; Addition, scalar multiplication, and dot product:

(defun elist-add (x y e)
  (if (consp x)
      (cons (fadd (car x) (car y) e)
            (elist-add (cdr x) (cdr y) e))
    ()))

(defun elist-scalar-mul (c x e)
  (if (consp x)
      (cons (fmul c (car x) e)
            (elist-scalar-mul c (cdr x) e))
    ()))

(defun edot (x y e)
  (if (consp x)
      (fadd (fmul (car x) (car y) e)
            (edot (cdr x) (cdr y) e)
	    e)
    (fzero e)))

;; mxn matrix over e:

(defun ematp (a m n e)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      (null a)
    (and (consp a)
	 (elistnp (car a) n e)
	 (ematp (cdr a) (1- m) n e))))

;; Matrix multiplication:

(defun edot-list (x l e)
  (if (consp l)
      (cons (edot x (car l) e)
            (edot-list x (cdr l) e))
    ()))

(defund emat* (a b e)
  (if (consp a)
      (cons (edot-list (car a) (transpose-mat b) e)
            (emat* (cdr a) b e))
    ()))

;; Solution of a system of linear m equations in n unknowns, represented as an mxn matrix:

(defund esolutionp (x a b e)
  (equal (emat* a (col-mat x) e)
         (col-mat b)))

;; The homogeneous case:

(defund esol0p (x a e)
  (and (elistnp x (len (car a)) e)
       (esolutionp x a (elistn0 (len a) e) e)))

;; We need the following lemmas, proved by functional instantiation of the corresponding lemmas in
;; "../linear/fmat.lisp":

(defthmd emat-entry-diff-lemma
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e) (ematp b m n e) (not (equal a b)))
	   (let* ((pair (entry-diff a b))
		  (i (car pair))
		  (j (cdr pair)))
	     (and (natp i) (< i m)
		  (natp j) (< j n)
		  (not (equal (entry i j a) (entry i j b)))))))

(defthmd ematp-transpose
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e))
	   (ematp (transpose-mat a) n m e)))

(defthm transpose-emat-entry
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose-mat a))
		  (entry i j a))))

(defthm transpose-emat-2
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e))
           (equal (transpose-mat (transpose-mat a))
	          a)))

(defthm ematp-emat*
  (implies (and (fieldp e) (ematp a m n e) (ematp b n p e) (posp m) (posp n) (posp p) )
           (ematp (emat* a b e) m p e)))

(defthmd nth-emat*
  (implies (and (fieldp e) (natp m) (ematp a m n e) (natp i) (< i m))
           (equal (nth i (emat* a b e))
	          (edot-list (nth i a) (transpose-mat b) e))))

;; The next 3 results are proved by functional instantiation of corresponding results in
;; "../linear/reduction.lisp".

;; The solution set is closed un addition and scalar multiplication:

(defthmd esol0p-fadd
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
                (esol0p x a e)
		(esol0p y a e))
	   (esol0p (elist-add x y e) a e)))

(defthmd esol0p-scalar-mul
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
                (esol0p x a e)
		(feltp c e))
	   (esol0p (elist-scalar-mul c x e) a e)))

;; If n > m, then there exists a nontrivial solution:

(defun-sk nontrivial-esol0p (a e)
  (exists (x)
    (and (not (elist0p x e))
         (esol0p x a e))))

(defthmd exists-esol0p
  (implies (and (fieldp e) (posp m) (posp n) (> n m) (ematp a m n e))
           (nontrivial-esol0p a e)))

;;-------------------------------------------

;; Proof of Artin's Lemma:  Let (order h) = m and let v be a list of elements of e of length n > m.  We
;; shall show that l is linearly dependent over k.

;; We define an mxn matrix, the ith row of which is the result of applying the ith element of h to each
;; member of v:

(defun embed-mat-aux (v l e f)
  (if (consp l)
      (cons (pembed v (car l) e f)
            (embed-mat-aux v (cdr l) e f))
    ()))

(defund embed-mat (v h e f)
  (embed-mat-aux v (elts h) e f))

(defthmd ematp-embed-mat
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)))
           (ematp (embed-mat v h e f) (order h) n e)))

(defthmd nth-embed-mat
  (implies (and (natp i) (< i (order h)))
           (equal (nth i (embed-mat v h e f))
	          (pembed v (nth i (elts h)) e f))))

;; Let a = (embed-nat v h e f).  We consider the solutions of the homogeneous system corresponding to a.
;; If (elistnp x n e) and i < m, then

;;    (nth i (emat* a (col-mat x) e)) = (edot-list (nth i a) (transpose-mat (col-mat x)) e)
;;                                    = (edot-list (nth i a) (transpose-mat (transpose-mat (list x))) e)
;;                                    = (edot-list (nth i a) (list x) e)
;;                                    = (list (edot (nth i a) x e))

;; and hence

;;    (entry i 0 (emat* a (col-mat x) e)) = (edot (nth i a) x e).

;; Thus, x is a solution iff (edot (nth i a) x e) = (fzero e) for all i < m.

;; We know that the set of solutions is closed under addition and scalar multiplication.  Furthermore, if x
;; is a solution and phi is in h, then (pembed x phi e f) is also a solution.  To prove this, let i < m.
;; For some j < m,

;;     (nth i (elts h)) = (comp-auto phi (nth j (elts h)) e f)

;; and hence

;;    (edot (nth i a) (pembed x phi e f) e)
;;      = (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e) 
;;      = (edot (pembed v (comp-auto phi (nth j (elts h)) e f) e f) (pembed x phi e f) e)
;;      = (edot (pembed (pembed v (nth j (elts h)) e f) phi e f) (pembed x phi e f) e)
;;      = (pembed (edot (pembed v (nth j (elts h)) e f) x e) phi e f)
;;      = (pembed (edot (nth j a) x e) phi e f)
;;      = (pembed (fzero e) phi e f)
;;      = (fzero e).

(defthm esol0p-pembed
  (implies (and (extensionp e f) (posp n) (elistnp v n e)
                (subgroupp h (autos e f))
		(in phi h)
		(esol0p x (embed-mat v h e f) e))
           (esol0p (pembed x phi e f) (embed-mat v h e f) e)))

;; The list of indices of the nonzero entries of an elist:

(defun elist-zeroes-aux (x n e)
  (if (consp x)
      (if (equal (car x) (fzero e))
          (cons n (elist-zeroes-aux (cdr x) (1+ n) e))
	(elist-zeroes-aux (cdr x) (1+ n) e))
    ()))

(defund elist-zeroes (x e)
  (elist-zeroes-aux x 0 e))

(defthmd member-elist-zeroes
  (iff (member k (elist-zeroes x e))
       (and (natp k)
            (< k (len x))
	    (equal (nth k x) (fzero e)))))

(defthm dlistp-elist-zeroes
  (dlistp (elist-zeroes x e)))
  
(defthmd elist-zeroes-bound
  (<= (len (elist-zeroes x e)) (len x)))
  
 ;; If x is a nontrivial solution, then the following locates its first nonzero entry:

(defun first-nonzero-entry (x e)
  (if (consp x)
      (if (equal (car x) (fzero e))
          (1+ (first-nonzero-entry (cdr x) e))
	0)
    ()))

;; If x is not lifted from k, then the following locates its first unlifted entry:

(defun first-unlifted (x k e)
  (if (consp x)
      (if (fliftedp (car x) k e)
          (1+ (first-unlifted (cdr x) k e))
	0)
    ()))

;; If x is a nontrivial solution, then the following multiplies x by the reciprocal of its first nonzero
;; entry:

(defund coerce-entry-to-1 (x e)
  (let ((i (first-nonzero-entry x e)))
    (elist-scalar-mul (frecip (nth i x) e) x e)))           

(defthmd esol0p-coerce-entry-to-1
  (implies (and (extensionp e f) (posp n) (elistnp v n e)
                (subgroupp h (autos e f))
                (esol0p x (embed-mat v h e f) e) (not (elist0p x e)))
	   (let ((x1 (coerce-entry-to-1 x e)))
	     (and (esol0p x1 (embed-mat v h e f) e)
	          (not (elist0p x1 e))
		  (equal (len (elist-zeroes x1 e))
		         (len (elist-zeroes x e)))
		  (equal (nth (first-nonzero-entry x1 e) x1)
		         (fone e))))))

;; Let x be a nontrivial solution.  We shall by show by induction on the number of nonzero entries of x that 
;; there exists a nontrivial solution that is lifted from k.  Let x' = (coerce-entry-to-1 x e).  We may
;; assume that  x' is not lifted from k.  The first nonzero entry of x' is 1.  We shall construct a nontrivial
;; solution with more zeroes than x as follows.  Let (nth j x') be the first entry of x' that is not lifted 
;; from k.  For some phi in h, (embed (nth j x') phi e f) != (nth j x').  Let

;;     x" = (elist-add x' (elist-scalar-mul (fneg (fone e) e) (pembed x' phi e f)) e).

;; By esol0p-pembed, esol0p-fadd, and esol0p-fmul, x" is a solution.  Since

;;     (nth j x") = (nth j x') + (fneg (fone e) e) * (embed (nth j x') phi e f) != 0,

;; x" is nontrivial.  All zeroes of x are also zeroes of x", and in addition, (nth i x") = 0.  Thus, x" has
;; more zeroes than x.

(defund increase-zeroes (x h e k f)
  (let* ((j (first-unlifted x k e))
	 (phi (fixedp-cex (nth j x) h e f)))
    (elist-add x (elist-scalar-mul (fneg (fone e) e) (pembed x phi e f) e) e)))

(defthmd zeroes-increase
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
		(fixed-field-p k h e f)
		(posp n)
	        (elistnp v n e)
                (esol0p x (embed-mat v h e f) e)
	        (not (elist0p x e))
		(not (pliftedp x k e))
		(equal (nth (first-nonzero-entry x e) x) (fone e)))
	   (let ((y (increase-zeroes x h e k f)))
	     (and (esol0p y (embed-mat v h e f) e)
	          (not (elist0p y e))
		  (<= (len (elist-zeroes y e)) n)
		  (> (len (elist-zeroes y e))
		     (len (elist-zeroes x e)))))))

;; The desired solution is computed recursively:

(defun plifted-solution-aux (x v n h e k f)
  (declare (xargs :measure (nfix (- n (len (elist-zeroes x e))))
                  :hints (("Goal" :use (esol0p-coerce-entry-to-1
		                        (:instance zeroes-increase (x (coerce-entry-to-1 x e))))))))
  (if (and (extensionp e f) (extensionp e k) (extensionp k f)
           (subgroupp h (autos e f))
	   (fixed-field-p k h e f)
	   (natp n) (> n (order h))
	   (elistnp v n e)
           (esol0p x (embed-mat v h e f) e)
	   (not (elist0p x e)))
      (let ((x1 (coerce-entry-to-1 x e)))
        (if (pliftedp x1 k e)
            x1
          (plifted-solution-aux (increase-zeroes x1 h e k f) v n h e k f)))
    ()))

(defund plifted-solution (v h e k f)
  (plifted-solution-aux (nontrivial-esol0p-witness (embed-mat v h e f) e) v (len v) h e k f))

;; The following is proved by induction on the number of nonzero entries of x:

(defthmd pliftedp-plifted-solution-aux
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (natp n) (> n (order h))
                (elistnp v n e)
                (esol0p x (embed-mat v h e f) e)
	        (not (elist0p x e)))
      (let ((x1 (plifted-solution-aux x v n h e k f)))
        (and (esol0p x1 (embed-mat v h e f) e)
	     (not (elist0p x1 e))
	     (pliftedp x1 k e)))))

;; By exists-esol0p, (nontrivial-esol0p-witness (embed-mat v h e f) e) satisfies the hypothesis, and
;; therefore we have

(defthmd pliftedp-plifted-solution
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (posp n) (> n (order h))
                (elistnp v n e))
	   (let ((x (plifted-solution v h e k f)))
             (and (esol0p x (embed-mat v h e f) e)
	          (not (elist0p x e))
	          (pliftedp x k e)))))

;; We instantiate this result with v = (ebasis0 e k), the canonical basis of e as a vector space over k, and
;; n = (len v) = (edegree e k).  We shall assume n > (order h) and derive a contradiction.  The conclusion
;; of the lemma holds for x = (plifted-solution v h e k f).  Let c = (pdrop x e k).  Then x = (plift c k e),
;; (elistnp c n k), and (not (elistn0p c k)).  Let a = (embed-mat v h e f).  Since (esol0p x a e),

;;     (emat* a (col-mat x) e) = (elistn0 m e)

;; and in particular,

;;     (car (emat* a (col-mat x) e)) = (edot (car a) x e) = 0

;; where

;;    (car a) = (pembed v (car (elts h)) e f) = v.

;; Thus, (ecomb c v e) = (edot v x e) = 0, contradicting ebasis0-lin-indep.

(defthmd artin-lemma
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f))
	   (<= (edegree e k) (order h))))
	   

;;----------------------------------------------------------------------------------------------------------
;;                                      Characteristic of a Field
;;----------------------------------------------------------------------------------------------------------

;; The following function computes the sum of n copies of an element of a field f:

(defun ntimes (n x f)
  (if (zp n)
      (fzero f)
    (fadd x (ntimes (1- n) x f) f)))

(defthm feltp-ntimes
  (implies (and (fieldp f) (feltp x f) (natp n))
           (feltp (ntimes n x f) f)))

(defthmd ntimes-plus
  (implies (and (fieldp f) (feltp x f) (natp n) (natp m))
           (equal (ntimes (+ n m) x f)
	          (fadd (ntimes n x f) (ntimes m x f) f))))

;; We have a natural mapping from the natural numbers to f:

(defund fnat (n f)
  (ntimes n (fone f) f))

(defthm feltp-fnat
  (implies (and (fieldp f) (natp n))
           (feltp (fnat n f) f)))

(defthm fnat-0
  (implies (fieldp f)
           (equal (fnat 0 f)
	          (fzero f))))

(defthmd fnat-plus
  (implies (and (fieldp f) (natp n) (natp m))
           (equal (fnat (+ n m) f)
	          (fadd (fnat n f) (fnat m f) f))))

(defthmd ntimes-fnat
  (implies (and (fieldp f) (feltp x f) (natp n))
           (equal (ntimes n x f)
	          (fmul (fnat n f) x f))))

(defthmd fnat-product
  (implies (and (fieldp f) (natp n) (natp m))
           (equal (fnat (* n m) f)
	          (fmul (fnat n f) (fnat m f) f))))

;; The characteristic of f is the minimal positive n such that (fnat n f) = (fzero f), or 0 if
;; no such n exists.  We use defchoose to formalize this notion:

(defchoose n0 n (f)
  (and (posp n)
       (equal (fnat n f) (fzero f))))

(defun fchar-aux (k n f)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (posp k) (posp n) (<= k n) (equal (fnat n f) (fzero f)))
      (if (equal (fnat k f) (fzero f))
          k
	(fchar-aux (1+ k) n f))
    0))

(defund fchar (f)
  (fchar-aux 1 (n0 f) f))

(defthmd fchar-0-fnat-non-0
  (implies (and (fieldp f) (equal (fchar f) 0) (posp n))
           (not (equal (fnat n f) (fzero f)))))

(defthmd fchar-not-0-fnat-0
  (implies (and (fieldp f) (not (equal (fchar f) 0)))
           (and (posp (fchar f))
	        (equal (fnat (fchar f) f) (fzero f)))))

(defthm fchar-min-0
  (implies (and (fieldp f) (not (equal (fchar f) 0))
                (posp n) (equal (fnat n f) (fzero f)))
	   (<= (fchar f) n)))

;; The rational field Q has characteristic 0:

(defthm fnat-Q
  (implies (natp n)
           (equal (fnat n 0) n)))

(defthmd fchar-Q
  (equal (fchar 0) 0))

;; The prime field Fp has characteristic p:

(defthmd ntimes-Fp
  (implies (and (primep f) (natp n))
           (equal (ntimes n 1 f) (mod n f))))

(defthm fnat-Fp
  (implies (and (primep f) (natp n))
           (equal (fnat n f) (mod n f))))

(defthmd fchar-fp
  (implies (primep p)
           (equal (fchar p) p)))

;; It follows from field-integral-domain that the characteristic of any field is either 0 or prime:

(defthm primep-fchar
  (implies (and (fieldp f) (not (equal (fchar f) 0)))
           (primep (fchar f))))

;; An equivalent condition for (ntimes n x f) = (fzero f):

(defthmd ntimes-fchar-0
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))) (posp n))
           (iff (equal (ntimes n x f) (fzero f))
	        (and (primep (fchar f))
		     (divides (fchar f) n)))))

(defthmd fnat-fchar-0
  (implies (and (fieldp f) (posp n))
           (iff (equal (fnat n f) (fzero f))
	        (and (primep (fchar f))
		     (divides (fchar f) n)))))

;; The characteristic of a field is the same as that of its base field:

(defthmd flift-ntimes
  (implies (and (extensionp e f) (natp n))
           (equal (flift (ntimes n (fone f) f) f e)
	          (ntimes n (fone e) e))))

(defthmd fnat-0-extension
  (implies (and (extensionp e f) (natp n))
           (iff (equal (fnat n e) (fzero e))
	        (equal (fnat n f) (fzero f)))))

(defthmd fchar-extension
  (implies (extensionp e f)
           (equal (fchar e) (fchar f))))

(defthm extensionp-base
  (implies (fieldp f)
           (extensionp f (fbase f))))

(defthmd fchar-base
  (implies (fieldp f)
           (equal (fchar f) (fchar (fbase f)))))


;;----------------------------------------------------------------------------------------------------------
;;                                           Formal Derivative
;;----------------------------------------------------------------------------------------------------------

;; The formal deriviative of a polynomial provides a test for multiple roots:

(defun derivative-aux (p f)
  (if (and (consp p) (consp (cdr p)))
      (cons (fmul (fnat (degree p) f) (car p) f)
            (derivative-aux (cdr p) f))
    ()))

(defun derivative (p f)
  (if (pconstp p)
      (pzero f)
    (pstrip (derivative-aux p f) f)))

;; The derivative of a polynomial is a polynomial:

(defthm feltsp-derivative-aux
  (implies (and (fieldp f) (feltsp p f))
           (feltsp (derivative-aux p f) f)))

(defthmd polyp-derivative
  (implies (and (fieldp f) (polyp p f))
           (let ((d (derivative p f)))
             (and (polyp d f)
	          (or (pconstp p)
		      (< (degree d) (degree p)))))))

;; The derivative of a constant is 0:

(defthmd derivative-pconstp
  (implies (pconstp p)
           (equal (derivative p f)
	          (pzero f))))

;; Derivative of a linear polynomial:

(defthmd derivative-linear
  (implies (and (fieldp f) (polyp p f) (equal (degree p) 1))
           (equal (derivative p f)
	          (list (car p)))))

;; The derivative of a non-constant polynomial is a polynomial of lesser degree:

(defthm len-derivative-aux
  (implies (and (fieldp f) (feltsp p f) (consp p))
           (equal (len (derivative-aux p f))
		  (1- (len p)))))

;; If (degree p) is not divisible by the characteristic of the field, then the degree of its
;; derivative is (degree p) - 1:

(defthmd derivative-max-degree
  (implies (and (fieldp f) (polyp p f) (not (pconstp p))
                (not (equal (fnat (degree p) f) (fzero f))))
	   (and (equal (derivative p f) (derivative-aux p f))
	        (equal (degree (derivative p f)) (1- (degree p))))))

;; Derivative of a sum:
			  
(defthmd derivative-aux-faddl
  (implies (and (fieldp f) (feltsp p f) (feltsp q f))
           (equal (derivative-aux (faddl p q f) f)
                  (faddl (derivative-aux p f)
		         (derivative-aux q f)
			 f))))

(defthmd pstrip-derivative-aux-pstrip
  (implies (and (fieldp f) (feltsp p f) (consp (cdr (pstrip p f))))
           (equal (pstrip (derivative-aux (pstrip p f) f) f)
	          (pstrip (derivative-aux p f) f ))))

(defthmd derivative-padd
  (implies (and (fieldp f) (polyp p f) (polyp q f))
           (equal (derivative (padd p q f) f)
	          (padd (derivative p f) (derivative q f) f))))

;; Proof:  The claim is trivial is either p or q is a constant.  If (padd p q f) = (pzero f), then
;; (padd (derivative p f) (derivative q f) f) = (pzero f) = (derivative (padd p f) (padd q f) f).
;; In the remaining case,

;; (derivative (padd p q f) f)
;;   = (pstrip (derivative-aux (padd p q f) f) f)                      [definition of derivative]
;;   = (pstrip (derivative-aux (pstrip (faddl p q f) f) f) f)          [definition of padd]
;;   = (pstrip (derivative-aux (faddl p q f) f) f)                     [pstrip-derivative-aux-pstrip]
;;   = (pstrip (faddl (derivative-aux p f) (derivative-aux q f) f) f)  [derivative-aux-faddl]
;;   = (pstrip (faddl (pstrip (derivative-aux p f) f)                  [pstrip-faddl-pstrip-pstrip]
;;                    (pstrip (derivative-aux q f) f)
;;                    f)
;;             f)
;;   = (pstrip (faddl (derivative p f) (derivative q f) f) f)          [definition of derivative]
;;   = (padd (derivative p f) (derivative q f) f)                      [definition of padd]

;;--------------------------------------------------

;; The proof of the product rule requires several lemmas:

(defthmd derivative-cmul
  (implies (and (fieldp f) (polyp p f) (feltp c f) (not (equal c (fzero f))))
	   (equal (derivative (cmul c p f) f)
	          (cmul c (derivative p f) f)))
  :hints (("Goal" :in-theory (enable pzero pstrip-cmul derivative)
                  :use (derivative-cmul-1 derivative-aux-cmul))))

(defthmd derivative-monomial
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k))
           (equal (derivative (monomial c k f) f)
	          (cmul (fnat k f) (monomial c (1- k) f) f)))
  :hints (("Goal" :in-theory (enable derivative pconstp monomial-rewrite)
                  :use (derivative-monomial-4 derivative-monomial-7))))

;; The following function is useful for expressing a formula for the derivative of a
;; shifted polynomial:

(defund pshift$ (p k f)
  (if (equal p (pzero f))
      (pzero f)
    (pshift p k f)))

(defthmd padd-pshift$
  (implies (and (fieldp f) (polyp p f) (polyp q f) (natp k))
           (equal (padd (pshift$ p k f) (pshift$ q k f) f)
	          (pshift$ (padd p q f) k f))))

(defthmd cmul-pshift$
  (implies (and (fieldp f) (feltp c f) (natp k)
                (polyp p f) (not (equal p (pzero f))))
           (equal (cmul c (pshift p k f) f)
	          (pshift$ (cmul c p f) k f))))

(defthmd derivative-pshift
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k))
           (equal (derivative (pshift p k f) f)
                  (padd (pshift$ (derivative p f) k f)
                        (cmul (fnat k f) (pshift p (1- k) f) f)
	                f))))

;; Proof: Let d = (degree p), c = (car p), p' = (pstrip (cdr p) f).  If d = 0, then p = (list c),
;; (derivative p f) = (pzero f), and

;;   (derivative (pshift p k f) f) = (derivative (monomial c k f) f)
;;                                 = (cmul (fnat k f) (monomial c (1- k) f) f)
;;                                 = (cmul (fnat k f) (pshift c (1- k) f) f)
;;                                 = (pshift$ (derivative p f) k f) + (cmul (fnat k f) (pshift c (1- k) f) f)

;; Assume d > 0.  Then p = (monomial c d f) + p' and

;;   (derivative (pshift (monomial c d f) k f) f)
;;     = (derivative (monomial c (+ d k) f) f)
;;     = (cmul (fnat (+ d k) f) (monomial c (1- (+ d k)) f) f)
;;     = (cmul (fnat d f) (monomial c (1- (+ d k)) f) f) + (cmul (fnat k f) (monomial c (1- (+ d k)) f) f)
;;     = (cmul (fnat d f) (pshift (monomial c (1- d) f) k f) f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)
;;     = (pshift$ (cmul (fnat d f) (monomial c (1- d) f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)
;;     = (pshift$ (derivative (monomial c d f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)

;; If p' = (pzero f), then

;;   (derivative (pshift p k f) f)
;;     = (derivative (pshift (monomial c d f) k f) f)
;;     = (pshift$ (derivative (monomial c d f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)
;;     = (pshift$ (derivative p f) k f) + (cmul (fnat k f) (pshift p (1- k) f) f)

;; Suppose p' != (pzero).  By induction,

;;   (derivative (pshift p' k f) f) = (pshift$ (derivative p' f) k f) + (cmul (fnat k f) (pshift p' (1- k) f) f)

;; Thus,

;;   (derivative (pshift p k f) f)
;;     = (derivative (pshift ((monomial c d f) + p') k f) f)
;;     = (derivative ((pshift (monomial c d f) k f) + (pshift p' k f)) f)
;;     = (derivative (pshift (monomial c d f) k f) f) + (derivative (pshift p' k f) f)
;;     =  ((pshift$ (derivative (monomial c d f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f))
;;      + ((pshift$ (derivative p' f) k f) + (cmul (fnat k f) (pshift p' (1- k) f) f))
;;     =  ((pshift$ (derivative (monomial c d f) f) k f) + (pshift$ (derivative p' f) k f))
;;      + ((cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f) + (cmul (fnat k f) (pshift p' (1- k) f) f))

;; where

;;   (pshift$ (derivative (monomial c d f) f) k f) + (pshift$ (derivative p' f) k f)
;;     = (pshift$ ((derivative (monomial c d f) f) + (derivative p' f)) k f)
;;     = (pshift$ (derivative ((monomial c d f) f) + p') k f) 
;;     = (pshift$ (derivative p f) k f)

;; and

;;   (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f) + (cmul (fnat k f) (pshift p' (1- k) f) f)
;;     = (cmul (fnat k f) ((pshift (monomial c d f) (1- k) f) + (pshift p' (1- k) f)) f)
;;     = (cmul (fnat k f) (pshift ((monomial c d f) + p') (1- k) f) f)
;;     = (cmul (fnat k f) (pshift p (1- k) f) f)

;; and hence

;;   (derivative (pshift p' k f) k f) = (pshift$ (derivative p f) k f) + (cmul (fnat k f) (pshift c (1- k) f) f).


(defthmd derivative-pmul
  (implies (and (fieldp f) (polyp p f) (polyp q f))
           (equal (derivative (pmul p q f) f)
                  (padd (pmul (derivative p f) q f)
                        (pmul p (derivative q f) f)
                        f))))                        

;; Proof:  We may assume (degree p) > 0 and (degree q) > 0.  Let k = (degree p), c = (car p), and
;; p' = (pstrip (cdr p) f).  Then

;;   p = (padd (monomial c k f) p' f)  [pdecomp]

;;   (derivative p f) = (padd (derivative (monomial c k f) f)            [derivative-padd]
;;                            (derivative p' f)
;;			      f)
;;                    = (padd (cmul (fnat k f) (monomial c (1- k) f) f)  [derivative-monomial]
;;                            (derivative p' f)
;;			      f)

;; and

;;   (derivative (pmul p q f) f) = (derivative (padd (pshift (cmul c q f) k f)     [definition of pmul]
;;                                                   (pmul p' q f)
;;                                                   f)
;;                                               f)
;;                               = (padd (derivative (pshift (cmul c q f) k f) f)  [derivative-padd] 
;;                                       (derivative (pmul p' q f) f)
;;                                       f)

;; Consider the 2 terms of the last sum.  The first term is

;;   (derivative (pshift (cmul c q f) k f) f)
;;     = (padd (pshift$ (derivative (cmul c q f) f) k f)              [derivative-pshift]
;;             (cmul (fnat k f) (pshift (cmul c q f) (1- k) f) f)
;;             f)

;; where

;;   (pshift$ (derivative (cmul c q f) f) k f)
;;     = (pshift$ (cmul c (derivative q f) f) k f)     [derivative-cmul]
;;     = (pmul (monomial c k f) (derivative q f) f)    [pmul-monomial]

;; and

;;   (cmul (fnat k f) (pshift (cmul c q f) (1- k) f) f)
;;     = (cmul (fnat k f) (pmul (monomial c (1- k) f) q f) f)   [pmul-monomial]
;;     = (pmul (cmul (fnat k f) (monomial c (1- k) f) f) q f)   [cmul-pmul]

;; By induction, the second term is

;;   (derivative (pmul p' q f) f) = (padd (pmul (derivative p' f) q f) (pmul p' (derivative q f) f) f)

;; Thus, by the algebraic properties of the polynomial ring,

;;   (derivative (pmul p q f) f)
;;     = (padd (padd (pmul (monomial c k f) (derivative q f) f)
;;                   (pmul (cmul (fnat k f) (monomial c (1- k) f) f) q f)
;;                   f)
;;             (padd (pmul (derivative p' f) q f)
;;                   (pmul p' (derivative q f) f)
;;                   f)
;;             f)
;;     = (padd (padd (pmul (cmul (fnat k f) (monomial c (1- k) f) f) q f)
;;                   (pmul (derivative p' f) q f)
;;		     f)
;;	       (padd (pmul (monomial c k f) (derivative q f) f)
;;	             (pmul p' (derivative q f) f)
;;		     f)
;;	       f)
;;     = (padd (pmul (padd (cmul (fnat k f) (monomial c (1- k) f) f)
;;                         (derivative p' f)
;;			   f)
;;		     q f)
;;	       (pmul (padd (monomial c k f) p' f) (derivative q f) f)
;;             f)
;;     = (padd (pmul (derivative p f) q f)
;;             (pmul p (derivative q f) f)
;;             f)

;;-----------------------------------------------------

;; The derivative commutes with phom:

(defthmd derivative-phom
  (implies (polyp p (fld1))
           (equal (derivative (phom p) (fld2))
	          (phom (derivative p (fld1))))))

;; By functional instantiation, the derivative commutes with both plift and pembed:

(defthmd derivative-plift
  (implies (and (extensionp e f) (polyp p f))
           (equal (derivative (plift p f e) e)
	          (plift (derivative p f) f e))))

(defthmd derivative-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e))
	   (equal (derivative (pembed p phi k f) k)
	          (pembed (derivative p e) phi k f))))
		  

;;----------------------------------------------------------------------------------------------------------
;;                                             Separable Polynomials
;;----------------------------------------------------------------------------------------------------------

;; Let r = (root-poly x f).  x is a multiple root of p iff r^2 divides p:

(defund multiple-prootp (x p f)
  (pdivides (ppower (root-poly x f) 2 f) p f))

;; Here p' will denote the derivative of p.  Let x be a root of p.  Then p = r * q, p' = q + r * q', and 
;; x is a multiple root of p <=> x is a root of q <=> x is a root of p':

(defthm derivative-root-poly
  (implies (and (fieldp f) (feltp x f))
           (equal (derivative (root-poly x f) f)
	          (pone f))))

(defthm root-poly-nonzero
  (implies (and (fieldp f) (feltp x f))
           (not (equal (root-poly x f) (pzero f)))))

(defthmd prootp-derivative
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (iff (multiple-prootp x p f)
                (and (prootp x p f)
                     (prootp x (derivative p f) f)))))

;; p is separable if p and p' are relatively prime:

(defund separablep (p f)
  (equal (pgcd p (derivative p f) f)
         (pone f)))

;; A separable polynomial over f has no multiple roots in f:

(defthmd separable-no-multiple-root
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (feltp x f))
           (not (multiple-prootp x p f))))

;; A nonzero constant polynomial is separable:

(defthmd pconstp-separablep
  (implies (and (fieldp f) (polyp p f) (= (degree p) 0) (not (equal p (pzero f))))
           (separablep p f)))
		        
;; A linear polynomial is separable:

(defthmd separablep-linear
  (implies (and (fieldp f) (polyp p f) (equal (degree p) 1))
           (separablep p f)))

;;----------------------------------------------------------------------------------------------------------
;; Suppose p is separable and divisible by q.  Let p = q * s.  Then p' = q' * s + q * s'.  Let 
;; g = (pgcd q q').  Since g divides q and q', g divides p and p', which implies g = 1 and q is separable:

(defthmd pdivides-separablep
  (implies (and (fieldp f) (polyp p f) (polyp q f) (>= (degree q) 1) (separablep p f)
                (not (equal p (pzero f))) (not (equal q (pzero f))) (pdivides q p f))
           (separablep q f)))

;; We shall prove that the product of relatively prime separable polynomials is separable.
;; Let p and q be nonzero separable polynomials with (pgcd p q f) = 1 and suppose p * q is not separable.
;; Then we can find a non-constant irreducible polynomial r that divides both p * q and 
;; (p * q)' = p' * q + p * q'.  Suppose r divides p.  Then r divides p * q' and therefore r divides
;; (p * q)' - p * q' = p' * q.  But then either r divides p', contradicting separability of p, or r
;; divides q, contradicting (pgcd p q f) = 1.  Thus r cannot divide p, and similarly, r cannot 
;; divide q.  By peuclid, r does not divide p * q, a contradiction.

(defthmd separablep-pmul
  (implies (and (fieldp f)
                (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (polyp q f) (not (equal q (pzero f))) (separablep q f)
                (equal (pgcd p q f) (pone f)))
	   (separablep (pmul p q f) f)))

;; By plift-pgcd and derivative-plift, p is separable over f iff (plift p f e) is separable over e:
			
(defthmd separablep-extension
  (implies (and (extensionp e f) (polyp p f) (not (equal p (pzero f))))
           (iff (separablep (plift p f e) e)
                (separablep p f))))

;; a separable polynomial over f has no multiple roots in any extension of f:

(defthmd separable-no-multiple-root-extension
  (implies (and (extensionp e f)
                (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (feltp x e))
           (not (multiple-prootp x (plift p f e) e))))
			
;; A separable polynomial has a nonzero derivative:

(defthmd derivative-pzero-not-separablep
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1) (equal (derivative p f) (pzero f)))
           (not (separablep p f))))

;; An irreducible polynomial is separable unless its derivative is 0:

(defthmd separablep-derivative-nonzero
  (implies (and (fieldp f) (polyp p f) (irreduciblep p f) (not (pconstp p)))
           (iff (separablep p f)
                (not (equal (derivative p f) (pzero f))))))

;; In a field of characteristic 0, the derivative of a non-constant polynomial cannot be 0.  Consequently, 
;; every irreducible polynomial over a field of characteric 0 is separable:

(defthmd char-0-derivative-nonzero
  (implies (and (fieldp f) (= (fchar f) 0) (polyp p f) (not (pconstp p)))
           (not (equal (derivative p f) (pzero f)))))

(defthmd char-0-separablep
  (implies (and (fieldp f) (= (fchar f) 0)
                (polyp p f) (irreduciblep p f) (not (equal p (pzero f))))
           (separablep p f)))
                        
;; It is also true that in any extension of Fp, i.e., any finite field, every polynomial is separable, but the
;; proof of this result is deferred to the book "finite".  Thus, only infinite fields of prime characteristic
;; may have inseparable polynomials.


;;----------------------------------------------------------------------------------------------------------
;;                                           Splitting Polynomials
;;----------------------------------------------------------------------------------------------------------

;; A polynomial over a field f splits in f if it is a product of linear factors:

(defund splits (p f)
  (equal (len (factorization p f))
         (degree p)))

;; A linear polynomial splits:

(defthmd linear-splits
  (implies (equal (degree p) 1)
           (splits p f)))

;; A non-linear irreducible polynomial does not split:

(defthmd irreducible-not-splits
  (implies (and (> (degree p) 1) (irreduciblep p f))
           (not (splits p f))))
	   
;; A polynomial splits in f iff it has no nonlinear irreducible factor over f.  To prove this, we define a
;; function that searches the factorization of p for such a factor:

(defun find-nonlinear-poly (l)
  (if (consp l)
      (if (> (degree (car l)) 1)
          (car l)
	(find-nonlinear-poly (cdr l)))
    ()))

(defund nonlinear-irred-factor (p f)
  (find-nonlinear-poly (factorization p f)))

(defthmd nonlinear-irred-factor-nonlinear
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (let ((q (nonlinear-irred-factor p f)))
             (implies q
                      (and (polyp q f) (monicp q f) (irreduciblep q f)
	                   (pdivides q p f) (> (degree q) 1))))))

(defthmd nonlinear-divisor-nonlinear-irred-factor
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (> (degree q) 1) (irreduciblep q f)
		(pdivides q p f))
           (nonlinear-irred-factor p f)))

(defthmd not-nonlinear-irred-factor-nonlinear
  (implies (and (member q (factorization p f)) (> (degree q) 1))
           (nonlinear-irred-factor p f)))

(defthmd splits-nonlinear-irred-factor
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (iff (splits p f)
	        (not (nonlinear-irred-factor p f)))))

;; If p splits, then so does any divisor of p:

(defthmd pdivides-splits
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1) (splits p f)
                (polyp q f) (monicp q f) (>= (degree q) 1) (pdivides q p f))
           (splits q f)))
			
;; If p and q both split, then so does p * q:

(defthmd splits-pmul
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits p f)
                (polyp q f) (monicp q f) (>= (degree q) 1) (splits q f))
	   (splits (pmul p q f) f)))

;; Let phi be an embedding of e in k over f and let p be a polynomial over e.  If p splits in e, then
;; (pembed p phi k f) splits in k.  The proof is by induction on (degree p).  If p is irreducible, then p is
;; linear and (embed p phi k f) is linear and therefore splits.  Otherwise, let q = (pfactor p e) and
;; r = (pquot p q e).  Then p = q * r and by pdivides-splits, q and r split in e.  By induction, we may
;; assume (embed q phi k f) and (embed r phi k f) both split in k.  But then by splits-pmul and pembed-pmul,

;;    (pembed p phi k f) = (embed q phi k f) * (embed r phi k f)

;; also splits in k.

(defthmd splits-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (monicp p e) (>= (degree p) 1) (splits p e))
	   (splits (pembed p phi k f) k)))

;; If a separable polynomial p splits, then it has (degree p) distinct roots:
	   
(defthmd len-proots-max
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (splits p f) (separablep p f))
           (equal (len (proots p f))
	          (degree p))))
		  

;;----------------------------------------------------------------------------------------------------------
;;                                    Extension by Roots of a Polynomial
;;----------------------------------------------------------------------------------------------------------

;; Let p be a polynomial over f.  An extension e of f is an extension by roots of p if e is 
;; constructed by successively adjoining roots of p:

(defun extension-by-roots-p (p e f)
  (if (extensionp e f)
      (if (equal e f)
          t
	(and (extension-by-roots-p p (cdr e) f)
	     (pdivides (car e) (plift p f (cdr e)) (cdr e))))
    ()))

;; Let p be a polynomial over f and let e and k be extensions of f. If e is an extension by roots of p and
;; p splits in k, then we can construct an embedding of e in k over f:

(defun embedding-of-extension-by-roots (e k f)
  (if (equal e f)
      ()
    (and (consp e)
         (let ((phi (embedding-of-extension-by-roots (cdr e) k f)))
           (cons (car (proots (pembed (car e) phi k f) k))
	         phi)))))

;; Let phi = (embedding-of-extension-by-roots e k f).  To prove that phi is indeed an embedding of e, we
;; assume that (cdr phi) is an embedding of (cdr e), and we must show that (pembed (car e) (cdr phi) k f)
;; has a root in k.  Since (car e) divides (plift p f (cdr e)), (pembed (car e) (cdr phi) k f) divides
;; (pembed (plift p f (cdr e)) (cdr phi) k f), which, according to pembed-fixes, is (plift p f k).  Since
;; (plift p f k) splits in k, so does its divisor (pembed (car e) (cdr phi) k f), which must therefore have
;; at least 1 root.

(defthmd pembed-splits
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k)
		(polyp q e) (monicp q e) (>= (degree q) 1) (pdivides q (plift p f e) e))
	   (let ((s (pembed q phi k f)))
	     (and (polyp s k)
	          (monicp s k)
		  (>= (degree s) 1)
		  (pdivides s (plift p f k) k)
		  (splits s k)))))

(defthmd proot-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k)
		(polyp q e) (monicp q e) (>= (degree q) 1) (pdivides q (plift p f e) e))
	   (consp (proots (pembed q phi k f) k))))

(defthmd embeddingp-embedding-of-extension-by-roots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (extension-by-roots-p p e f)
                (extensionp k f) (splits (plift p f k) k))
	   (embeddingp (embedding-of-extension-by-roots e k f) e k f)))

;; If the hypothesis of embeddingp-embedding-of-extension-by-roots is extended with the assumption that p
;; is separable, then the number of such embeddings is the degree of e over f.  (Note that this is the
;; maximum number allowed by the lemma len-embeddings.)

(defthmd proots-pembed-separablep
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k) (separablep p f)
		(polyp q e) (monicp q e) (>= (degree q) 1) (pdivides q (plift p f e) e))
	   (equal (len (proots (pembed q phi k f) k))
	          (degree q))))

(defthmd len-embeddings-separablep
  (implies (and (extensionp e f) (extensionp k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (separablep p f)
		(extension-by-roots-p p e f) (splits (plift p f k) k))
	   (equal (len (embeddings e k f))
	          (edegree e f))))

;; We shall prove that the degree of an extension by roots of p over f is at most the factorial of the 
;; degree of p.  This requires a couple of lemmas.  This is the first:

;; Let p be a non-constant monic polynomial over f and suppose p does not split in f.  Let q be a nonlinear 
;; irreducible factot of p,  let e be the simple extension field (q . f), and let p' = (plift p f e) and 
;; q' = (plift q f e).  The number of roots of p' in e is greater than the number of roots of p in f.

;; First note that each root of p in f lifts to a unique root of p' in e:

(defthmd prootp-flift
  (implies (and (extensionp e f) (feltp x f) (polyp p f) (prootp x p f))
           (prootp (flift x f e) (plift p f e) e))
  :hints (("Goal" :in-theory (enable prootp)  
                  :use (flift-peval ))))

(defthmd dlistp-plift-proots
  (implies (and (extensionp e f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (dlistp (plift (proots p f) f e))))

(defthmd sublistp-plift-proots
  (implies (and (extensionp e f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (sublistp (plift (proots p f) f e)
	             (proots (plift p f e) e))))

;; Now (primitive e) is a root of p', since it is a root of q' and q' divides p:

(defthmd pdivides-prootp
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f)))
                (polyp q f) (pdivides p q f)
                (feltp x f) (prootp x p f))
	   (prootp x q f)))

(defthmd prootp-primitive-plift
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (> (degree q) 1) (pdivides q p f))
           (let ((e (cons q f)))
	     (and (fieldp e)
	          (member (primitive e) (proots (plift p f e) e))))))

;; Furthermore, (primitive e) is not lifted from f, since its minimal polynomial p is nonlinear:
 
(defthmd primitive-not-lifted
  (implies (and (fieldp f) (consp f) (feltsp l (cdr f)))
           (not (member (primitive f) (plift l (cdr f) f)))))

(defthmd not-member-primitive-plift-proots
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (monicp p (cdr f)) (>= (degree p) 1))
           (not (member (primitive f) (plift (proots p (cdr f)) (cdr f) f)))))

;; Thus, we have the following:

(defthmd len-proots-increases
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (> (degree q) 1) (pdivides q p f))
	   (let ((e (cons q f)))
	     (> (len (proots (plift p f e) e))
	        (len (proots p f))))))

;; Now let e be an extension by roots of p over f.  let d = (degree p) and n = (len e) - (len f).  
;; It follows from len-proots-increases by induction that n <= (len (proots (plift p f e) e):

(defthmd len-proots-extension-by-roots
  (implies (and (extensionp e f)
                (polyp p f)  (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (- (len e) (len f)) (len (proots (plift p f e) e)))))

;; We also need the following:
                
(defthmd degree-irreducible-factor-bound
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (> (degree q) 1) (pdivides q p f))
           (<= (degree q) (- (degree p) (len (proots p f))))))

;; It follows from the last 2 results by induction that

;;    (edegree e f) <= d * (d - 1) * ... * (d - n) = d!/(d - n - 1)!,

;; which is a strong version of the desired result:

(defthmd degree-extension-by-roots-bound-induction
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (edegree e f)
	       (/ (fact (degree p))
	          (fact (- (degree p) (- (len e) (len f)))))))
  :hints (("Goal" :use (degree-extension-by-roots-bound-induction-1 len-proots-extension-by-roots len-extends
                        (:instance fact-quot-rewrite (d (degree p)) (n (- (len e) (len f))))
			(:instance len-proots-bound (f e) (p (plift p f e)))))))

(defthmd degree-extension-by-roots-bound
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (edegree e f)
	       (fact (degree p)))))


;;----------------------------------------------------------------------------------------------------------
;;                                           Splitting Fields
;;----------------------------------------------------------------------------------------------------------

;; An extension e of f is a splitting field of p if e is an extension by roots of p and p splits in e:

(defund splitting-field-p (p e f)
  (and (extension-by-roots-p p e f)
       (splits (plift p f e) e)))

;; Every polynomial has a splitting field, as constructed by the function splitting-field, defined below.
;; The admissibility of this function depends on the lemma len-proots-increases, which guarantees that the 
;; declared measure decreases on the recursive call:

(defthmd splitting-field-measure-decreases
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1) (not (splits p f)))
           (let* ((q (nonlinear-irred-factor p f))
	          (e (cons q f)))
	     (< (nfix (- (degree (plift p f e)) (len (proots (plift p f e) e))))
	        (nfix (- (degree p) (len (proots p f))))))))

(defun splitting-field (p f)
  (declare (xargs :measure (nfix (- (degree p) (len (proots p f))))
                  :hints (("Goal" :use (splitting-field-measure-decreases)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
      (if (splits p f)
          f
	(let* ((q (nonlinear-irred-factor p f))
	       (e (cons q f)))
	  (splitting-field (plift p f e) e)))
    ()))

(defthmd extensionp-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (extensionp (splitting-field p f) f)))

(defthmd splits-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (let ((e (splitting-field p f)))
             (splits (plift p f e) e))))

(defthmd extension-by-roots-transitive
  (implies (and (extensionp d f) (extension-by-roots-p p d f)
                (extensionp e d) (extension-by-roots-p (plift p f d) e d))
	   (extension-by-roots-p p e f)))

(defthmd extension-by-roots-p-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (extension-by-roots-p p (splitting-field p f) f)))

(defthmd splitting-field-p-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (splitting-field-p p (splitting-field p f) f)))

;;---------------------------

;; Let e be a splitting field of a polynomial p over f.  Let a and a' be elements of e with the same
;; minimal polynomial m over f.  We shall show that there exists an automorphism of e over f that maps a to a'.

;; We may assume (degree m) > 1.  Let s = (m . f) be the simple extension of f generated by m.  Let
;; k = (splitting-field (plift p f s) s) and let phi = (embedding-of-extension-by-roots e k f).  We have
;; shown that phi is an embedding of e in k over f.

;; Note that (list a) is an embeddingp of s in e over f:

(defthmd embeddingp-list-a
  (implies (and (extensionp e f) (not (equal e f)) (feltp a e) (not (fliftedp a f e)))
	   (embeddingp (list a) (cons (min-poly a e f) f) e f)))

;; This may be extended an embedding psi = (psi a k e f) of k in e over f:

(defun psi (a k e f)
  (if (equal k (cons (min-poly a e f) f))
      (list a)
    (and (consp k)
         (cons (car (proots (pembed (car k) (psi a (cdr k) e f) e f) e))
	       (psi a (cdr k) e f)))))

;; The proof of the following is essentially the same as that of embeddingp-embedding-of-extension-by-roots:

(defthmd embeddingp-psi
  (let ((s (cons (min-poly a e f) f)))
    (implies (and (extensionp e f) (not (equal e f)) (polyp p f)
                  (monicp p f) (>= (degree p) 1) (splitting-field-p p e f)
		  (feltp a e) (not (fliftedp a f e))
		  (extension-by-roots-p (plift p f s) k s))
	     (embeddingp (psi a k e f) k e f))))

;; Thus, (edegree e f) = (edegree k f) and psi is an isomorphism.

;; Let b = (flift (primitive s) s k).  By embed-flift-gen and embed-primitive,

;;   (embed b psi e f) = (embed (flift (primitive s) s k) psi e f)
;;                     = (embed (primitive s) (restrict-embedding psi k s) e f)
;;		       = (embed (primitive s) (list a) e f)
;;		       = a

;; Similarly, psi' = (psi a' k e f) is an embedding of k in e over f and (embed b psi' e f) = a'.
;; Composing psi' with the inverse of psi, we have the desired automorphism of e:

(defund roots-auto (a a1 p e f)
  (let* ((m (min-poly a e f))
         (s (cons m f))
	 (k (splitting-field (plift p f s) s)))         
    (comp-embedding (psi a1 k e f) (inv-embedding (psi a k e f) k e f) e e f)))

(defthmd roots-auto-lemma
  (implies (and (extensionp e f) (not (equal e f)) (polyp p f)
                (monicp p f) (>= (degree p) 1) (splitting-field-p p e f)
                (feltp a e) (feltp a1 e) (not (fliftedp a f e))
		(equal (min-poly a e f) (min-poly a1 e f)))
	   (and (autop (roots-auto a a1 p e f) e f)
	        (equal (embed a (roots-auto a a1 p e f) e f)
		       a1))))


;;----------------------------------------------------------------------------------------------------------
;;                                             Galois Extensions
;;----------------------------------------------------------------------------------------------------------

;; e is a galois extension of f if e is a splitting field of a separable polynomial over f:

(defun-sk galoisp (e f)
  (exists (p)
    (and (polyp p f)
         (monicp p f)
	 (>= (degree p) 1)
         (separablep p f)
	 (splitting-field-p p e f))))

;; In the trivial case, f itself is a splitting field of the separable polynomial (root-poly (fone f) f):

(defthmd galoisp-trivial
  (implies (fieldp f)
           (galoisp f f)))

;; The automorphism group of a galois extension is called the galois group:

(defund galois (e f) (autos e f))

;; By len-embeddings-separablep, the order of the galois group is the degree of the extension:

(defthmd order-galois-group
  (implies (and (extensionp e f) (galoisp e f))
           (equal (order (galois e f))
	          (edegree e f))))

;;---------------------------

;; We shall prove the following critical property of galois extensions: If e is galois over f and a is
;; an element of e that is fixed by every element of (galois e f), then (degree (min-poly a e f)) = 1,
;; i.e., a is lifted from f. 

;; Let e be a splitting field of a separable polynomial p over f.  Let a be an element of e such that
;; (fixedp a (galois e f) e f).  Let m = (min-poly a e f) and suppose that (degree m) > 1.
;; Let s, k, b, phi, and psi be defined as in the preceding section.  Thus, phi is an embedding of e in k
;; over f, psi is an embedding of k in e over f, b is an element of k, and (embed b psi e f) = a.

;; Since a is fixed by (comp-embedding psi phi e e f),

;;   a = (embed a (comp-embedding psi phi e e f) e f) = (embed (embed a phi k f) psi e f).

;; Since psi is injective, it follows that (embed a phi k f) = b.  Let inv = (inv-embedding phi e k f).  
;; Then (embed b inv e f) = a.

;; Since (edegree e f) = (edegree k f) > (edegree k s), (order (galois e f)) > (order (galois k s)).
;; However, we shall construct an injection of (galois e f) into (galois k s), a contradiction.

;; First we define a map from (galois e f) into (galois k f).

;; Given x in (galois e f), let y = (galois-map x a e f p) be the image of x under the galois group
;; isomorphism induced by phi:

;;    y = (galois-map x a e f p)
;;      = (auto-map-image x phi e k f)
;;      = (comp-embedding phi (comp-embedding x inv k e f) k k f).

(defun s% (a e f) (cons (min-poly a e f) f))

(defun k% (a e f p) (splitting-field (plift p f (s% a e f)) (s% a e f)))

(defun phi% (a e f p) (embedding-of-extension-by-roots e (k% a e f p) f))

(defun inv% (a e f p) (inv-embedding (phi% a e f p) e (k% a e f p) f))

(defund galois-map (x a e f p)
  (let* ((k (k% a e f p))
	 (phi (phi% a e f p))
	 (inv (inv% a e f p)))
    (comp-embedding phi (comp-embedding x inv k e f) k k f)))

;; Then y is in (galois k f) and

;;    (embed b y k f) = (embed (embed (embed b inv e f) x k f) phi k f)
;;                    = (embed (embed a x k f) phi k f)
;;                    = (embed a phi k f)
;;                    = b.

;; Let n = (len k) - (len s) and y' = (nthcdr n y) = (restrict-embedding y k s).  By 
;; embeddingp-restrict-embedding, y' is an embedding of s in k over f.  Thus,
;; y' = (list (car y'), where

;;    (car y') = (embed (primitive s) y' k f)             [embed-primitive]
;;             = (embed (flift (primitive s) s k) y k f)  [embed-flift-gen]
;;             = (embed b y k f)
;;             = b

;; and hence y' = (list b) = (list (flift (primitive s) s k)) = (trivial-embedding s k f).

;; Let y" = (galois-inj x a e f) = (firstn n y):

(defund galois-inj (x a e f p)
  (firstn (- (len (k% a e f p)) (len (s% a e f)))
          (galois-map x a e f p)))

;; By firstn-auto, y" is in (galois k s) and for all c in k, (embed c y" k s) = (embed c y k f).
;; To see that galois-inj is an injection, let x1 and x2 be in (galois e f), let

;;    y1 = (galois-map x1 a e f p)
;;    y2 = (galois-map x2 a e f p)
;;    y1" = (galois-inj x1 a e f p)
;;    y2" = (galois-inj x2 a e f p)

;; and suppose y1" = y2".  Then for all c in k,

;;    (embed c y1 k f) = (embed c y1" k s) = (embed c y2" k s) = (embed c y2 k f).

;; By embed-cex-lemma, y1 = y2, and it follows from the properties of comp-embedding (comp-embedding-assoc,
;; comp-inv-embedding, and comp-id-embedding) that x1 = x2.

(defthm galois-inj-injective
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x1 (galois e f))
		(in x2 (galois e f))
		(equal (galois-inj x1 a e f p)
		       (galois-inj x2 a e f p)))
 	   (equal x1 x2))
  :rule-classes ())

;; As argued above, it follows that a is lifted from f:

(defthmd galois-no-fixed-elt
  (implies (and (extensionp e f) (galoisp e f)
                (feltp a e) (fixedp a (galois e f) e f))
	   (fliftedp a f e)))

;;-------------------------

;; Let e be an extension of f.  We shall say that the extension is normal if the minimal polynomial of every 
;; element of e splits in e:

(defun-sk normal-extension-p (e f)
  (forall (x)
    (implies (feltp x e)
             (splits (plift (min-poly x e f) f e) e))))

;; The extension is separable if the minimal polynomial of every element of e is separable:

(defun-sk separable-extension-p (e f)
  (forall (x)
    (implies (feltp x e)
             (separablep (min-poly x e f) f))))
	     
;; We shall prove that an extension is galois iff it is normal and separable.

;; First suppose e is a galois extension of f.
;; Let z be an element of e with p = (min-poly z e f), p' = (plift p f e), d = (proots p' e), and
;; g = (galois e f).  It is easily verified that if x is an element of g and s is a member of d, then
;; (embed s x e e) is also a member of d.  In fact, embed may be viewed as a group action of g on d:

(defaction perm-proots
  ;; parameters:
  (e f z)
  ;; acting group:
  (galois e f)
  ;; parameter conditions:
  (and (extensionp e f) (galoisp e f) (feltp z e))
  ;; domain:
  (proots (plift (min-poly z e f) f e) e)
  ;; action of group element x on domain element s:
  (embed s x e f))

;; Let a denote this action, i.e., a = (perm-proots e f z).  For x in g and s in d,
;; (act x s a g) = (embed s x e f).

;; Let (orbit z a g) = (z1 z2 .. zk).

(defthmd sublistp-orbit-perm-roots
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (let ((l (orbit z (perm-proots e f z) (galois e f))))
	     (and (dlistp l)
	          (sublistp l (proots (plift (min-poly z e f) f e) e))
		  (member z l)))))

(defthmd feltsp-orbit-perm-proots
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (feltsp (orbit z (perm-proots e f z) (galois e f)) e)))

;; We shall compute the polynomial product (root-poly z1 e) * ... * (root-poly zk e).

(defun root-poly-list (l e)
  (if (consp l)
      (cons (root-poly (car l) e)
            (root-poly-list (cdr l) e))
    ()))

(defund root-orbit-poly-list (z e f)
  (root-poly-list (orbit z (perm-proots e f z) (galois e f)) e))

(defund root-orbit-poly (z e f)
  (pmul-list (root-orbit-poly-list z e f) e))

;; Let l = (orbit z a g), r = (root-poly-list l e) = (root-orbit-poly-list z e f), and 
;; q = (pmul-list r e) = (root-orbit-poly z e f).

(defthmd monic-irreducible-listp-root-poly-list
  (implies (and (fieldp e) (feltsp l e))
           (monicp-irreduciblep-listp (root-poly-list l e) e)))

(defthm polyp-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (and (polyp (root-orbit-poly z e f) e)
	        (monicp (root-orbit-poly z e f) e))))

;; If (feltsp m e), then by induction, (pmul-list (root-poly-list m e) e) has no monic irreducible factor 
;; of degree > 1.  It follows that q splits in e:

(defthmd splits-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (splits (root-orbit-poly z e f) e)))

;; If (feltsp m e) and (dlistp m), then by separablep-pmul and induction, (pmul-list (root-poly-list m e) e) 
;; is separable.  In particular, q is separable:

(defthmd separablep-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (separablep (root-orbit-poly z e f) e)))

;; Since z is in l, (root-poly z e) is in r, which implies (root-poly z e) divides q and z is a root of q:

(defthmd member-z-root-orbit-poly-list
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (member (root-poly z e) (root-orbit-poly-list z e f))))

(defthmd pdivides-root-poly-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (pdivides (root-poly z e) (root-orbit-poly z e f) e)))

(defthmd prootp-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (prootp z (root-orbit-poly z e f) e)))

;; Let x be an element of (galois e f).  We shall show that (pembed q x e f) = q.  Let r' be the result of 
;; applying x to each member of r.  Let p be a member of r'.  Then p = (list (fone e) (cadr p)), where (cadr p) 
;; is the image under x of some member of l, which implies (cadr p) is a member of l, amd therefore p is a 
;; member of r.  Thus, r' is a sublist of r:  

(defthmd member-root-poly-list
  (implies (and (fieldp e) (feltsp l e))
           (iff (member x (root-poly-list l e))
                (and (equal x (root-poly (fneg (cadr x) e) e))
		     (feltp (cadr x) e)
		     (member (fneg (cadr x) e) l)))))

(defun pembed-list (l x e f)
  (if (consp l)
      (cons (pembed (car l) x e f)
            (pembed-list (cdr l) x e f))
    ()))

(defthmd member-pembed-root-poly-list
  (implies (and (extensionp e f) (feltsp l e) (in x (galois e f)))
           (iff (member p (pembed-list (root-poly-list l e) x e f))
	        (and (feltp (cadr p) e)
		     (equal p (root-poly (fneg (cadr p) e) e))		     
		     (member (embed (fneg (cadr p) e) (inv-auto x e f) e f) l)))))

(defthmd sublistp-pembed-root-poly-list
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (in x (galois e f)))
           (sublistp (pembed-list (root-orbit-poly-list z e f) x e f)
	             (root-orbit-poly-list z e f))))

;; r and r' are dlists of the same length, and therefore r' is a permutation of r:

(defthmd dlistp-root-poly-list
  (implies (and (fieldp e) (feltsp l e) (dlistp l))
           (dlistp (root-poly-list l e))))

(defthmd dlistp-pembed-root-poly-list
  (implies (and (extensionp e f) (feltsp l e) (dlistp l) (in x (galois e f)))
           (dlistp (pembed-list (root-poly-list l e) x e f))))

(defthm len-pembed-list
  (equal (len (pembed-list l phi k f))
         (len l)))

(defthmd permp-pembed-root-poly-list
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (in x (galois e f)))
           (permp (pembed-list (root-orbit-poly-list z e f) x e f)
	          (root-orbit-poly-list z e f))))

;; It follows that (pmul-list r' e) = q:

(defthmd monicp-irreduciblep-listp-perm
  (implies (and (dlistp m) (monicp-irreduciblep-listp l f) (permp m l))
           (monicp-irreduciblep-listp m f)))

(defthmd pmul-list-perm
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (permutationp m l))
           (equal (pmul-list m f)
	          (pmul-list l f))))

;; It follows from pembed-pmul that (pmul-list r' e) = (pembed (pmul-list r e) x e f) = (pembed q e f):

(defthmd pmul-list-pembed-list
  (implies (and (extensionp e f) (monicp-irreduciblep-listp r e) (in x (galois e f)))
           (equal (pembed (pmul-list r e) x e f)
	          (pmul-list (pembed-list r x e f) e))))

;; Combining pmul-list-pembed-list with pmul-list-perm and permp-pembed-root-poly-list, we have
;; (pembed q x e f) = q:

(defthmd pembed-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (in x (galois e f)))
           (equal (pembed (root-orbit-poly z e f) x e f)
	          (root-orbit-poly z e f))))

;; As a consequence of pembed-root-orbit-poly, we shall show that q is lifted from f.  It will suffice
;; to show that q satisfies the following:

(defun pfixedp (p e f)
  (if (consp p)
      (and (fixedp (car p) (galois e f) e f)
           (pfixedp (cdr p) e f))
    t))

;; The desired result will then follow from galois-no-fixed-elt:

(defthmd pfixedp-pliftedp
  (implies (and (extensionp e f) (galoisp e f)
                (feltsp p e) (pfixedp p e f))
	   (pliftedp p f e)))

;; The proof requires 2 additional definitions.  First we define

(defun fixedp-aux-list (p l e f)
  (if (consp p)
      (and (fixedp-aux (car p) l e f)
           (fixedp-aux-list (cdr p) l e f))
    t))

;; and note the following trivial relation:

(defthmd fixedp-aux-list-pfixedp
  (implies (and (extensionp e f)
                (feltsp p e)
                (fixedp-aux-list p (auto-list e f) e f))
           (pfixedp p e f)))

;; Next, we define

(defun pfixedp-list (p l e f)
  (if (consp l)
      (and (equal (pembed p (car l) e f) p)
           (pfixedp-list p (cdr l) e f))
    t))

;; and note the following consequence of pembed-root-orbit-poly:

(defthmd pfixedp-list-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e)
                (sublistp l (auto-list e f)))
           (pfixedp-list (root-orbit-poly z e f) l e f)))

;; The following is proved by double induction on the lengths of p and l:

(defthmd pfixedp-fixed-fixedp-aux-list
  (implies (and (extensionp e f)
                (feltsp p e)
                (sublistp l (auto-list e f))
		(pfixedp-list p l e f))
 	   (fixedp-aux-list p l e f)))

;; Combining the above lemmas, we have the desired result:

(defthmd pliftedp-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (pliftedp (root-orbit-poly z e f) f e)))

;; Let p = (min-poly z e f).  Since z is a root of q = (plift (pdrop q e f) f e), p divides (pdrop q e f) by
;; min-poly-divides:

(defthmd pdivides-min-poly-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (pdivides (min-poly z e f) (pdrop (root-orbit-poly z e f) e f) f)))

;; Since p divides (pdrop q e f), (plift p f e) divides q by pdivides-plift.  Since q splits in e, it follows 
;; from pdivides-splits (plift p f e) splits in e:

(defthmd splits-min-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (splits (plift (min-poly z e f) f e) e)))

;; Since q is separable in e, (pdrop q e f) is separable in f by separablep-extension.  Since p divides 
;; (pdrop q e f), p splits in f by pdivides-separablep:

(defthmd separablep-min-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (separablep (min-poly z e f) f)))

;; Since z is an arbitrary element of e, e is a normal and separable extension of f:

(defthmd galois-normal-separable
  (implies (and (extensionp e f) (galoisp e f))
           (and (normal-extension-p e f)
	        (separable-extension-p e f))))

;;-----------------------

;; Conversely, let e be a normal and separable extension of f.  The following function computes the lcm of
;; the minimal polynomials over f of the primitive elements of e:

(defun generating-poly (e f)
  (if (and (extensionp e f) (not (equal e f)))
      (let ((p (generating-poly (cdr e) f))
            (q (min-poly (primitive e) e f)))
	(if (pdivides q p f)
	    p
	  (pmul q p f)))
    (pone f)))

;; Let p = (generating-poly e f).  We shall prove that p is separable and e is a splitting field of p.
;; It is easily proved by induction on e that p is a monic polynomial over f:

(defthm polyp-generating-poly
  (implies (extensionp e f)
           (let ((p (generating-poly e f)))
             (and (polyp p f)
	          (monicp p f)
	          (not (equal p (pzero f)))))))

;; If e != f, then p is not a constant:

(defthm generating-poly-not-constant
  (implies (and (extensionp e f) (not (equal e f)))
           (>= (degree (generating-poly e f))
	       1)))

;; Note that as a consequence of min-poly-flift-min-poly, if k is an intermediate field between e and f, then 
;; k is a separable extension of f:

(defthmd separable-extension-p-intermediate
  (implies (and (extensionp e k) (extensionp k f) (separable-extension-p e f))
           (separable-extension-p k f)))

;; We shall use this result to prove by induction on e that p is separable over f.  Assume that e != f.  Then 
;; by (cdr e) is a separable extension of f.  Let m = (min-poly (primitive e) e f) and p' = (generating-poly 
;; (cdr e) f) f).  By induction, p' is separable, and by hypothesis, so is m.  If m divides p', then p = p'.  
;; Otherwise, by pgcd-irreduciblep, (pgcd m p') = 1 and by separablep-pmul, p is separable:

(defthm separablep-generating-poly
  (implies (and (extensionp e f) (separable-extension-p e f))
           (separablep (generating-poly e f) f)))

;; Let k be an intermediate field between e and f.  It is easily proved by induction on e that 
;; (generating-poly k f) divides p:

(defthmd pdivides-generating-poly
  (implies (and (extensionp e k) (extensionp k f))
           (pdivides (generating-poly k f)
	             (generating-poly e f)
		     f)))

;; We shall also prove, by induction on k, that (generating-poly k f) splits in e.
;; Assume that k != f and (generating-poly (cdr k) f) splits in e.  We need only show that 
;; (min-poly (primitive k) k f) splits in e.  But by min-poly-flift-min-poly, (min-poly (primitive k) k f)
;; = (min-poly (flift (primitive k) k e) e f), which splits in e since e is a normal extension of f:

(defthm splits-generating-poly
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)) (normal-extension-p e f))
           (splits (plift (generating-poly k f) f e) e)))

;; To complete the proof that e is a splitting field of p, we shall prove by induction on k that k is an 
;; extension of f by roots of p.  Suppose k != f and that (cdr k) is an extension of f by roots of p.  We must 
;; show that (car k) divides (plift p f (cdr k)).  By pdivides-generating-poly,

;;   (generating-poly e k) divides (generating-poly e f) = p

;; and by definition, 

;;   (min-poly (primitive k) k f) divides (generating-poly e k).

;;   It follows that (min-poly (primitive k) k f) divides p, which implies

;;   (plift (min-poly (primitive k) k f) f (cdr k)) divides (plift p f (cdr k)).

;; Therefore, it suffices to show that

;;   (car k) divides (plift (min-poly (primitive k) k f) f (cdr k)).

;; By min-poly-primitive,

;;    (car k) = (min-poly (primitive k) k (cdr k)).

;; By prootp-min-poly, (primitive k) is a root of

;;    (plift (min-poly (primitive k) k f) f k)
;;      = (plift (plift (min-poly (primitive k) k f) f (cdr k)) (cdr k) k).

;; Thus, by min-poly-pdivides,

;;    (car k) divides (plift (min-poly (primitive k) k f) f (cdr k))

;; as required.

(defthmd extension-by-roots-p-generating-poly
  (implies (and (extensionp e k) (extensionp k f))
           (extension-by-roots-p (generating-poly e f) k f)))

;; Thus, e is a galois extension of f and we have the following equivalence:

(defthmd galois-equivalence
  (implies (extensionp e f)
           (iff (galoisp e f)
	        (and (normal-extension-p e f)
		     (separable-extension-p e f)))))

;;-----------------------

;; Let e and k be isomorphic extensions of f.  We shall prove the unsurprising result that if e galois over 
;; f, then so is k.  Let phi be an embedding of e in k over f.  Let x be an element of k and

;;     y = (embed x (inv-embedding phi e k f) e f).

;; Then x = (embed y phi k f).  Since e is a separable and normal extension of f, (min-poly x e k) is
;; separable and (plift (min-poly x e k) f e) splits in e.  By pembed-min-poly, (min-poly x e k) =
;; (min-poly y e f), and we need only show that (plift (min-poly x k f) f k) splits in k.  But by pembed-fixes,

;;    (plift (min-poly x k f) f k) = (plift (min-poly y e f) f k)
;;                                 = (pembed (plift (min-poly y e f) f e) phi k f),

;; which splits in k by splits-pembed.

(defthmd galoisp-isomorphic
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
		(galoisp e f))
	   (galoisp k f)))
	   

;;----------------------------------------------------------------------------------------------------------
;;                                   Fundamental Theorem of Galois Theory
;;----------------------------------------------------------------------------------------------------------

;; Suppose k is an extension of f, e is an extension of k, and e is galois over f.  Let x be an element of e
;; with m = (min-poly x e f) and m' = (min-poly x e k).  Then m is separable and splits in e, and m' divides
;; m by min-poly-divides-min-poly-plift.  By pdivides-splits, m' splits in e, and by separablep-extension and
;; pdivides-separablep, m' is separable over k.  Thus, e is galois over k:

(defthmd galoisp-subfield
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (galoisp e k)))

;; On the other hand, let x be an element of k.  By min-poly-flift-min-poly, (min-poly x k f) =
;; (min-poly (flift x k e) e f), which is separable since e is a separable extension of f.
;; Thus, k is a separable extension of f:

(defthmd separable-extension-p-subfield
  (implies (and (extensionp e k) (extensionp k f) (separable-extension-p e f))
           (separable-extension-p k f)))

;; Thus, if k is a normal extension of f, then k is galois over f:

(defthmd normal-extension-p-subfield
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (galoisp k f)))

;; The usual formulation of the fundamental theorem establishes to a 1-1 correspondence between the subgroups 
;; of g and the intermediate fields between e and f, with an intermediate field k corresponding to the galois
;; group of e over k, which consists of those automorphisms of e that fix the elements of k.

;; The first problem that we face is that in our formalization, an automorphism of e over k is strictly not
;; an automorphism of e over f.  However, we shall define (galois-subgroup k e f) to be the subgroup of g
;; consisting of the automorphisms of g that fix k and show that there is a natural isomorphism between this
;; group and (galois e k).

;; The second problem that we face is that in our formalization of finite group theory, the elements of a group
;; form an ordered list rather that a set, and therefore distinct groups may have the same elements.  Thus, if
;; k is the fixed field of a subgroup of g, then we cannot conclude that h = (galois-subgroup k e f), but only
;; that these groups have the same elements, i.e., that each is a subgroup of the other.

;; Thus, we shall establish the following properties of the correspondence:

;;    (1) k is the fixed field of (galois-subgroup k e f);
;;    (2) If h is a subgroup of g and k is the fixed field of h, then h and (galois-subgroup k e f) have the
;;        same elements;
;;    (3) k is a normal extension of f iff (galois-subgroup k e f) is a normal subgroup of g;
;;    (4) If k is a normal extension of f, then (galois k f) is isomorphic to the quotient group of h in g.

;; Yet another problem that we face is that in our formalization, there is no guarantee that a given subgroup h 
;; of g is the galois subgroup corresponding to any of the fields that occur in the construction of e as an 
;; extension of f.  However, we shall construct an extension k of f, an extension d of k, and an isomorphism phi 
;; from d to e over f such that h is the image of the galois subgroup of k under the galois group isomorphism 
;; induced by phi, i.e.,

;;     (image (auto-map phi d e f) (galois-subgroup k d f) (galois e f)) = h.

;;-----------------------------------------------

;; Let g = (galois e f).  We shall define a subgroup of g, (galois-subgroup k e f), consisting of those
;; automorphisms of e over f that fix k, or more precisely, that lift each element of k to e.  We shall
;; show that this subgroup is isomorphic to (galois e k).

;; The element list of (galois-subgroup k e f) is defined as follows:

(defun fixing-autos-aux (l k e f)
  (if (consp l)
      (if (equal (restrict-embedding (car l) e k)
                 (trivial-embedding k e f))
          (cons (car l) (fixing-autos-aux (cdr l) k e f))
	(fixing-autos-aux (cdr l) k e f))
    ()))

(defund fixing-autos (k e f)
  (fixing-autos-aux (auto-list e f) k e f))

;; Thus, an automorphism of e over f is in (galois-subgroup k e f) iff its restriction to k is the trivial
;; embedding of k in e over f:

(defthmd member-fixing-autos
  (iff (member x (fixing-autos k e f))
       (and (member x (auto-list e f))
            (equal (restrict-embedding x e k)
                   (trivial-embedding k e f)))))

;; Clearly, the identity automorphism is a member of (fixing-autos k e f):

(defthm member-id-auto-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (member (id-auto e f) (fixing-autos k e f))))

;; If phi is a member of (fixing-autos k e f) and x is an element of e lifted from k, then

;;    (embed x phi e f) = x.

;; We derive this result as a corollary of the following generalization, which may be proved by induction:

;; Let d be an intermediate field between e and k and let phi be an embedding of d in e over 
;; f such that (restrict-embedding phi d k) = (trivial-embedding k e f).  Let x be an element 
;; of k.  Then (embed (flift x k d) phi e f) = (flift x k e).

;; Proof: If d = k, then phi = (trivial-embedding k e f) and the claim follows from
;; trivial-embedding-flift.  If d != k, then by induction and embed-flift,

;;    (embed (flift x k d) phi e f) = (embed (flift (flift x k (cdr d)) (cdr d) d) phi e f)
;;                                  = (embed (flift x k (cdr d)) (cdr phi) e f)
;;				    = (flift x k e).

;; Substituting e for d yields the following:

(defthmd fixing-auto-fixes
  (implies (and (extensionp e k) (extensionp k f)
		(member phi (fixing-autos k e f))
		(feltp x k))
	   (equal (embed (flift x k e) phi e f)
	          (flift x k e))))

;; To prove that (fixing-autos k e f) forms a subgroup of g, we must prove the appropriate instances of the 6 
;; lemmas listed in the comment preceding the definition of defsubgroup ("../groups/groups.lisp").  The first
;; 4 are trivial:

(defthm dlistp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (dlistp (fixing-autos k e f))))

(defthm sublistp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (sublistp (fixing-autos k e f) (auto-list e f))))

(defthm consp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (consp (fixing-autos k e f))))

(defthm car-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (equal (car (fixing-autos k e f))
	          (id-auto e f))))

;; The proof of closure of the group operation requires 2 inductions.  Let x be a member of (fixing-autos k e f).
;; First we show, using fixing-auto-fixes, that if d is an intermediate field between k and f, then

;;    (comp-embedding x (trivial-embedding d e f) d e f) = (trivial-embedding d e f).

;; Using this result for the case d = k, we then show that if d is an intermediate field between e and k and y 
;; is an embedding of d in e over f such that (restrict-embedding y d k) = (trivial-embedding k e f), then the 
;; same is true of (comp-embedding x y d e f).  The desired result is the case d = e:

(defthm comp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
                (member y (fixing-autos k e f)))
           (member (comp-auto x y e f) (fixing-autos k e f))))

;; The proof of closure under the inverse operator similary requires 2 inductions.  Let x be a member of 
;; (fixing-autos k e f).  First we show, using fixing-auto-fixes, that if d is an intermediate field between
;; k and f, then

;;     (inv-embedding-aux x e e d f) = (trivial-embedding d e f).

;; Using this result for the case d = k, we then show that if d is an intermediate field between e and k, then

;;    (restrict-embedding (inv-embedding-aux x e e d f) d k) = (trivial-embedding k e f).

;; The desired result is the case d = e:

(defthm inv-fixing-autos
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
	   (member (inv-auto x e f) (fixing-autos k e f))))
	   
;; The following now succeeds automatically:

(defsubgroup galois-subgroup (k e f) (galois e f)
  (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f))
  (fixing-autos k e f))

;;-----------------------------------------------

;; Let h = (galois-subgroup k e f).  We shall define an isomorphism from h to (galois e k).  According
;; to the lemma autop-trunc-embedding, we have a map from h to (galois e k):

(defmap galois-subgroup-map (k e f)
  (fixing-autos k e f)
  (trunc-embedding x e k))

(defthm autop-trunc-embedding-rewrite
  (implies (and (member x (fixing-autos k e f))
                (extensionp e k) (extensionp k f))                
	   (autop (trunc-embedding x e k) e k)))

;; To prove that this is a homomorphism, we first observe that (id-auto e f) is mapped to (id-auto e k):

(defthm trunc-embedding-id-auto
  (implies (and (extensionp e k) (extensionp k f))
           (equal (trunc-embedding (id-auto e f) e k)
	          (id-auto e k))))

;; To prove that the group operation is preserved, we note first that if x and y are in h and a is an
;; element of e, then by autop-trunc-embedding and embeddingp-comp-embedding,

;;    (embed a (comp-embedding (trunc-embedding x e k) (trunc-embedding y e k) e e k) e k)
;;      = (embed (embed a (trunc-embedding y e k) e k) (trunc-embedding x e k) e k)
;;      = (embed (embed a y e f) (trunc-embedding x e k) e k)
;;      = (embed (embed a y e f) x e f)
;;      = (embed a (comp-embedding x y e e f) e f)
;;      = (embed a (trunc-embedding (comp-embedding x y e e f) e k) e k)

;; and we appeal to embed-cex-lemma:

(defthm trunc-embedding-comp-auto
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
                (member y (fixing-autos k e f)))
	   (equal (trunc-embedding (comp-auto x y e f) e k)
	          (comp-auto (trunc-embedding x e k) (trunc-embedding y e k) e k))))

;; Similarly,

;;    (embed a (comp-auto (trunc-embedding (inv-auto x e f) e k) (trunc-embedding x e k) e k) e k)
;;      = (embed (embed a (trunc-embedding x e k) e k) (trunc-embedding (inv-auto x e f) e k) e k)
;;      = (embed (embed a x e f) (trunc-embedding (inv-auto x e f) e k) e k)
;;      = (embed (embed a x e f) (inv-auto x e f) e f)
;;      = (embed a (comp-auto x (inv-auto x e f) e f) e f)
;;      = (embed a (id-auto e f) e f)
;;      = a

;; which implies

;;    (comp-auto (trunc-embedding (inv-auto x e f) e k) (trunc-embedding x e k) e k) = (id-auto e k),

;; and therefore (trunc-embedding (inv-auto x e f) e k) = (inv-auto (trunc-embedding x e k) e k):

(defthm trunc-embedding-inv-auto
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
           (equal (trunc-embedding (inv-auto x e f) e k)
	          (inv-auto (trunc-embedding x e k) e k))))

;; The following is now proved automatically:

(prove-homomorphismp galois-subgroup-map
  (galois-subgroup-map k e f)
  (galois-subgroup k e f)
  (galois e k)
  (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f)))

(DEFTHM HOMOMORPHISMP-GALOIS-SUBGROUP-MAP
  (IMPLIES (AND (EXTENSIONP E K)
                (EXTENSIONP K F)
                (EXTENSIONP E F)
                (GALOISP E F))
           (HOMOMORPHISMP (GALOIS-SUBGROUP-MAP K E F)
                          (GALOIS-SUBGROUP K E F)
                          (GALOIS E K))))

;; If x is in (fixing-autos k e f) and (trunc-embedding x d k) = (trivial-embedding d e k), then
;; x = (trivial-embedding d e f).  Thus, galois-subgroup-map is an endomorphism:

(defthmd endomorphismp-galois-subgroup-map
  (implies (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f))
           (endomorphismp (galois-subgroup-map k e f)
                          (galois-subgroup k e f)
                          (galois e k))))

;; To prove that galois-subgroup-map is an epimorphism, we define its inverse:

(defund extend-embedding (x k e f)
  (append x (trivial-embedding k e f)))

;; The following is a consequence of pembed-trunc-embedding:

(defthmd embeddingp-extend-embedding
  (implies (and (extensionp e k) (extensionp k f)
                (extensionp e d) (extensionp d k)
		(embeddingp x d e k))
           (and (embeddingp (extend-embedding x k e f) d e f)
	        (equal (restrict-embedding (extend-embedding x k e f) d k)
		       (trivial-embedding k e f))
		(equal (trunc-embedding (extend-embedding x k e f) d k)
		       x))))

;; It follows from the case d = e that galois-subgroup-map is an epimorphism, and therefore an isomorphism:

(defthmd trunc-extend-embedding
  (implies (and (extensionp e k) (extensionp k f)
		(autop x e k))
           (and (member (extend-embedding x k e f) (fixing-autos k e f))
	        (equal (trunc-embedding (extend-embedding x k e f) e k)
	               x))))

(defthmd epimorphismp-galois-subgroup-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (epimorphismp (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k))))

(defthmd isomorphismp-galois-subgroup-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (isomorphismp (galois-subgroup-map k e f)
			 (galois-subgroup k e f)
	                 (galois e k))))

;;----------------------------------------------------

;; Let x be an element of e.  Suppose x is lifted from k, i.e, x = (flift z k e), where z is in k.  If phi 
;; is in (galois-subgroup k e f), then by fixing-auto-fixes, (embed x phi e f) = x.  Thus,
;; (fixedp x (galois-subgroup k e f) e f).  Now suppose (fixedp x (galois-subgroup k e f) e f).
;; Given psi in (galois e k), phi = (extend-embedding psi k e f).  By trunc-extend-embedding, 
;; autop-trunc-embedding, and fixedp-embed,

;;   (embed x psi e k) = (embed x (trunc-embedding phi e k) e f) = x.

;; Therefore, (fixedp x (galois e k) e k) and by galois-no-fixed-elt, x is lifted from k.  Thus, k is the
;; fixed field of h:

(defthmd galois-subgroup-fixed-field-p
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (fixed-field-p k (galois-subgroup k e f) e f)))

;; Conversely, let h be an arbitrary subgroup of g and suppose (fixed-field-p k h e f).  

;; To show that h is a subgroup of (galois-subgroup k e f), suppose v is in h.  Let x be an element of k and
;; let x' = (flift x k e).  Since (fixedp x' h e f), by embed-flift-gen,

;;     (embed x (restrict-embedding v e k) e f) = (embed x' v e f)
;;                                              = x'
;;                                              = (embed x (trivial-embedding k e f) e f).

;; By embed-cex-lemma, (restrict-embedding v e k) = (trivial-embedding k e f), and by member-fixing-autos,
;; v is in (galois-subgroup k e f).  Thus, h is a subgroup of (galois-subgroup k e f).

;; By Artin's Lemma, (edegree d k) <= (order h) and therefore

;;     (edegree d k) <= (order h) <= (order (galois-subgroup k d f)) = (edegree d k),

;; which implies (order h) = (order (galois-subgroup k d f)) and h = (galois-subgroup k d f).

(defthmd fixed-field-p-galois-subgroup
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f))
                (fixed-field-p k h e f))
	   (and (subgroupp h (galois-subgroup k e f))
	        (subgroupp (galois-subgroup k e f) h))))

;;----------------------------------------------------

;; Let h = (galois-subgroup k d f).  We shall show that h is a normal subgroup of g <=> k is a normal
;; extension of f and that in the normal case, (galois k f) is isomorphic to the quotient group of h in g.

;; First we assume that k is not a normal extension and show that h is not a normal subgroup. There exists 
;; an element x of k such that (plift (min-poly x k f) f k) does not split in k.  Let m = (min-poly x k f) 
;; and m' = (plift m f k).  By len-proots-<=-len-factorization and len-factorization-bound, 

;;    (len (proots m' k)) <= (len (factorization m' k)) < (degree m') = (degree m).

;; Let x' = (flift x k e).  By min-poly-flift-min-poly, m = (min-poly x' e f).  Let m" = (plift m' k e) =
;; (plift m f e).  Since e is normal over f, m" splits in e.  By len-proots-max,

;;    (len (proots m" e)) = (degree m) > (len (proots m' k)).

;; It follows that m" has a root that is not flifted from k.  To prove this, let y be a member of (proots m" e)
;; that is not a member of (plift (proots m' k) k e).  If y = (flift z k e), then we have

;;    (prootp (flift z k e) mm e) => (peval m" (flift z k e) e) = 0
;;                                => (flift (peval m' z k) k e) = 0
;;                                => (peval m' z k) = 0
;;                                => (prootp z m' k)
;;                                => z is a member of (proots m' k)
;;                                => (flift z k e) is a member of (plift (proots m' k) k e)

;; a contradiction.

;; By galois-no-fixed-elt, y is not fixed by (galois e k).  It follows from autop-trunc-embedding that there
;; exists an element phi of h such that (embed y phi e f) != y.

;; By roots-auto-lemma, there exists an element psi of g such that (embed y psi e f) = x'.
;; Let rho be the conjugate of phi by psi:

;;    rho = (conj phi psi g) = (comp-auto (comp-auto psi phi e f) (inv-auto psi e f) e f).

;; Let z = (embed y phi e f).  Since z != y, (embed z psi e f) != x' and hence

;;    (embed x' rho e f) = (embed (embed (embed x' (inv-auto psi e f) e f) phi e f) psi e f)
;;                       = (embed (embed y phi e f) psi e f)
;;                       = (embed z psi e f)
;;                      != x'.

;; By fixing-auto-fixes, rho is not in h, and therefore h is not normal in g.

(defthmd normalp-galois-subgroup-normal-extension-p
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (normalp (galois-subgroup k e f) (galois e f)))
	   (normal-extension-p k f)))

;; Now suppose k is a normal extension of f.  We shall construct a group homomorphism from g to (galois k f)
;; with kernel h.

;; Let x be an element of k.  Let x' = (flift x k e), m = (min-poly x k f), m' = (plift m f k), and
;; m" = (plift m f e).  Then m = (min-poly x' e f), m' splits in k, and m" splits in e.  By len-proots-max,

;;    (len (proots m' k)) = (len (proots m" e)) = (degree m).

;; It follows that every root of m" is lifted from k.  To prove this, note that if z is a member of
;; (proots m' k), then

;;    (peval m" (flift z k e) e) = (flift (peval m' z k) k e) = (flift (fzero k) k e) = (fzero e)

;; and hence (flift z k e) is a member of (proots m" e).  Thus, (plift (proots m' k) k e) is a sublist 
;; of (proots m" e).  Since (plift (proots m' k) k e) is a dlist of the same length as (proots m" e),
;; (plift (proots m' k) k e) is a permutation of (proots m" e) and every member of the latter is a
;; member of the former, which is lifted from k.

;; Let phi be an embedding of k in e over f.  By pembed-fixes and peval-pembed,

;;    (peval m" (embed x phi e f) e) = (peval (pembed m' phi e f) (embed x phi e f) e)
;;                                   = (embed (peval m' x k) phi e f)
;;                                   = (embed (fzero k) phi e f)
;;                                   = (fzero e),

(defthmd fliftedp-embed
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k))
	   (fliftedp (embed x phi e f) k e)))

;; Based on this observation, we shall define the automorphism of k induced by phi.
;; First we show that the following function is a meta-automorphism of k over f:

(defund fdrop-embed (x phi e k f)
  (fdrop (embed x phi e f) e k))

(defthm fdrop-embed-image
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k))
	   (feltp (fdrop-embed x phi e k f) k)))

(defthm fdrop-embed-fzero-fone
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f))
	   (and (equal (fdrop-embed (fzero k) phi e k f) (fzero k))
	        (equal (fdrop-embed (fone k) phi e k f) (fone k)))))

(defthm fdrop-embed-fadd
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k) (feltp y k))
	   (equal (fdrop-embed (fadd x y k) phi e k f)
	          (fadd (fdrop-embed x phi e k f) (fdrop-embed y phi e k f) k))))

(defthm fdrop-embed-fmul
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k) (feltp y k))
	   (equal (fdrop-embed (fmul x y k) phi e k f)
	          (fmul (fdrop-embed x phi e k f) (fdrop-embed y phi e k f) k))))

(defthm fdrop-embed-fixes
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x f))
	   (equal (fdrop-embed (flift x f k) phi e k f)
	          (flift x f k))))


;; The corresponding automorphism is defined by emulating the definition of phi1:

(defun fdrop-embedding-aux (phi e d k f)
  (if (and (extensionp e k) (extensionp k d) (extensionp d f) (not (equal d f)))
      (cons (fdrop-embed (flift (primitive d) d k) phi e k f)
            (fdrop-embedding-aux phi e (cdr d) k f))
    ()))

(defund fdrop-embedding (phi e k f)
  (fdrop-embedding-aux phi e k k f))

;; By functional instantiation of phi1-phi0, fdrop-embedding is the reification of fdrop-embed:

(defthmd autop-fdrop-embedding
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f))
	   (let ((phi1 (fdrop-embedding phi e k f)))
	     (and (autop phi1 k f)
	          (implies (feltp x k)
		           (equal (embed x phi1 k f)
			          (fdrop (embed x phi e f) e k)))))))

;; Next we define a homomorphism from (galois e f) to (galois k f):

(defun galois-restriction (phi e k f)
  (fdrop-embedding (restrict-embedding phi e k) e k f))

(defmap galois-restriction-map (e k f)
  (auto-list e f)
  (galois-restriction x e k f))

;; By embeddingp-restrict-embedding, and autop-fdrop-embedding, galois-restriction-map maps
;; (galois e f) to (galois k f):

(defthm autop-galois-restriction
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)))
	   (autop (galois-restriction phi e k f) k f)))

;; If phi is in g and let x be an element of k, then

;;  (embed x (galois-restriction phi e k f) k f)
;;    = (embed x (fdrop-embedding (restrict-embedding phi e k) e k f) k f)  [definition]
;;    = (fdrop (embed x (restrict-embedding phi e k) e f) e k)              [autop-fdrop-embedding]
;;    = (fdrop (embed (flift x k e) phi e f) e k)                           [embed-flift-gen]

(defthmd embed-galois-restriction
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (autop phi e f) (feltp x k))
           (equal (embed x (galois-restriction phi e k f) k f)
	          (fdrop (embed (flift x k e) phi e f) e k))))

;; In particular,

;;  (embed x (galois-restriction (id-auto e f) e k f) k f)
;;    = (fdrop (embed (flift x k e) (id-auto e f) e f) e k)
;;    = (fdrop (flift x k e) e k)
;;    = x

(defthmd embed-galois-restriction-id
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (feltp x k))
           (equal (embed x (galois-restriction (id-auto e f) e k f) k f)
	          x)))

;; Combine this with embed-cex-lemma:

(defthm galois-restriction-id
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (equal (galois-restriction (id-auto e f) e k f)
	          (id-auto k f))))

;; Now let phi and psi be in g.  By embed-comp-auto, autop-comp-auto, and embed-galois-restriction,

;; (embex x (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f) k f)
;;   = (embed (embed x (galois-restriction phi e k f) k f) (galois-restriction psi e k f) k f)
;;   = (embed (fdrop (embed (flift x k e) phi e f) e k) (galois-restriction psi e k f) k f)
;;   = (fdrop (embed (flift (fdrop (embed (flift x k e) phi e f) e k) k e) psi e f) e k)
;;   = (fdrop (embed (embed (flift x k e) phi e f) psi e f) e k)
;;   = (fdrop (embed (flift x k e) (comp-auto psi phi e f) e f) e k)
;;   = (embed x (galois-restriction (comp-auto psi phi e f) e k f) k f)

(defthm embed-galois-restriction-comp
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)) (in psi (autos e f))
		(feltp x k))
	   (equal (embed x (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f) k f)
	          (embed x (galois-restriction (comp-auto psi phi e f) e k f) k f))))

;; Once again we apply embed-cex-lemma:

(defthm galois-restriction-comp
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)) (in psi (autos e f)))
	   (equal (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f)
	          (galois-restriction (comp-auto psi phi e f) e k f))))

;; This is now proved automatically:

(prove-homomorphismp galois-restriction-map
  (galois-restriction-map e k f)
  (galois e f)
  (galois k f)
  (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f) (normal-extension-p k f)))

(DEFTHM HOMOMORPHISMP-GALOIS-RESTRICTION-MAP
  (IMPLIES (AND (EXTENSIONP E K)
                (EXTENSIONP K F)
                (EXTENSIONP E F)
                (GALOISP E F)
                (NORMAL-EXTENSION-P K F))
          (HOMOMORPHISMP (GALOIS-RESTRICTION-MAP E K F)
                         (GALOIS E F)
                         (GALOIS K F))))

;; We have noted that if phi is in g and x is an element of k, then

;;  (embed x (galois-restriction phi e k f) k f)
;;    = (fdrop (embed x (restrict-embedding phi e k) k f) e k)

;; Suppose phi is in h.  Then (restrict-embedding phi e k) = (trivial-embedding k e f) and
;; we have

;;   (embed x (galois-restriction phi e k f) k f) = (fdrop (flift x k e) e k) = x

;; and hence (galois-restriction phi e k f) = (id-auto k f).
;; Conversely, if (galois-restriction phi e k f) = (id-auto k f), then we have

;;   (fdrop (embed x (restrict-embedding phi e k) e f) e k) = x

;; which implies (embed x (restrict-embedding phi e k) k f) = (flift x k e) and hence
;; (restrict-embedding phi e k) = (trivial-embedding k e f), i.e., phi is in h.

(defthmd fixing-autos-kelts
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (galois e f)))
	   (iff (equal (galois-restriction phi e k f) (id-auto k f))
	        (equal (restrict-embedding phi e k)
	               (trivial-embedding k e f)))))

;; It follows that h is the kernel of (galois-restriction-map e k f):

(defthmd kernel-galois-restriction-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
	        (normal-extension-p k f))
           (equal (kernel (galois-restriction-map e k f) 
	                  (galois k f)
                          (galois e f))
	          (galois-subgroup k e f))))

;; Thus, h is normal in g:

(defthmd normalp-normal-extension-p
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (iff (normalp (galois-subgroup k e f) (galois e f))
	        (normal-extension-p k f))))

;; Every homomorphism induces an endomorphism on the quotient of its kernel:

(defthmd endomorphismp-quotient-map-galois-restriction-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
	   (endomorphismp (quotient-map (galois-restriction-map e k f) (galois e f) (galois k f))
	                  (quotient (galois e f) (galois-subgroup k e f))
			  (galois k f))))

;; By isomorphismp-galois-subgroup-map, (order (galois-subgroup k e f)) = (order (galois e k)).
;; Thus, by order-galois-group, edegree-mult, and order-quotient,

;;   (order (quotient (galois e f) (galois-subgroup e k f))) = (order (galois k f),

;; and by equal-orders-isomorphism, this endomorphism is an isomorphism:

(defthmd isomorphismp-quotient-map-galois-restriction-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
	   (isomorphismp (quotient-map (galois-restriction-map e k f) (galois e f) (galois k f))
	                 (quotient (galois e f) (galois-subgroup k e f))
			 (galois k f))))

;;---------------------------------------------------

;; Let h be a subgroup of g.  We shall construct an extension k of f, an extension d of k, and an 
;; isomorphism phi from d to e over f such that h is the image of the galois subgroup of k under the galois
;; group isomorphism induced by phi, i.e.,

;;     (image (auto-map phi d e f) (galois-subgroup k d f) (galois e f)) = h.

;; The proof is based on functional instantiation of metafield-field, with the substitution of the predicate

;;     (lambda (x) (and (feltp x e) (fixedp x h e f)))

;; for the metafield m$.

;; Thus, we must show that this predicate recognizes a metafield containing f:

(defthm fixedp-fadd
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (feltp x e) (fixedp x h e f)
                (feltp y e) (fixedp y h e f))
	   (and (feltp (fadd x y e) e) (fixedp (fadd x y e) h e f))))

(defthm fixedp-fmul
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (feltp x e) (fixedp x h e f)
                (feltp y e) (fixedp y h e f))
	   (and (feltp (fmul x y e) e) (fixedp (fmul x y e) h e f))))

(defthm fixedp-flift
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (feltp x f))
	   (fixedp (flift x f e) h e f)))

;; There is some work in defining the analogs of the functions underlying metafield-field, but once the
;; theorem is proved, these definitions may be forgotten:

(defun-sk range-includes-fixed (phi d h e f)
  (forall (y)
    (implies (and (feltp y e) (fixedp y h e f))
             (in-range-p y phi d e f))))

(defthm extend-range-to-fixed-measure-decreases
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (extensionp d f)
                (embeddingp phi d e f)
		(feltp y e)
		(fixedp y h e f)
		(not (in-range-p y phi d e f)))
	   (and (posp (edegree d f))
	        (posp (edegree e f))
	        (< (edegree d f)
	           (edegree (cons (extension-poly y phi d e f) d) f))
	        (<= (edegree (cons (extension-poly y phi d e f) d) f)
	            (edegree e f)))))

(defun extend-range-to-fixed (d phi h e f)
  (declare (xargs :measure (nfix (- (edegree e f) (edegree d f)))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-range-to-fixed-measure-decreases
				         (y (range-includes-fixed-witness phi d h e f))))))))
  (let* ((y (range-includes-fixed-witness phi d h e f))
         (q (extension-poly y phi d e f)))
    (if (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
             (extensionp d f) (embeddingp phi d e f)
	     (feltp y e) (fixedp y h e f) (not (in-range-p y phi d e f)))
        (extend-range-to-fixed (cons q d) (cons y phi) h e f)
      (mv d phi))))

(defthm extend-fixed-measure-decreases
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (extensionp d f)
                (embeddingp phi d e f)
		(feltp y e)
		(not (in-range-p y phi d e f)))
	   (and (posp (edegree d f))
	        (posp (edegree e f))
	        (< (edegree d f)
	           (edegree (cons (extension-poly y phi d e f) d) f))
	        (<= (edegree (cons (extension-poly y phi d e f) d) f)
	            (edegree e f)))))

(defun extend-fixed (d phi h e f)
  (declare (xargs :measure (nfix (- (edegree e f) (edegree d f)))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-fixed-measure-decreases
				          (y (range-includes-e-witness phi d e f))))))))
  (let* ((y (range-includes-e-witness phi d e f))
         (q (extension-poly y phi d e f)))
    (if (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
             (extensionp d f) (embeddingp phi d e f) (feltp y e)
             (not (in-range-p y phi d e f)))
        (extend-fixed (cons q d) (cons y phi) h e f)
      (mv d phi))))

(defund k* (h e f) (mv-nth 0 (mv-list 2 (extend-range-to-fixed f () h e f))))

(defund psi* (h e f) (mv-nth 1 (mv-list 2 (extend-range-to-fixed f () h e f))))

(defund d* (h e f) (mv-nth 0 (mv-list 2 (extend-fixed (k* h e f) (psi* h e f) h e f))))

(defund phi* (h e f) (mv-nth 1 (mv-list 2 (extend-fixed (k* h e f) (psi* h e f) h e f))))

;; The functional instance of metafield-field:

(defthmd fixed-field
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f)))
           (and (extensionp (d* h e f) (k* h e f)) (extensionp (k* h e f) f)
                (iso-embeddingp (phi* h e f) (d* h e f) e f)
                (implies (feltp x (d* h e f))
                         (iff (fixedp (embed x (phi* h e f) e f) h e f)
                              (fliftedp x (k* h e f) (d* h e f)))))))


