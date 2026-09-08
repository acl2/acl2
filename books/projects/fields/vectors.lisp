(in-package "DM")

(include-book "extensions")
(local (include-book "support/embeddings"))

;; Various results in subsequent books depends on the observation that if e is a field extension of f, then
;; e is a vector space over f.  This allows us to apply the results of "../linear/" by functional 
;; instantiation.  First we define analogs, in the context of field extensions, of the relevant functions of 
;; "../linear/fmat" and "../linear/reduction" pertaining to matrices and row reduction.  The we define 
;; analogs of the constrained vector space functions of "../vectors" and prove the they satisfy the vector
;; space axioms.

;;----------------------------------------------------------------------------------------------------------
;;                                             Matrices over a Field
;;----------------------------------------------------------------------------------------------------------

;; List of field elements of length n:

(defun elistnp (x n f)
  (if (zp n)
      (null x)
    (and (consp x)
         (feltp (car x) f)
	 (elistnp (cdr x) (1- n) f))))

;; List of zeroes:

(defun elist0p (x f)
  (if (consp x)
      (and (= (car x) (fzero f))
           (elist0p (cdr x) f))
    (null x)))

;; List of n zeroes:

(defun elistn0 (n f)
  (if (zp n)
      ()
      (cons (fzero f) (elistn0 (1- n) f))))

;; Sum of members of a list:

(defun elist-sum (l f)
  (if (consp l)
      (fadd (car l) (elist-sum (cdr l) f) f)
    (fzero f)))

;; List of sums of corresponding members:

(defun elist-add (x y f)
  (if (consp x)
      (cons (fadd (car x) (car y) f)
            (elist-add (cdr x) (cdr y) f))
    ()))

;; Scalar multiplication:

(defun elist-scalar-mul (c x f)
  (if (consp x)
      (cons (fmul c (car x) f)
            (elist-scalar-mul c (cdr x) f))
    ()))

;; Dot product:

(defun edot (x y f)
  (if (consp x)
      (fadd (fmul (car x) (car y) f)
            (edot (cdr x) (cdr y) f)
	    f)
    (fzero f)))

(defun edot-list (x l f)
  (if (consp l)
      (cons (edot x (car l) f)
            (edot-list x (cdr l) f))
    ()))

;; Matrix of field elements:

(defun ematp (x m n f)
  (if (zp m)
      (null x)
    (and (consp x)
         (elistnp (car x) n f)
	 (ematp (cdr x) (1- m) n f))))

;; Identity matrix:

(defun eunit (j n f)
  (if (zp n)
      ()
    (if (zp j)
        (cons (fone f) (elistn0 (1- n) f))
      (cons (fzero f) (eunit (1- j) (1- n) f)))))

(defun id-emat-aux (j n f)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (eunit j n f) (id-emat-aux (1+ j) n f))
    ()))

(defund id-emat (n f)
  (id-emat-aux 0 n f))

;; Matrix multiplication:

(defun col (j a)
  (if (consp a)
      (cons (nth j (car a))
            (col j (cdr a)))
    ()))

(defun transpose-mat-aux (a j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (col j a) (transpose-mat-aux a (1+ j) n))
    ()))

(defund transpose-mat (a)
  (transpose-mat-aux a 0 (len (car a))))

(defund emat* (a b f)
  (if (consp a)
      (cons (edot-list (car a) (transpose-mat b) f)
            (emat* (cdr a) b f))
      ()))

;; Row reduction:

(defun replace-row (a k r)
  (if (zp k)
      (cons r (cdr a))
    (cons (car a) (replace-row (cdr a) (1- k) r))))

(defund emat-ero1 (a c k f)
  (replace-row a k (elist-scalar-mul c (nth k a) f)))

(defund emat-ero2 (a c j k f)
  (replace-row a k (elist-add (elist-scalar-mul c (nth j a) f) (nth k a) f)))

(defund emat-ero3 (a j k)
  (replace-row (replace-row a k (nth j a)) j (nth k a)))

(defun clear-emat-column (a k j m f)
  (if (zp m)
      a
    (if (= (1- m) k)
	(clear-emat-column a k j (1- m) f)
      (clear-emat-column (emat-ero2 a (fneg (nth j (nth (1- m) a)) f) k (1- m) f)
		         k j (1- m) f))))

(defun first-nonzero-elist (r f)
  (if (consp r)
      (if (= (car r) (fzero f))
          (1+ (first-nonzero-elist (cdr r) f))
	0)	
    ()))

(defun emat-row-with-nonzero-at-least-index (a m k f)
  (if (and (natp k) (natp m) (< k m))
      (let ((i (emat-row-with-nonzero-at-least-index a (1- m) k f)))
	(if (or (elist0p (nth (1- m) a) f)
	        (and i (<= (first-nonzero-elist (nth i a) f) (first-nonzero-elist (nth (1- m) a) f))))
	    i
	  (1- m)))
    ()))

(defund row-reduce-emat-step (a m k i j f)
  (clear-emat-column (emat-ero3 (emat-ero1 a (frecip (nth j (nth i a)) f) i f)
		                i k)
		     k j m f))

(defun row-reduce-emat-aux (a m k f)
  (declare (xargs :measure (nfix (- m k))))
  (let ((i (emat-row-with-nonzero-at-least-index a m k f)))
    (if (and (natp k) (natp m) (< k m) i)
        (row-reduce-emat-aux (row-reduce-emat-step a m k i (first-nonzero-elist (nth i a) f) f)
		   	     m (1+ k) f)
      a)))

(defund row-reduce-emat (a f)
  (row-reduce-emat-aux a (len a) 0 f))

(defun num-nonzero-rows-emat (a f)
  (if (consp a)
      (if (elist0p (car a) f)
          0
	(1+ (num-nonzero-rows-emat (cdr a) f)))
    0))

(defun emat-row-rank (a f)
  (num-nonzero-rows-emat (row-reduce-emat a f) f))

;; Inverse matrix:

(defund apply-emat-row-op (op a f)
  (case (car op)
    (1 (emat-ero1 a (cadr op) (caddr op) f))
    (2 (emat-ero2 a (cadr op) (caddr op) (cadddr op) f))
    (3 (emat-ero3 a (cadr op) (caddr op)))))

(defun clear-emat-column-ops (a k j m f)
  (if (zp m)
      ()
    (if (= k (1- m))
        (clear-emat-column-ops a k j (1- m) f)
      (cons (list 2 (fneg (nth j (nth (1- m) a)) f) k (1- m))
	    (clear-emat-column-ops (emat-ero2 a (fneg (nth j (nth (1- m) a)) f) k (1- m) f) k j (1- m) f)))))

(defund row-reduce-emat-step-ops (a m k i j f)
  (cons (list 1 (frecip (nth j (nth i a)) f) i)
        (cons (list 3 i k)
	      (clear-emat-column-ops (emat-ero3 (emat-ero1 a (frecip (nth j (nth i a)) f) i f)
				                i k)
			             k j m f))))

(defun row-reduce-emat-aux-ops (a m k f)
  (declare (xargs :measure (nfix (- m k))))
  (let* ((i (emat-row-with-nonzero-at-least-index a m k f))
	 (j (and i (first-nonzero-elist (nth i a) f))))
    (if (and (natp k) (natp m) (< k m) i)
        (append (row-reduce-emat-step-ops a m k i j f)
	        (row-reduce-emat-aux-ops (row-reduce-emat-step a m k i j f) m (1+ k) f))                
      ())))

(defund row-reduce-emat-ops (a f)
  (row-reduce-emat-aux-ops a (len a) 0 f))

(defund elem-emat (op m f)
  (apply-emat-row-op op (id-emat m f) f))

(defund row-ops-emat (ops m f)
  (if (consp ops)
      (emat* (row-ops-emat (cdr ops) m f)
             (elem-emat (car ops) m f)
             f)
    (id-emat m f)))

(defund row-reduction-emat (a f)
  (row-ops-emat (row-reduce-emat-ops a f) (len a) f))

(defund inverse-emat (a f)
  (row-reduction-emat a f))


;;----------------------------------------------------------------------------------------------------------
;;                                        Field Extensions as Vector Spaces
;;----------------------------------------------------------------------------------------------------------

;; We shall show that an extension e of f is a vector space over f.  That is, we shall define functions
;; corresponding to the functions that are introduced by the encapsulation of "../linear/vectors" that 
;; characterize a vector space and prove the theorems corresponding to the vector space axioms.

;; The first 6 of these functions are easily defined, and their required properties are readily verified:

;;  vp        (lambda (x) (feltp x e))
;;  v+        (lambda (x y) (fadd x y e))
;;  v0        (lambda () (fzero e))
;;  v-        (lambda (x) (fneg x e))
;;  v*        (lambda (c x) (fmul (flift c f e) x e))
;;  vlistnp   (lambda (x n) (elistnp x n e))

;; The remaining 4 functions are defined below:

;;  vcomb     (lambda (flist elist) (ecomb flist elist e))
;;  vdim      (lambda () (edegree e f))
;;  vbasis    (lambda () (ebasis0 e f))
;;  vcoords   (lambda (x) (ecoords0 x e f))

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

(defthm posp-edegree
  (implies (extensionp e f)
           (posp (edegree e f)))
  :rule-classes (:type-prescription :rewrite))

;; Note that edegree is multiplicative in the following sense:

(defthmd edegree-mult
  (implies (and (extensionp e k) (extensionp k f))
           (equal (edegree e f)
	          (* (edegree e k) (edegree k f))))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/1" :use ((:instance len-extends (e k) (f e))	  
	                        (:instance len-extends (e (cdr e)) (f k))))))

;; A lower bound on the degree of an extension:

(defthmd edegree-lower-bound
  (implies (extensionp e f)
           (>= (edegree e f) (expt 2 (- (len e) (len f)))))
  :hints (("Subgoal *1/2" :nonlinearp t :use ((:instance degree-car-field (f e))))))

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
           (ematp (split n x) m n f)))
	   
;; List of linear combinations of b:

(defun ecomb-list (c b e f)
  (if (consp c)
      (cons (ecomb (car c) b e f)
            (ecomb-list (cdr c) b e f))
    ()))

(defthmd elistnp-ecomb-list
  (implies (and (extensionp e f)
                (ematp c m n f)
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
	          (elist-sum (ecomb-lists (split n c) (split n b) e f) e))))

(defthmd ecomb-decomp
  (implies (and (extensionp e f) (natp m) (natp n)
                (elistnp c (* m n) f)
		(elistnp b (* m n) e))
	   (equal (ecomb c b e f)
	          (elist-sum (ecomb-lists (split n c) (split n b) e f) e))))

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

(defthmd elist-sum-ecomb-step
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (natp m) (natp n)
                (ematp c m n f)
		(elistnp b1 m e) (consp b1)
		(elistnp b2 n (cdr e)) (consp b2)
		(equal (elist-sum (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
		       (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))))
	   (equal (elist-sum (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
	          (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e)))))
			
;; Proof:

;; (elist-sum (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
;;   = (fadd (ecomb (car c) (firstn n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f)
;;           (elist-sum (ecomb-lists (cdr c) (split n (nthcdr n (fmul-lists b1 (plift b2 (cdr e) e) e))) e f) e)
;; 	     e)
;;   = (fadd (ecomb (car c) (fmul-list (car b1) (plift b2 (cdr e) e) e) e f)
;;           (elist-sum (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
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
                (ematp c m (len b) f)
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
;;           = (elist-sum (ecomb-lists (split n c) (split n (ebasis0 e f)) e f) e)        [ecomb-decomp]
;;           = (elist-sum (ecomb-lists (split n c)                                        [definition of ebasis0]
;; 	                               (split n (fmul-lists b1 (plift b2 (cdr e) e) e))
;; 				       e f)
;; 		          e)
;;           = (ecomb (ecomb-list (split n c) b2 (cdr e) f) b1 e (cdr e))                 [elist-sum-ecomb]

;; => (ecomb-list (split n c) b2 (cdr e) f) = (elist0n m (cdr e))                         [simple-extension-basis-lin-indep]

;; => (split n c) = (elistn0-list n m f)                                                  [ecomb-list-elistn0-listp]

;; => c = (elistn0 (* m n) f))
;;----------------------------------------------------------------------------------------------------------


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


