(in-package "DM")

(include-book "fmat")
(include-book "projects/groups/symmetric" :dir :system)
(local (include-book "support/fdet"))

;; The term contributed by a permutation p in (sym n) to the determinant of an nxn
;;  matrix a is computed as follows:
;;   (1) select an entry from each row of a, the selection from row i being the one
;;       in column (nth i p), i.e., (entry i (nth i p) a);
;;   (2) compute the product of these n entries;
;;   (3) negate the product if p is an odd permutation.

(defun fdet-prod (a p n)
  (if (zp n)
      (f1)
    (f* (fdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(defund fdet-term (a p n)
  (if (even-perm-p p n)
      (fdet-prod a p n)
    (f- (fdet-prod a p n))))

;; The determinant of a is the sum over (slist n) of these signed products:

(defun fdet-sum (a l n)
  (if (consp l)
      (f+ (fdet-term a (car l) n)
	  (fdet-sum a (cdr l) n))
    (f0)))

(defund fdet (a n)
  (fdet-sum a (slist n) n))

;; By pair-listp-perm-pairs and fp-pairs-prod, fdet-prod and fdet-term return ring elements:

(defthm fp-fdet-prod
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(natp k) (<= k n))
           (fp (fdet-prod a p k))))

(defthm fp-fdet-term
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n)))
           (fp (fdet-term a p n))))

(defthm fp-fdet
  (implies (and (fmatp a n n) (posp n))
	   (fp (fdet a n))))

;;-------------------------------------------------------------------------------------------------------
;;   Properties of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; To compute (fdet (id-fmat n) n), note that if p is any permutation other than (ninit n), we can find
;; i < n such that (nth i p) <> i, and hence (entry i (nth i p) (id-fmat n)) = (f0), which implies
;; (fdet-term (id-fmat p n)) = (f0).  On the other hand, (nth i (ninit n)) = i for all i, which implies
;; (fdet-term (id-fmat (ninit n) n)) = (f1).   Thus,

(defthm fdet-id-fmat
  (implies (posp n)
           (equal (fdet (id-fmat n) n)
	          (f1))))

;; fdet is invariant under transpose-mat.  This follows from the observation that the term contributed
;; to the determinant of the transpose of a by a permutation p is the same as the term contributed to
;; the determinant of a by the inverse of p:
  
(defthmd fdet-term-transpose
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n)))
           (equal (fdet-term (transpose-mat a) p n)
	          (fdet-term a (inv-perm p n) n))))

(defthmd fdet-transpose
  (implies (and (posp n) (fmatp a n n))
           (equal (fdet (transpose-mat a) n)
	          (fdet a n))))

;; fdet is alternating, i.e., if 2 rows of a are equal, then its determinant is (f0).

;; To prove this, suppose rows i and j of a are equal, where i <> j.  Given a permutation p, let
;; p' = (comp-perm p (transpose i j n) n).  Then the factors of (fdet-prod a p' n) are the same as
;; those of (fdet-prod a p n):

(defthmd fdet-prod-comp-perm
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (fdet-prod a (comp-perm p (transpose i j n) n) n)
	          (fdet-prod a p n))))

;; If p is even, then p' is odd, and therefore (fdet-term a p' n) is the negative of (fdet-term a p n):

(defthmd fdet-term-comp-perm
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (f+ (fdet-term a (comp-perm p (transpose i j n) n) n)
	              (fdet-term a p n))
		  (f0))))

;; Consequently, the sum of terms contributed by the odd permutations is the negative of the
;; sum of terms contributed by the even permutations:

(defthmd fdet-alternating
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (equal (fdet a n) (f0))))

;; fdet is n-linear, i.e, linear as a function of each row.  This property is
;; specified in terms of the basic operation of replacing a row of a with a given list.
;; For a given row i and permutation p, the term contributed by p to the determinant of
;; (replace-row a i x) by each permutation is a linear function of x:

(defthm fdet-term-replace-row
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(flistnp x n) (flistnp y n) (fp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (fdet-term a3 p n)
	            (f+ (f* c (fdet-term a1 p n))
			(fdet-term a2 p n))))))

;; The desired result follows by summing over all permutations:
	          
(defthm fdet-n-linear
  (implies (and (fmatp a n n) (posp n) (natp i) (< i n)
		(flistnp x n) (flistnp y n) (fp c))
	   (equal (fdet (replace-row a i (flist-add (flist-scalar-mul c x) y)) n)
		  (f+ (f* c (fdet (replace-row a i x) n))
		      (fdet (replace-row a i y) n)))))

;; As a consequence of fdet-n-linear, if a has a zero row, then its deteminant is (f0).
;; To prove this, we instantiate fdet-n-linear with c = (f1) and x = y = (flistn0 n):

(defthmd fdet-replace-0-1
  (implies (and (fmatp a n n) (posp n) (natp k) (< k n))
           (equal (f+ (fdet (replace-row a k (flistn0 n)) n)
	              (fdet (replace-row a k (flistn0 n)) n))
		  (fdet (replace-row a k (flistn0 n)) n))))

;; It follows that (fdet (replace-row a k (flistn0 n)) n) = (f0).  But if (row k a) = (flistn0 n),
;; then (replace-row a k (flistn0 n)) = a:

(defthmd fdet-row-0
  (implies (and (fmatp a n n) (posp n) (natp k) (< k n) (= (nth k a) (flistn0 n)))
           (equal (fdet a n)
	          (f0))))


;;-------------------------------------------------------------------------------------------------------
;;   Uniqueness of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; We shall show that for given n, fdet is the unique n-linear alternating function on
;; nxn matrices such that (fdet (id-fmat n) n) = (f1).  To that end, we constrain the
;; function fdetn as follows:

(encapsulate (((n) => *))
  (local (defun n () 2))
  (defthm posp-n
    (posp (n))
    :rule-classes (:type-prescription :rewrite)))

(encapsulate (((fdetn *) => *))
  (local (defun fdetn (a) (fdet a (n))))
  (defthm fp-fdetn
    (implies (fmatp a (n) (n))
             (fp (fdetn a))))
  (defthmd fdetn-n-linear
    (implies (and (fmatp a (n) (n)) (natp i) (< i (n))
		  (flistnp x (n)) (flistnp y (n)) (fp c))
	     (equal (fdetn (replace-row a i (flist-add (flist-scalar-mul c x) y)))
		    (f+ (f* c (fdetn (replace-row a i x)))
		        (fdetn (replace-row a i y))))))
  (defthmd fdetn-adjacent-equal
    (implies (and (fmatp a (n) (n))
		  (natp i) (< i (1- (n))) (= (row i a) (row (1+ i) a)))
	     (equal (fdetn a) (f0)))
    :hints (("Goal" :use ((:instance fdet-alternating (n (n)) (j (1+ i))))))))

;; Our objective is to prove that (fdetn a) = (f* (fdet a (n)) (fdetn (id-fmat (n)))):

;; (defthmd fdet-unique
;;   (implies (fmatp a (n) (n))
;;            (equal (fdetn a)
;;                   (f* (fdet a (n))
;;                       (fdetn (id-fmat (n)))))))

;; If we also prove that for a given function f, (f a n) satisfies the constraints on (fdetn a),
;; we may conclude by functional instantiation that (f a n) = (f* (fdet a n) (f (id-fmat n))).
;; From this it follows that if f has the additional property (f (id-fmat n)) = (f1), then
;; (f a) = (fdet a (n)).

;; Note that we have replaced the property that fdetn is alternating with the weaker property
;; fdetn-adjacent-equal, which says that the value is (f0) if 2 adjacent rows are equal.  This
;; relaxes the proof obligations for functional instantiation, which will be critical for the
;; proof of correctness of cofactor expansion.  We shall show that this property together with
;; n-linearity implies that the same holds for 2 non-adjacent rows.

;; It follows from fdetn-n-linear and fdetn-adjacent-equal that transposing 2 adjacent rows negates
;; the value of fdetn:

(defthmd fdetn-interchange-adjacent
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (fdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
	          (f- (fdetn a)))))

;; Interchanging adjacent rows may be expressed as a permutation:

(defthmd interchange-adjacent-fmat-permute
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a))
	          (permute a (transpose i (1+ i) (n))))))

(defthmd fdetn-permute-adjacent-transpose
  (implies (and (fmatp a (n) (n))
                (natp i) (< i (1- (n))))
           (equal (fdetn (permute a (transpose i (1+ i) (n))))
                  (f- (fdetn a)))))

;; Note that applying any permutation to the rows of a produces a matrix of the
;; same dimensions:

(defthm fmatp-permute
  (implies (and (fmatp a m n) (posp m) (posp n)
                (in p (sym m)))
	   (fmatp (permute a p) m n)))

;; Next we show that fdetn-permute-adjacent-transpose applies to a transposition of any
;; 2 rows.  First note that for 0 <= i and i - 1 < j < n, (transpose i j (n)) is the
;; result of conjugating (transpose i (1- j) (n)) by (transpose (1- j) j (n)):

(defthmd conj-adjacent-transpose-fmat
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< i (1- j)) (< j (n)))
           (equal (comp-perm (comp-perm (transpose (1- j) j (n))
                                        (transpose i (1- j) (n))
			                (n))
		             (transpose (1- j) j (n))
		             (n))
		  (transpose i j (n)))))

;; The claim follows by induction:

(defthmd fdetn-permute-transpose
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< i j) (< j (n)))
	   (equal (fdetn (permute a (transpose i j (n))))
                  (f- (fdetn a)))))
       
;; Now suppose (row i a) = (row j a), where 0 <= i < j < (n).  We would like to show that 
;; (fdetn a) = (f0).  If j = i + 1 ,then apply fdetn-adjacent-equal.  Otherwise, let
;; a' = (permute (transpose (1+ i) j (n)) a).  By nth-permute,

;;   (nth i a') = (nth (nth i (transpose (1+ i) j (n))) a) = (nth i a)

;; and

;;   (nth (1+ i) a') = (nth (nth (1+ i) (transpose (1+ i) j (n))) a) = (nth j a) = (nth i a)

;; and by fdetn-adjacent-equal, (fdetn a') = (f0).  By fdetn-transpose-rows,

;;   (fdetn a) = (f- (fdetn a') = (f- (f0)) = (f0).

;; Thus, fdetn is an alternating function:

(defthmd fdetn-alternating
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< i (n)) (< j (n)) (not (= i j)) (= (row i a) (row j a)))
	   (equal (fdetn a) (f0))))

;; We shall require a generalization of fdetn-transpose-rows to arbitrary permutations.
;; First note that fdetn-permute-transpose may be restated as follows:

(defthmd fdetn-permute-rows
  (implies (and (fmatp a (n) (n))
                (in p (sym (n))))
	   (equal (fdetn (permute a p))
	          (if (even-perm-p p (n))
		      (fdetn a)
		    (f- (fdetn a))))))

;; Since fdet satisfies the constraints on fdetn, this applies to fdet by functional
;; instantiation:

(defthmd fdet-permute-rows
  (implies (and (fmatp a n n) (posp n)
                (in p (sym n)))
	   (equal (fdet (permute a p) n)
	          (if (even-perm-p p n)
		      (fdet a n)
		    (f- (fdet a n))))))

;; The proof of fdet-unique is based on lists of k-tuples of natural numbers less than (n),
;; where k <= (n):

(defun tuplep (x k)
  (if (zp k)
      (null x)
    (and (consp x)
         (natp (car x))
         (< (car x) (n))
	 (tuplep (cdr x) (1- k)))))

(defun tuple-list-p (l k)
  (if (consp l)
      (and (tuplep (car l) k)
           (tuple-list-p (cdr l) k))
    (null l)))

;; We recursively define a dlist containing all such k-tuples:

(defun extend-tuple-aux (x m) 
  (if (consp m)
      (cons (append x (list (car m)))
            (extend-tuple-aux x (cdr m)))
    ()))

(defund extend-tuple (x)
  (extend-tuple-aux x (ninit (n))))

(defun extend-tuples (l)
  (if (consp l)
      (append (extend-tuple (car l))
              (extend-tuples (cdr l)))
    ()))

(defun all-tuples (k)
  (if (zp k)
      (list ())
    (extend-tuples (all-tuples (1- k)))))

(defthm dlistp-all-tuples
  (implies (and (natp k) (<= k (n)))
           (dlistp (all-tuples k))))

(defthmd member-all-tuples
  (implies (and (natp k) (<= k (n)))
           (iff (member x (all-tuples k))
	        (tuplep x k))))

;; Let a be a fixed (n)x(n) matrix.  We associate a value with a k-tuple x as follows:

(defun extract-entries (x a)
  (if (consp x)
      (cons (nth (car x) (car a))
            (extract-entries (cdr x) (cdr a)))
    ()))

(defun funits (x)
  (if (consp x)
      (cons (funit (car x) (n))
            (funits (cdr x)))
    ()))

(defun feval-tuple (x k a)
  (f* (flist-prod (extract-entries x a))
      (fdetn (append (funits x) (nthcdr k a)))))

(defthm fp-feval-tuple
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n)) (tuplep x k))
           (fp (feval-tuple x k a))))

;; The sum of the values of a list of k-tuples: 

(defun fsum-tuples (l k a)
  (if (consp l)
      (f+ (feval-tuple (car l) k a)
	  (fsum-tuples (cdr l) k a))
    (f0)))

(defthm fp-fsum-tuples
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k))
           (fp (fsum-tuples l k a))))

;; We would like to compute (fsum-tuples (all-tuples k) k a).  The case k = 0 is trivial:

(defthmd feval-tuple-nil
  (implies (fmatp a (n) (n))
           (equal (feval-tuple () 0 a)
	          (fdetn a))))

(defthm fsum-0-tuples
  (implies (fmatp a (n) (n))
           (equal (fsum-tuples (all-tuples 0) 0 a)
	          (fdetn a))))

;; We shall prove, as a consequence of n-linearity of fdetn, that incrementing k does not change the value of the sum.

;; If (flistnp r (n)), We may think of r as a sum of multiples of unit vectors.  Given a sublist l of (ninit (n)),
;; (fsum-select l n) is the sum of the subset of these multiples corresponding to the members of l:

(defun fsum-select (l r)
  (if (consp l)
      (flist-add (flist-scalar-mul (nth (car l) r) (funit (car l) (n)))
                 (fsum-select (cdr l) r))
    (flistn0 (n))))

(defthm fsum-select-ninit
  (implies (flistnp r (n))
           (equal (fsum-select (ninit (n)) r)
	          r)))

;; We shall derive a formula for (fsum-tuples (extend-tuple x) (1+ k) a).

;; Let l be a sublist of (ninit (n)).  According to the definitions of fsum-tuples and extend-tuple-aux,

;;   (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (f+ (feval-tuple (append x (list (car l))) (1+ k) a)
;;             (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)),

;; where
  
;;   (feval-tuple (append x (list i)) (1+ k) a)
;;     = (f* (flist-prod (extract-entries (append x (list i)) a))
;;           (fdetn (append (funits (append x (list i))) (nthcdr (1+ k) a))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (f* (nth i (nth k a))
;;               (fdetn (append (append (funits x) (list (unit i (n)))) (nthcdr (1+ k) a)))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (f* (nth i (nth k a))
;;	         (fdetn (replace-row (append (funits x) (nthcdr k a) k (unit i (n)))))))

;; and

;;   (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
;;     = (feval-tuple x k (replace-row a k (fsum-select (cdr l) (nth k a))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select (cdr l) (nth k a)))))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select (cdr l) (nth k a))))).

;; Thus, by fdetn-n-linear,

;;   (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select l (nth k a)))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select l (nth k a)))))))
;;     = (feval-tuple x k (replace-row a k (fsum-select l (nth k a)))).

;; Substitute (ninit (n)) for l:

;;   (fsum-tuples (extend-tuple x) (1+ k) a)
;;     = (feval-tuple x k (replace-row a k (fsum-select (ninit (n)) (nth k a))))
;;     = (feval-tuple x k (replace-row a k (nth k a)))
;;     = (feval-tuple x k a):

(defthm fsum-tuples-extend-tuple
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (fsum-tuples (extend-tuple x) (1+ k) a)
		  (feval-tuple x k a))))

;; This leads to the recurrence formula

;;    (fsum-tuples (all-tuples k) k a) = (fsum-tuples (all-tuples (1- k)) (1- k) a):

(defthm fsum-tuples-append
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k) (tuple-list-p m k))
           (equal (fsum-tuples (append l m) k a)
	          (f+ (fsum-tuples l k a) (fsum-tuples m k a)))))
                        
(defthmd fsum-tuples-extend-tuples
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
		(tuple-list-p l k))
	   (equal (fsum-tuples (extend-tuples l) (1+ k) a)
	          (fsum-tuples l k a))))

(defthm fsum-tuples-extend-all-tuples
  (implies (and (fmatp a (n) (n))
                (posp k) (<= k (n)))
	   (equal (fsum-tuples (all-tuples k) k a)
	          (fsum-tuples (all-tuples (1- k)) (1- k) a))))

;; By induction, (fsum-tuples (all-tuples (n)) (n) a) = (fdetn a):

(defthmd fsum-tuples-fdetn
  (implies (fmatp a (n) (n))
	   (equal (fsum-tuples (all-tuples (n)) (n) a)
	          (fdetn a))))

;; If x is an (n)-tuple, then (feval-tuple x (n) a) = (fdetn (funits x)).  Since fdetn
;; is alternating, this value is (f0) unless x is a dlist:

(defthm fdetn-funits-0
  (implies (and (tuplep x (n)) (not (dlistp x)))
           (equal (fdetn (funits x))
	          (f0))))

(defthm feval-tuple-r0
  (implies (and (fmatp a (n) (n))
                (tuplep x (n))
		(not (dlistp x)))
	   (equal (feval-tuple x (n) a)
	          (f0))))

;; But (select-dlists (all-tuples (n))) = (slist (n)), and therefore (fsum-tuples (slist (n)) (n) a) = (fdetn a).
;; However, that first equation looks like it would be hard to prove, so we shall instead prove
;; (permp (select-dlists (all-tuples (n))) (slist (n)) and derive the second equation from that.
                        
;; Combine these results with fsum-tuples-dlists and fsum-tuples-fdetn:

(defthmd fsum-tuples-n
  (implies (fmatp a (n) (n))
	   (equal (fsum-tuples (slist (n)) (n) a)
	          (fdetn a))))
			
;; For p in (slist (n)),

;;   (feval-tuple p (n) a) = (f* (flist-prod (extract-entries p a))
;;                              (fdetn (funits p))),
				
;; where (flist-prod (extract-entries p a)) = (fdet-prod a p (n)).

;; But

;;   (fdetn (funits p)) = (fdetn (permute (id-fmat (n)) p))
;;                     = (f* (if (even-perm-p p (n)) (f1) (f- (f1)))
;;                           (fdetn (id-fmat (n)))).

(defthmd funits-permute-id-mat
  (implies (member p (slist (n)))
           (equal (funits p)
	          (permute (id-fmat (n)) p))))

(defthmd feval-tuple-fdet-prod
  (implies (and (fmatp a (n) (n))
                (member p (slist (n))))
	   (equal (feval-tuple p (n) a)
	          (f* (fdet-prod a p (n))
		      (fdetn (funits p))))))

(defthmd fdetn-permute-rows
  (implies (and (fmatp a (n) (n))
                (in p (sym (n))))
	   (equal (fdetn (permute a p))
	          (if (even-perm-p p (n))
		      (fdetn a)
		    (f- (fdetn a))))))
		    
;; Thus, we have

(defthmd feval-tuple-perm
  (implies (and (fmatp a (n) (n))
                (member p (slist (n))))
	   (equal (feval-tuple p (n) a)
	          (f* (fdet-term a p (n))
		      (fdetn (id-fmat (n)))))))

;; The desired result follows by summing over (slist (n)):

(defthmd fsum-tuples-slist
  (implies (fmatp a (n) (n))
	   (equal (fsum-tuples (slist (n)) (n) a)
	          (f* (fdet a (n))
		      (fdetn (id-fmat (n)))))))
	          
(defthmd fdet-unique
  (implies (fmatp a (n) (n))
           (equal (fdetn a)
                  (f* (fdet a (n))
                      (fdetn (id-fmat (n)))))))


;;-------------------------------------------------------------------------------------------------------
;;   Multiplicativity of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; As an application of fdet-unique, we shall prove that for nxn matrices a and b,

;;   (fdet (fmat* a b) n) = (f* (fdet a n) (fdet b n).

;; To this end, we shall show that the following is a determinant function of its first
;; argument, i.e., it satisfies the constraints on fdetn:

(defun fdet-fmat* (a b n)
  (fdet (fmat* a b) n))

;; First show that fdet-fmat* is n-linear:

;;   (fdet-fmat* (replace-row a k (flist-add (flist-scalar-mul c x) y)) b n)
;;      = (fdet (fmat* (replace-row a k (flist-add (flist-scalar-mul c x) y)) b) n)
;;      = (fdet (replace-row (fmat* a b)
;;                           k
;;     		             (fdot-list (flist-add (flist-scalar-mul c x) y) (transpose-mat b)))
;;     	        n)
;;      = (fdet (replace-row (fmat* a b)
;;                           k
;;     		             (flist-add (flist-scalar-mul c (fdot-list x (transpose-mat b)))
;;     		                        (fdot-list y (transpose-mat b))))
;;              n)
;;      = (f+ (f* c (fdet (replace-row (fmat* a b) k (fdot-list x (transpose-mat b))) n)
;;            (fdet (replace-row (fmat* a b) k (fdot-list y (transpose-mat b))) n)
;;      = (f+ (f* c (fdet (fmat* (replace-row a k x) b) n))
;;            (fdet (fmat* (replace-row a y x) b) n))
;;      = (f+ (f* c (fdet-fmat* (replace-row a k x) b n))
;;            (fdet-fmat* (replace-row a k y) b n))

(defthmd fdet-fmat*-n-linear
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (natp k) (< k n)
                (flistnp x n) (flistnp y n) (fp c))
           (equal (fdet-fmat* (replace-row a k (flist-add (flist-scalar-mul c x) y)) b n)
                  (f+ (f* c (fdet-fmat* (replace-row a k x) b n))
                      (fdet-fmat* (replace-row a k y) b n)))))

;; The proof of the alternating property is easier:

(defthm fmat*-row
  (implies (and (natp m) (natp n) (fmatp a m n) (fmatp b n n) (natp k) (< k m))
           (equal (nth k (fmat* a b))
	          (fdot-list (nth k a) (transpose-mat b)))))
		      
(defthmd fdet-fmat*-adjacent-equal
  (implies (and (fmatp a n n) (fmatp b n n) (posp n)
		(natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (fdet-fmat* a b n) (f0))))

;; Now apply functional instantiation:

(defthmd fdet-fmat*-val-n
  (implies (and (fmatp a (n) (n)) (fmatp b (n) (n)))
           (equal (fdet-fmat* a b (n))
	          (f* (fdet a (n))
		      (fdet-fmat* (id-fmat (n)) b (n))))))

(defthmd fdet-multiplicative
  (implies (and (fmatp a n n) (fmatp b n n) (posp n))
           (equal (fdet (fmat* a b) n)
	          (f* (fdet a n) (fdet b n)))))
		  

;;-------------------------------------------------------------------------------------------------------
;;   Cofactor Expansion
;;-------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we define the submatrix (minor i j a) to be the result of deleting
;; the ith row and the jth column of a:

(defun delete-row (k a)
  (if (zp k)
      (cdr a)
    (cons (car a) (delete-row (1- k) (cdr a)))))

(defund delete-col (k a)
  (transpose-mat (delete-row k (transpose-mat a))))

(defund minor (i j a)
  (delete-col j (delete-row i a)))

(defthmd fmatp-delete-row
  (implies (and (fmatp a m n) (natp m) (natp k) (< k m))
           (fmatp (delete-row k a) (1- m) n)))

(defthmd fmatp-delete-col
  (implies (and (fmatp a m n) (posp m) (natp n) (> n 1) (natp k) (< k n))
           (fmatp (delete-col k a) m (1- n))))

(defthmd fmatp-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (fmatp (minor i j a) (1- n) (1- n))))

;; We derive an expression for an entry of (minor i j a):

(defthmd entry-fmat-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
	   (equal (entry r s (minor i j a))
	          (entry (if (>= r i) (1+ r) r)
		         (if (>= s j) (1+ s) s)
			 a))))

;; We shall also require an expression for the rth row of (minor i j a).  This is based on the
;; following function, which deletes the jth member of a list l:

(defun delete-nth (j l)
  (if (zp j)
      (cdr l)
    (cons (car l) (delete-nth (1- j) (cdr l)))))

(defthmd row-fmat-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j a))
	          (delete-nth j (nth (if (< r i) r (1+ r)) a)))))

;; minor commutes with transpose-mat:

(defthmd transpose-minor-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (and (fmatp (transpose-mat (minor i j a)) (1- n) (1- n))
	        (equal (transpose-mat (minor i j a))
	               (minor j i (transpose-mat a))))))

;; Next, we define the cofactor of an entry of a:

(defund fdet-cofactor (i j a n)
  (if (evenp (+ i j))
      (fdet (minor i j a) (1- n))
    (f- (fdet (minor i j a) (1- n)))))

;; Cofactor expansion of the determinant of a by column j:

(defun expand-fdet-col-aux (a i j n)
  (if (zp i)
      (f0)
    (f+ (f* (entry (1- i) j a)
            (fdet-cofactor (1- i) j a n))
	(expand-fdet-col-aux a (1- i) j n))))

(defund expand-fdet-col (a j n)
  (expand-fdet-col-aux a n j n))

;; Cofactor expansion of the determinant of a by row i:

(defun expand-fdet-row-aux (a i j n)
  (if (zp j)
      (f0)
    (f+ (f* (entry i (1- j) a)
            (fdet-cofactor i (1- j) a n))
	(expand-fdet-row-aux a i (1- j) n))))

(defund expand-fdet-row (a i n)
  (expand-fdet-row-aux a i n n))

;; Cofactor expansion by column i is equivalent to expansion of the transpose by row i:

(defthm fdet-cofactor-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (< i n) (natp j) (< j n))
	   (equal (fdet-cofactor j i (transpose-mat a) n)
	          (fdet-cofactor i j a n))))

(defthmd expand-fdet-row-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (< i n))
           (equal (expand-fdet-row (transpose-mat a) i n)
	          (expand-fdet-col a i n))))

;; We shall prove, by functional instantiation of fdet-unique,  that the result of cofactor
;; expansion by a column has the same value as the determinant, and it will follow that the
;; same is true for expansion by a row.  The requires proving analogs of the constraints on
;; fdetn.

(defthm fp-fdet-cofactor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (fp (fdet-cofactor i j a n))))

(defthm fp-expand-fdet-col
  (implies (and (fmatp a n n) (> n 1) (natp j) (< j n))
           (fp (expand-fdet-col a j n))))

;; The effect on (minor i j a) of replacing a row of a other than row i:

(defthmd minor-replace-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n))
	   (equal (minor i j (replace-row a k x))
	          (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))))

;; Replacing row i of a does not alter (minor i j a):

(defthmd minor-replace-fmat-row-i
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n))
	   (equal (minor i j (replace-row a i x))
	          (minor i j a))))

(defthmd cofactor-replace-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n))
	   (equal (fdet-cofactor i j (replace-row a i x) n)
	          (fdet-cofactor i j a n))))

;; It follows that cofactor expansion by column j is n-linear:

(defthmd expand-fdet-col-n-linear
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k n) (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col (replace-row a k (flist-add (flist-scalar-mul c x) y)) j n)
		  (f+ (f* c (expand-fdet-col (replace-row a k x) j n))
		      (expand-fdet-col (replace-row a k y) j n)))))

;; Now suppose adjacent rows k and k+1 of a are equal.  Then for any i other than k and k+1, (minor i j a)
;; has 2 adjacent rows,and therefore (fdet-cofactor i j a n) = (f0).  Meanwhile, (minor k j) = (minor (1+ k) j)
;; and (entry k j a) = (entry (1+ k) j a), but k + j and (k + 1) + j have opposite parities, and therefore
;; (fdet-cofactor k j a n) + (fdet-cofactor (1+ k) j a n) = (f0).  Thus, (expand-fdet-col a j n) = r0:

(defthmd expand-fdet-col-adjacent-equal
  (implies (and (fmatp a n n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (expand-fdet-col a j n)
	          (f0))))

;; By functional instantiation of fdet-unique,we have the following:

(defthmd expand-fdet-col-val
  (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-fdet-col a k n)
	          (f* (fdet a n)
		      (expand-fdet-col (id-fmat n) k n)))))

;; It remains to show that (expand-fdet-col (id-fmat n) k n) = (f1).
;; By row-fmat-minor, we habe the following expression for the rth row of (minor i j (id-fmat n)):

(defthmd nth-minor-id-fmat
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j (id-fmat n)))
	          (delete-nth j (funit (if (< r i) r (1+ r)) n)))))

;; The following is a consequence of the definirtions of funit and delete-nth:

(defthmd delete-nth-funit
  (implies (and (posp n) (natp j) (< j n) (natp k) (< k n))
           (equal (delete-nth j (funit k n))
	          (if (< j k)
		      (funit (1- k) (1- n))
		    (if (> j k)
		        (funit k (1- n))
		      (flistn0 (1- n)))))))

;; Consequently, if i <> j, then we find a zero row of (minor i j (id-fmat n)), which implies that
;; its determinant is (f0):

(defthmd nth-minor-id-fmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (nth (if (< j i) j (1- j)) (minor i j (id-fmat n)))
	          (flistn0 (1- n)))))

(defthmd fdet-minor-id-fmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (fdet (minor i j (id-fmat n)) (1- n))
	          (f0))))

;; On the other hand, (minor j j (id-fmat n)) = (id-fmat (1- n)):

(defthmd nth-minor-id-fmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n) (natp r) (< r (1- n)))
	   (equal (nth r (minor j j (id-fmat n)))
	          (nth r (id-fmat (1- n))))))

(defthmd minor-id-fmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n))
	   (equal (minor j j (id-fmat n))
	          (id-fmat (1- n)))))

;; Thus, the corresponding cofactor is (f1), as is the cofactor expansion:

(defthmd expand-fdet-col-id-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n))
           (equal (expand-fdet-col (id-fmat n) j n)
	          (f1))))

;; Combine this with expand-fdet-col-val:

(defthmd expand-fdet-col-fdet
  (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-fdet-col a k n)
	          (fdet a n))))

;; It follows from fdet-transpose, expand-fdet-row-transpose, and transpose-fmat-2 that the same holds
;; for row expansion:

(defthmd expand-fdet-row-fdet
  (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-fdet-row a k n)
	          (fdet a n))))

;; As a consequence of expand-fdet-row-fdet, we have a recursive version of fdet, based on cofactor
;; expansion with respect to row 0:

(mutual-recursion

  (defund fdet-rec-cofactor (j a n)
    (declare (xargs :measure (list (nfix n) 0 0)))
    (if (zp n)
        ()
      (if (evenp j)
          (fdet-rec (minor 0 j a) (1- n))
        (f- (fdet-rec (minor 0 j a) (1- n))))))

  (defun expand-fdet-rec-aux (a j n)
    (declare (xargs :measure (list (nfix n) 1 (nfix j))))
    (if (zp j)
        (f0)
      (f+ (f* (entry 0 (1- j) a)
              (fdet-rec-cofactor (1- j) a n))
	  (expand-fdet-rec-aux a (1- j) n))))

  (defund expand-fdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 2 0)))
    (expand-fdet-rec-aux a n n))

  (defun fdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 3 0)))
    (if (zp n)
        (f0)
      (if (= n 1)
          (entry 0 0 a)
        (expand-fdet-rec a n))))

)

(defthmd fdet-rec-fdet
  (implies (and (fmatp a n n) (posp n))
           (equal (fdet-rec a n)
	          (fdet a n))))


;;---------------------------------------------------------------------------------------------------------
;;    Classical Adjoint
;;---------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we shall define its cofactor matrix (cofactor-fmat a n) to be the nxn
;; matrix with entries

;;    (entry i j (cofactor-fmat a n)) = (fdet-cofactor i j a n).

;; We begin by defining the ith row of the cofactor matrix:

(defun cofactor-fmat-row-aux (i j a n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (> n 1) (natp j) (< j n))
      (cons (fdet-cofactor i j a n)
            (cofactor-fmat-row-aux i (1+ j) a n))
    ()))

(defund cofactor-fmat-row (i a n)
  (cofactor-fmat-row-aux i 0 a n))

(defthm flistnp-cofactor-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (flistnp (cofactor-fmat-row i a n) n)))

(defthmd nth-cofactor-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (nth j (cofactor-fmat-row i a n))
	          (fdet-cofactor i j a n))))

(defthm cofactor-fmat-row-replace-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (flistnp x n))
	   (equal (cofactor-fmat-row i (replace-row a i x) n)
                  (cofactor-fmat-row i a n))))

;; The cofactor matrix may now be defined:

(defun cofactor-fmat-aux (i a n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp n) (natp i) (< i n))
      (cons (cofactor-fmat-row i a n)
            (cofactor-fmat-aux (1+ i) a n))
    ()))

(defund cofactor-fmat (a n)
  (cofactor-fmat-aux 0 a n))

(defthm fmatp-cofactor-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (cofactor-fmat a n) n n)))

(defthmd nth-cofactor-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (nth i (cofactor-fmat a n))
	          (cofactor-fmat-row i a n))))

(defthmd cofactor-fmat-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-fmat a n))
	          (fdet-cofactor i j a n))))

;; The classsical adjoint of a is the transpose of its cofactor matrix:

(defund adjoint-fmat (a n)
  (transpose-mat (cofactor-fmat a n)))

(defthm fmatp-adjoint
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (adjoint-fmat a n) n n)))

(defthmd adjoint-fmat-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (adjoint-fmat a n))
	          (fdet-cofactor j i a n))))

;; By cofactor-fmat-entry and fdet-cofactor-transpose,

;;    (entry i j (cofactor-fmat (transpose-mat a) n))
;;      = (fdet-cofactor i j (transpose-mat a) n)
;;      = (fdet-cofactor j i a n))
;;      = (entry j i (cofactor-fmat a n))
;;      = (entry i j (transpose-mat (cofactor-fmat a n)))
;;      = (entry i j (adjoint-fmat a n))

(defthmd cofactor-fmat--entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-fmat (transpose-mat a) n))
                  (entry i j (adjoint-fmat a n)))))

;; Therefore,

(defthmd cofactor-fmat-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (equal (cofactor-fmat (transpose-mat a) n)
	          (adjoint-fmat a n))))

;; Note that the the dot product of (row i a) and (cofactor-fmat-row i a n) is a rearrangemnt of
;; the sum (expand-fdet-row a i n):

(defthmd fdot-cofactor-fmat-row-expand-fdet-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (fdot (row i a) (cofactor-fmat-row i a n))
                  (expand-fdet-row a i n))))

;; Combining this with expand-fdet-row-fdet, we have the following expression for the determinant:

(defthmd fdot-cofactor-fmat-row-fdet
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (fdot (row i a) (cofactor-fmat-row i a n))
                  (fdet a n))))

;; Next we substitute (replace-row a i (row k a)) for a in fdot-cofactor-fmat-row-fdet, where k <> i.
;; Since this matrix has 2 identical rows, its determinant is (f0) by fdet-alternating, and we have

(defthmd fdot-cofactor-fmat-row-fdet-0
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n) (not (= k i)))
           (equal (fdot (row k a) (cofactor-fmat-row i a n))
                  (f0))))

;; Thus, we have the following for general k:

(defthmd fdot-cofactor-fmat-row-fdelta
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n))
           (equal (fdot (row k a) (cofactor-fmat-row i a n))
                  (f* (fdelta i k) (fdet a n)))))

;; This yields an expression for the nxn matrix product of a and its adjoint:

(defthmd fmatp-fmat*-adjoint
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (fmat* a (adjoint-fmat a n)) n n)))

(defthmd fmat*-adjoint-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (fmat* a (adjoint-fmat a n)))
	          (f* (fdelta i j) (fdet a n)))))

(defthm fmatp-fmat-scalar-mul-fdet-id-mat
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (fmat-scalar-mul (fdet a n) (id-fmat n)) n n)))

(defthmd fmat-scalar-mul-fdet-id-mat-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (fmat-scalar-mul (fdet a n) (id-fmat n)))
	          (f* (fdelta i j) (fdet a n)))))

(defthmd fmat*-adjoint-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (equal (fmat* a (adjoint-fmat a n))
	          (fmat-scalar-mul (fdet a n) (id-fmat n)))))
