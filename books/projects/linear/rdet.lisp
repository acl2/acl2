(in-package "DM")

(include-book "rmat")
(include-book "projects/groups/symmetric" :dir :system)
(local (include-book "support/rdet"))

;; The term contributed by a permutation p in (sym n) to the determinant of an nxn
;;  matrix a is computed as follows:
;;   (1) select an entry from each row of a, the selection from row i being the one
;;       in column (nth i p), i.e., (entry i (nth i p) a);
;;   (2) compute the product of these n entries;
;;   (3) negate the product if p is an odd permutation.

(defun rdet-prod (a p n)
  (if (zp n)
      (r1)
    (r* (rdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(defund rdet-term (a p n)
  (if (even-perm-p p n)
      (rdet-prod a p n)
    (r- (rdet-prod a p n))))

;; The determinant of a is the sum over (slist n) of these signed products:

(defun rdet-sum (a l n)
  (if (consp l)
      (r+ (rdet-term a (car l) n)
	  (rdet-sum a (cdr l) n))
    (r0)))

(defund rdet (a n)
  (rdet-sum a (slist n) n))

;; By pair-listp-perm-pairs and rp-pairs-prod, rdet-prod and rdet-term return ring elements:

(defthm rp-rdet-prod
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(natp k) (<= k n))
           (rp (rdet-prod a p k))))

(defthm rp-rdet-term
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n)))
           (rp (rdet-term a p n))))

(defthm rp-rdet
  (implies (and (rmatp a n n) (posp n))
	   (rp (rdet a n))))


;;-------------------------------------------------------------------------------------------------------
;;   Properties of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; To compute (rdet (id-rmat n) n), note that if p is any permutation other than (ninit n), we can find
;; i < n such that (nth i p) <> i, and hence (entry i (nth i p) (id-rmat n)) = (r0), which implies
;; (rdet-term (id-rmat p n)) = (r0).  On the other hand, (nth i (ninit n)) = i for all i, which implies
;; (rdet-term (id-rmat (ninit n) n)) = (r1).   Thus,

(defthm rdet-id-rmat
  (implies (posp n)
           (equal (rdet (id-rmat n) n)
	          (r1)))
  :hints (("Goal" :in-theory (enable rdet)
                  :use ((:instance rdet-sum-id-rmat (l (slist n)))))))


;; rdet is invariant under transpose-mat.  This follows from the observation that the term contributed
;; to the determinant of the transpose of a by a permutation p is the same as the term contributed to
;; the determinant of a by the inverse of p:
  
(defthmd rdet-term-transpose
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n)))
           (equal (rdet-term (transpose-mat a) p n)
	          (rdet-term a (inv-perm p n) n))))

(defthmd rdet-transpose
  (implies (and (posp n) (rmatp a n n))
           (equal (rdet (transpose-mat a) n)
	          (rdet a n))))


;; rdet is alternating, i.e., if 2 rows of a are equal, then its determinant is (r0).
;; To prove this, suppose rows i and j of a are equal, where i <> j.  Given a permutation p, let
;; p' = (comp-perm p (transpose i j n) n).  Then the factors of (rdet-prod a p' n) are the same as
;; those of (rdet-prod a p n):

(defthmd rdet-prod-comp-perm
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (rdet-prod a (comp-perm p (transpose i j n) n) n)
	          (rdet-prod a p n))))

;; If p is even, then p' is odd, and therefore (rdet-term a p' n) is the negative of (rdet-term a p n):

(defthmd rdet-term-comp-perm
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (r+ (rdet-term a (comp-perm p (transpose i j n) n) n)
	              (rdet-term a p n))
		  (r0))))

;; Consequently, the sum of terms contributed by the odd permutations is the negative of the
;; sum of terms contributed by the even permutations:

(defthmd rdet-alternating
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (equal (rdet a n) (r0))))
		        

;; rdet is n-linear, i.e, linear as a function of each row.  This property is
;; specified in terms of the basic operation of replacing a row of a with a given list.
;; For a given row i and permutation p, the term contributed by p to the determinant of
;; (replace-row a i x) by each permutation is a linear function of x:

(defthm rdet-term-replace-row
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (rdet-term a3 p n)
	            (r+ (r* c (rdet-term a1 p n))
			(rdet-term a2 p n))))))

;; The desired result follows by summing over all permutations:
	          
(defthm rdet-n-linear
  (implies (and (rmatp a n n) (posp n) (natp i) (< i n)
		(rlistnp x n) (rlistnp y n) (rp c))
	   (equal (rdet (replace-row a i (rlist-add (rlist-scalar-mul c x) y)) n)
		  (r+ (r* c (rdet (replace-row a i x) n))
		      (rdet (replace-row a i y) n)))))

;; As a consequence of rdet-n-linear, if a has a zero row, then its deteminant is (r0).
;; To prove this, we instantiate rdet-n-linear with c = (r1) and x = y = (rlistn0 n):

(defthmd rdet-replace-0-1
  (implies (and (rmatp a n n) (posp n) (natp k) (< k n))
           (equal (r+ (rdet (replace-row a k (rlistn0 n)) n)
	              (rdet (replace-row a k (rlistn0 n)) n))
		  (rdet (replace-row a k (rlistn0 n)) n))))

;; It follows that (rdet (replace-row a k (rlistn0 n)) n) = (r0).  But if (row k a) = (rlistn0 n),
;; then (replace-row a k (rlistn0 n)) = a:

(defthmd rdet-row-0
  (implies (and (rmatp a n n) (posp n) (natp k) (< k n) (= (nth k a) (rlistn0 n)))
           (equal (rdet a n)
	          (r0))))


;;-------------------------------------------------------------------------------------------------------
;;   Uniqueness of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; We shall show that for given n, rdet is the unique n-linear alternating function on
;; nxn matrices such that (rdet (id-rmat n) n) = (r1).  To that end, we constrain the
;; function rdetn as follows:

(encapsulate (((n) => *))
  (local (defun n () 2))
  (defthm posp-n
    (posp (n))
    :rule-classes (:type-prescription :rewrite)))

(encapsulate (((rdetn *) => *))
  (local (defun rdetn (a) (rdet a (n))))
  (defthm rp-rdetn
    (implies (rmatp a (n) (n))
             (rp (rdetn a))))
  (defthmd rdetn-n-linear
    (implies (and (rmatp a (n) (n)) (natp i) (< i (n))
		  (rlistnp x (n)) (rlistnp y (n)) (rp c))
	     (equal (rdetn (replace-row a i (rlist-add (rlist-scalar-mul c x) y)))
		    (r+ (r* c (rdetn (replace-row a i x)))
		        (rdetn (replace-row a i y))))))
  (defthmd rdetn-adjacent-equal
    (implies (and (rmatp a (n) (n))
		  (natp i) (< i (1- (n))) (= (row i a) (row (1+ i) a)))
	     (equal (rdetn a) (r0)))
    :hints (("Goal" :use ((:instance rdet-alternating (n (n)) (j (1+ i))))))))

;; Our objective is to prove that (rdetn a) = (r* (rdet a (n)) (rdetn (id-rmat (n)))):

;; (defthmd rdet-unique
;;   (implies (rmatp a (n) (n))
;;            (equal (rdetn a)
;;                   (r* (rdet a (n))
;;                       (rdetn (id-rmat (n)))))))

;; If we also prove that for a given function f, (f a n) satisfies the constraints on (rdetn a),
;; we may conclude by functional instantiation that (f a n) = (r* (rdet a n) (f (id-rmat n))).
;; From this it follows that if f has the additional property (f (id-rmat n)) = (r1), then
;; (f a) = (rdet a (n)).

;; Note that we have replaced the property that rdetn is alternating with the weaker property
;; rdetn-adjacent-equal, which says that the value is (r0) if 2 adjacent rows are equal.  This
;; relaxes the proof obligations for functional instantiation, which will be critical for the
;; proof of correctness of cofactor expansion.  We shall show that this property together with
;; n-linearity implies that the same holds for 2 non-adjacent rows.

;; It follows from rdetn-n-linear and rdetn-adjacent-equal that transposing 2 adjacent rows negates
;; the value of rdetn:

(defthmd rdetn-interchange-adjacent
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (rdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
	          (r- (rdetn a)))))

;; Interchanging adjacent rows may be expressed as a permutation:

(defthmd interchange-adjacent-rmat-permute
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a))
	          (permute a (transpose i (1+ i) (n))))))

(defthmd rdetn-permute-adjacent-transpose
  (implies (and (rmatp a (n) (n))
                (natp i) (< i (1- (n))))
           (equal (rdetn (permute a (transpose i (1+ i) (n))))
                  (r- (rdetn a)))))

;; Note that applying any permutation to the rows of a produces a matrix of the
;; same dimensions:

(defthm rmatp-permute
  (implies (and (rmatp a m n) (posp m) (posp n)
                (in p (sym m)))
	   (rmatp (permute a p) m n)))

;; Next we show that rdetn-permute-adjacent-transpose applies to a transposition of any
;; 2 rows.  First note that for 0 <= i and i - 1 < j < n, (transpose i j (n)) is the
;; result of conjugating (transpose i (1- j) (n)) by (transpose (1- j) j (n)):

(defthmd conj-adjacent-transpose-rmat
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i (1- j)) (< j (n)))
           (equal (comp-perm (comp-perm (transpose (1- j) j (n))
                                        (transpose i (1- j) (n))
			                (n))
		             (transpose (1- j) j (n))
		             (n))
		  (transpose i j (n)))))

;; The claim follows by induction:

(defthmd rdetn-permute-transpose
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i j) (< j (n)))
	   (equal (rdetn (permute a (transpose i j (n))))
                  (r- (rdetn a)))))
       
;; Now suppose (row i a) = (row j a), where 0 <= i < j < (n).  We would like to show that 
;; (rdetn a) = (r0).  If j = i + 1 ,then apply rdetn-adjacent-equal.  Otherwise, let
;; a' = (permute (transpose (1+ i) j (n)) a).  By nth-permute,

;;   (nth i a') = (nth (nth i (transpose (1+ i) j (n))) a) = (nth i a)

;; and

;;   (nth (1+ i) a') = (nth (nth (1+ i) (transpose (1+ i) j (n))) a) = (nth j a) = (nth i a)

;; and by rdetn-adjacent-equal, (rdetn a') = (r0).  By rdetn-transpose-rows,

;;   (rdetn a) = (r- (rdetn a') = (r- (r0)) = (r0).

;; Thus, rdetn is an alternating function:

(defthmd rdetn-alternating
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i (n)) (< j (n)) (not (= i j)) (= (row i a) (row j a)))
	   (equal (rdetn a) (r0))))

;; We shall require a generalization of rdetn-transpose-rows to arbitrary permutations.
;; First note that rdetn-permute-transpose may be restated as follows:

(defthmd rdetn-permute-rows
  (implies (and (rmatp a (n) (n))
                (in p (sym (n))))
	   (equal (rdetn (permute a p))
	          (if (even-perm-p p (n))
		      (rdetn a)
		    (r- (rdetn a))))))

;; Since rdet satisfies the constraints on rdetn, this applies to rdet by functional
;; instantiation:

(defthmd rdet-permute-rows
  (implies (and (rmatp a n n) (posp n)
                (in p (sym n)))
	   (equal (rdet (permute a p) n)
	          (if (even-perm-p p n)
		      (rdet a n)
		    (r- (rdet a n))))))

;; The proof of rdet-unique is based on lists of k-tuples of natural numbers less than (n),
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

(defun runits (x)
  (if (consp x)
      (cons (runit (car x) (n))
            (runits (cdr x)))
    ()))

(defun reval-tuple (x k a)
  (r* (rlist-prod (extract-entries x a))
      (rdetn (append (runits x) (nthcdr k a)))))

(defthm rp-reval-tuple
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n)) (tuplep x k))
           (rp (reval-tuple x k a))))

;; The sum of the values of a list of k-tuples: 

(defun rsum-tuples (l k a)
  (if (consp l)
      (r+ (reval-tuple (car l) k a)
	  (rsum-tuples (cdr l) k a))
    (r0)))

(defthm fp-rsum-tuples
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k))
           (rp (rsum-tuples l k a))))

;; We would like to compute (rsum-tuples (all-tuples k) k a).  The case k = 0 is trivial:

(defthmd reval-tuple-nil
  (implies (rmatp a (n) (n))
           (equal (reval-tuple () 0 a)
	          (rdetn a))))

(defthm rsum-0-tuples
  (implies (rmatp a (n) (n))
           (equal (rsum-tuples (all-tuples 0) 0 a)
	          (rdetn a))))

;; We shall prove, as a consequence of n-linearity of rdetn, that incrementing k does not change the value of the sum.

;; If (rlistnp r (n)), We may think of r as a sum of multiples of unit vectors.  Given a sublist l of (ninit (n)),
;; (rsum-select l n) is the sum of the subset of these multiples corresponding to the members of l:

(defun rsum-select (l r)
  (if (consp l)
      (rlist-add (rlist-scalar-mul (nth (car l) r) (runit (car l) (n)))
                 (rsum-select (cdr l) r))
    (rlistn0 (n))))

(defthm rsum-select-ninit
  (implies (rlistnp r (n))
           (equal (rsum-select (ninit (n)) r)
	          r)))

;; We shall derive a formula for (rsum-tuples (extend-tuple x) (1+ k) a).

;; Let l be a sublist of (ninit (n)).  According to the definitions of rsum-tuples and extend-tuple-aux,

;;   (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (r+ (reval-tuple (append x (list (car l))) (1+ k) a)
;;             (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)),

;; where
  
;;   (reval-tuple (append x (list i)) (1+ k) a)
;;     = (r* (rlist-prod (extract-entries (append x (list i)) a))
;;           (rdetn (append (runits (append x (list i))) (nthcdr (1+ k) a))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (r* (nth i (nth k a))
;;               (rdetn (append (append (runits x) (list (unit i (n)))) (nthcdr (1+ k) a)))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (r* (nth i (nth k a))
;;	         (rdetn (replace-row (append (runits x) (nthcdr k a) k (unit i (n)))))))

;; and

;;   (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
;;     = (reval-tuple x k (replace-row a k (rsum-select (cdr l) (nth k a))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select (cdr l) (nth k a)))))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select (cdr l) (nth k a))))).

;; Thus, by rdetn-n-linear,

;;   (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select l (nth k a)))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select l (nth k a)))))))
;;     = (reval-tuple x k (replace-row a k (rsum-select l (nth k a)))).

;; Substitute (ninit (n)) for l:

;;   (rsum-tuples (extend-tuple x) (1+ k) a)
;;     = (reval-tuple x k (replace-row a k (rsum-select (ninit (n)) (nth k a))))
;;     = (reval-tuple x k (replace-row a k (nth k a)))
;;     = (reval-tuple x k a):

(defthm rsum-tuples-extend-tuple
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (rsum-tuples (extend-tuple x) (1+ k) a)
		  (reval-tuple x k a))))

;; This leads to the recurrence formula

;;    (rsum-tuples (all-tuples k) k a) = (rsum-tuples (all-tuples (1- k)) (1- k) a):

(defthm rsum-tuples-append
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k) (tuple-list-p m k))
           (equal (rsum-tuples (append l m) k a)
	          (r+ (rsum-tuples l k a) (rsum-tuples m k a)))))
                        
(defthmd rsum-tuples-extend-tuples
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
		(tuple-list-p l k))
	   (equal (rsum-tuples (extend-tuples l) (1+ k) a)
	          (rsum-tuples l k a))))

(defthm rsum-tuples-extend-all-tuples
  (implies (and (rmatp a (n) (n))
                (posp k) (<= k (n)))
	   (equal (rsum-tuples (all-tuples k) k a)
	          (rsum-tuples (all-tuples (1- k)) (1- k) a))))

;; By induction, (rsum-tuples (all-tuples (n)) (n) a) = (rdetn a):

(defthmd rsum-tuples-rdetn
  (implies (rmatp a (n) (n))
	   (equal (rsum-tuples (all-tuples (n)) (n) a)
	          (rdetn a))))

;; If x is an (n)-tuple, then (reval-tuple x (n) a) = (rdetn (runits x)).  Since rdetn
;; is alternating, this value is (r0) unless x is a dlist:

(defthm rdetn-runits-0
  (implies (and (tuplep x (n)) (not (dlistp x)))
           (equal (rdetn (runits x))
	          (r0))))

(defthm reval-tuple-r0
  (implies (and (rmatp a (n) (n))
                (tuplep x (n))
		(not (dlistp x)))
	   (equal (reval-tuple x (n) a)
	          (r0))))

;; But (select-dlists (all-tuples (n))) = (slist (n)), and therefore (rsum-tuples (slist (n)) (n) a) = (rdetn a):

(defthmd rsum-tuples-n
  (implies (rmatp a (n) (n))
	   (equal (rsum-tuples (slist (n)) (n) a)
	          (rdetn a))))
			
;; For p in (slist (n)),

;;   (reval-tuple p (n) a) = (r* (rlist-prod (extract-entries p a))
;;                              (rdetn (runits p))),
				
;; where (rlist-prod (extract-entries p a)) = (rdet-prod a p (n)).

;; But

;;   (rdetn (runits p)) = (rdetn (permute (id-rmat (n)) p))
;;                     = (r* (if (even-perm-p p (n)) (r1) (r- (r1)))
;;                           (rdetn (id-rmat (n)))).

(defthmd runits-permute-id-mat
  (implies (member p (slist (n)))
           (equal (runits p)
	          (permute (id-rmat (n)) p))))

(defthmd reval-tuple-rdet-prod
  (implies (and (rmatp a (n) (n))
                (member p (slist (n))))
	   (equal (reval-tuple p (n) a)
	          (r* (rdet-prod a p (n))
		      (rdetn (runits p))))))

(defthmd rdetn-permute-rows
  (implies (and (rmatp a (n) (n))
                (in p (sym (n))))
	   (equal (rdetn (permute a p))
	          (if (even-perm-p p (n))
		      (rdetn a)
		    (r- (rdetn a))))))
		    
;; Thus, we have

(defthmd reval-tuple-perm
  (implies (and (rmatp a (n) (n))
                (member p (slist (n))))
	   (equal (reval-tuple p (n) a)
	          (r* (rdet-term a p (n))
		      (rdetn (id-rmat (n)))))))

;; The desired result follows by summing over (slist (n)):

(defthmd rsum-tuples-slist
  (implies (rmatp a (n) (n))
	   (equal (rsum-tuples (slist (n)) (n) a)
	          (r* (rdet a (n))
		      (rdetn (id-rmat (n)))))))
	          
(defthmd rdet-unique
  (implies (rmatp a (n) (n))
           (equal (rdetn a)
                  (r* (rdet a (n))
                      (rdetn (id-rmat (n)))))))


;;-------------------------------------------------------------------------------------------------------
;;   Multiplicativity of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; As an application of rdet-unique, we shall prove that for nxn matrices a and b,

;;   (rdet (rmat* a b) n) = (r* (rdet a n) (rdet b n).

;; To this end, we shall show that the following is a determinant function of its first
;; argument, i.e., it satisfies the constraints on rdetn:

(defun rdet-rmat* (a b n)
  (rdet (rmat* a b) n))

;; First show that rdet-rmat* is n-linear:

;;   (rdet-rmat* (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) b n)
;;      = (rdet (rmat* (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) b) n)
;;      = (rdet (replace-row (rmat* a b)
;;                           k
;;     		             (rdot-list (rlist-add (rlist-scalar-mul c x) y) (transpose-mat b)))
;;     	        n)
;;      = (rdet (replace-row (rmat* a b)
;;                           k
;;     		             (rlist-add (rlist-scalar-mul c (rdot-list x (transpose-mat b)))
;;     		                        (rdot-list y (transpose-mat b))))
;;              n)
;;      = (r+ (r* c (rdet (replace-row (rmat* a b) k (rdot-list x (transpose-mat b))) n)
;;            (rdet (replace-row (rmat* a b) k (rdot-list y (transpose-mat b))) n)
;;      = (r+ (r* c (rdet (rmat* (replace-row a k x) b) n))
;;            (rdet (rmat* (replace-row a y x) b) n))
;;      = (r+ (r* c (rdet-rmat* (replace-row a k x) b n))
;;            (rdet-rmat* (replace-row a k y) b n))

(defthmd rdet-rmat*-n-linear
  (implies (and (rmatp a n n) (rmatp b n n) (posp n) (natp k) (< k n)
                (rlistnp x n) (rlistnp y n) (rp c))
           (equal (rdet-rmat* (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) b n)
                  (r+ (r* c (rdet-rmat* (replace-row a k x) b n))
                      (rdet-rmat* (replace-row a k y) b n)))))

;; The proof of the alternating property is easier:

(defthm rmat*-row
  (implies (and (natp m) (natp n) (rmatp a m n) (rmatp b n n) (natp k) (< k m))
           (equal (nth k (rmat* a b))
	          (rdot-list (nth k a) (transpose-mat b)))))
		      
(defthmd rdet-rmat*-adjacent-equal
  (implies (and (rmatp a n n) (rmatp b n n) (posp n)
		(natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (rdet-rmat* a b n) (r0))))

;; Now apply functional instantiation:

(defthmd rdet-rmat*-val-n
  (implies (and (rmatp a (n) (n)) (rmatp b (n) (n)))
           (equal (rdet-rmat* a b (n))
	          (r* (rdet a (n))
		      (rdet-rmat* (id-rmat (n)) b (n))))))

(defthmd rdet-multiplicative
  (implies (and (rmatp a n n) (rmatp b n n) (posp n))
           (equal (rdet (rmat* a b) n)
	          (r* (rdet a n) (rdet b n)))))
		  

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

(defthmd rmatp-delete-row
  (implies (and (rmatp a m n) (natp m) (natp k) (< k m))
           (rmatp (delete-row k a) (1- m) n)))

(defthmd rmatp-delete-col
  (implies (and (rmatp a m n) (posp m) (natp n) (> n 1) (natp k) (< k n))
           (rmatp (delete-col k a) m (1- n))))

(defthmd rmatp-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (rmatp (minor i j a) (1- n) (1- n))))

;; We derive an expression for an entry of (minor i j a):

(defthmd entry-rmat-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
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

(defthmd row-rmat-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j a))
	          (delete-nth j (nth (if (< r i) r (1+ r)) a)))))

;; minor commutes with transpose-mat:

(defthmd transpose-minor-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (and (rmatp (transpose-mat (minor i j a)) (1- n) (1- n))
	        (equal (transpose-mat (minor i j a))
	               (minor j i (transpose-mat a))))))

;; Next, we define the cofactor of an entry of a:

(defund rdet-cofactor (i j a n)
  (if (evenp (+ i j))
      (rdet (minor i j a) (1- n))
    (r- (rdet (minor i j a) (1- n)))))

;; Cofactor expansion of the determinant of a by column j:

(defun expand-rdet-col-aux (a i j n)
  (if (zp i)
      (r0)
    (r+ (r* (entry (1- i) j a)
            (rdet-cofactor (1- i) j a n))
	(expand-rdet-col-aux a (1- i) j n))))

(defund expand-rdet-col (a j n)
  (expand-rdet-col-aux a n j n))

;; Cofactor expansion of the determinant of a by row i:

(defun expand-rdet-row-aux (a i j n)
  (if (zp j)
      (r0)
    (r+ (r* (entry i (1- j) a)
            (rdet-cofactor i (1- j) a n))
	(expand-rdet-row-aux a i (1- j) n))))

(defund expand-rdet-row (a i n)
  (expand-rdet-row-aux a i n n))

;; Cofactor expansion by column i is equivalent to expansion of the transpose by row i:

(defthm rdet-cofactor-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (< i n) (natp j) (< j n))
	   (equal (rdet-cofactor j i (transpose-mat a) n)
	          (rdet-cofactor i j a n))))

(defthmd expand-rdet-row-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (< i n))
           (equal (expand-rdet-row (transpose-mat a) i n)
	          (expand-rdet-col a i n))))

;; We shall prove, by functional instantiation of rdet-unique,  that the result of cofactor
;; expansion by a column has the same value as the determinant, and it will follow that the
;; same is true for expansion by a row.  The requires proving analogs of the constraints on
;; rdetn.

(defthm rp-rdet-cofactor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (rp (rdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable rdet-cofactor)
                  :use (rmatp-minor rp-entry))))

(defthm rp-expand-rdet-col
  (implies (and (rmatp a n n) (> n 1) (natp j) (< j n))
           (rp (expand-rdet-col a j n))))

;; The effect on (minor i j a) of replacing a row of a other than row i:

(defthmd minor-replace-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n))
	   (equal (minor i j (replace-row a k x))
	          (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))))

;; Replacing row i of a does not alter (minor i j a):

(defthmd minor-replace-rmat-row-i
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n))
	   (equal (minor i j (replace-row a i x))
	          (minor i j a))))

(defthmd cofactor-replace-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n))
	   (equal (rdet-cofactor i j (replace-row a i x) n)
	          (rdet-cofactor i j a n))))

;; It follows that cofactor expansion by column j is n-linear:

(defthmd expand-rdet-col-n-linear
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k n) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) j n)
		  (r+ (r* c (expand-rdet-col (replace-row a k x) j n))
		      (expand-rdet-col (replace-row a k y) j n)))))

;; Now suppose adjacent rows k and k+1 of a are equal.  Then for any i other than k and k+1, (minor i j a)
;; has 2 adjacent rows,and therefore (rdet-cofactor i j a n) = (r0).  Meanwhile, (minor k j) = (minor (1+ k) j)
;; and (entry k j a) = (entry (1+ k) j a), but k + j and (k + 1) + j have opposite parities, and therefore
;; (rdet-cofactor k j a n) + (rdet-cofactor (1+ k) j a n) = (r0).  Thus, (expand-rdet-col a j n) = r0:

(defthmd expand-rdet-col-adjacent-equal
  (implies (and (rmatp a n n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (expand-rdet-col a j n)
	          (r0))))

;; By functional instantiation of rdet-unique, we have the following:

(defthmd expand-rdet-col-val
  (implies (and (rmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-rdet-col a k n)
	          (r* (rdet a n)
		      (expand-rdet-col (id-rmat n) k n)))))

;; It remains to show that (expand-rdet-col (id-rmat n) k n) = (r1).
;; By row-rmat-minor, we have the following expression for the rth row of (minor i j (id-rmat n)):

(defthmd nth-minor-id-rmat
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j (id-rmat n)))
	          (delete-nth j (runit (if (< r i) r (1+ r)) n)))))

;; The following is a consequence of the definirtions of runit and delete-nth:

(defthmd delete-nth-runit
  (implies (and (posp n) (natp j) (< j n) (natp k) (< k n))
           (equal (delete-nth j (runit k n))
	          (if (< j k)
		      (runit (1- k) (1- n))
		    (if (> j k)
		        (runit k (1- n))
		      (rlistn0 (1- n)))))))

;; Consequently, if i <> j, then we find a zero row of (minor i j (id-rmat n)), which implies that
;; its determinant is (r0):

(defthmd nth-minor-id-rmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (nth (if (< j i) j (1- j)) (minor i j (id-rmat n)))
	          (rlistn0 (1- n)))))

(defthmd rdet-minor-id-rmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (rdet (minor i j (id-rmat n)) (1- n))
	          (r0))))

;; On the other hand, (minor j j (id-rmat n)) = (id-rmat (1- n)):

(defthmd nth-minor-id-rmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n) (natp r) (< r (1- n)))
	   (equal (nth r (minor j j (id-rmat n)))
	          (nth r (id-rmat (1- n))))))

(defthmd minor-id-rmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n))
	   (equal (minor j j (id-rmat n))
	          (id-rmat (1- n)))))

;; Thus, the corresponding cofactor is (r1), as is the cofactor expansion:

(defthmd expand-rdet-col-id-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n))
           (equal (expand-rdet-col (id-rmat n) j n)
	          (r1))))

;; Combine this with expand-rdet-col-val:

(defthmd expand-rdet-col-rdet
  (implies (and (rmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-rdet-col a k n)
	          (rdet a n))))

;; It follows from rdet-transpose, expand-rdet-row-transpose, and transpose-2 that the same holds
;; for row expansion:

(defthmd expand-rdet-row-rdet
  (implies (and (rmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-rdet-row a k n)
	          (rdet a n))))


;; As a consequence of expand-rdet-row-rdet, we have a recursive version of rdet, based on cofactor
;; expansion with respect to row 0:

(mutual-recursion

  (defund rdet-rec-cofactor (j a n)
    (declare (xargs :measure (list (nfix n) 0 0)))
    (if (zp n)
        ()
      (if (evenp j)
          (rdet-rec (minor 0 j a) (1- n))
        (r- (rdet-rec (minor 0 j a) (1- n))))))

  (defun expand-rdet-rec-aux (a j n)
    (declare (xargs :measure (list (nfix n) 1 (nfix j))))
    (if (zp j)
        (r0)
      (r+ (r* (entry 0 (1- j) a)
              (rdet-rec-cofactor (1- j) a n))
	  (expand-rdet-rec-aux a (1- j) n))))

  (defund expand-rdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 2 0)))
    (expand-rdet-rec-aux a n n))

  (defun rdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 3 0)))
    (if (zp n)
        (r0)
      (if (= n 1)
          (entry 0 0 a)
        (expand-rdet-rec a n))))

)

(defthmd rdet-rec-rdet
  (implies (and (rmatp a n n) (posp n))
           (equal (rdet-rec a n)
	          (rdet a n))))


;;---------------------------------------------------------------------------------------------------------
;;    Classical Adjoint
;;---------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we shall define its cofactor matrix (cofactor-rmat a n) to be the nxn
;; matrix with entries

;;    (entry i j (cofactor-rmat a n)) = (rdet-cofactor i j a n).

;; We begin by defining the ith row of the cofactor matrix:

(defun cofactor-rmat-row-aux (i j a n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (> n 1) (natp j) (< j n))
      (cons (rdet-cofactor i j a n)
            (cofactor-rmat-row-aux i (1+ j) a n))
    ()))

(defund cofactor-rmat-row (i a n)
  (cofactor-rmat-row-aux i 0 a n))

(defthm rlistnp-cofactor-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (rlistnp (cofactor-rmat-row i a n) n)))

(defthmd nth-cofactor-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (nth j (cofactor-rmat-row i a n))
	          (rdet-cofactor i j a n))))

(defthm cofactor-rmat-row-replace-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (rlistnp x n))
	   (equal (cofactor-rmat-row i (replace-row a i x) n)
                  (cofactor-rmat-row i a n))))

;; The cofactor matrix may now be defined:

(defun cofactor-rmat-aux (i a n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp n) (natp i) (< i n))
      (cons (cofactor-rmat-row i a n)
            (cofactor-rmat-aux (1+ i) a n))
    ()))

(defund cofactor-rmat (a n)
  (cofactor-rmat-aux 0 a n))

(defthm rmatp-cofactor-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (cofactor-rmat a n) n n)))

(defthmd nth-cofactor-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (nth i (cofactor-rmat a n))
	          (cofactor-rmat-row i a n))))

(defthmd cofactor-rmat-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-rmat a n))
	          (rdet-cofactor i j a n))))

;; The classsical adjoint of a is the transpose of its cofactor matrix:

(defund adjoint-rmat (a n)
  (transpose-mat (cofactor-rmat a n)))

(defthm rmatp-adjoint
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (adjoint-rmat a n) n n)))

(defthmd adjoint-rmat-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (adjoint-rmat a n))
	          (rdet-cofactor j i a n))))

;; By cofactor-rmat-entry and rdet-cofactor-transpose,

;;    (entry i j (cofactor-rmat (transpose-mat a) n))
;;      = (rdet-cofactor i j (transpose-mat a) n)
;;      = (rdet-cofactor j i a n))
;;      = (entry j i (cofactor-fmat a n))
;;      = (entry i j (transpose-mat (cofactor-rmat a n)))
;;      = (entry i j (adjoint-rmat a n))

(defthmd cofactor-rmat--entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-rmat (transpose-mat a) n))
                  (entry i j (adjoint-rmat a n)))))

;; Therefore,

(defthmd cofactor-rmat-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (equal (cofactor-rmat (transpose-mat a) n)
	          (adjoint-rmat a n))))

;; Note that the the dot product of (row i a) and (cofactor-rmat-row i a n) is a rearrangemnt of
;; the sum (expand-rdet-row a i n):

(defthmd rdot-cofactor-rmat-row-expand-rdet-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (rdot (row i a) (cofactor-rmat-row i a n))
                  (expand-rdet-row a i n))))

;; Combining this with expand-rdet-row-rdet, we have the following expression for the determinant:

(defthmd rdot-cofactor-rmat-row-rdet
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (rdot (row i a) (cofactor-rmat-row i a n))
                  (rdet a n))))

;; Next we substitute (replace-row a i (row k a)) for a in rdot-cofactor-rmat-row-rdet, where k <> i.
;; Since this matrix has 2 identical rows, its determinant is (r0) by rdet-alternating, and we have

(defthmd rdot-cofactor-rmat-row-rdet-0
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n) (not (= k i)))
           (equal (rdot (row k a) (cofactor-rmat-row i a n))
                  (r0))))

;; Thus, we have the following for general k:

(defthmd rdot-cofactor-rmat-row-rdelta
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n))
           (equal (rdot (row k a) (cofactor-rmat-row i a n))
                  (r* (rdelta i k) (rdet a n)))))

;; This yields an expression for the nxn matrix product of a and its adjoint:

(defthmd rmatp-rmat*-adjoint
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (rmat* a (adjoint-rmat a n)) n n)))

(defthmd rmat*-adjoint-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (rmat* a (adjoint-rmat a n)))
	          (r* (rdelta i j) (rdet a n)))))

(defthm rmatp-rmat-scalar-mul-rdet-id-mat
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (rmat-scalar-mul (rdet a n) (id-rmat n)) n n)))

(defthmd rmat-scalar-mul-rdet-id-mat-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (rmat-scalar-mul (rdet a n) (id-rmat n)))
	          (r* (rdelta i j) (rdet a n)))))

(defthmd rmat*-adjoint-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (equal (rmat* a (adjoint-rmat a n))
	          (rmat-scalar-mul (rdet a n) (id-rmat n)))))
