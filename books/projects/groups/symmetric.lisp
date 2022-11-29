;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(include-book "quotients")
(local (include-book "support/alt"))

;;--------------------------------------------------------------------------------------------------------------
;; Permutations
;;--------------------------------------------------------------------------------------------------------------

;; perms constructs a list of all permutations of a dlist:

(defun conses (x l)
  (if (consp l)
      (cons (cons x (car l)) (conses x (cdr l)))
    ()))


(mutual-recursion

  (defun perms-aux (l m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count l) 0)))
    (if (and (consp l) (member (car l) m))
        (append (conses (car l) (perms (remove1-equal (car l) m)))
                (perms-aux (cdr l) m))
      ()))

  (defund perms (m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count m) 1)))
    (if (consp m)
        (perms-aux m m)
      (list ())))
)

(defthmd len-perms
  (implies (dlistp l)
	   (equal (len (perms l))
		  (fact (len l)))))

;; A predicate that recognizes a permutation of a dlist:

(defund permp (l m)
  (and (dlistp l)
       (dlistp m)
       (sublistp l m)
       (sublistp m l)))

(defthmd permp-perms
  (implies (and (dlistp l) (member-equal p (perms l)))
           (permp p l)))

(defthmd perms-permp
  (implies (and (dlistp l) (permp p l))
           (member-equal p (perms l))))

(defthm dlistp-perms
  (implies (dlistp l)
           (dlistp (perms l))))

(defthmd car-perms
  (implies (and (dlistp l) (consp l))
           (equal (car (perms l))
                  l)))

(defthmd permp-eq-len
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (equal (len l) (len m)))
                (permp l m)))


;;--------------------------------------------------------------------------------------------------------------
;; Symmetric Groups
;;--------------------------------------------------------------------------------------------------------------

;; The list of members of the symmetric group:

(defund slist (n)
  (perms (ninit n)))

;; Some properties of (slist n):

(defthmd len-slist
  (implies (posp n)
           (equal (len (slist n))
	          (fact n))))

(defthm car-slist
  (implies (posp n)
           (equal (car (slist n))
	          (ninit n))))

(defthm consp-slist
  (implies (posp n)
           (consp (slist n))))

(defthmd permp-slist
  (implies (posp n)
           (iff (member-equal x (slist n))
                (permp x (ninit n)))))

(defthm dlistp-perm
  (implies (and (posp n) (member-equal x (slist n)))
           (dlistp x)))

(defthm slist-non-nil
  (implies (posp n)
           (not (member-equal () (slist n)))))

(defthmd len-perm
  (implies (and (posp n) (member-equal x (slist n)))
           (equal (len x) n)))

(defthmd member-perm
  (implies (and (posp n) (member-equal x (slist n)))
           (iff (member-equal k x)
	        (and (natp k) (< k n)))))

(defthmd nth-perm-ninit
  (implies (and (posp n) (member-equal x (slist n)) (natp k) (< k n))
           (and (natp (nth k x)) (< (nth k x) n))))

(defthm dlistp-slist
  (implies (posp n)
           (dlistp (slist n))))

(defthmd member-perm-slist
  (implies (and (posp n)
                (dlistp x)
                (sublistp x (ninit n))
		(= (len x) n))
	   (member-equal x (slist n))))

(defthmd nth-diff-perm
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (not (equal x y)))
           (let ((k (nth-diff x y)))
             (and (natp k)
                  (< k n)
                  (not (= (nth k x) (nth k y)))))))

;; A permutation cannot have the same element at 2 distinct indices:

(defthmd nth-perm-distinct
  (implies (and (posp n) (member x (slist n)) (natp i) (natp j) (< i n) (< j n) (not (= i j)))
           (not (equal (nth i x) (nth j x)))))

;; We may think of an element p of (slist n) as a bijection from (ninit n) to itself, under
;; which the image p(k) of an index k is (nth k p).   The operation of the symmetric group is
;; functional composition:

(defun comp-perm-aux (x y l)
  (if (consp l)
      (cons (nth (nth (car l) y) x)
            (comp-perm-aux x y (cdr l)))
    ()))

(defund comp-perm (x y n)
  (comp-perm-aux x y (ninit n)))

(defthm nth-comp-perm
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (comp-perm x y n))
	          (nth (nth k y) x))))

;;; Product of a list of permutations:

(defun comp-perm-list (l n)
  (if (consp l)
      (comp-perm (car l) (comp-perm-list (cdr l) n) n)
    (ninit n)))

;; Closure:

(defthm sym-closed
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n)))
           (member-equal (comp-perm x y n) (slist n))))

;; (ninit n) is the left identity:

(defthm sym-identity
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (equal (comp-perm (ninit n) x n)
	          x)))

;; Associativity:

(defthm sym-assoc
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (member-equal z (slist n)))
	   (equal (comp-perm x (comp-perm y z n) n)
	          (comp-perm (comp-perm x y n) z n))))

;; Inverse operator:

(defun inv-perm-aux (x l)
  (if (consp l)
      (cons (index (car l) x)
            (inv-perm-aux x (cdr l)))
    ()))

(defund inv-perm (x n)
  (inv-perm-aux x (ninit n)))

(defthm nth-inv-perm
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (inv-perm x n))
	          (index k x))))

(defthm sym-inverse
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (and (member-equal (inv-perm x n) (slist n))
	        (equal (comp-perm (inv-perm x n) x n) (ninit n)))))

;; We have proved all of the properties required by defgroup:

(defgroup sym (n)
  (posp n)
  (slist n)
  (comp-perm x y n)
  (inv-perm x n))

(defthmd order-sym
  (implies (posp n)
	   (equal (order (sym n))
		  (fact n))))


;;--------------------------------------------------------------------------------------------------------------
;; Transpositions
;;--------------------------------------------------------------------------------------------------------------

;; A permutation that transposes 2 indices:

(defun transpose-aux (i j l)
  (if (consp l)
      (if (equal (car l) i)
          (cons j (transpose-aux i j (cdr l)))
	(if (equal (car l) j)
            (cons i (transpose-aux i j (cdr l)))
          (cons (car l) (transpose-aux i j (cdr l)))))
    ()))

(defund transpose (i j n)
  (transpose-aux i j (ninit n)))

;; A characterization of suitable arguments of transpose, the purpose of which is to avoid typing the
;; conditions repeatedly:

(defun trans-args-p (i j n)
  (and (posp n) (natp i) (natp j) (< i n) (< j n) (not (= i j))))

(defthmd permp-transpose
  (implies (trans-args-p i j n)
           (in (transpose i j n) (sym n))))

(defthmd transpose-vals
  (implies (and (trans-args-p i j n)
                (natp k) (< k n))
	   (equal (nth k (transpose i j n))
	          (if (= k i) j
		      (if (= k j) i
		          k)))))

(defthmd transpose-transpose
  (implies (trans-args-p i j n)
           (equal (transpose i j n)
	          (transpose j i n))))

(defthmd transpose-involution
  (implies (trans-args-p i j n)
           (equal (comp-perm (transpose i j n) (transpose i j n) n)
	          (ninit n))))

;; The least index that is moved by a permutation:

(defun least-moved-aux (p k)
  (if (and (consp p) (equal (car p) k))
      (least-moved-aux (cdr p) (1+ k))
    k))

(defund least-moved (p)
  (least-moved-aux p 0))

(defthmd least-moved-bounds
  (let ((m (least-moved p)))
    (and (natp m)
         (<= m (len p)))))

(defthmd least-moved-moved
  (let ((m (least-moved p)))
    (implies (< m (len p))
	     (not (equal (nth m p) m)))))

(defthmd least-moved-least
  (implies (and (natp n)
                (< n (least-moved p)))
           (equal (nth n p) n)))

(defthmd least-moved-transpose
  (implies (trans-args-p i j n)
           (equal (least-moved (transpose i j n))
	          (min i j))))

(defthmd least-moved-n-ninit
  (implies (and (posp n)
                (in p (sym n))
		(>= (least-moved p) n))
	   (equal (ninit n) p)))


;; Transposition recognizer:

(defund transp (p n)
  (let ((m (least-moved p)))
    (and (trans-args-p m (nth m p) n)
         (equal p (transpose m (nth m p) n)))))

(defthmd permp-transp
  (implies (and (posp n) (transp p n))
           (in p (sym n))))

(defthmd transp-transpose
  (implies (trans-args-p i j n)
           (transp (transpose i j n) n)))

;; List of transpositions:

(defun trans-list-p (l n)
  (if (consp l)
      (and (transp (car l) n) (trans-list-p (cdr l) n))
    t))

(defthmd permp-trans-list
  (implies (and (posp n) (trans-list-p l n))
           (in (comp-perm-list l n) (sym n))))


;; We shall prove constructively that every permutation is a product of transpositions.
;; The construction uses a measure based on least-moved:

(defthm perm-meas-dec
  (let ((m (least-moved p)))
    (implies (and (posp n)
                  (in p (sym n))
                  (< m n))
               (< (least-moved p)
	          (least-moved (comp-perm (transpose m (nth m p) n) p n))))))

(defun trans-list (p n)
  (declare (xargs :measure (nfix (- n (least-moved p)))))
  (let* ((m (least-moved p))
         (trans (transpose m (nth m p) n))
	 (comp (comp-perm trans p n)))
    (if (and (posp n)
             (in p (sym n))
	     (< m n))
        (cons trans (trans-list comp n))
      ())))

(defthmd trans-list-p-trans-list
  (implies (and (posp n) (in p (sym n)))
           (trans-list-p (trans-list p n) n)))

(defthmd perm-prod-trans
  (implies (and (posp n) (in p (sym n)))
           (equal (comp-perm-list (trans-list p n) n)
	          p)))


;;--------------------------------------------------------------------------------------------------------------
;; Parity
;;--------------------------------------------------------------------------------------------------------------

;; Given naturals 0 <= j <= k < n, compute the list of all pairs (i . k) with 0 <= i < j:

(defun pairs-aux (j k)
  (if (zp j)
      ()
    (cons (cons (1- j) k)
          (pairs-aux (1- j) k))))

;; The list of all pairs (i . j) with 0 <= i < j < n:

(defund pairs (n)
  (if (zp n)
      ()
    (append (pairs-aux (1- n) (1- n))
            (pairs (1- n)))))
            
(defthmd member-pairs
  (implies (natp n)
           (iff (member-equal x (pairs n))
	        (and (consp x)
		     (natp (car x))
		     (natp (cdr x))
		     (< (car x) (cdr x))
		     (< (cdr x) n)))))

(defthm dlistp-pairs
  (implies (natp n)
           (dlistp (pairs n))))

;; Given a permutation p, extract the list of pairs (i . j) with p(i) > p(j): 

(defun invs-aux (p pairs)
  (if (consp pairs)
      (if (> (nth (caar pairs) p) (nth (cdar pairs) p))
          (cons (car pairs) (invs-aux p (cdr pairs)))
	(invs-aux p (cdr pairs)))
    ()))

;; The list of inversions of p:

(defund invs (p n)
  (invs-aux p (pairs n)))

;; The parity of p:

(defund parity (p n)
  (mod (len (invs p n)) 2))

(defthmd parity-0-1
  (member (parity p n) '(0 1)))

(defund even-perm-p (p n)
  (equal (parity p n) 0))

(defund odd-perm-p (p n)
  (equal (parity p n) 1))

;; (ninit n) is an even permutation:

(defthm invs-ninit
  (equal (invs (ninit n) n) ()))

(defthm evenp-ninit
  (even-perm-p (ninit n) n))
  
;; A permutation and its inverse have the same parity:

(defthmd parity-inv
  (implies (and (posp n) (in p (sym n)))
           (equal (parity (inv-perm p n) n)
	          (parity p n))))

;; Parity is a homomorphism from (sym n) into Z/2Z:

(defthmd parity-comp-perm
  (implies (and (posp n)
                (in p (sym n))
	        (in r (sym n)))
	   (equal (parity (comp-perm r p n) n)
	          (mod (+ (parity p n) (parity r n)) 2))))

;; It follows from parity-inv and parity-comp-perm that parity is preserved by conjugation:

(defthmd parity-conjugate
  (implies (and (posp n)
                (in p (sym n))
	        (in a (sym n)))
	   (equal (parity (conj p a (sym n)) n)
		  (parity p n))))

;; A transposition of adjacent elements performs a single inversion and therefore has odd parity:

(defthmd transpose-adjacent-odd
  (implies (trans-args-p i (1+ i) n)
           (equal (parity (transpose i (1+ i) n) n)
	          1)))

;; Every transposition is a conjugate of an adjacent transposition:

(defthmd transpose-conjugate
  (implies (and (trans-args-p i j n) (< (1+ i) j))
           (equal (transpose i j n)
	          (comp-perm (transpose (1+ i) j n)
		             (comp-perm (transpose i (1+ i) n)
			                (transpose (1+ i) j n)
					n)
			     n))))

;; Therefore, all transpositions are odd:

(defthmd transpose-odd
  (implies (trans-args-p i j n)
           (odd-perm-p (transpose i j n) n)))

(defthmd transp-odd
  (implies (transp p n)
           (odd-perm-p p n)))
			
;; It follows that the parity of a product of a list of transpositions is that of the length of the list:

(defthmd parity-trans-list
  (implies (and (posp n) (trans-list-p l n))
           (equal (parity (comp-perm-list l n) n)
	          (mod (len l) 2))))

;; In particular,

(defthmd parity-len-trans-list
  (implies (and (posp n) (in p (sym n)))
           (equal (parity p n)
	          (mod (len (trans-list p n)) 2))))


;;--------------------------------------------------------------------------------------------------------------
;; Determinants
;;--------------------------------------------------------------------------------------------------------------

;; This is just an aside, but some day I hope to formalize basic linear algebra.

;; An mxn matrix is a list of m rows (of rationals, I suppose) of length n.
;; The entry in row i and column j:

(defun entry (i j mat)
  (nth j (nth i mat)))

;; The term contributed by a permutation p to the determinant of an nxn matrix:

(defun det-term-aux (mat p l)
  (if (consp l)
      (* (entry (car l) (nth (car l) p) mat)
	 (det-term-aux mat p (cdr l)))
    1))

(defun det-term (mat p n)
  (* (expt -1 (parity p n))
     (det-term-aux mat p (ninit n))))

;; The determinant of an nxn matrix:

(defun det-aux (mat l n)
  (if (consp l)
      (+ (det-term mat (car l) n)
	 (det-aux mat (cdr l) n))
    0))

(defund det (mat n)
  (det-aux mat (slist n) n))


;;--------------------------------------------------------------------------------------------------------------
;; Alternating Group
;;--------------------------------------------------------------------------------------------------------------

;; The alternating group is the subgroup of the symmetric group comprising the even permutations:

(defun even-perms-aux (l n)
  (if (consp l)
      (if (even-perm-p (car l) n)
          (cons (car l) (even-perms-aux (cdr l) n))
	(even-perms-aux (cdr l) n))
    ()))

(defund even-perms (n)
  (even-perms-aux (slist n) n))

(defthmd even-perms-even
  (implies (posp n) 
           (iff (member-equal p (even-perms n))
	        (and (in p (sym n)) (even-perm-p p n)))))

;; The prerequisites of defsubgroup:

(defthm sublistp-even-perms-slist
  (implies (posp n)
           (sublistp (even-perms n) (slist n))))

(defthm dlistp-even-perms
  (implies (posp n)
           (dlistp (even-perms n))))

(defthm car-even-perms
  (implies (posp n)
           (equal (car (even-perms n))
	          (ninit n))))

(defthm consp-even-perms
  (implies (posp n)
           (consp (even-perms n))))

(defthm even-perms-closed
  (implies (and (posp n)
                (member-equal x (even-perms n))
                (member-equal y (even-perms n)))
           (member-equal (comp-perm x y n) (even-perms n))))

(defthm even-perms-inverse
  (implies (and (posp n)
                (member-equal x (even-perms n)))
	   (member-equal (inv-perm x n) (even-perms n))))

(defsubgroup alt (n) (sym n)
  (posp n)
  (even-perms n))

;; It follows from parity-conjugate that (alt n) is a normal subgroup of (sym n):

(defthmd alt-normal
  (implies (posp n)
           (normalp (alt n) (sym n))))

;; If n > 1, then (sym n) has at least one odd element, e.g., (transpose 0 1 n), and therefore 
;; (alt n) is a proper subgroup.  Since every element of (sym n) is either odd or even, it follows 
;; from parity-comp-perm and parity-inv that for every p in (sym n), either p or 
;; (comp-perm (inv-perm (transpose 0 1 n) n) p n) is in (alt n), and by member-lcoset-iff, p is in
;; either (lcoset (ninit) (alt n) (sym n)) or (lcoset (transpose 0 1 n) (alt n) (sym n)).  Therefore,
;; these are the only elements of (lcosets (alt n) (sym n)):

(defthmd subgroup-index-alt
  (implies (and (natp n) (> n 1))
           (equal (subgroup-index (alt n) (sym n))
	          2)))

;; The order of (alt n) follows from Lagrange's Theorem:

(defthmd order-alt
  (implies (and (natp n) (> n 1))
           (equal (order (alt n))
	          (/ (fact n) 2))))

