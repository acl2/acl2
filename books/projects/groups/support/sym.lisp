(in-package "DM")

(include-book "perms")
(include-book "maps")
(local (include-book "rtl/rel11/lib/top" :dir :system))

;; The list of members of the symmetric group:

(defund slist (n)
  (perms (ninit n)))

;; Some consequences of the results of perms.lisp 

(defthm len-ninit
  (implies (natp n)
           (equal (len (ninit n)) n)))

(defthm len-slist
  (implies (posp n)
           (equal (len (slist n))
	          (fact n)))
  :hints (("Goal" :in-theory (enable slist)
                  :use ((:instance len-perms (l (ninit n)))))))

(defthm car-slist
  (implies (posp n)
           (equal (car (slist n))
	          (ninit n)))
  :hints (("Goal" :in-theory (enable slist))))

(defthm consp-slist
  (implies (posp n)
           (consp (slist n)))
  :hints (("Goal" :use (car-slist))))

(defthmd permp-slist
  (implies (posp n)
           (iff (member-equal x (slist n))
                (permp x (ninit n))))
  :hints (("Goal" :in-theory (enable slist))))

(defthm dlistp-perm
  (implies (and (posp n) (member-equal x (slist n)))
           (dlistp x))
  :hints (("Goal" :in-theory (enable permp-slist permp))))

(defthm slist-non-nil
  (implies (posp n)
           (not (member-equal () (slist n))))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance permp-slist (x ()))))))

(defthm len-perm
  (implies (and (posp n) (member-equal x (slist n)))
           (equal (len x) n))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-slist (:instance sublistp-equal-len (l x) (m (ninit n)))))))

(defthmd member-perm
  (implies (and (posp n) (member-equal x (slist n)))
           (iff (member-equal k x)
	        (and (natp k) (< k n))))
  :hints (("Goal" :in-theory (enable permp permp-slist)
                  :use ((:instance member-ninit (x k))))))

(defthmd nth-perm-ninit
  (implies (and (posp n) (member-equal x (slist n)) (natp k) (< k n))
           (and (natp (nth k x)) (< (nth k x) n)))
  :hints (("Goal" :use ((:instance member-perm (k (nth k x)))
                        (:instance member-nth (n k) (l (x)))))))

(defthm dlistp-slist
  (implies (posp n)
           (dlistp (slist n)))
  :hints (("Goal" :in-theory (enable slist))))

(defthm member-perm-slist
  (implies (and (posp n)
                (dlistp x)
                (sublistp x (ninit n))
		(= (len x) n))
	   (member-equal x (slist n)))
  :hints (("Goal" :in-theory (enable slist)
                  :use (permp-slist (:instance permp-eq-len (l x) (m (ninit n)))))))

;; A permutation cannot have the same element at 2 distinct indices:

(defthmd nth-perm-distinct
  (implies (and (posp n) (member x (slist n)) (natp i) (natp j) (< i n) (< j n) (not (= i j)))
           (not (equal (nth i x) (nth j x))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-slist (:instance nth-dlist-distinct (l x))))))

                        
;;--------------------------------------------------------------------------------------------------------------------

;; Composition of permutations (the operation of the symmetric group):		

(defun comp-perm-aux (x y l)
  (if (consp l)
      (cons (nth (nth (car l) y) x)
            (comp-perm-aux x y (cdr l)))
    ()))

(defund comp-perm (x y n)
  (comp-perm-aux x y (ninit n)))

(defthm nth-comp-perm-aux
  (implies (and (natp k) (< k (len l)))
           (equal (nth k (comp-perm-aux x y l))
	          (nth (nth (nth k l) y) x))))

(defthm nth-ninit
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (ninit n))
	          k))
  :hints (("Goal" :in-theory (enable ninit))))

(defthm nth-comp-perm
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (comp-perm x y n))
	          (nth (nth k y) x)))
  :hints (("Goal" :in-theory (enable comp-perm))))

;;; Product of a list of permutations:

(defun comp-perm-list (l n)
  (if (consp l)
      (comp-perm (car l) (comp-perm-list (cdr l) n) n)
    (ninit n)))

;--------------------------------------------------------------------------------------------------------------------

;; To prove the closure property, we apply member-perm-slist:

(defthm len-comp-perm-aux
  (equal (len (comp-perm-aux x y l))
         (len l)))

(defthm len-comp-perm
  (implies (posp n)
           (equal (len (comp-perm x y n))
                  n))
  :hints (("Goal" :in-theory (enable comp-perm))))

(defthmd nth-comp-perm-ninit
  (implies (and (posp n)
                (member-equal x (slist n))
		(member-equal y (slist n))
                (natp k)
		(< k n))
           (member-equal (nth k (comp-perm x y n))
	                 (ninit n)))
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use ((:instance member-perm (x y))
                        (:instance member-perm (x y) (k (nth k y)))
			(:instance member-perm (k (nth (nth k y) x)))))))

(defthmd sublist-comp-perm-ninit
  (implies (and (posp n)
                (member-equal x (slist n))
		(member-equal y (slist n)))
           (sublistp (comp-perm x y n)
	             (ninit n)))
  :hints (("Goal" :use ((:instance nth-comp-perm-ninit (k (scex2 (comp-perm x y n) (ninit n))))
                        (:instance scex2-lemma (l (comp-perm x y n)) (m (ninit n)))))))

(defthmd nth-comp-perm-distinct
  (implies (and (posp n) (natp i) (natp j) (< i j) (< j n)
                (member-equal x (slist n))
		(member-equal y (slist n)))
           (not (equal (nth i (comp-perm x y n)) (nth j (comp-perm x y n)))))
  :hints (("Goal" :use ((:instance nth-perm-distinct (x y))
                        (:instance nth-perm-distinct (i (nth i y)) (j (nth j y)))
			(:instance member-perm (x y) (k (nth i y)))
			(:instance member-perm (x y) (k (nth j y)))))))

(defthmd dlistp-comp-perm
  (implies (and (posp n)
                (member-equal x (slist n))
		(member-equal y (slist n)))
           (dlistp (comp-perm x y n)))
  :hints (("Goal" :use ((:instance nth-comp-perm-distinct (i (dcex1 (comp-perm x y n))) (j (dcex2 (comp-perm x y n))))
                        (:instance dcex-lemma (l (comp-perm x y n)))))))

(defthm sym-closed
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n)))
           (member-equal (comp-perm x y n) (slist n)))
  :hints (("Goal" :use (len-comp-perm sublist-comp-perm-ninit dlistp-comp-perm
                        (:instance member-perm-slist (x (comp-perm x y n)))))))

;;--------------------------------------------------------------------------------------------------------------------

;; (ninit n) is the left identity:

(defthmd nth-comp-perm-ninit-x
  (implies (and (posp n) (natp k) (< k n) (member x (slist n)))
           (equal (nth k (comp-perm (ninit n) x n))
	          (nth k x)))
  :hints (("Goal" :use ((:instance member-perm (k (nth k x)))))))

(defthmd nth-diff-perm
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (not (equal x y)))
           (let ((k (nth-diff x y)))
             (and (natp k)
                  (< k n)
                  (not (= (nth k x) (nth k y))))))
 :hints (("goal" :use (nth-diff-diff))))

(defthm sym-identity
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (equal (comp-perm (ninit n) x n)
	          x))
  :hints (("Goal" :use ((:instance nth-comp-perm-ninit-x (k (nth-diff x (comp-perm (ninit n) x n))))
                        (:instance nth-diff-perm (y (comp-perm (ninit n) x n)))))))

;;--------------------------------------------------------------------------------------------------------------------

;; Associativity:

(defthmd nth-comp-perm-comp-perm
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (member-equal z (slist n))
		(natp k) (< k n))
	   (equal (nth k (comp-perm x (comp-perm y z n) n))
	          (nth k (comp-perm (comp-perm x y n) z n))))		  
  :hints (("Goal" :use ((:instance member-perm (x z) (k (nth k z)))))))

(defthm sym-assoc
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (member-equal z (slist n)))
	   (equal (comp-perm x (comp-perm y z n) n)
	          (comp-perm (comp-perm x y n) z n)))
  :hints (("Goal" :use ((:instance nth-comp-perm-comp-perm
                         (k (nth-diff (comp-perm x (comp-perm y z n) n) (comp-perm (comp-perm x y n) z n))))
			(:instance nth-diff-perm (x (comp-perm x (comp-perm y z n) n))
			                         (y (comp-perm (comp-perm x y n) z n)))))))

;;--------------------------------------------------------------------------------------------------------------------

;; The inverse operator:

(defun inv-perm-aux (x l)
  (if (consp l)
      (cons (index (car l) x)
            (inv-perm-aux x (cdr l)))
    ()))

(defund inv-perm (x n)
  (inv-perm-aux x (ninit n)))

(defthm nth-inv-perm-aux
  (implies (and (natp k) (< k (len l)))
           (equal (nth k (inv-perm-aux x l))
	          (index (nth k l) x))))

(defthm nth-inv-perm
  (implies (and (posp n) (natp k) (< k n))
           (equal (nth k (inv-perm x n))
	          (index k x)))
  :hints (("Goal" :in-theory (enable inv-perm))))

(defthm len-inv-perm-aux
  (equal (len (inv-perm-aux x l))
         (len l)))

(defthm len-inv-perm
  (implies (posp n)
           (equal (len (inv-perm x n))
                  n))
  :hints (("Goal" :in-theory (enable inv-perm))))

(defthmd nth-inv-perm-ninit
  (implies (and (posp n)
                (member-equal x (slist n))
                (natp k)
		(< k n))
           (member-equal (nth k (inv-perm x n))
	                 (ninit n)))
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use (member-perm (:instance ind<len (x k) (l x))))))

(defthmd sublist-inv-perm-ninit
  (implies (and (posp n)
                (member-equal x (slist n)))
           (sublistp (inv-perm x n)
	             (ninit n)))
  :hints (("Goal" :use ((:instance nth-inv-perm-ninit (k (scex2 (inv-perm x n) (ninit n))))
                        (:instance scex2-lemma (l (inv-perm x n)) (m (ninit n)))))))

(defthmd nth-inv-perm-distinct
  (implies (and (posp n) (natp i) (natp j) (< i j) (< j n)
                (member-equal x (slist n)))
           (not (equal (nth i (inv-perm x n)) (nth j (inv-perm x n)))))	   
  :hints (("Goal" :in-theory (disable nth-ind)
                  :use ((:instance member-perm (k i))
			(:instance member-perm (k j))
			(:instance nth-ind (x i) (l x))
			(:instance nth-ind (x j) (l x))))))

(defthmd dlistp-inv-perm
  (implies (and (posp n)
                (member-equal x (slist n)))
           (dlistp (inv-perm x n)))
  :hints (("Goal" :use ((:instance nth-inv-perm-distinct (i (dcex1 (inv-perm x n))) (j (dcex2 (inv-perm x n))))
                        (:instance dcex-lemma (l (inv-perm x n)))))))

(defthm permp-inv-perm
  (implies (and (posp n)
                (member-equal x (slist n)))
           (member-equal (inv-perm x n) (slist n)))
  :hints (("Goal" :use (len-inv-perm sublist-inv-perm-ninit dlistp-inv-perm
                        (:instance member-perm-slist (x (inv-perm x n)))))))

(defthm nth-comp-perm-inv-perm
  (implies (and (posp n)
                (member-equal x (slist n))
		(natp k) (< k n))
           (equal (nth k (comp-perm (inv-perm x n) x n))
	          k))		  
  :hints (("Goal" :use ((:instance member-perm (k (nth k x)))))))

(defthm comp-perm-inv-perm
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (equal (comp-perm (inv-perm x n) x n) (ninit n)))
  :hints (("Goal" :use ((:instance nth-diff-perm (x (comp-perm (inv-perm x n) x n)) (y (ninit n)))
                        (:instance nth-comp-perm-inv-perm (k (nth-diff (comp-perm (inv-perm x n) x n) (ninit n))))))))

(defthm sym-inverse
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (and (member-equal (inv-perm x n) (slist n))
	        (equal (comp-perm (inv-perm x n) x n) (ninit n)))))

;;--------------------------------------------------------------------------------------------------------------------

;; We have proved all the prerequisites of defgroup:

(defund slist (n)
  (perms (ninit n)))

(defthm car-slist
  (implies (posp n)
           (equal (car (slist n))
	          (ninit n))))

(defthm consp-slist
  (implies (posp n)
           (consp (slist n))))

(defthm slist-non-nil
  (implies (posp n)
           (not (member-equal () (slist n)))))

(defthm dlistp-slist
  (implies (posp n)
           (dlistp (slist n))))

(defun comp-perm-aux (x y l)
  (if (consp l)
      (cons (nth (nth (car l) y) x)
            (comp-perm-aux x y (cdr l)))
    ()))

(defund comp-perm (x y n)
  (comp-perm-aux x y (ninit n)))

(defthm sym-closed
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n)))
           (member-equal (comp-perm x y n) (slist n))))

(defthm sym-identity
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (equal (comp-perm (ninit n) x n)
	          x)))

(defthm sym-assoc
  (implies (and (posp n)
                (member-equal x (slist n))
                (member-equal y (slist n))
                (member-equal z (slist n)))
	   (equal (comp-perm x (comp-perm y z n) n)
	          (comp-perm (comp-perm x y n) z n))))

(defun inv-perm-aux (x l)
  (if (consp l)
      (cons (index (car l) x)
            (inv-perm-aux x (cdr l)))
    ()))

(defund inv-perm (x n)
  (inv-perm-aux x (ninit n)))

(defthm sym-inverse
  (implies (and (posp n)
                (member-equal x (slist n)))
	   (and (member-equal (inv-perm x n) (slist n))
	        (equal (comp-perm (inv-perm x n) x n) (ninit n)))))

(defgroup sym (n)
  (posp n)
  (slist n)
  (comp-perm x y n)
  (inv-perm x n))

(defthmd order-sym
  (implies (posp n)
	   (equal (order (sym n))
		  (fact n))))

;; These rules got me into big trouble:
(in-theory (disable len-perm dlistp-perm))
