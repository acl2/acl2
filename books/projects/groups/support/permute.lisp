(in-package "DM")

(include-book "projects/numbers/euclid" :dir :system)
(include-book "sym")

(defun permute (l p)
  (if (consp p)
      (cons (nth (car p) l)
            (permute l (cdr p)))
    ()))

(local-defthmd nth-permute-1
  (implies (and (dlistp p)
                (sublistp p (ninit (len l)))
		(natp k)
		(< k (len p)))
	   (equal (nth k (permute l p))
	          (nth (nth k p) l))))

(defthm nth-permute
  (implies (and (consp l)
                (in p (sym (len l)))
		(natp k)
		(< k (len l)))
	   (equal (nth k (permute l p))
	          (nth (nth k p) l)))
  :hints (("Goal" :in-theory (enable len-perm permp)
                  :use (nth-permute-1
                        (:instance permp-slist (n (len l)) (x p))))))

(local-defthmd len-permute-1
  (equal (len (permute l p))
         (len p)))

(local-defthm consp-len-pos
  (implies (consp l)
           (> (len l) 0))
  :rule-classes (:linear))

(local-defthm len-permute
  (implies (and (consp l)
                (in p (sym (len l))))
	   (equal (len (permute l p))
	          (len l)))
  :hints (("Goal" :use (len-permute-1 (:instance len-perm (n (len l)) (x p))))))

(local-defthmd sublistp-permute-1
  (implies (and (consp l)
                (sublistp p (ninit (len l))))
	   (sublistp (permute l p) l))
  :hints (("Subgoal *1/2" :use ((:instance member-ninit (x (car p)) (n (len l)))))
          ("Subgoal *1/1" :use ((:instance member-ninit (x (car p)) (n (len l)))))))

(local-defthm sublistp-permute
  (implies (and (consp l)
                (in p (sym (len l))))
	   (sublistp (permute l p) l))
  :hints (("Goal" :in-theory (enable permp)
                  :use (sublistp-permute-1
                        (:instance permp-slist (x p) (n (len l)))))))

(local-defthmd dlistp-permute-1
  (implies (and (consp l)
                (dlistp l)
                (dlistp p)
                (sublistp p (ninit (len l)))
		(natp k)
		(< k (len l))
		(not (member k p)))
	   (not (member (nth k l) (permute l p))))
  :hints (("Subgoal *1/4" :use ((:instance member-ninit (x (car p)) (n (len l)))
                                (:instance nth-dlist-distinct (i k) (j (car p)))))))

(local-defthmd dlistp-permute-2
  (implies (and (consp l)
                (dlistp l)
                (dlistp p)
                (sublistp p (ninit (len l))))
	   (dlistp (permute l p) ))
  :hints (("Subgoal *1/3" :use ((:instance member-ninit (x (car p)) (n (len l)))
                                (:instance  dlistp-permute-1 (k (car p)) (p (cdr p)))))))

(local-defthmd dlistp-permute
  (implies (and (consp l)
                (dlistp l)
                (in p (sym (len l))))
	   (dlistp (permute l p) ))
  :hints (("Goal" :in-theory (enable permp)
                  :use (dlistp-permute-2
                        (:instance permp-slist (n (len l)) (x p))))))

(defthm permp-permute
  (implies (and (dlistp l)
                (consp l)
                (in p (sym (len l))))
	   (permp (permute l p) l))
  :hints (("Goal" :use (dlistp-permute (:instance permp-eq-len (l (permute l p)) (m l))))))

(defun find-perm (l m)
  (if (consp m)
      (cons (index (car m) l)
            (find-perm l (cdr m)))
    ()))

(local-defthm len-find-perm
  (equal (len (find-perm l m))
         (len m)))

(local-defthm sublistp-find-perm
  (implies (and (dlistp m)
                (consp l)
                (sublistp m l))
	   (sublistp (find-perm l m) (ninit (len l))))
  :hints (("Subgoal *1/3" :use ((:instance member-ninit (x (index (car m) l)) (n (len l)))))))

(local-defthmd dlistp-find-perm-1
  (implies (and (dlistp m)
                (consp l)
                (sublistp m l)
		(member-equal x l)
		(not (member-equal x m)))
	   (not (member-equal (index x l) (find-perm l m))))
  :hints (("Subgoal *1/6" :use ((:instance index-1-to-1 (y (car m)))))))

(local-defthm dlistp-find-perm
  (implies (and (dlistp m)
                (consp l)
                (sublistp m l))
	   (dlistp (find-perm l m)))	   
  :hints (("Subgoal *1/3" :use ((:instance dlistp-find-perm-1 (x (car m)) (m (cdr m)))))))

(local-defthm permp-find-perm-1
  (implies (and (consp l)
                (permp l m))
	   (permp (find-perm l m) (ninit (len l))))	   
  :hints (("Goal" :in-theory (enable permp)
                  :use (eq-len-permp (:instance permp-eq-len (l (find-perm l m)) (m (ninit (len l))))))))

(defthm permp-find-perm
  (implies (and (consp l)
                (permp l m))
	   (in (find-perm l m) (sym (len l))))
  :hints (("Goal" :use (permp-find-perm-1
		        (:instance permp-slist (x (find-perm l m)) (n (len l)))))))

(local-defthmd nth-find-perm
  (implies (and (natp k) (< k (len m)))
           (equal (nth k (find-perm l m))
	          (index (nth k m) l))))

(local-defthm nth-find-perm-1
  (implies (and (natp k) (< k (len l)) (permp l m))
           (equal (nth k (find-perm l m))
	          (index (nth k m) l)))
  :hints (("Goal" :use (eq-len-permp nth-find-perm))))

(local-defthmd permute-find-perm-1
  (implies (and (consp l)
                (permp l m)
		(natp k)
		(< k (len l)))
           (member (nth k m) l))
  :hints (("Goal" :in-theory (e/d (permp) (member-nth))
                  :use (eq-len-permp (:instance member-nth (n k) (l m))))))

(local-defthmd permute-find-perm-2
  (implies (and (consp l)
                (permp l m)
		(natp k)
		(< k (len l)))
	   (equal (nth k (permute l (find-perm l m)))
	          (nth k m)))
  :hints (("Goal" :use (permp-find-perm permute-find-perm-1
                       (:instance nth-permute (p (find-perm l m)))))))

(defthm permute-find-perm
  (implies (and (consp l)
                (permp l m))
	   (equal (permute l (find-perm l m))
	          m))
  :hints (("Goal" :in-theory (enable permp)
                  :use (eq-len-permp
		        (:instance permute-find-perm-2 (k (nth-diff (permute l (find-perm l m)) m)))
                        (:instance nth-diff-diff (x (permute l (find-perm l m))) (y m))))))
			    
(defthm permute-e
  (implies (and (true-listp l) (consp l))
	   (equal (permute l (ninit (len l)))
	          l))		  
  :hints (("Goal" :use ((:instance nth-diff-diff (x l) (y (permute l (ninit (len l)))))))))

(local-defthmd permute-comp-perm-1
  (implies (and (true-listp l)
                (consp l)
		(in y (sym (len l)))
		(in x (sym (len l)))
		(natp k)
		(< k (len l)))
	   (equal (nth k (permute l (comp-perm x y (len l))))
	          (nth k (permute (permute l x) y))))
  :hints (("Goal" :in-theory (e/d (len-perm) (len-permute))
                  :use ((:instance len-permute (p x))
			(:instance nth-permute (p y) (l (permute l x)))
			(:instance nth-permute (k (nth k y)) (p x))
			(:instance nth-permute (p (comp-perm x y (len l))))
			(:instance member-perm (k (nth k y)) (x y) (n (len l)))))))


(defthm permute-comp-perm
  (implies (and (true-listp l)
                (consp l)
		(in x (sym (len l)))
		(in y (sym (len l))))
	   (equal (permute (permute l x) y)
	          (permute l (comp-perm x y (len l)))))
  :hints (("Goal" :in-theory (e/d (len-perm) (len-permute))
                  :use ((:instance nth-diff-diff (x (permute (permute l x) y))
                                                 (y (permute l (comp-perm x y (len l)))))
			(:instance permute-comp-perm-1 (k (nth-diff (permute (permute l x) y) (permute l (comp-perm x y (len l))))))
			(:instance len-permute (p x))
			(:instance len-permute (p y) (l (permute l x)))
			(:instance len-permute (p (comp-perm x y (len l))))))))

(defthm permute-inverse
  (implies (and (true-listp l)
                (consp l)
		(in x (sym (len l))))
	   (equal (permute (permute l (inv x (sym (len l)))) x)
	          l))
  :hints (("Goal" :in-theory (e/d (e) (sym-inv-rewrite sym-inverse group-left-inverse))
	          :use ((:instance group-left-inverse (g (sym (len l))))
		        (:instance car-slist (n (len l)))))))


;;--------------------------------------------------------------------------------------------------------------------

;; (select p l) is the sublist of l constructed by extracting the members of l at indices that are members of p:

(defun select-aux (p l n)
  (if (consp l)
      (if (member-equal n p)
          (cons (car l) (select-aux p (cdr l) (1+ n)))
	(select-aux p (cdr l) (1+ n)))
    ()))

(defund select (p l)
  (select-aux p l 0))

(defthm select-aux-nil
  (equal (select-aux () l n) ()))

(defthm select-nil
  (equal (select () l) ())
  :hints (("Goal" :in-theory (enable select))))

;; If l is a true-list and p includes all indices of l, then (select p l) = l:

(local-defthm select-aux-all
  (implies (and (true-listp l)
                (natp n)
                (sublistp (ninit (+ n (len l))) p))
	   (equal (select-aux p l n)
	          l))
  :hints (("Subgoal *1/10" :use ((:instance member-ninit (x n) (n (+ n (len l))))))))

(defthm select-all
  (implies (and (true-listp l)
                (sublistp (ninit (len l)) p))
	   (equal (select p l) l))
  :hints (("Goal" :in-theory (enable select))))

;; By induction, if p is a dlist and its members are all indices in l, then every x has the 
;; same number of occurrences in (permute l p) as in (select p l):

(local-defthm select-aux-hits
  (implies (and (dlistp p)
		(natp n))
          (equal (hits x (select-aux p l n))
                 (if (and (natp (car p))
		          (>= (car p) n)
		          (< (car p) (+ n (len l)))
                          (equal x (nth (- (car p) n) l)))
	             (1+ (hits x (select-aux (cdr p) l n)))
	           (hits x (select-aux (cdr p) l n)))))
  :hints (("Subgoal *1/2" :use ((:instance hits-cdr (a x) (l (select-aux p l n)))))))

(defthm select-hits
  (implies (and (dlistp p)
                (natp (car p))
		(< (car p) (len l)))
          (equal (hits x (select p l))
                 (if (equal x (nth (car p) l))
	             (1+ (hits x (select (cdr p) l)))
	           (hits x (select (cdr p) l)))))
  :hints (("Goal" :in-theory (enable select))))
		        
(defthm hits-permute
  (implies (and (natp (car p))
                (< (car p) (len l)))
	   (equal (hits x (permute l p))
	          (if (equal x (nth (car p) l))
		      (1+ (hits x (permute l (cdr p))))
		    (hits x (permute l (cdr p))))))
  :hints (("Goal" :use ((:instance hits-cdr (l (permute l p)))))))

(defthmd permutationp-permute-1
  (implies (and (dlistp p)
                (sublistp p (ninit (len l))))
	   (equal (hits x (permute l p))
	          (hits x (select p l))))
  :hints (("Subgoal *1/3" :use ((:instance member-ninit (x (car p)) (n (len l)))))))

;; The desired result follows from hits-diff-perm and hits-diff-diff:

(defthm permutationp-permute
  (implies (and (true-listp l)
                (consp l)
                (in p (sym (len l))))
	   (permutationp l (permute l p)))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance hits-diff-diff (m (permute l p)) (x (hits-cex l (permute l p))))
		        (:instance permp-slist (x p) (n (len l)))
                        (:instance permutationp-permute-1 (x (HITS-CEX L (PERMUTE L P))))))))

;; We shall prove a generalization of the above result.  Let val be an arbitrary unary function:

(encapsulate (((val *) => *))
  (local (defun val (x) x)))

(defun collect-vals (l)
  (if (consp l)
      (cons (val (car l)) (collect-vals (cdr l)))
    ()))

(local-defthm select-aux-hits-val
  (implies (and (dlistp p)
		(natp n))
          (equal (hits x (collect-vals (select-aux p l n)))
                 (if (and (natp (car p))
		          (>= (car p) n)
		          (< (car p) (+ n (len l)))
                          (equal x (val (nth (- (car p) n) l))))
	             (1+ (hits x (collect-vals (select-aux (cdr p) l n))))
	           (hits x (collect-vals (select-aux (cdr p) l n))))))
  :hints (("Subgoal *1/2" :use ((:instance hits-cdr (a x) (l (collect-vals (select-aux p l n))))))))

(local-defthm select-hits-val
  (implies (and (dlistp p)
                (natp (car p))
		(< (car p) (len l)))
          (equal (hits x (collect-vals (select p l)))
                 (if (equal x (val (nth (car p) l)))
	             (1+ (hits x (collect-vals (select (cdr p) l))))
	           (hits x (collect-vals (select (cdr p) l))))))
  :hints (("Goal" :in-theory (enable select))))
		        
(local-defthm hits-permute-val
  (implies (and (natp (car p))
                (< (car p) (len l)))
	   (equal (hits x (collect-vals (permute l p)))
	          (if (equal x (val (nth (car p) l)))
		      (1+ (hits x (collect-vals (permute l (cdr p)))))
		    (hits x (collect-vals (permute l (cdr p)))))))
  :hints (("Goal" :use ((:instance hits-cdr (l (collect-vals (permute l p))))))))

(local-defthmd permutationp-permute-vals-1
  (implies (and (dlistp p)
                (sublistp p (ninit (len l))))
	   (equal (hits x (collect-vals (permute l p)))
	          (hits x (collect-vals (select p l)))))
  :hints (("Subgoal *1/3" :use ((:instance member-ninit (x (car p)) (n (len l)))))))

;; The proof of the following is an adaptation of that of permutationp-permute.
;; We shall apply it in the proof of the Fundamental Theorem of Finite Abelian Groups by functional instantiation:

(defthm permutationp-permute-vals
  (implies (and (true-listp l)
                (consp l)
                (in p (sym (len l))))
	   (permutationp (collect-vals l)
	                 (collect-vals (permute l p))))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance hits-diff-diff (l (collect-vals l))
		                                  (m (collect-vals (permute l p)))
						  (x (hits-cex (collect-vals l) (collect-vals (permute l p)))))
		        (:instance permp-slist (x p) (n (len l)))
                        (:instance permutationp-permute-vals-1 (x (HITS-CEX (collect-vals L) (collect-vals (PERMUTE L P)))))))))


;;--------------------------------------------------------------------------------------------------------------------

;; An encapsulated totally set with recognizer tleq-dom, totally ordered by tleq:

(encapsulate (((tleq-dom *) => *) ((tleq * *) => *))
  (local (defun tleq-dom (x) (natp x)))
  (local (defun tleq (x y) (<= x y)))
  (defthmd tleq-reflexive
    (implies (tleq-dom x) (tleq x x)))
  (defthmd tleq-antisymmetric
    (implies (and (tleq-dom x) (tleq-dom y) (not (= x y)))
             (not (and (tleq x y) (tleq y x)))))
  (defthmd tleq-transitive
    (implies (and (tleq-dom x) (tleq-dom y) (tleq-dom z)
                  (tleq x y) (tleq y z))
	     (tleq x z)))
  (defthmd tleq-total
    (implies (and (tleq-dom x) (tleq-dom y))
             (or (tleq x y) (tleq y x)))))

;; A list of elements of the domain:

(defun tleq-dom-list-p (l)
  (if (consp l)
      (and (tleq-dom (car l)) (tleq-dom-list-p (cdr l)))
    (null l)))

(local-defthm tleq-dom-member
  (implies (and (tleq-dom-list-p l)
                (member-equal x l))
	   (tleq-dom x)))

;; List l is ordered by tleq-:

(defun tleq-orderedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (tleq (car l) (cadr l))
           (tleq-orderedp (cdr l)))
    t))

;; A valid index in l:

(local-defun indp (ind l)
  (and (natp ind) (< ind (len l))))

(local-defthm tleq-dom-nth-ind
  (implies (and (tleq-dom-list-p l)
                (indp ind l))
           (tleq-dom (nth ind l))))

;; A valid list of indices in l:

(local-defun indsp (inds l)
  (if (consp inds)
      (and (indp (car inds) l)
	   (indsp (cdr inds) l))
    t))

(local-defthm tleq-dom-inds
  (implies (and (tleq-dom-list-p l)
                (indsp inds l)
                (member-equal ind inds))
           (tleq-dom (nth ind l))))

;; Given a list of indices into l, find one at which a minimum element occurs:

(defun tleq-min-aux (ind inds l)
  (if (consp inds)
      (tleq-min-aux (if (tleq (nth ind l) (nth (car inds) l))
                      ind
	            (car inds))
		  (cdr inds)
		  l)
    ind))

(defund tleq-min (inds l)
  (tleq-min-aux (car inds) (cdr inds) l))

(local-defthm tleq-min-min-aux
  (implies (and (tleq-dom-list-p l)
                (indp ind l)
		(indsp inds l))
           (let ((min (tleq-min-aux ind inds l)))
	     (and (or (equal min ind) (member-equal min inds))
	          (tleq (nth min l) (nth ind l))
		  (implies (member-equal i inds)
		           (tleq (nth min l) (nth i l))))))
  :hints (("Subgoal *1/2" :use ((:instance tleq-reflexive (x (nth ind l)))))
          ("Subgoal *1/1" :use ((:instance tleq-antisymmetric (x (nth ind l)) (y (nth (car inds) l)))
	                        (:instance tleq-total (x (nth ind l)) (y (nth (car inds) l)))
	                        (:instance tleq-total (x (nth ind l)) (y (nth (car inds) l)))
				(:instance tleq-transitive (x (nth (tleq-MIN-AUX IND (CDR INDS) L) l))
				                         (y (nth ind l))
							 (z (nth (car inds) l)))
	                        (:instance tleq-transitive (x (nth (tleq-min-aux (car inds) (cdr inds) l) l))
				                         (y (nth (car inds) l))
							 (z (nth ind l)))
				(:instance tleq-transitive (x (nth (tleq-min-aux (car inds) (cdr inds) l) l))
				                         (z (nth (car inds) l))
							 (y (nth ind l)))))))

(local-defthmd tleq-min-min
  (implies (and (tleq-dom-list-p l)
                (consp inds)
		(indsp inds l))
           (let ((min (tleq-min inds l)))
	     (and (member-equal min inds)
		  (implies (member-equal i inds)
		           (tleq (nth min l) (nth i l))))))
  :hints (("Goal" :in-theory (enable tleq-min)
                  :use ((:instance tleq-min-min-aux (ind (car inds)))))))

;; Replace n with m in the list inds:

(defun replace (m n inds)
  (if (consp inds)
      (if (equal (car inds) n)
          (cons m (cdr inds))
	(cons (car inds) (replace m n (cdr inds))))
    ()))

(local-defthm len-replace
  (equal (len (replace m n inds))
         (len inds)))

(local-defthm indsp-replace
  (implies (and (indsp inds l)
                (indp m l))
	   (indsp (replace m n inds) l)))

(local-defthmd sublistp-replace
  (sublistp (replace m n inds)
            (cons m inds)))

(local-defthm not-member-replace-1
  (implies (and (not (member-equal x inds))
                (not (equal x m)))
	   (not (member-equal x (replace m n inds)))))

(local-defthm not-member-replace-2
  (implies (and (dlistp inds)
                (not (equal m n)))
	   (not (member-equal n (replace m n inds)))))

(local-defthm dlistp-replace
  (implies (and (dlistp inds)
                (not (member-equal m inds)))
	   (dlistp (replace m n inds))))

;; Construct an ordered permutation of a tleq-dom-list:

(defun tleq-ordering-perm-aux (inds l)
  (declare (xargs :measure (len inds)))
  (if (and (consp inds) (consp (cdr inds)))
      (let ((min (tleq-min inds l)))
        (if (equal min (car inds))
            (cons (car inds) (tleq-ordering-perm-aux (cdr inds) l))
          (cons min (tleq-ordering-perm-aux (replace (car inds) min (cdr inds)) l))))
   inds))

(defund tleq-ordering-perm (l)
  (tleq-ordering-perm-aux (ninit (len l)) l))

(local-defthm sublistp-tleq-ordering-perm-aux
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (tleq-ordering-perm-aux inds l)
	             inds))
  :hints (("Subgoal *1/4" :use (tleq-min-min
                                (:instance sublistp-replace (m (car inds)) (inds (cdr inds)) (n (tleq-min inds l)))
				(:instance sublistp-sublistp (l (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L))
				                             (m (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)))
							     (n inds))))))

(local-defthm dlistp-tleq-ordering-perm-aux
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l)
		(dlistp inds))
           (dlistp (tleq-ordering-perm-aux inds l)))	   
 :hints (("Subgoal *1/6" :use ((:instance member-sublist (x (tleq-min inds l))
                                                 (l (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L))
						 (m (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS))))))))

(local-defthm len-tleq-ordering-perm-aux
  (equal (len (tleq-ordering-perm-aux inds l))
         (len inds)))

(local-defthm indsp-ninit-1
  (implies (and (consp l)
                (sublistp inds (ninit (len l))))
	   (indsp inds l))
  :hints (("Subgoal *1/3" :use ((:instance member-ninit (n (len l)) (x (car inds)))))))

(local-defthm indsp-ninit
  (implies (consp l)
	   (indsp (ninit (len l)) l)))

(local-defthm ninit-indsp
  (implies (and (consp l)
                (indsp inds l))
	   (sublistp inds (ninit (len l))))	   
  :hints (("Subgoal *1/3" :use ((:instance member-ninit (n (len l)) (x (car inds)))))))
                
(local-defthm permp-tleq-ordering-perm
  (implies (and (consp l)
                (tleq-dom-list-p l))
	   (in (tleq-ordering-perm l) (sym (len l))))
  :Hints (("Goal" :in-theory (enable tleq-ordering-perm)
                  :use ((:instance member-perm-slist (x (tleq-ordering-perm l)) (n (len l)))))))

(local-defun nth-inds (inds l)
  (if (consp inds)
      (cons (nth (car inds) l)
            (nth-inds (cdr inds) l))
    ()))

(local-defthm member-nth-inds
  (implies (member-equal ind inds)
           (member-equal (nth ind l) (nth-inds inds l))))

(local-defthmd sublistp-nth-inds
  (implies (sublistp m inds)
           (sublistp (nth-inds m l) (nth-inds inds l))))

(local-defthmd member-nth-inds-nth
  (implies (member x (nth-inds inds l))
           (let ((ind (nth (index x (nth-inds inds l)) inds)))
	     (and (member-equal ind inds)
                  (equal (nth ind l) x)))))

(local-defthm tleq-min-nth-inds
  (implies (and (tleq-dom-list-p l)
                (consp inds)
		(indsp inds l)
		(member-equal x (nth-inds inds l)))
	   (tleq (nth (tleq-min inds l) l) x))
  :hints (("Goal" :use (member-nth-inds-nth (:instance tleq-min-min (i (nth (index x (nth-inds inds l)) inds)))))))

(local-defthm sublistp-permute-aux-1
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L)
                     inds))
  :hints (("Goal" :use ((:instance sublistp-sublistp (l (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L))
                                                     (m (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)))
					             (n inds))
			(:instance sublistp-replace (m (car inds)) (n (tleq-min inds l)) (inds (cdr inds)))))))

(local-defthm sublistp-permute-aux-2
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L)
                     (ninit (len l))))
  :hints (("Goal" :use (sublistp-permute-aux-1
                        (:instance sublistp-sublistp (l (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L))
                                                     (m inds)
					             (n (ninit (len l))))
			(:instance sublistp-replace (m (car inds)) (n (tleq-min inds l)) (inds (cdr inds)))))))

(local-defthm sublistp-permute-aux-3
  (implies (and (consp l)
		(indsp inds l)
		(sublistp r inds))
           (sublistp (permute l r)
                     (nth-inds inds l))))

(local-defthm sublistp-permute-aux-4
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (permute l (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L))
                     (nth-inds inds l)))
  :hints (("Goal" :use (sublistp-permute-aux-1
                        (:instance sublistp-permute-aux-3 (r (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L)))))))

(local-defthm sublistp-permute-aux-5
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l)
		(consp (cdr inds)))
           (member-equal (car (permute l (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L)))
                         (nth-inds inds l)))
  :hints (("Goal" :use (sublistp-permute-aux-4
                        (:instance len-permute-1 (p (tleq-ORDERING-PERM-AUX (REPLACE (CAR INDS) (tleq-MIN INDS L) (CDR INDS)) L)))))))

(local-defthm sublistp-permute-aux-6
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (tleq-ORDERING-PERM-AUX (cdr inds) L)
                     inds))
  :hints (("Goal" :use ((:instance sublistp-sublistp (l (tleq-ORDERING-PERM-AUX (cdr inds) L))
                                                     (m (cdr inds))
					             (n inds))
			(:instance sublistp-replace (m (car inds)) (n (tleq-min inds l)) (inds (cdr inds)))))))

(local-defthm sublistp-permute-aux-7
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (tleq-ORDERING-PERM-AUX (cdr inds) L)
                     (Ninit (len l))))
  :hints (("Goal" :use (sublistp-permute-aux-6
                        (:instance sublistp-sublistp (l (tleq-ORDERING-PERM-AUX (cdr inds) L))
                                                     (m inds)
					             (n (ninit (len l))))
			(:instance sublistp-replace (m (car inds)) (n (tleq-min inds l)) (inds (cdr inds)))))))

(local-defthm sublistp-permute-aux-3
  (implies (and (consp l)
		(indsp inds l)
		(sublistp r inds))
           (sublistp (permute l r)
                     (nth-inds inds l))))

(local-defthmd sublistp-permute-aux-8
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
           (sublistp (permute l (tleq-ORDERING-PERM-AUX (cdr inds) L))
                     (nth-inds inds l)))
  :hints (("Goal" :use (sublistp-permute-aux-6
                        (:instance sublistp-permute-aux-3 (r (tleq-ORDERING-PERM-AUX (cdr inds) L)))))))

(local-defthmd sublistp-permute-aux-9
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l)
		(consp (cdr inds)))
           (member-equal (car (permute l (tleq-ORDERING-PERM-AUX (cdr inds) L)))
                         (nth-inds inds l)))
  :hints (("Goal" :in-theory (disable SUBLISTP-tleq-ORDERING-PERM-AUX SUBLISTP-PERMUTE-AUX-3)
                  :use (sublistp-permute-aux-8
                        (:instance len-permute-1 (p (tleq-ORDERING-PERM-AUX (cdr inds) L)))))))

(local-defthm tleq-ordering-perm-aux-orders
  (implies (and (consp l)
                (tleq-dom-list-p l)
		(indsp inds l))
	   (let ((m (permute l (tleq-ordering-perm-aux inds l))))
	     (and (sublistp m (nth-inds inds l))
                  (tleq-orderedp m))))		  
  :hints (("Subgoal *1/4" :use (sublistp-permute-aux-5))  
          ("Subgoal *1/2" :in-theory (disable tleq-min-nth-inds SUBLISTP-tleq-ORDERING-PERM-AUX SUBLISTP-PERMUTE-AUX-3)
	                  :use (sublistp-permute-aux-9
			        (:instance tleq-min-nth-inds (x (car (permute l (tleq-ORDERING-PERM-AUX (cdr inds) L)))))))))	                  

(defthmd tleq-ordering-perm-orders
  (implies (and (consp l)
                (tleq-dom-list-p l))
           (let ((p (tleq-ordering-perm l)))
	     (and (in p (sym (len l)))
	          (tleq-orderedp (permute l p)))))
  :hints (("Goal" :in-theory (enable tleq-ordering-perm) :use (permp-tleq-ordering-perm))))
