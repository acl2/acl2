(in-package "DM")

(include-book "lists")
(include-book "projects/numbers/euclid" :dir :system)
(local (include-book "rtl/rel11/lib/top" :dir :system))

;; perms constructs a list of all permutations of a dlist:

(defun conses (x l)
  (if (consp l)
      (cons (cons x (car l)) (conses x (cdr l)))
    ()))

(defthm count-remove
  (implies (member-equal x l)
           (< (acl2-count (remove1-equal x l))
	      (acl2-count l)))
  :rule-classes (:linear))
	   

(encapsulate ()

  (local (include-book "ordinals/lexicographic-book" :dir :system))

  (set-well-founded-relation acl2::l<)

  (mutual-recursion

    (defun perms-aux (l m)
      (declare (xargs :measure (list (acl2-count m) (acl2-count l) 0)))
      (if (and (consp l) (member (car l) m))
          (append (conses (car l) (perms (remove1-equal (car l) m)))
                  (perms-aux (cdr l) m))
        ()))

    (defun perms (m)
      (declare (xargs :measure (list (acl2-count m) (acl2-count m) 1)))
      (if (consp m)
          (perms-aux m m)
        (list ())))
  )
)

;; A predicate that recognizes a permutation of a dlist:

(defund permp (l m)
  (and (dlistp l)
       (dlistp m)
       (sublistp l m)
       (sublistp m l)))

(defthmd eq-len-permp
  (implies (permp l m)
	   (equal (len l) (len m)))
  :hints (("Goal" :in-theory (enable permp) :use (sublistp-equal-len))))

;; We shall prove the following properties of perms and permp::

;; (defthm len-perms
;;   (implies (dlistp l)
;; 	   (equal (len (perms l))
;; 		  (fact (len l)))))

;; (defthm permp-perms
;;   (implies (and (dlistp l) (member-equal p (perms l)))
;; 	      (permp p l)))

;; (defthm perms-permp
;;   (implies (and (dlistp l) (permp p l))
;; 	      (member-equal p (perms l))))

;; (defthm dlistp-perms
;;   (implies (dlistp l)
;; 	      (dlistp (perms l))))

;; (defthm car-perms
;;   (implies (and (dlistp l) (consp l))
;;            (equal (car (perms l))
;;                  l)))

;; (defthm permp-eq-len
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m) (equal (len l) (len m)))
;;            (permp l m)))

;;--------------------------------------------------------------------------------------------------------------------

;; (defthm len-perms
;;   (implies (dlistp l)
;; 	   (equal (len (perms l))
;; 		  (fact (len l)))))

;; This will be derived as an instance of the following more general result:

;; (defthm len-perms-aux
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m)) ; this will be the usual hypothesis for (perms-aux l m)
;; 	      (equal (len (perms-aux l m))
;; 		     (* (len l) (fact (1- (len m)))))))

;; The proof of the latter uses an induction scheme based on the recursive structure of perms-aux.  Thus, we need two
;; inductive hypotheses, corresponding to the following variable substituions:
;;   (1) l <- (remove-equal (car l) m), m <- (remove-equal (car l) m)
;;   (2) l <- (cdr l)
;; This scheme is produced by an :induct hint that refers to the function len-perms-induct below.  The admissibility of
;; this function is established with the same trick that we used in the definition of perms-aux:

(encapsulate ()

  (local (include-book "ordinals/lexicographic-book" :dir :system))

  (set-well-founded-relation acl2::l<)

  (defun len-perms-induct (l m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count l))))
    (if (and (consp l) (member (car l) m))
        (list (len-perms-induct (remove1-equal (car l) m) (remove1-equal (car l) m))
              (len-perms-induct (cdr l) m))
      ()))
)

;; Before asking ACL2 to prove the lemma, let's think it through.  According to the definition, (perms-aux l m) is produced
;; by appending 2 lists, and according to the built-in ACL2 rewrite rule len-of-append, its length is the sum of the lengths
;; of those 2 lists.  To compute the length of the first list, we prove the following simple rewrite rule:

(defthm len-conses
  (equal (len (conses x l))
	 (len l)))

;; This reduces

;;   (len (conses (car l) (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))

;; to

;;   (len (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m))).

;; But we have an inductive hypothesis that reduces this to

;;   (* (len (remove1-equal (car l) m)) (fact (1- (len (remove1-equal (car l) m))))).

;; According to the definition of fact, this is just

;;   (fact (len (remove1-equal (car l) m)))

;; and according to len-remove1-equal (in groups.lisp), this is

;;   (fact (1- (len m))).

;; As for the second of the 2 lists, our second inductive hypothesis says that

;;   (len (perms-aux (cdr l) m))

;; is

;;   (* (len (cdr l)) (fact (1- (len m))

;; So when we add the 2 lengths, we get

;;     (plus (fact (1- (len m))) (* (len (cdr l)) (fact (1- (len m)))))
;;   = (* (+ 1 (len (cdr l))) (fact (1- (len m))))
;;   = (* (len l) (fact (1- (len m)))).

;; So it looks like the proof just might go through.  Let's try it:

;; (defthm len-perms-aux
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m))
;; 	      (equal (len (perms-aux l m))
;; 		     (* (len l) (fact (1- (len m))))))
;;   :hints (("Goal" :induct (len-perms-induct l m))))

;; Oops.  The proof output tells me there is a case that didn't work:

;; Subgoal *1/1.2''
;; (IMPLIES (AND (CONSP L)
;;               (MEMBER-EQUAL (CAR L) M)
;;               (EQUAL (+ (FACT (+ -2 (LEN M)))
;;                         (LEN (PERMS-AUX (REMOVE1-EQUAL (CAR L) M)
;;                                         (REMOVE1-EQUAL (CAR L) M))))
;;                      (* (LEN M) (FACT (+ -2 (LEN M)))))
;;               (<= (LEN M) 1)
;;               (EQUAL (LEN (PERMS-AUX (CDR L) M))
;;                      (LEN (CDR L)))
;;               (NOT (MEMBER-EQUAL (CAR L) (CDR L)))
;;               (DLISTP (CDR L))
;;               (DLISTP M)
;;               (SUBLISTP (CDR L) M)
;;               (CONSP (REMOVE1-EQUAL (CAR L) M)))
;;          (EQUAL (LEN (PERMS-AUX (REMOVE1-EQUAL (CAR L) M)
;;                                 (REMOVE1-EQUAL (CAR L) M)))
;;                 1))

;; I don't know where this case came from, but I see that the hypotheses (MEMBER-EQUAL (CAR L) M) and (<= (LEN M) 1) 
;; are inconsistent with the hypothesis (CONSP (REMOVE1-EQUAL (CAR L) M).  In fact, I can prove this as a rewrite rule:

(defthm len-1-remove
  (implies (and (member-equal x l) (<= (len l) 1))
	   (not (consp (remove1-equal x l)))))

(defthm length-append
  (equal (len (append l m))
	 (+ (len l) (len m))))

;; Now the proof goes through:

(defthm len-perms-aux
  (implies (and (dlistp l) (dlistp m) (sublistp l m))
	   (equal (len (perms-aux l m))
		  (* (len l) (fact (1- (len m))))))
  :hints (("Goal" :induct (len-perms-induct l m))))

;; The desired result follows:

(defthm len-perms
  (implies (dlistp l)
	   (equal (len (perms l))
		  (fact (len l)))))

;;--------------------------------------------------------------------------------------------------------------------

;; Next, we prove that every element of (perms l) is a permutation of l:

;; (defthm permp-perms
;;   (implies (and (dlistp l) (member-equal p (perms l)))
;; 	      (permp p l)))

;; (defthm permp-perms-aux
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m) (member-equal p (perms-aux l m)))
;; 	      (permp p m)))

;; Once again, we need an induction scheme that gives us 2 inductive hypotheses corresponding to the 2 lists that are
;; appended in the definition of perms-aux.  The second is the same as in the preceding proof, derived from the simple
;; substitution l <- (cdr l).  The first one is tricky.  Suppose p is a member of the first of the appended lists,

;;   (conses (car l) (perms-aux (remove-equal (car l) m) (remove-equal (car l) m))).

;; This means that (car p) = (car l) and (cdr p) is a member of

;;   (perms-aux (remove-equal (car l) m) (remove-equal (car l) m).

;; To exploit this fact we prove the following rewrite rule:

(defthm conses-car-cdr
  (iff (member-equal p (conses x l))
       (and (consp p)
            (equal (car p) x)
            (member-equal (cdr p) l))))

;; Now suppose we had the following inductive hypothesis:

;;   (permp (cdr p) (remove-equal (car l) m)).

;; Then we could conclude that (permp p m) if we could prove the following:

;; (defthm permp-cons
;;   (implies (and (dlistp m) (consp p) (member (car p) m) (permp (cdr p) (remove1-equal (car p) m)))
;;            (permp p m)))

;; I thought through the proof and decided that I needed 2 more lemmas:

(defthm sublist-remove-sublist
  (implies (sublistp l (remove1-equal x m))
           (sublistp l m)))

(defthm sublist-remove-member
  (implies (and (sublistp (remove1-equal x l) m)
                (member-equal x m))
	   (sublistp l m)))

;; The proof did not go through.  I looked at the proof output and saw that the prover failed to discover sublist-remove-member.
;; I also expected it to apply member-sublist, but it didn't do that either.  So I added 2 explicit :use hints.  Note that I
;; also had to enable the definition of permp:

(defthm permp-cons
  (implies (and (dlistp m) (consp p) (member (car p) m) (permp (cdr p) (remove1-equal (car p) m)))
           (permp p m))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance member-sublist (x (car p)) (l (cdr p)) (m (remove1-equal (car p) m)))
		        (:instance sublist-remove-member (x (car p)) (l m) (m p))))))

;; So now we know what variable substitutions we want:
;;   (1) p <- (cdr p), l <- (remove-equal (car l) m), m <- (remove-equal (car l) m)
;;   (2) l <- (cdr l)
;; Since 3 variables are involved, this scheme is produced by an :induct hint that refers to function of 3 arguments:

(encapsulate ()

  (local (include-book "ordinals/lexicographic-book" :dir :system))

  (set-well-founded-relation acl2::l<)

  (set-irrelevant-formals-ok t)
  
  (defun permp-perms-induct (p l m)    
    (declare (xargs :measure (list (acl2-count m) (acl2-count l))))
    (if (and (consp l) (member (car l) m))
        (list (permp-perms-induct (cdr p) (remove1-equal (car l) m) (remove1-equal (car l) m))
              (permp-perms-induct p (cdr l) m))
      ()))
)

(defthm permp-perms-aux
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (member-equal p (perms-aux l m)))
	   (permp p m))
  :hints (("Goal" :induct (permp-perms-induct p l m))))

(defthm permp-perms
  (implies (and (dlistp l) (member-equal p (perms l)))
           (permp p l)))

;;--------------------------------------------------------------------------------------------------------------------

;; (defthm perms-permp
;;   (implies (and (dlistp l) (permp p l))
;; 	      (member-equal p (perms l))))

;; For the generalization to perms-aux, we need the additional hypothesis (member-equal (car p) l):

;; (defthm perms-aux-permp
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m) (permp p m) (member-equal (car p) l))
;; 	      (member-equal p (perms-aux l m))))

;; We shall use the same induction scheme as for permp-perms-aux.  Once again, the interesting case is
;; (equal (car p) (car l)).  First we eliminate the trivial subcase (null (cdr p)):

(defthmd perms-aux-null-cdr
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (permp p m) (member-equal (car p) l) (null (cdr p)))
           (member-equal p (perms-aux l m)))
  :hints (("Goal" :in-theory (enable permp))))

;; In order to apply the inductive hypothesis in the remaining case, we need (member-equal (cadr p) l)):

(defthmd member-cadr-remove-car
  (implies (and (dlistp m) (permp p m) (cdr p))
           (member-equal (cadr p) (remove1-equal (car p) m)))
  :hints (("Goal" :in-theory (enable permp))))

;; We also need (permp (cdr p) (remove1-equal (car p) m):

(defthm sublist-remove-cdr
  (implies (and (dlistp m) (sublistp m p))
           (sublistp (remove1-equal (car p) m) (cdr p))))

(defthmd permp-cdr-remove
  (implies (and (dlistp m) (permp p m))
           (permp (cdr p) (remove1-equal (car p) m)))
  :hints (("Goal" :in-theory (enable permp))))

;; Finally, we need the converse of conses-car-cdr:

(defthm conses-car-cdr-converse
  (implies (and (consp p) (member-equal (cdr p) l))
           (member-equal p (conses (car p) l))))

;; I found that 3 of the above lemmas must be supplied by :use hints:

(defthm perms-aux-permp
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (permp p m) (member-equal (car p) l))
           (member-equal p (perms-aux l m)))
  :hints (("Goal" :induct (permp-perms-induct p l m))
          ("Subgoal *1/1" :use (perms-aux-null-cdr permp-cdr-remove member-cadr-remove-car))))

;; To derive the final result from the above, we must enable permp to relieve the hypothesis (member-equal (car p) l):

(defthm perms-permp
  (implies (and (dlistp l) (permp p l))
           (member-equal p (perms l)))
  :hints (("Goal" :in-theory (enable permp))))

;;--------------------------------------------------------------------------------------------------------------------

;; (defthm dlistp-perms
;;   (implies (dlistp l)
;;            (dlistp (perms l))))

;; The generalization to perms-aux:

;; (defthm dlistp-perms-aux
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m))
;;            (dlistp (perms-aux l m))))

;; We use the same induction scheme as for len-perms-aux.  Thus, we have 2 inductive hypotheses:

;;   (dlistp (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))

;;   (dlistp (perms-aux (cdr l) m))

;; From these we must derive

;;   (dlistp (append (conses (car l) (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))
;;                   (perms-aux (cdr l) m)))

;; We are appending 2 dlists.  This is a consequence of the following:

(defthm dlistp-conses
  (implies (dlistp l)
           (dlistp (conses x l))))

;; We shall show that the 2 lists are disjoint and apply the lemma dlistp-append in groups.lisp.
;; First we show that the car of every element of the first list is (car l):

(defthmd car-conses
  (implies (member-equal p (conses x l))
           (equal (car p) x)))

;; Next we show that the car of every element of the second list is in (cdr l):

(defthmd car-perms-aux
  (implies (member p (perms-aux l m))
           (member (car p) l))
  :hints (("Goal" :induct (len-perms-induct l m))))

;; It follows that the 2 lists have no common elements:

(defthm permp-aux-no-intersect
  (implies (and (dlistp l)
                (member-equal p (conses (car l) (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))))
           (not (member-equal p (perms-aux (cdr l) m))))
  :hints (("Goal" :use ((:instance car-conses (x (car l))
                                              (l (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m))))
                        (:instance car-perms-aux (l (cdr l)))))))

;; But if 2 lists are not disjoint, then they have a common element.  This is provided by the following witness
;; function:

(defun intersect-witness (l m)
  (if (consp l)
      (if (member (car l) m)
          (car l)
        (intersect-witness (cdr l) m))
    ()))

(defthmd intersect-witness-member
  (implies (not (disjointp l m))
           (and (member-equal (intersect-witness l m) l)
	        (member-equal (intersect-witness l m) m))))

;; Therefore, the 2 lists of interest must be disjoint:

(defthmd permp-aux-disjoint
  (implies (dlistp l)
           (disjointp (conses (car l) (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))
	              (perms-aux (cdr l) m)))
  :hints (("Goal" :use ((:instance permp-aux-no-intersect
                         (p (intersect-witness (conses (car l)
			                               (perms-aux (remove1-equal (car l) m)
						                  (remove1-equal (car l) m)))
					       (perms-aux (cdr l) m))))
			(:instance intersect-witness-member
			 (l (conses (car l) (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m))))
			 (m (perms-aux (cdr l) m)))))))

;; We conclude that the appended list is a dlist:

(defthm dlistp-perms-aux-append
  (implies (and (dlistp l)
                (dlistp (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))
		(dlistp (perms-aux (cdr l) m)))
	   (dlistp (append (conses (car l) (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m)))
                           (perms-aux (cdr l) m))))
  :hints (("Goal" :use (permp-aux-disjoint
                        (:instance dlistp-conses (x (car l))
                                                 (l (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m))))
			(:instance dlistp-append (l (conses (car l)
			                                    (perms-aux (remove1-equal (car l) m) (remove1-equal (car l) m))))
						 (m (perms-aux (cdr l) m)))))))

;; The first attempted proof of the following failed. The only outstanding goal was

;;   (NOT (MEMBER-EQUAL (LIST (CAR L)) (PERMS-AUX (CDR L) M)).

;; I don't know where this came from, but the problem was solved easily enough with a :use hint:

(defthm dlistp-perms-aux
  (implies (and (dlistp l) (dlistp m) (sublistp l m))
           (dlistp (perms-aux l m)))
  :hints (("Goal" :induct (len-perms-induct l m))
          ("Subgoal *1/1" :use ((:instance car-perms-aux (p (list (car l))) (l (cdr l)))))))

(defthm dlistp-perms
  (implies (dlistp l)
           (dlistp (perms l))))

;;--------------------------------------------------------------------------------------------------------------------

;; (defthm car-perms
;;   (implies (and (dlistp l) (consp l))
;;            (equal (car (perms l))
;;                  l)))

(defthm car-perms-aux-l
  (implies (and (dlistp l) (consp l))
           (and (consp (perms-aux l l))
	        (equal (car (perms-aux l l))
	               l)))
  :hints (("Goal" :induct (len l))))

(defthm car-perms
  (implies (and (dlistp l) (consp l))
           (equal (car (perms l))
                  l)))

(in-theory (disable perms))

;;--------------------------------------------------------------------------------------------------------------------

;; (defthm permp-eq-len
;;   (implies (and (dlistp l) (dlistp m) (sublistp l m) (equal (len l) (len m)))
;;            (permp l m)))

(encapsulate ()

  (set-irrelevant-formals-ok t)

  (defun permp-eq-len-induct (l m)
     (if (consp l)
        (permp-eq-len-induct (cdr l) (remove1-equal (car l) m))
      ()))
)

(defthm permp-eq-len
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (equal (len l) (len m)))
                (permp l m))
  :hints (("Goal" :induct (permp-eq-len-induct l m))))


;;--------------------------------------------------------------------------------------------------------------------

;; While trying to prove the Fundamental Theorem of Finite Abelian Groups, I found a need for the following:

(defun permutationp (l m)
  (if (consp l)
      (and (member-equal (car l) m)
           (permutationp (cdr l) (remove1-equal (car l) m)))
    (endp m)))

(defthmd permutationp-member-iff
  (implies (permutationp l m)
	   (iff (member-equal x l) (member-equal x m))))

(defthmd permutationp-eq-len
  (implies (permutationp l m)
	   (equal (len l) (len m))))

(defthmd sublistp-remove1-sublistp
  (implies (and (sublistp (remove1-equal x l) m)
	        (member-equal x m))
	   (sublistp l m))
  :hints (("Goal" :induct (remove1-equal x l))))

(local-defthm permp-remove1
  (implies (and (dlistp l)
                (dlistp m)
                (consp l)
                (member-equal (car l) m))
           (iff (permp (cdr l) (remove1-equal (car l) m))
	        (permp l m)))	        
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance sublistp-sublistp (l (cdr l)) (m (remove1-equal (car l) m)) (n m))
		        (:instance sublistp-remove1-sublistp (x (car l)) (l m) (m l))))))

(defthmd permp-permutationp
  (implies (and (dlistp l) (dlistp m))
           (iff (permutationp l m)
	        (permp l m)))
  :hints (("Subgoal *1/3" :in-theory (enable permp))
          ("Subgoal *1/2" :in-theory (enable permp))))

;; An equivalent formulation of permutationp:

;; The number of occurrences of x in l:

(defun hits (x l)
  (if (consp l)
      (if (equal x (car l))
          (1+ (hits x (cdr l)))
        (hits x (cdr l)))
    0))

(defthm hits-member
  (implies (not (member-equal x l))
	   (equal (hits x l) 0)))

(defthm hits-consp
  (implies (not (consp l))
	   (equal (hits x l) 0)))

;; Search for an x that has different numbers of occurrences in l and m:

(defun hits-diff-aux (test l m)
  (if (consp test)
      (if (equal (hits (car test) l) (hits (car test) m))
          (hits-diff-aux (cdr test) l m)
	(list (car test)))
    ()))

(defund hits-diff (l m)
  (hits-diff-aux (append l m) l m))

(defund hits-cex (l m)
  (car (hits-diff l m)))

(local-defthm hits-diff-aux-diff
  (implies (hits-diff-aux test l m)
           (not (equal (hits (car (hits-diff-aux test l m)) l)
                       (hits (car (hits-diff-aux test l m)) m)))))

(local-defthmd hits-diff-aux-equal
  (implies (and (not (hits-diff-aux test l m))
		(member-equal x test))
	   (equal (hits x l) (hits x m))))

(defthmd hits-diff-diff
  (if (hits-diff l m)
      (not (equal (hits (hits-cex l m) l)
                  (hits (hits-cex l m) m)))
   (equal (hits x l) (hits x m)))
  :hints (("Goal" :in-theory (enable hits-diff hits-cex)
	          :use ((:instance hits-diff-aux-equal (test (append l m)))))))

(defthm hits-cdr
  (implies (consp l)
           (equal (hits a (cdr l))
                  (if (equal a (car l))
	              (1- (hits a l))
	            (hits a l)))))

(defthm hits-remove1
  (equal (hits a (remove1-equal x l))
         (if (and (equal a x) (member-equal x l))
	     (1- (hits a l))
	   (hits a l))))

(defthm hits-diff-perm
  (iff (permutationp l m)
       (not (hits-diff l m)))
  :hints (("Subgoal *1/3" :use ((:instance hits-diff-diff (x (car l)))
				(:instance hits-diff-diff (x (car m)))))
          ("Subgoal *1/2" :use ((:instance hits-diff-diff (x (car l)))
				(:instance hits-diff-diff (x (car m)))))
	  ("Subgoal *1/1.2" :use ((:instance hits-diff-diff (l (cdr l)) (m (remove1 (car l) m)))
			  	  (:instance hits-cdr (a (HITS-cex (CDR L) (REMOVE1-EQUAL (CAR L) M))))
				  (:instance hits-remove1 (a (HITS-cex (CDR L) (REMOVE1-EQUAL (CAR L) M))))
				  (:instance hits-diff-diff (x (HITS-cex (CDR L) (REMOVE1-EQUAL (CAR L) M))))))
	  ("Subgoal *1/1.1" :use (hits-diff-diff
				  (:instance hits-diff-diff (l (cdr l)) (m (remove1 (car l) m)) (x (hits-cex l m)))
			  	  (:instance hits-cdr (a (HITS-cex l m)))
				  (:instance hits-remove1 (a (HITS-cex l m)))))))

(defthmd perm-equal-hits
  (implies (permutationp l m)
           (equal (hits x l) (hits x m)))
  :hints (("Goal" :use (hits-diff-diff hits-diff-perm))))

(defthm permutationp-reflexive
  (permutationp l l)
  :hints (("Goal" :use ((:instance hits-diff-diff (m l))))))

(defthmd permutationp-symmetric
  (implies (permutationp l m)
	   (permutationp m l))
  :hints (("Goal" :use ((:instance hits-diff-diff (x (hits-cex m l)))
			(:instance hits-diff-diff (l m) (m l))))))

(defthmd permutationp-transitive
  (implies (and (permutationp l m)
	        (permutationp m n))
	   (permutationp l n))
  :hints (("Goal" :use ((:instance hits-diff-diff (x (hits-cex l n)))
			(:instance hits-diff-diff (x (hits-cex l n)) (l m) (m n))
			(:instance hits-diff-diff (m n))))))



