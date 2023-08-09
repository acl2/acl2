
(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

;; The electorate is a list p of distinct voters. In an election, each voter casts a ballot
;; for one of two candidates, A and B.  An election is modeled as a sublist e of the
;; electorate consisting of those who vote for candidate A.  The number of votes cast for
;; each candidate in an election e:

(defun a-count (p e)
  (if (consp p)
      (if (member-equal (car p) e)
          (1+ (a-count (cdr p) e))
	(a-count (cdr p) e))
    0))

(defun b-count (p e)
  (- (len p) (a-count p e)))

;; A tally of the votes is a sequential count represented as a permutation of p, i.e., a 
;; member of (perms p).  If A maintains a strict lead throughout a tally, then the tally 
;; is considered to be favorable.  To facilitate the definition of this predicate, a tally 
;; c is understood to list the voters in the reverse of the order in which their votes are 
;; counted, so that (car c) is the voter whose vote is counted last:

(defun favp (c e)
  (if (consp c)
      (if (consp (cdr c))
          (and (favp (cdr c) e)
               (> (a-count c e) (b-count c e)))
	(member-equal (car c) e))
    ()))
	      
;; Given an election e and a list l of possible tallies of e, (fav-tallies l e) is the sublist
;; consisting of all favorable tallies and (num-favs l e) is its length:

(defun fav-tallies (l e)
  (if (consp l)
      (if (favp (car l) e)
	  (cons (car l) (fav-tallies (cdr l) e))
	(fav-tallies (cdr l) e))
    ()))

(defun num-favs (l e)
  (if (consp l)
      (if (favp (car l) e)
	  (1+ (num-favs (cdr l) e))
	(num-favs (cdr l) e))
    0))

;; The favorable tallies of an election with electorate (A B C D E) of which A, C, and E
;; vote for candidate A:

;; DM !>(fav-tallies (perms '(a b c d e)) '(a c e))
;; ((B A D C E)
;;  (B A D E C)
;;  (B C D A E)
;;  (B C D E A)
;;  (B D A C E)
;;  (B D A E C)
;;  (B D C A E)
;;  (B D C E A)
;;  (B D E A C)
;;  (B D E C A)
;;  (B E D A C)
;;  (B E D C A)
;;  (D A B C E)
;;  (D A B E C)
;;  (D B A C E)
;;  (D B A E C)
;;  (D B C A E)
;;  (D B C E A)
;;  (D B E A C)
;;  (D B E C A)
;;  (D C B A E)
;;  (D C B E A)
;;  (D E B A C)
;;  (D E B C A))
 
;; DM !>(num-favs (perms '(a b c d e)) '(a c e))
;; 24

;; The function prob computes the probability that a random tally of an election e is 
;; favorable by counting the favorable tallies and dividing by the total number of tallies:

(defund prob (p e)
  (/ (num-favs (perms p) e)
     (fact (len p))))

;; DM !>(prob '(a b c d e) '(a b c))
;; 1/5

;; Bertrand's ballot theorem provides a formula for this probability as a function of the
;; number of votes cast for each candidate:

;; (defthm ballot-theorem
;;   (let ((a (a-count p e)) (b (b-count p e)))
;;     (implies (and (dlistp p) (> a b))
;;              (equal (prob p e)
;;                     (/ (- a b) (+ a b))))))

;; DM !>(let* ((p '(a b c d e)) (e '(a b c)) (a  (a-count p e)) (b (b-count p e)))
;;        (/ (- a b) (+ a b)))
;; 1/5

;; Let n = (len p).  Then b = (- n a) and the equation in the theorem may be expressed as

;;   (num-favs (perms p) e) = n!(a - (n - a))/n = (n - 1)!(2a - n).

;; To aid the induction, we shall prove that this equation holds under the weaker assumption
;; 2a >= n.  The usual informal inductive proof goes like this:

;; We have 2a >= n, but if 2a = n, then the claim holds trivially (0 = 0).  We may assume,
;; therefore, that 2a > n.  Let x be a member of p and consider the tallies c with (car c) = x,
;; i.e., in which the vote of x is counted last.  Since a > n - a, c is favorable iff (cdr c) is
;; favorable.  If x is in e (x is an A voter),  the length and a-count of (cdr c) are n - 1 and
;; a - 1.  By induction, the number of such favorable tallies is

;;    (n - 2)!(2(a - 1) - (n - 1)) = (n - 2)!(2a - n - 1).

;; Thus, the number of favorable tallies c with (car c) in e is

;;   a(n - 2)!(2 a - n - 1) = (n - 2)!(2a^2 - an - a).

;; On the other hand, if x is not in e (x is a B voter), then the length and a-count of (cdr c)
;; are n - 1 and a, and we find that the number of favorable tallies c with (car c) not in e is

;;   (n - a)(n - 2)!(2a - (n - 1)) = (n - 2)!(3an + n  - n^2 - 2a^2 - a)

;; The total number of favorable tallies is the sum

;;   (n - 2)!(a(2a^2 - an - a + 3an + n  - n^2 - 2a^2 - a) = (n - 2)!(2an - 2a + n - n^2)
;;                                                         = (n - 2)!(n - 1)(2a - n)
;;                                                         = (n - 1)!(2a - n).

;; As suggested by the mutually recursive definition of perms, the formalization of this proof 
;; requires a generalization pertaining to the function perms-aux.  Assume that p$ is a dlist and
;; sublist of p.  The members of (perms-aux p$ p) are the tallies c such that (car c) is in p$.
;; Let n and a be the length and a-count of p, and let n$ and a$ be the length and a-count of p$.
;; Assume that 2a >= n.  Reasoning aline the same lines as the above argument leads to this formula
;; for the number of favorable tallies in this list:

;;    (num-favs (perms-aux p$ p) e) = (n - 2)!(n$(2a - n + 1) - 2a$)  if 2a > n > 1
;;                                    a$                              if 2a > n = 1
;;                                    0                               if 2a = n
                                      
;; Note that if p$ = p, then n$ = n and a$ = a, and this formula reduces to

;;    (num-fave (perms p) e) = (num-favs (perms-aux p$ p) e) = (n - 1)!(2a - n).

;; This is trivially true if either 2a > n = 1 or 2a = n, and in the remaining case 2a > n > 1,

;;    (num-favs (perms p) e) = (num-favs (perms-aux p p) e)
;;                           = (n - 2)!(2an - n^2 + n - 2a)
;;                           = (n - 2)!(2a - n)(n - 1)
;;                           = (n - 1)!(2a - n).

;; We shall prove the correctness of the general formula using the induction scheme suggested by
;; the definitions of perms and perms-aux.  If p$ = NIL, then the claim holds trivially.  In the
;; remaining case,

;;    (perms-aux p$ p) = (append (conses (car p$) (perms (remove1-equal (car p$) p)))
;;                               (perms-aux (cdr p$) p)))

;; and (num-favs (perms-aux p$ p) is the sum of 2 terms:

;;    (1) (num-favs (conses (car p$) (perms (remove1-equal (car p$) p))) e)

;; and

;;    (2) (num-favs (perms-aux (cdr p$) p) e).

;; If n = 1, then (2) is 0 and

;;   (conses (car p$) (perms (remove1-equal (car p$) p))) = (conses (car p$) (()))
;;                                                        = (list (list (car p$))),

;; so (1) is a$ and the claim holds.

;; In the remaining case, note that every member of the list
;; (conses (car p$) (perms (remove1-equal (car p$) p))) has the same length and a-count as p.
;; Suppose 2a = n.  Then (1) is 0, as is (2) by induction, and (num-favs (perms-aux p$ p) e) = 0
;; as claimed.  Thus, we may assume 2a > n.  For every member c of
;; (conses (car p$) (perms (remove1-equal (car p$) p))), c is favorable iff (cdr c) is favorable.
;; Consequently, (1) may be replaced by

;;    (1') (num-favs (perms (remove1-equal (car p$) p)) e).

;; We consider 2 cases:

;; Case 1: (car p$) is a member of e (i.e., an A voter).
;; The length and a-count of (remove1-equal (car l) p) are n - 1 and a - 1.  By induction, if
;; 2(a - 1) > (n - 1), then the value of (1') is

;;    ((n - 1) - 1)!(2(a - 1) - (n - 1)).

;; On the other hand, if 2(a - 1) <= (n - 1), then we must have 2(a - 1) = (n - 1); by induction,
;; the value of (1') is then 0, so the same formula holds.

;; The length and a-count of (cdr p$) are n$ - 1 and a$ - 1.  By induction, the value of (2) is

;;   (n - 2)!((n$ - 1)(2a - n + 1) - 2(a$ - 1)).

;; The sum is easily checked to be (n - 2)!(n$(2a - n + 1) - 2a$).

;; Case 2: (car p$) is not a member of e.
;; The length and a-count of (remove1-equal (car p$) p) are n - 1 and a.  By induction, the
;; value of (1') is

;;    ((n - 1) - 1)!(2a - (n - 1)).

;; The length and a-count of (cdr p$) are n$ - 1 and a$.  By induction, the value of (2) is

;;   (n - 2)!((n$ - 1)(2a - n + 1) - 2a$).

;; The sum is again easily checked to be (n - 2)!(n$(2a - n + 1) - 2a$).

(local (defund hyp (p$ p e)
  (let ((n (len p)) (a (a-count p e))
        (n$ (len p$)) (a$ (a-count p$ e)))        
    (implies (and (dlistp p) (dlistp p$) (sublistp p$ p) (>= (* 2 a) n))
             (equal (num-favs (perms-aux p$ p) e)
	            (if (> a (- n a))
		        (if (= n 1)
			    a$
                          (* (fact (- n 2))
                             (- (* n$ (1+ (- (* 2 a) n)))
                                (* 2 a$))))
		      0))))))

(local (defthmd hyp-p$=p
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (>= (* 2 a) n) (hyp p p e))
             (equal (num-favs (perms-aux p p) e)
	            (* (fact (1- n)) (- (* 2 a) n)))))
  :hints (("Goal" :in-theory (enable hyp))
          ("Subgoal 1" :expand ((a-count p e) (a-count (cdr p) e))))))

(local (defthm a-count-remove1
  (implies (member-equal x l)
           (equal (a-count (remove1-equal x l) e)
                  (if (member-equal x e)
	              (1- (a-count l e))
	            (a-count l e))))))

(local (defthmd a-count-perm-1
  (implies (permutationp l m)
           (equal (a-count m e) (a-count l e)))))

(local (defthmd a-count-perm
  (implies (and (dlistp l) (member-equal m (perms l)))
           (equal (a-count m e) (a-count l e)))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance permp-perms (p m))
                        (:instance permp-permutationp (l m) (m l))
                        (:instance a-count-perm-1 (l m) (m l)))))))

(local (defthm favs-append
  (equal (num-favs (append l m) e)
         (+ (num-favs l e) (num-favs m e)))))

(local (defthm no-favs
  (implies (<= (a-count l e) (b-count l e))
           (null (favp l e)))))

(local (defthm favp-cdr
  (implies (and (> (a-count l e) (b-count l e))
                (consp (cdr l)))
           (iff (favp l e)
	        (favp (cdr l) e)))))

(local (defthm no-favs-sublist-perms
  (implies (and (dlistp p)
                (<= (a-count p e) (b-count p e))
                (member-equal x p)
                (sublistp l (perms (remove1-equal x p))))
	   (equal (num-favs (conses x l) e)
	          0))
  :hints (("Goal" :induct (conses x l))
          ("Subgoal *1/1" :in-theory (enable permp)
	                  :use ((:instance a-count-perm (l (remove1-equal x p)) (m (car l)))
	                        (:instance permutationp-eq-len (l (remove1-equal x p)) (m (car l)))
				(:instance permp-permutationp (l (remove1-equal x p)) (m (car l)))
				(:instance permp-perms (p (car l)) (l (remove1-equal x p))))))))

(local (defthmd favs-perms-aux-0
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (sublistp p$ p) (<= a (- n a)))
             (equal (num-favs (perms-aux p$ p) e)
                    0)))
  :hints (("Subgoal *1/2" :expand ((perms-aux p$ p))))))

(local (defthmd hyp-nil
  (implies (or (not (consp p)) (not (consp p$)))
           (hyp p$ p e))
  :hints (("Goal" :in-theory (enable hyp) :expand ((perms-aux p$ p))))))

(local (defthm hyp-0
  (implies (equal (* 2 (a-count p e)) (len p))
           (hyp p$ p e))
  :hints (("Goal" :in-theory (enable hyp) :use (favs-perms-aux-0)))))

(local (defthmd len-1-null-cdr
  (implies (and (dlistp p) (equal (len p) 1))
           (null (cdr p)))))

(local (defthm favs-perms-aux-1
  (let ((n (len p)) (a$ (a-count p$ e)))
    (implies (and (dlistp p) (sublistp p$ p) (= n 1))
             (equal (num-favs (perms-aux p$ p) e)
                    a$)))
  :hints (("Subgoal *1/4" :use (len-1-null-cdr) :expand ((perms-aux p$ p)))
          ("Subgoal *1/2" :use (len-1-null-cdr) :expand ((perms-aux p$ p))))))

(local (defthm hyp-1
  (implies (equal (len p) 1)
           (hyp p$ p e))
  :hints (("Goal" :in-theory (enable hyp) :use (favs-perms-aux-1)))))

(local (defthm favs-sublist-perms
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p)
                  (> (* 2 a) n)
                  (member-equal x p)
		  (> n 1)
                (sublistp l (perms (remove1-equal x p))))
	   (equal (num-favs (conses x l) e)
	          (num-favs l e))))
  :hints (("Goal" :induct (conses x l))
          ("Subgoal *1/1" :in-theory (enable permp)
	                  :use ((:instance a-count-perm (l (remove1-equal x p)) (m (car l)))
	                        (:instance permutationp-eq-len (l (remove1-equal x p)) (m (car l)))
				(:instance permp-permutationp (l (remove1-equal x p)) (m (car l)))
				(:instance permp-perms (p (car l)) (l (remove1-equal x p))))))))

(local (defthm favs-conses-perms
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p)
                  (> (* 2 a) n)
		  (> n 1)
                  (member-equal x p))
	   (equal (num-favs (conses x (perms (remove1-equal x p))) e)
	          (num-favs (perms (remove1-equal x p)) e))))))

(local (defthmd case-1-a
    (implies (and (consp p$) (sublistp p$ p))
             (member-equal (car p$) p))))

(local (defthmd case-1-b
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (dlistp p$) (consp p$) (sublistp p$ p) (> (* 2 a) n) (> n 1)
                  (hyp (remove1-equal (car p$) p) (remove1-equal (car p$) p) e)
		  (member-equal (car p$) e))
             (equal (num-favs (perms (remove1-equal (car p$) p)) e)
	            (* (fact (- n 2))
		       (- (* 2 (1- a)) (1- n))))))
  :hints (("Goal" :expand ((perms (remove1-equal (car p$) p)))
                  :use (case-1-a (:instance hyp-p$=p (p (remove1-equal (car p$) p))))))))

(local (defthmd case-1-c
  (let ((n (len p)) (a (a-count p e)) (n$ (len p$)) (a$ (a-count p$ e)))
    (implies (and (dlistp p) (dlistp p$) (consp p$) (sublistp p$ p) (> (* 2 a) n) (> n 1)
                  (hyp (cdr p$) p e)
		  (member-equal (car p$) e))
             (equal (num-favs (perms-aux (cdr p$) p) e)
	            (* (fact (- n 2))
		       (- (* (1- n$) (1+ (- (* 2 a) n)))
		          (* 2 (1- a$)))))))
  :hints (("Goal" :in-theory (enable hyp)))))

(local (defthmd case-1-d
  (let ((n (len p)) (a (a-count p e)) (n$ (len p$)) (a$ (a-count p$ e)))
    (implies (and (dlistp p) (dlistp p$) (consp p$) (sublistp p$ p) (> (* 2 a) n) (> n 1)
                  (hyp (remove1-equal (car p$) p) (remove1-equal (car p$) p) e)
                  (hyp (cdr p$) p e)
		  (member-equal (car p$) e))
             (equal (num-favs (perms-aux p$ p) e)
	            (* (fact (- n 2))
                       (- (* n$ (1+ (- (* 2 a) n)))
                          (* 2 a$))))))
  :hints (("Goal" :in-theory (enable case-1-b case-1-c)))))

(local (defthmd case-1
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (consp p$) (> (* 2 a) n) (> n 1)
                  (hyp (remove1-equal (car p$) p) (remove1-equal (car p$) p) e)
                  (hyp (cdr p$) p e)
		  (member-equal (car p$) e))
             (hyp p$ p e)))
  :hints (("Goal" :use (case-1-d) :expand ((hyp p$ p e))))))

(local (defthmd case-2-a
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (dlistp p$) (consp p$) (sublistp p$ p) (> (* 2 a) n) (> n 1)
                  (hyp (remove1-equal (car p$) p) (remove1-equal (car p$) p) e)
		  (not (member-equal (car p$) e)))
             (equal (num-favs (perms (remove1-equal (car p$) p)) e)
	            (* (fact (- n 2))
		       (- (* 2 a) (1- n))))))
  :hints (("Goal" :expand ((perms (remove1-equal (car p$) p)))
                  :use (case-1-a (:instance hyp-p$=p (p (remove1-equal (car p$) p))))))))

(local (defthmd case-2-b
  (let ((n (len p)) (a (a-count p e)) (n$ (len p$)) (a$ (a-count p$ e)))
    (implies (and (dlistp p) (dlistp p$) (consp p$) (sublistp p$ p) (> (* 2 a) n) (> n 1)
                  (hyp (cdr p$) p e)
		  (not (member-equal (car p$) e)))
             (equal (num-favs (perms-aux (cdr p$) p) e)
	            (* (fact (- n 2))
		       (- (* (1- n$) (1+ (- (* 2 a) n)))
		          (* 2 a$))))))
  :hints (("Goal" :in-theory (enable hyp)))))

(local (defthmd case-2-c
  (let ((n (len p)) (a (a-count p e)) (n$ (len p$)) (a$ (a-count p$ e)))
    (implies (and (dlistp p) (dlistp p$) (consp p$) (sublistp p$ p) (> (* 2 a) n) (> n 1)
                  (hyp (remove1-equal (car p$) p)(remove1-equal (car p$) p) e)
                  (hyp (cdr p$) p e)
		  (not (member-equal (car p$) e)))
             (equal (num-favs (perms-aux p$ p) e)
	            (* (fact (- n 2))
                       (- (* n$ (1+ (- (* 2 a) n)))
                          (* 2 a$))))))
  :hints (("Goal" :in-theory (enable case-2-a case-2-b)))))

(local (defthmd case-2
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (consp p$) (> (* 2 a) n) (> n 1)
                  (hyp (remove1-equal (car p$) p) (remove1-equal (car p$) p) e)
                  (hyp (cdr p$) p e)
		  (not (member-equal (car p$) e)))
             (hyp p$ p e)))
  :hints (("Goal" :use (case-2-c) :expand ((hyp p$ p e))))))

(local (defthmd hyp-lemma
  (implies (or (not (consp p$))
               (and (>= (* 2 (a-count p e)) (len p))
	            (hyp (remove1-equal (car p$) p) (remove1-equal (car p$) p) e)
                    (hyp (cdr p$) p e)))
           (hyp p$ p e))
  :hints (("Goal" :use (case-1 case-2 hyp-nil hyp-0 hyp-1) :expand ((len p))))))

(local (in-theory (enable hyp perms perms-aux)))


(local (encapsulate ()

(local (include-book "projects/groups/support/perms" :dir :system))

(defthmd hyp-induction
  (hyp p$ p e)
  :hints (("Goal" :induct (len-perms-induct p$ p))
          ("Subgoal *1/2" :in-theory (enable hyp))
          ("Subgoal *1/1" :use (hyp-lemma))))
))

(defthmd ballot-theorem-gen
  (let ((n (len p)) (a (a-count p e))
        (n$ (len p$)) (a$ (a-count p$ e)))        
    (implies (and (dlistp p) (dlistp p$) (sublistp p$ p) (>= (* 2 a) n))
             (equal (num-favs (perms-aux p$ p) e)
	            (if (> a (- n a))
		        (if (= n 1)
			    a$
                          (* (fact (- n 2))
                             (- (* n$ (1+ (- (* 2 a) n)))
                                (* 2 a$))))
		      0))))
  :hints (("Goal" :use (hyp-induction))))

(local (in-theory (disable hyp)))

(local (defthmd bt-1
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (> (* 2 a) n))
             (equal (num-favs (perms p) e)
	            (* (fact (1- n)) (- (* 2 a) n)))))
  :hints (("Goal" :in-theory (disable hyp num-favs) :use (hyp-p$=p (:instance hyp-induction (p$ p)))))))

(local (in-theory (disable num-favs)))

(local (defthmd bt-2
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (> (* 2 a) n))
             (equal (prob p e)
	            (/ (* (fact (1- n)) (- (* 2 a) n))
		       (fact n)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (bt-1):expand ((prob p e))))))

(local (defthmd bt-3
  (let ((n (len p)) (a (a-count p e)))
    (implies (and (dlistp p) (> (* 2 a) n))
             (posp n)))))

(local (defthmd bt-4
  (let ((n (len p)) (a (a-count p e)) (b (b-count p e)))
    (implies (and (dlistp p) (> (* 2 a) n))
             (equal (/ (* (fact (1- n)) (- (* 2 a) n))
		       (fact n))
		    (/ (- a b) (+ a b)))))
  :hints (("Goal" :use (bt-2 bt-3) :expand ((fact (len p)))))))

;; As noted above, substituting p for p$ yields the expected formula for (num-favs (perms p) e), 
;; and the theorem follows:

(defthm ballot-theorem
  (let ((a (a-count p e)) (b (b-count p e)))
    (implies (and (dlistp p) (> a b))
             (equal (prob p e)
                    (/ (- a b) (+ a b)))))
  :hints (("Goal" :use (bt-4 bt-2))))
