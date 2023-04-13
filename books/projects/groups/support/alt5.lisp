(in-package "DM")

(include-book "alt")
(include-book "a5")

;; A simple group is one that does not have a proper normal subgroup:

(defund proper-normalp (h g)
  (and (normalp h g)
       (> (order h) 1)
       (< (order h) (order g))))

;;  For example, (alt 4) is not simple:

(defund normal-subgroup-of-alt-4 ()
  (subgroup '((0 1 2 3) (1 0 3 2) (2 3 0 1) (3 2 1 0))
	    (sym 4)))

(defthmd alt-4-not-simple
  (proper-normalp (normal-subgroup-of-alt-4) (alt 4))
  :hints (("Goal" :in-theory (enable alt proper-normalp))))

;; However, (alt n) is simple for all n > 4.  For no reason other than sheer laziness, we shall prove
;; this only for n = 5.  We shall also show that if (order g) < 60 = (alt 5), then g is not simple.

;;---------------------------------------------------------------------------------------------------
;; Simplicity of (alt 5)
;;---------------------------------------------------------------------------------------------------

;; Let h be a normal subgroup of g.  If x is in h, then (conjs x g) is a sublist of (elts h).  Thus,
;; (select-conjs (non-trivial-conjs g) h) is a list of all non-trivial conjugacy classes that are
;; included in h:

(defun select-conjs (l h)
  (if (consp l)
      (if (in (caar l) h)
	  (cons (car l) (select-conjs (cdr l) h))
	(select-conjs (cdr l) h))
    ()))

;; Thus, if we append the elements of that list and throw in the center, we have a permutaiton of
;; the elements of h.  In the casse of interestm the center happens to be trivial:

(local-defthmd dlistp-select-conjs
  (implies (dlistp l)
           (and (sublistp (select-conjs l h) l)
	        (dlistp (select-conjs l h)))))

(local-defthmd disjointp-dlistp-sublist
  (implies (and (sublistp l m)
                (dlistp l)
		(disjointp-pairwise m)
		(dlistp-list m))
	   (and (disjointp-pairwise l)
		(dlistp-list l))))

(local-defthm dlistp-append-list-select-conjs
  (implies (groupp g)
           (dlistp (append-list (select-conjs (conjs-list g) h))))	   
  :hints (("Goal" :use ((:instance dlistp-select-conjs (l (conjs-list g)))
                        (:instance disjointp-dlistp-sublist (l (select-conjs (conjs-list g) h)) (m (conjs-list g)))))))

(local-defthmd member-sublist-append-list
  (implies (and (sublistp l m)
                (member x (append-list l)))
	   (member x (append-list m))))

(local-defthm e-not-in-append-list-select-conjs
  (implies (groupp g)
           (not (member-equal (e g) (append-list (select-conjs (conjs-list g) h)))))	   
  :hints (("Goal" :use ((:instance dlistp-select-conjs (l (conjs-list g)))
                        (:instance center-conjs-list (c (e g)))
			(:instance member-sublist-append-list (x (e g)) (l (select-conjs (conjs-list g) h)) (m (conjs-list g)))))))

(local-defthm dlistp-cons-e-append-list-select-conjs
  (implies (groupp g)
           (dlistp (cons (e g) (append-list (select-conjs (conjs-list g) h))))))


(local-defthmd sublistp-append-list-select-conjs-1
  (implies (and (groupp g)
                (normalp h g)
                (sublistp l (conjs-list g))
		(member-equal x (append-list (select-conjs l h))))
	   (in x h))
  :hints (("Subgoal *1/1" :use ((:instance conjs-list-cars (c (car l)))
                                (:instance conjs-conjer (x (caar l)) (y x))
				(:instance normalp-conj (x (caar l)) (y (conjer x (caar l) g)))))))

(local-defthmd sublistp-append-list-select-conjs-2
  (implies (and (groupp g)
                (normalp h g)
                (sublistp l (conjs-list g)))
	   (sublistp (append-list (select-conjs l h))
	             (elts h)))
  :hints (("Goal" :use ((:instance sublistp-append-list-select-conjs-1 (x (scex1 (append-list (select-conjs l h)) (elts h))))
                        (:instance scex1-lemma (l (append-list (select-conjs l h))) (m (elts h)))))))

(local-defthmd sublistp-append-list-select-conjs
  (implies (and (groupp g)
                (normalp h g)
                (sublistp l (conjs-list g)))
	   (sublistp (cons (e g) (append-list (select-conjs l h)))
	             (elts h)))
  :hints (("Goal" :in-theory (disable subgroup-e in-e-g)
                  :use (subgroup-e sublistp-append-list-select-conjs-2 (:instance in-e-g (g h))))))

(local-defthmd consp-conjs
  (implies (and (groupp g) (in x g))
           (consp (conjs x g)))
  :hints (("Goal" :use (conj-reflexive))))

(local-defthmd sublistp-h-append-list-select-conjs-1
  (implies (and (groupp g)
                (normalp h g)
		(in x h)
		(member-equal (conjs x g) l))
	   (member-equal x (append-list (select-conjs l h))))
  :hints (("Subgoal *1/2" :use (consp-conjs
                                (:instance conjs-conjer (y (caar l)))
                                (:instance normalp-conj (y (conjer (caar l) x g)))))))

(local-defthmd sublistp-h-append-list-select-conjs-2
  (implies (and (groupp g)
                (normalp h g)
		(in x h)
		(not (in x (center g))))
	   (member-equal x (append-list (select-conjs (conjs-list g) h))))
  :hints (("Goal" :use (member-lconjs-conjs-list
                        (:instance sublistp-h-append-list-select-conjs-1 (l (conjs-list g)))))))

(local-defthmd sublistp-h-append-list-select-conjs-3
  (implies (and (groupp g)
                (normalp h g)
		(equal (cent-elts g) (list (e g)))
		(in x h))
	   (member-equal x (cons (e g) (append-list (select-conjs (conjs-list g) h)))))
  :hints (("Goal" :use (sublistp-h-append-list-select-conjs-2))))

(local-defthmd sublistp-h-append-list-select-conjs
  (implies (and (groupp g)
                (normalp h g)
		(equal (cent-elts g) (list (e g))))
	   (sublistp (elts h)
	             (cons (e g) (append-list (select-conjs (conjs-list g) h)))))
  :hints (("Goal" :use ((:instance sublistp-h-append-list-select-conjs-3 (x (scex1 (elts h) (cons (e g) (append-list (select-conjs (conjs-list g) h))))))
                        (:instance scex1-lemma (m (cons (e g) (append-list (select-conjs (conjs-list g) h)))) (l (elts h)))))))

(defthmd permp-select-conjs
  (implies (and (normalp h g)
                (equal (cent-elts g) (list (e g))))
           (permp (cons (e g) (append-list (select-conjs (conjs-list g) h)))
	          (elts h)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (dlistp-cons-e-append-list-select-conjs sublistp-h-append-list-select-conjs
		        (:instance sublistp-append-list-select-conjs (l (conjs-list g)))))))

;; This gives us an expression for the order of h:

(defthmd len-select-conjs
  (implies (and (normalp h g)
                (equal (cent-elts g) (list (e g))))
           (equal (order h)
	          (1+ (len (append-list (select-conjs (conjs-list g) h))))))
  :hints (("Goal" :use (permp-select-conjs
                        (:instance eq-len-permp (l (cons (e g) (append-list (select-conjs (conjs-list g) h))))
				                (m (elts h)))))))

;; Thus, (order h) = (1+ (len (append-list l))) for some dlist sublist l of (conjs-list g).  We shall compute this value
;; for all such sublists of (conjs-list (alt 5)) and observe that none of these values is a divisor of 60, and therefore
;; none of these values can be the order of a subgroup of (alt 5).

;; Unfortunately, the function conjs-list is computationally impractical for a group of order 60.  We shall define a
;; more efficient equivalent function, based on a tail-recursive version of conjs:

(defun conjs-fast-aux (x l m g)
  (if (consp l)
      (let ((c (conj x (car l) g)))
        (if (member-equal c m)
	    (conjs-fast-aux x (cdr l) m g)
	  (conjs-fast-aux x (cdr l) (insert c m g) g)))
    m))

(defun conjs-fast (x g)
  (conjs-fast-aux x (elts g) () g))

(local-defthm ordp-conjs-fast-aux
  (implies (and (groupp g)
		(in x g)
		(sublistp l (elts g))
		(sublistp m (elts g))
		(ordp m g))
	   (ordp (conjs-fast-aux x l m g) g)))

(local-defthm ordp-conjs-fast
  (implies (and (groupp g)
		(in x g))
	   (ordp (conjs-fast x g) g)))

(local-defthm conj-in-conjs-fast-aux
  (implies (and (groupp g)
		(in x g)
		(sublistp l (elts g))
		(ordp m g)
		(or (member-equal y l)
		    (member-equal (conj x y g) m)))
	   (member-equal (conj x y g) (conjs-fast-aux x l m g))))

(local-defthm conj-in-conjs-fast
  (implies (and (groupp g)
		(in x g)
		(in y g))
	   (member-equal (conj x y g) (conjs-fast x g))))

(local-defthmd conjs-conjer-fast-aux
  (implies (and (groupp g)
		(in x g)
		(sublistp l (elts g))
		(ordp m g)
		(member-equal y (conjs-fast-aux x l m g))
		(not (member-equal y m)))
           (let ((c (conjer-aux y x l g)))
	     (and (member-equal c l)
	          (equal (conj x c g) y)))))

(local-defthm conjs-fast-conjer
  (implies (and (groupp g)
		(in x g)
		(member-equal y (conjs-fast x g)))
           (let ((c (conjer y x g)))
	     (and (in c g)
	          (equal (conj x c g) y))))
  :hints (("Goal" :expand ((conjer y x g)) :use ((:instance conjs-conjer-fast-aux (l (elts g)) (m ()))))))

(in-theory (disable conjs conjer conjs-fast))

(local-defthmd member-conjs-conjs-fast
  (implies (and (groupp g)
		(in x g)
		(member-equal y (conjs x g)))
	   (member-equal y (conjs-fast x g)))
  :hints (("Goal" :use (conjs-conjer (:instance conj-in-conjs-fast (y (conjer y x g)))))))

(local-defthmd member-conjs-fast-conjs
  (implies (and (groupp g)
		(in x g)
		(member-equal y (conjs-fast x g)))
	   (member-equal y (conjs x g)))
  :hints (("Goal" :use (conjs-fast-conjer (:instance conj-in-conjs (a (conjer y x g)))))))

(local-defthmd sublistp-conjs-fast-conjs
  (implies (and (groupp g)
		(in x g))
	   (and (sublistp (conjs x g) (conjs-fast x g))
		(sublistp (conjs-fast x g) (conjs x g))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (conjs x g)) (m (conjs-fast x g)))
			(:instance scex1-lemma (l (conjs-fast x g)) (m (conjs x g)))
			(:instance member-conjs-conjs-fast (y (scex1 (conjs x g) (conjs-fast x g))))
			(:instance member-conjs-fast-conjs (y (scex1 (conjs-fast x g) (conjs x g))))))))

(defthmd conjs-fast-conjs
  (implies (and (groupp g)
		(in x g))
	   (equal (conjs-fast x g)
		  (conjs x g)))
  :hints (("Goal" :use (sublistp-conjs-fast-conjs
			(:instance ordp-equal (x (conjs x g)) (y (conjs-fast x g)))))))


(defun conjs-list-fast-aux (l g)
  (if (consp l)
      (let ((conjs (conjs-list-fast-aux (cdr l) g)))
	(if (or (in (car l) (center g))
	        (member-list (car l) conjs))
	    conjs
	  (cons (conjs-fast (car l) g) conjs)))
    ()))

(defund conjs-list-fast (g)
  (conjs-list-fast-aux (elts g) g))

(local-defthm conjs-list-fast-conjs-list-aux
  (implies (and (groupp g)
		(sublistp l (elts g)))
	   (equal (conjs-list-fast-aux l g)
	          (conjs-list-aux l g)))
  :hints (("Goal" :in-theory (enable conjs-fast-conjs))))

(defthmd conjs-list-fast-conjs-list
  (implies (groupp g)
	   (equal (conjs-list-fast g)
	          (conjs-list g)))
  :hints (("Goal" :in-theory (enable conjs-list-fast conjs-list))))

;; The lengths of the conjugacy classes can now be easily computed using conj-list-fast:

(defun lens (l)
  (if (consp l)
      (cons (len (car l)) (lens (cdr l)))
    ()))

(local-defthm lens-conjs-list-a5
  (equal (lens (conjs-list-fast (a5)))
         '(20 12 12 15))
  :hints (("Goal" :in-theory (enable (a5)))))

(defthmd lens-conjs-list-alt-5
  (equal (lens (conjs-list-fast (alt 5)))
         '(20 12 12 15))
  :hints (("Goal" :in-theory (enable a5-rewrite))))

;; To complete the proof, we shall compute a list of numbers that contains (len (append-list s))
;; for every sublist s of (conjs-list (alt 5)).

;; A list of the sublists of a list:

(defun sublists (l)
  (if (consp l)
      (append (conses (car l) (sublists (cdr l)))
	      (sublists (cdr l)))
    (list ())))

;; In particular:

(defthmd member-select-conjs
  (member-equal (select-conjs l h)
                (sublists l)))

;; If l is a list of lists of lists, then for every s in l, (len (append-list s)) is a member of
;; (append-lens l), defined as follows:

(defun append-lens (l)
  (if (consp l)
      (cons (len (append-list (car l)))
            (append-lens (cdr l)))
    ()))

(defthmd member-append-len
  (implies (member-equal s l)
           (member-equal (len (append-list s))
	                 (append-lens l))))

;; This provides a list that contains the order of any normal subgroup:

(defun add1-list (l)
  (if (consp l)
      (cons (1+ (car l)) (add1-list (cdr l)))
    ()))

(local-defthmd member-add1-list
  (implies (member-equal n l)
	   (member-equal (1+ n) (add1-list l))))

(defthmd normalp-order
  (implies (and (normalp h g)
                (equal (cent-elts g) (list (e g))))
	   (member-equal (order h)
	                 (add1-list (append-lens (sublists (conjs-list-fast g))))))
  :hints (("Goal" :in-theory (enable conjs-list-fast-conjs-list)
                  :use (len-select-conjs
                        (:instance member-select-conjs (l (conjs-list g)))
			(:instance member-append-len (s (select-conjs (conjs-list g) h))
			                             (l (sublists (conjs-list g))))
			(:instance member-add1-list (n (len (append-list (select-conjs (conjs-list g) h))))
			                            (l (append-lens (sublists (conjs-list g)))))))))
(local (include-book "a5"))

(local-defthmd normalp-lens-a5
  (and (equal (cent-elts (a5)) (list (e (a5))))
       (equal (add1-list (append-lens (sublists (conjs-list-fast (a5)))))
              '(60 45 48 33 48 33 36 21 40 25 28 13 28 13 16 1)))
  :hints (("Goal" :in-theory (enable (a5)))))

(defthmd normalp-lens-alt-5
  (and (equal (cent-elts (alt 5)) (list (e (alt 5))))
       (equal (add1-list (append-lens (sublists (conjs-list-fast (alt 5)))))
              '(60 45 48 33 48 33 36 21 40 25 28 13 28 13 16 1)))
  :hints (("Goal" :in-theory (enable a5-rewrite) :use (normalp-lens-a5))))(in-theory (enable (a5)))

;; Finally, we observe that none of these values can be the order of a proper subgroup:

(defthmd alt-5-simple
  (not (proper-normalp h (alt 5)))
  :hints (("Goal" :use (normalp-lens-alt-5
                        (:instance normalp-order (g (alt 5)))
			(:instance order-subgroup-divides (g (alt 5))))
                  :in-theory (enable proper-normalp))))
