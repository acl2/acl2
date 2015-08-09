;;
;; Material in this ACL2 book is described in a short paper
;;
;; "Encapsulation for Practical Simplification Procedures"
;; by Olga Shumsky Matlin and William McCune
;;
;; submitted to the Fourth International Workshop on the
;; ACL2 Theorem Prover and Its Applications (ACL2-2003)
;;
;; For more information contact
;;   Olga Shumsky Matlin (matlin@mcs.anl.gov)
;;   William McCune (mccune@mcs.anl.gov)
;;
;;
;; Direct Incorporation Algorithm:
;;
;;     While(Q)
;;       C = dequeue(Q)
;;       C = rewrite(C,S)
;;       if (C != True)
;;         for each D in S rewritable by C
;;           remove D from S
;;           add to Q D simplified by C
;;         S = S + C
;;
;; Limbo Incorporation Algorithm:
;;
;;     preprocess(C, S, Limbo):
;;       C = rewrite(C, S+Limbo)
;;       if (C != TRUE)
;;         return Limbo
;;       else
;;         return Limbo+C
;;
;;     Loop1: Initial Limbo Computation
;;     while(Q)
;;       C = dequeue(Q)
;;       Limbo = preprocess(C, S, Limbo);
;;
;;     Loop2: Limbo Processing
;;     while(Limbo)
;;       C = dequeue(Limbo)
;;       for each D in S rewritable by C
;;         S = remove D from S
;;         Limbo = preprocess(D, S, Limbo+C)
;;       S = S + C
;;

(in-package "ACL2")
(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(encapsulate

 ;;----------------- Signatures (constrained functions)

 (
  (simplify (x y) t)      ; simplify x by element of list y

  (true-symbolp (x) t)    ; expression x is a true-symbolp

  (ceval (x i) t)         ; evaluate clause x in interpretation i

  (scount (x) t)          ; size evaluator for measure functions
 )

 ;;------------------- Witnesses

 (local (defun simplify (x y)
	  (declare (xargs :guard t)
		   (ignore y))
	  x))

 (local (defun true-symbolp (x)
	  (declare (xargs :guard t)
		   (ignore x))
	  t))

 (local (defun ceval (x i)
	  (declare (xargs :guard t)
		   (ignore x i))
	  t))

 (local (defun scount (x)
	  (declare (xargs :guard t))
	  (acl2-count x)))

 ;;------------------- Properties and Exported Functions

 (defthm scount-natural
   (and (integerp (scount x))
	(<= 0 (scount x)))
   :rule-classes :type-prescription)

 (defthm scount-simplify
   (or (equal (simplify x y) x)
       (< (scount (simplify x y))
	  (scount x)))
   :rule-classes nil)

 (defthm simplify-idempotent
   (equal (simplify (simplify x y) y)
 	  (simplify x y)))

 (defthm simplify-subset
   (implies (and (not (equal (simplify a x) a))
		 (subsetp-equal x y))
            (not (equal (simplify a y) a)))
   :rule-classes ((:rewrite :match-free :all)))

 (defthm simplify-append
   (implies (and (equal (simplify a x) a)
		 (equal (simplify a y) a))
	    (equal (simplify a (append x y)) a)))

 (defthm ceval-boolean
   (or (equal (ceval x i) t)
       (equal (ceval x i) nil))
   :rule-classes :type-prescription)

 (defthm true-symbolp-ceval
   (implies (true-symbolp x)
	    (ceval x i)))

 (defun ceval-list (x i)
   (declare (xargs :guard (true-listp x)
; Added by Matt Kaufmann after v3-6-1 to because of restriction on guard
; verification for functions depending on signature functions:
                   :verify-guards nil))
   (if (endp x)
       t
     (and (ceval (car x) i) (ceval-list (cdr x) i))))

; The following was added by Matt Kaufmann after ACL2 Version 3.4 because of
; a soundness bug fix; see ``subversive'' in :doc note-3-5.
 (defthm ceval-list-type
   (booleanp (ceval-list x i))
   :rule-classes :type-prescription)

 (defthm simplify-sound
   (implies (ceval-list y i)
	    (equal (ceval (simplify x y) i)
		   (ceval x i))))

 ) ;; end of encapsulate

; Added by Matt Kaufmann after v3-6-1 (see comment for (defun ceval-list ...)
; above):
(verify-guards ceval-list)

(defun rewritable (x y)
  (declare (xargs :guard t))
  (not (equal (simplify x y) x)))

(defthm scount-simplify-rewritable
  (implies (rewritable x y)
	   (< (scount (simplify x y)) (scount x)))
  :hints (("goal" :use scount-simplify)))

(defthm simplified-not-rewritable
  (not (rewritable (simplify x y) y)))

(defthm simplify-subset-restated
  (implies (and (rewritable a x)
		(subsetp-equal x y))
	   (rewritable a y))
  :rule-classes ((:rewrite :match-free :all)))

(defthm simplify-append-restated
  (implies (and (not (rewritable a x))
		(not (rewritable a y)))
	   (not (rewritable a (append x y)))))

(in-theory (disable rewritable))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Direct Formalization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; produces a list of Ds in S, such that D is rewritable by X
(defun extract-rewritables (x s)
  (declare (xargs :guard (true-listp s)))
  (cond ((endp s) nil)
	((rewritable (car s) (list x))
	 (cons (car s) (extract-rewritables x (cdr s))))
	(t (extract-rewritables x (cdr s)))))

;; produces a list of Ds in S, such that D is rewritable by X
;; D is simplified by x before being placed on the list
(defun extract-n-simplify-rewritables (x s)
  (declare (xargs :guard (true-listp s)))
  (cond ((endp s) nil)
	((rewritable (car s) (list x))
	 (cons (simplify (car s) (list x))
	       (extract-n-simplify-rewritables x (cdr s))))
	(t (extract-n-simplify-rewritables x (cdr s)))))

;; removes from S elements rewritable by X
(defun remove-rewritables (x s)
  (declare (xargs :guard (true-listp s)))
  (cond ((endp s) nil)
	((rewritable (car s) (list x))
	 (remove-rewritables x (cdr s)))
	(t (cons (car s) (remove-rewritables x (cdr s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For the proof of termination of direct-incorporation:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lcount (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      0
    (+ 1 (scount (car x)) (lcount (cdr x)))))

(defthm extract-consp
  (implies (not (consp (extract-rewritables x s)))
	   (not (consp (extract-n-simplify-rewritables x s)))))

(local
 (include-book "../../../../arithmetic/top-with-meta"))

(defthm small-sum-<-large-sum
  (implies (and (< x y)
		(< u v))
	   (< (+ u x) (+ y v))))

(defthm lcount-extract
  (implies (consp (extract-rewritables x s))
	   (< (lcount (extract-n-simplify-rewritables x s))
	      (lcount (extract-rewritables x s)))))

(defthm lcount-remove
  (implies (true-listp s)
	   (equal (lcount (remove-rewritables x s))
		  (- (lcount s)
		     (lcount (extract-rewritables x s))))))

(defthm lcount-append
  (implies (true-listp x)
	   (equal (lcount (append x y))
		  (+ (lcount x) (lcount y)))))

(defthm inequality-helper
  (implies (and (<= x y)
		(< u v))
	   (< (+ x u (- v)) y)))

(defthm less-n-greater-equal
  (implies (and (<= (scount q1) (scount x))
		(<= (scount x) (scount q1)))
	   (equal (scount q1) (scount x)))
  :rule-classes ((:rewrite :match-free :all)))

(defthm scount-simplify-combined
   (<= (scount (simplify x y)) (scount x))
   :hints (("goal" :use scount-simplify)))

;;;;;; end of termination proof preparations
(defun direct-incorporation (q s)
  (declare
   (xargs
    :guard (and (true-listp q) (true-listp s))
    :measure (cons (+ 1 (lcount q) (lcount s)) (+ 1 (lcount q)))
    :hints (("subgoal 2"
	     :cases
	     ((consp (extract-rewritables (simplify (car q) s) s))
	      (not (consp (extract-rewritables (simplify (car q) s) s))))))))
  (cond ((or (not (true-listp q)) (not (true-listp s))) 'INPUT-ERROR)
	((endp q) s)
	((true-symbolp (simplify (car q) s)) (direct-incorporation (cdr q) s))
	(t (direct-incorporation
	    (append (cdr q)
		    (extract-n-simplify-rewritables (simplify (car q) s) s))
	    (cons (simplify (car q) s)
		  (remove-rewritables (simplify (car q) s) s))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proving Correctness of Naive Formalization:
;;   the simple processing function produces a clean database
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; x neither rewrites, nor is rewritable by, anything in s
(defun mutually-irreducible-el-list (x s)
  (declare (xargs :guard (true-listp s)))
  (cond ((endp s) t)
	((or (rewritable x (list (car s)))
	     (rewritable (car s) (list x))) nil)
	(t (mutually-irreducible-el-list x (cdr s)))))

(defun irreducible-list (s)
  (declare (xargs :guard (true-listp s)))
  (cond ((endp s) t)
	((mutually-irreducible-el-list (car s) (cdr s))
	 (irreducible-list (cdr s)))
	(t nil)))

(defthm remove-rewritables-mutually-irreducible-el-list
  (implies (mutually-irreducible-el-list x s)
	   (mutually-irreducible-el-list x (remove-rewritables y s))))

(defthm remove-rewritables-irreducible
  (implies (irreducible-list s)
	   (irreducible-list (remove-rewritables x s))))

(defthm subsetp-append-1
  (subsetp-equal s (append x s)))

(defthm subsetp-cons
  (subsetp-equal s (cons x s))
  :hints (("goal"
	   :do-not-induct t
	   :in-theory (disable subsetp-append-1)
	   :use ((:instance subsetp-append-1 (x (list x)))))))

(defthm forward-simplify-irreducible
  (implies (and (irreducible-list s)
		(not (rewritable x s)))
	   (mutually-irreducible-el-list x (remove-rewritables x s))))

;; top level correctness proof for direct-incorporation
(defthm direct-incorporation-is-irreducible
  (implies (irreducible-list s)
	   (irreducible-list (direct-incorporation q s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proving Soundness of Naive Formalization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm ceval-append-1
  (implies (not (ceval-list x i))
	   (not (ceval-list (append x y) i))))

(defthm ceval-append-2
  (implies (not (ceval-list y i))
	   (not (ceval-list (append x y) i))))

(defthm ceval-append-3
  (implies (and (ceval-list x i)
		(ceval-list y i))
	   (ceval-list (append x y) i)))

(defthm ceval-remove-rewritables
  (implies (ceval-list s i)
	   (ceval-list (remove-rewritables x s) i)))

(defthm ceval-extract-n-simp-1
  (implies (and (ceval x i)
		(ceval-list s i))
	   (ceval-list (extract-n-simplify-rewritables x s) i)))

(defthm ceval-extract-n-simp-2
  (implies (and (ceval-list (remove-rewritables x s) i)
		(ceval x i)
		(not (ceval-list s i)))
	   (not (ceval-list (extract-n-simplify-rewritables x s) i))))

(defthm direct-incorporation-sound-iff
  (implies (and (true-listp q)
		(true-listp s))
	   (iff (and (ceval-list q i) (ceval-list s i))
		(ceval-list (direct-incorporation q s) i)))
  :hints (("Subgoal *1/2"
	   :in-theory (disable true-symbolp-ceval)
	   :use ((:instance true-symbolp-ceval
			    (x (simplify (car q) s)))))
	  ("subgoal *1/3.6"
	   :use ((:instance ceval-extract-n-simp-2
			    (x (simplify (car q) s))))))
  :rule-classes nil)

;; top soundness lemma
(defthm direct-incorporation-is-sound
  (implies (and (true-listp q)
		(true-listp s))
	   (equal (ceval-list (direct-incorporation q s) i)
		  (and (ceval-list q i) (ceval-list s i))))
  :hints (("goal" :use direct-incorporation-sound-iff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Limbo-Based Formalization
;;
;; processing with forward and backward
;; demodulation/subsumption in two separate loops,
;; using a limbo list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun preprocess (x s l)
  (declare (xargs :guard (and (true-listp s)
			      (true-listp l))))
  (if (true-symbolp (simplify x (append s l)))
      l
    (append l (list (simplify x (append s l))))))

(defun initial-limbo (q s l)
  (declare (xargs :guard (and (true-listp q)
			      (true-listp s)
			      (true-listp l))))
  (if (endp q)
      l
    (initial-limbo (cdr q) s (preprocess (car q) s l))))

(defthm limbo-true-list
  (implies (true-listp l)
	   (true-listp (initial-limbo q s l))))

(defun preprocess-list (d s r)
  (declare (xargs :guard (and (true-listp d)
			      (true-listp s)
			      (true-listp r))))
  (if (endp d)
      r
      (preprocess-list (cdr d) s (preprocess (car d)
				  (append s (cdr d))
				  r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For the proof of termination of limbo-process:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; auxiliary function; this function is easier to reason about
;; than preprocess-list, so it is used in the correctness proof as well
(defun special-ppd (d s r)
  (declare (xargs :guard (and (true-listp d)
			      (true-listp s)
			      (true-listp r))))
  (if (endp d)
      nil
      (let ((e (simplify (car d) (append s (cdr d) r))))
	(if (true-symbolp e)
	    (special-ppd (cdr d) s r)
	    (cons e (special-ppd (cdr d) s (append r (list e))))))))

;; auxiliary function: every element of x is rewritable by something in y
(defun rewritable-list-by-list (x y)
  (declare (xargs :guard (and (true-listp x)
			      (true-listp y))))
  (cond ((endp x) t)
	((rewritable (car x) y)
	 (rewritable-list-by-list (cdr x) y))
	(t nil)))

(defthm subsetp-append-2
  (subsetp-equal s (append s r)))

(defthm subsetp-append-3
  (subsetp-equal s (append s c r))
  :hints (("goal"
	   :use ((:instance subsetp-append-2 (r (append c r)))))))

(defthm scount-rewritable-append
  (implies (rewritable d s)
           (< (scount (simplify d (append s r)))
	      (scount d))))

(defthm lcount-special-ppd-consp
  (implies (and (consp d)
		(true-listp d)
                (rewritable-list-by-list d s))
           (< (lcount (special-ppd d s r))
              (lcount d))))

(defthm append-nil
  (implies (true-listp r)
	   (equal (append r nil) r)))

(defthm append-multiple
  (equal (append (append d s) r)
	 (append d s r)))

(defthm preprocess-list-special-ppd
  (implies (true-listp r)
	   (equal (preprocess-list d s r)
		  (append r (special-ppd d s r)))))

;; auxiliary function: all elements of l are writable by x
(defun all-rewritable-list (l x)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) t)
	((rewritable (car l) (list x)) (all-rewritable-list (cdr l) x))
	(t nil)))

(defthm extract-all-rewritable
  (all-rewritable-list (extract-rewritables x s) x))

(defthm all-rewritable-append ;; 3 inductions, hint required
  (implies (all-rewritable-list d x)
	   (rewritable-list-by-list d (append s (cons x l))))
  :hints (("goal" :do-not fertilize)))

;;;;;; end of termination proof preparations

(defun process-limbo (l s)
  (declare
   (xargs
    :guard (and (true-listp l) (true-listp s))
    :measure (cons (+ 1 (lcount l) (lcount s)) (+ 1 (lcount l)))
    :hints (("subgoal 1"
	     :cases ((consp (extract-rewritables (car l) s))
		     (not (consp (extract-rewritables (car l) s))))))))
  (cond ((or (not (true-listp l)) (not (true-listp s))) 'INPUT-ERROR)
	((endp l) s)
	(t (process-limbo
	    (append
	     (cdr l)
	     (preprocess-list (extract-rewritables (car l) s)
			      (append (remove-rewritables (car l) s) l)
			      nil))
	    (cons (car l)
		  (remove-rewritables (car l) s))))))

;; two-loop processing function
(defun limbo-incorporation (q s)
  (declare (xargs :guard (and (true-listp q) (true-listp s))))
  (process-limbo (initial-limbo q s nil) s))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proving Correctness:
;;   the split processing function produces a clean
;;   (irreducible) database
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; no element of l is rewritable by an element in s
(defun irreducible-list-by-list (l s)
  (declare (xargs :guard (and (true-listp l) (true-listp s))))
  (cond ((endp l) t)
	((rewritable (car l) s) nil)
	(t (irreducible-list-by-list (cdr l) s))))

;; x rewrites nothing in l
(defun irreducible-list-by-el (x l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) t)
	((rewritable (car l) (list x)) nil)
	(t (irreducible-list-by-el x (cdr l)))))

;; forall A,B in L, pos[A]<pos[B] -> A does not rewrite B
(defun irreducible-tail-by-head (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) t)
	((irreducible-list-by-el (car l) (cdr l))
	 (irreducible-tail-by-head (cdr l)))
	(t nil)))

;;;;;;;;;;
(defthm irreducible-list-by-list-append-el
  (implies (and (irreducible-list-by-list l s)
		(not (rewritable x s)))
	   (irreducible-list-by-list (append l (list x)) s)))

(defthm rewritable-element-by-list-append-left
  (implies (rewritable x s)
	   (rewritable x (append s l))))

(defthm simplify-not-rewritable-append-left
  (not (rewritable (simplify x (append s l)) s))
  :hints (("Goal" :use ((:instance rewritable-element-by-list-append-left
				   (x (simplify x (append s l))))))))

;; mini-goal
(defthm limbo-irreducible-list-by-list
  (implies (irreducible-list-by-list l s)
	   (irreducible-list-by-list (initial-limbo q s l) s)))

;;;;;;;;;;

(defthm append-irreducible-list-by-el
  (implies (and (irreducible-list-by-el x l)
                (not (rewritable y (list x))))
	   (irreducible-list-by-el x (append l (list y)))))

(defthm not-rewritable-cons
  (implies (not (rewritable x (cons l1 l2)))
	   (not (rewritable x (list l1))))
  :rule-classes ((:rewrite :match-free :all)))

(defthm append-irreducible-tail-by-head
  (implies (and (not (rewritable x l))
		(irreducible-tail-by-head l))
	   (irreducible-tail-by-head (append l (list x)))))

(defthm rewritable-element-by-list-append-right
  (implies (rewritable x l)
	   (rewritable x (append s l))))

(defthm simplify-not-rewritable-append-right
  (not (rewritable (simplify x (append s l)) l))
  :hints (("Goal" :use ((:instance rewritable-element-by-list-append-right
				   (x (simplify x (append s l))))))))

;; mini-goal
(defthm limbo-irreducible-tail-by-head
  (implies (irreducible-tail-by-head l)
	   (irreducible-tail-by-head (initial-limbo q s l))))

;;;;;;;;;;
(defthm remove-rewritables-subset
    (subsetp-equal (remove-rewritables x s) s))

(defthm irreducible-cons-remove-rewritables
  (implies (and (irreducible-list-by-list l s)
		(irreducible-list-by-el x l))
	   (irreducible-list-by-list l (cons x (remove-rewritables x s))))
  :hints (("subgoal *1/2"
	   :use ((:instance simplify-append-restated
			    (a (car l))
			    (x (list x))
			    (y (remove-rewritables x s)))))))

(defthm irreducible-cons
  (implies (and (irreducible-list-by-list l s)
		(irreducible-list-by-el x l))
	   (irreducible-list-by-list l (cons x s)))
  :hints (("Subgoal *1/2"
	   :use ((:instance simplify-append-restated
			    (a (car l))
			    (x (list x))
			    (y s))))))

(defthm irreducible-list-by-list-append-2
  (implies (and (irreducible-list-by-list l1 s)
		(irreducible-list-by-list l2 s))
	   (irreducible-list-by-list (append l1 l2) s)))

(defthm irreducible-list-by-el-append-cons
  (implies (and (not (rewritable x1 (list l1)))
		(irreducible-list-by-el l1 (append l2 x2)))
	   (irreducible-list-by-el l1 (append l2 (cons x1 x2)))))

(defthm irreducible-tail-by-head-append-cons
  (implies (and (not (rewritable x1 l))
		(irreducible-tail-by-head (append l x2))
		(irreducible-list-by-el x1 x2))
         (irreducible-tail-by-head (append l (cons x1 x2)))))

(defthm irreducible-tail-by-head-append
  (implies (and (true-listp l)
		(true-listp x)
		(irreducible-tail-by-head l)
		(irreducible-tail-by-head x)
		(irreducible-list-by-list x l))
	   (irreducible-tail-by-head (append l x))))

;;;;;;;;;;

(defthm member-append-all ;; several inductions
  (member-equal x (append s (cons x (append l d2 r)))))

(defthm rewritable-by-member
  (implies (and (not (rewritable x l))
		(member-equal y l))
	   (not (rewritable x (list y))))
  :rule-classes nil)

(defthm rewritable-simplify-append-all
  (not (rewritable (simplify y (append s (cons x (append l d2 r)))) (list x)))
  :hints (("goal"
	   :use ((:instance
		  rewritable-by-member
		  (x (simplify y (append s (cons x (append l d2 r)))))
		  (y x)
		  (l (append s (cons x (append l d2 r)))))))))

;; mini-goal
(defthm  special-irreducible-x
  (irreducible-list-by-el x (special-ppd d (append s (cons x l)) r)))

;;;;;;;;;;

;; mini-goal
(defthm special-irreducible-s
  (irreducible-list-by-list (special-ppd d (append s (cons x l)) r) s))

;;;;;;;;;;

(defthm subsetp-append-4
  (subsetp-equal l (append l d2 r)))

(defthm subsetp-cons-2
  (implies (subsetp-equal l z)
	   (subsetp-equal l (cons x z))))

(defthm subsetp-append-5
  (implies (subsetp-equal l z)
	   (subsetp-equal l (append x z))))

(defthm rewritable-element-by-list-append-all
  (implies (rewritable y l)
	   (rewritable y (append s (cons x (append l d2 r))))))

(defthm simplify-not-rewritable-append-all
  (not (rewritable
	(simplify y (append s (cons x (append l d2 r))))
	l))
  :hints (("goal"
	   :use ((:instance
		  rewritable-element-by-list-append-all
		  (y (simplify y (append s (cons x (append l d2 r))))))))))

;; mini-goal
(defthm  special-irreducible-l
  (irreducible-list-by-list (special-ppd d (append s (cons x l)) r) l))

;;;;;;;;;;

(defthm append-subset-7
  (subsetp-equal r (append l d2 r)))

(defthm rewritable-element-by-list-append-last
  (implies
   (rewritable y r)
   (rewritable y (append s (cons x (append l d2 r))))))

(defthm simplify-not-rewritable-append-last
  (not (rewritable
	(simplify y (append s (cons x (append l d2 r)))) r))
  :hints (("goal"
	   :in-theory (disable rewritable-element-by-list-append-last)
	   :use ((:instance
		  rewritable-element-by-list-append-last
		  (y (simplify y (append s (cons x (append l d2 r))))))))))

(defthm irreducible-list-by-list-append-1
  (implies (not (irreducible-list-by-list x l))
	   (not (irreducible-list-by-list x (append l z)))))

;; mini-mini-goal
(defthm special-irreducible-r
  (irreducible-list-by-list (special-ppd d (append s (cons x l)) r) r)
  :hints (("goal" :do-not generalize)))

(defthm irreducible-member
  (implies (and (not (irreducible-list-by-el x l))
		(member-equal x s))
	   (not (irreducible-list-by-list l s)))
  :rule-classes nil)

(defthm member-append-el
  (member-equal x (append r (list x))))

(defthm special-head-tail-helper
  (implies
   (irreducible-tail-by-head
    (special-ppd d (append s (cons x l)) (append r (list y))))
   (irreducible-list-by-el
    y (special-ppd d (append s (cons x l)) (append r (list y)))))
  :hints (("goal"
	   :do-not-induct t
	   :use ((:instance
		  irreducible-member
		  (x y)
		  (l (special-ppd d (append s (cons x l))
				  (append r (list y))))
		  (s (append r (list y))))))))

;; mini-goal
(defthm special-ppd-irreducible-tail-by-head
  (irreducible-tail-by-head (special-ppd d (append s (cons x l)) r)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm process-limbo-irreducible ;; main theorem of subsection
  (implies (and (irreducible-list s)
		(irreducible-tail-by-head l)
		(irreducible-list-by-list l s))
	   (irreducible-list (process-limbo l s)))
  :hints (("goal" :induct (process-limbo l s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; top level correctness proof for limbo-incorporation
(defthm limbo-incorporation-is-irreducible
  (implies (irreducible-list s)
	   (irreducible-list (limbo-incorporation q s)))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable process-limbo-irreducible)
	   :use ((:instance process-limbo-irreducible
			    (l (initial-limbo q s nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proving Soundness of Two-Step Formalization:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Computation of initial-limbo list is sound
(defthm limbo-sound-l
  (implies (and (not (ceval-list l i))
                     (ceval-list s i))
           (not (ceval-list (initial-limbo q s l) i))))

(defthm limbo-sound-1
  (implies (and (not (ceval-list q i))
		(ceval-list s i)
		(ceval-list l i))
           (not (ceval-list (initial-limbo q s l) i)))
  :hints (("Subgoal *1/2.2"
	   :in-theory (disable true-symbolp-ceval)
	   :use ((:instance true-symbolp-ceval
			    (x (SIMPLIFY (CAR Q) (APPEND S L))))))))

(defthm limbo-sound
  (implies (and (ceval-list q i) (ceval-list s i) (ceval-list l i))
	   (ceval-list (initial-limbo q s l) i)))

;; Incorporating the limbo list is sound

;; positive direction

(defthm ceval-extract
  (implies (ceval-list s i)
	   (ceval-list (extract-rewritables x s) i)))

(defthm special-ppd-sound-1
  (implies (and (ceval-list d i)
		(ceval-list s i)
		(ceval-list r i))
	   (ceval-list (special-ppd d s r) i)))

(defthm process-limbo-sound
  (implies (and (ceval-list l i)
		(ceval-list s i))
	   (ceval-list (process-limbo l s) i)))

;; negative direction

(defthm special-ppd-sound-2
  (implies (and (ceval-list r i)
		(ceval-list s i)
		(not (ceval-list d i)))
	   (not (ceval-list (special-ppd d s r) i)))
  :hints (("Subgoal *1/2"
	   :in-theory (disable true-symbolp-ceval)
	   :use ((:instance true-symbolp-ceval
			    (x (simplify (car d) (append s (cdr d) r))))))))

(defthm extract-remove-together
  (implies (and (ceval-list (extract-rewritables x s) i)
		(ceval-list (remove-rewritables x s) i))
	   (ceval-list s i))
  :rule-classes ((:rewrite :match-free :all)))

(defthm ceval-append-big-helper
  (implies
   (and (true-listp l)
	(true-listp s)
	(ceval-list r i)
	(not (ceval-list (append l s) i)))
   (not (ceval-list (append l
			    (special-ppd (extract-rewritables x s)
					 (append (remove-rewritables x s)
						 (cons x l))
					 r)
			    (cons x (remove-rewritables x s)))
		    i)))
  :hints (("goal" :do-not-induct t
	   :cases ((and (ceval x i)
			(ceval-list l i)
			(ceval-list (remove-rewritables x s) i))
		   (not (and (ceval x i)
			     (ceval-list l i)
			     (ceval-list (remove-rewritables x s) i)))))
	  ("subgoal 2"
	   :in-theory (disable special-ppd-sound-2)
	   :use ((:instance
		  special-ppd-sound-2
		  (d (extract-rewritables x s))
		  (s (append (remove-rewritables x s) (cons x l))))))))

(defthm process-limbo-sound-append
  (implies (and (true-listp l)
		(true-listp s)
		(not (ceval-list (append l s) i)))
	   (not (ceval-list (process-limbo l s) i)))
  :hints (("goal" :induct (process-limbo l s))))


;; putting things together
(defthm split-process-sound-1
  (implies (and (true-listp s)
                (ceval-list q i)
                (ceval-list s i))
           (ceval-list (limbo-incorporation q s) i)))

(defthm split-process-sound-2
  (implies (and (true-listp s)
                (not (ceval-list q i))
                (ceval-list s i))
           (not (ceval-list (limbo-incorporation q s) i))))

(defthm limbo-incorporation-sound-iff
  (implies (true-listp s)
	   (iff (and (ceval-list q i) (ceval-list s i))
		(ceval-list (limbo-incorporation q s) i)))
  :hints (("Goal" :use (split-process-sound-1 split-process-sound-2)))
  :rule-classes nil)

;; top soundness lemma
(defthm limbo-incorporation-is-sound
  (implies (true-listp s)
	   (equal (ceval-list (limbo-incorporation q s) i)
		  (and (ceval-list q i) (ceval-list s i))))
  :hints (("goal"
	   :in-theory (disable limbo-incorporation)
	   :use limbo-incorporation-sound-iff)))

