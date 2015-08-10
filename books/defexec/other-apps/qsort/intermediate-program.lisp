(in-package "ACL2")

#|

  intermediate-program.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~~~

In this book, we attempt to define a functional version of qsort. This qsort
version is defined with the intension of proof of the stobj-based in-situ qsort
correct. Basically, this qsort is what can be perceived as functionally closest
to the stobj-based qsort, and yet, being applicative we reason about this using
the standard inductive arguments and a proof that this is equivalent to isort
should follow easily.

|#


(include-book "total-order")
(include-book "permutations")


(defun del-last (x)
  (if (endp (rest x)) nil
    (cons (first x) (del-last (rest x)))))

(defun last-val (x)
  (if (endp x) nil
    (if (endp (rest x)) (first x)
      (last-val (rest x)))))

(defun snoc (x e)
  (if (endp x) (list e)
    (cons (first x) (snoc (rest x) e))))

(defun lower-part (x splitter)
  (if (endp x) nil
    (if (and (<<= splitter (first x))
	     (<< (last-val x) splitter))
	(cons (last-val x) (lower-part (del-last (rest x)) splitter))
      (if (and (<<= splitter (first x))
	       (<<= splitter (last-val x)))
	  (lower-part (del-last x) splitter)
	(if (and (<< (first x) splitter)
		 (<< (last-val x) splitter))
	    (cons (first x) (lower-part (rest x) splitter))
	  (cons (first x)
		(lower-part (del-last (rest x)) splitter)))))))

(defun upper-part (x splitter)
  (if (endp x) nil
    (if (and (<<= splitter (first x))
	     (<< (last-val x) splitter))
	(snoc (upper-part (del-last (rest x)) splitter)
	      (first x))
      (if (and (<<=  splitter (first x))
	       (<<= splitter (last-val x)))
	  (snoc (upper-part (del-last x) splitter)
		(last-val x))
	(if (and (<< (first x) splitter)
		 (<< (last-val x) splitter))
	    (upper-part (rest x) splitter)
	  (snoc (upper-part (del-last (rest x)) splitter)
		(last-val x)))))))

;; We need to prove something about the lower-part and upper-part functions we
;; defined simply to get ourselves to admit the definition of qsort we have in
;; mind. This sucks big time, but I dont see a more elegant way of proving the
;; theorems. It is a clean blow to my normal structured proof techniques where I
;; define functions separately and prove facts about them later, --- clearly an
;; indication that qsort even functionally is not an easy function to reason
;; about, or I am the dumbest person on earth......


(defthm how-many-snoc-reduction
  (equal (how-many a (snoc x e))
	 (+ (if (equal a e) 1 0)
	    (how-many a x))))

(local
(defthm how-many-del-last-reduction
  (equal (how-many e (del-last x))
	 (- (how-many e x)
	    (if (and (consp x) (equal e (last-val x))) 1 0))))
)

(local
(defthm how-many-lower-upper-reduction
  (equal (+ (how-many e (lower-part x splitter))
	    (how-many e (upper-part x splitter)))
         (how-many e x)))
)

;; The following theorem is placed just to give enough hint to ACL2 to use
;; how-many to prove perm in the next theorem.


(defthm how-many-lower-upper-reduction-reduced-to-append
  (equal (how-many e (append (lower-part x splitter)
                             (upper-part x splitter)))
         (how-many e x)))


(defthm perm-append-lower-upper-reduction
  (perm (append (lower-part x splitter)
		(upper-part x splitter))
	x)
  :rule-classes nil)


(local
(defthm len-lower-part-reduction
  (equal (len (append (lower-part x splitter)
		      (upper-part x splitter)))
	 (len x))
  :hints (("Goal"
           :use perm-append-lower-upper-reduction)))
)

(local
(defthm len-consp-reduction-1
  (implies (and (equal (len (append x y)) n)
		(consp x))
	   (< (len y) n))
  :rule-classes nil)
)


(defthm upper-has-less-len
  (implies (consp (lower-part x splitter))
	   (< (len (upper-part x splitter)) (len x)))
  :hints (("Goal"
	   :use ((:instance len-consp-reduction-1
			    (x (lower-part x splitter))
			    (y (upper-part x splitter))
			    (n (len x)))))))


(local
(defthm len-consp-reduction-2
  (implies (and (equal (len (append x y)) n)
		(consp y))
	   (< (len x) n)))
)

(local
(defthm upper-part-is-consp
  (implies (consp x)
	   (consp (upper-part x (first x)))))
)


(defthm lower-has-less-len
  (implies (consp x)
	   (< (len (lower-part x (first x)))
	      (len x)))
  :hints (("Goal"
	   :in-theory (disable len-consp-reduction-2)
	   :use ((:instance len-consp-reduction-2
			    (x (lower-part x (first x)))
			    (y (upper-part x (first x)))
			    (n (len x)))))))


(defthm len-is-an-ordinal
  (o-p (len x)))


(defthm len-less-in-cdr
  (implies (consp x)
	   (< (len (cdr x)) (len x))))

(in-theory (disable len))

(defun qsort-fn (lst)
  (declare (xargs :measure (len lst)))
  (if (endp lst) nil
    (if (endp (rest lst))
	(list (first lst))
      (let ((lower (lower-part lst (first lst)))
	    (upper (upper-part lst (first lst))))
	(if (endp lower)
	    (cons (first lst)
		  (qsort-fn (rest lst)))
	  (append (qsort-fn lower)
		  (qsort-fn upper)))))))
