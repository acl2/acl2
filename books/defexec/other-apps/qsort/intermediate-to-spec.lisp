(in-package "ACL2")

#|

 intermediate-to-spec.lisp
 ~~~~~~~~~~~~~~~~~~~~~~~~~

In this file we prove that the functional qsort qsort-fn is the same as
isort. Basically we show that qsort-fn is an ordered permutation, and then we
use the main spec property, anything that produces an ordered permutation is
the same as qsort, to prove the result.

|#

(include-book "intermediate-program")
(include-book "spec-properties")

(local
(defthm del-last-true-listp-reduction
   (true-listp (del-last x)))
)

(defthm snoc-del-last-reduction
  (implies (and (true-listp x)
                (consp x))
           (equal (snoc (del-last x) (last-val x))
                  x))
  :rule-classes :forward-chaining)


(local
(defthm lower-part-is-true-listp
  (implies (true-listp x) (true-listp (lower-part x e))))
)

(local
(defthm true-listp-cons-reduction
  (implies (true-listp x)
	   (true-listp (cons e x))))
)

(local
(defthm true-listp-snoc-reduction
  (implies (true-listp x)
	   (true-listp (snoc x e))))
)

(local
(defthm true-listp-append-reduction
  (implies (and (true-listp x) (true-listp y))
	   (true-listp (append x y))))
)

(defthm upper-part-is-true-listp
  (implies (true-listp x)
	   (true-listp (upper-part x e))))

(defthm qsort-fn-is-int-listp
  (implies (true-listp x)
	   (true-listp (qsort-fn x))))

(defthm qsort-fn-is-a-permutation
  (perm (qsort-fn x) x))

(local
(defun lessp (e x)
  (if (endp x) T
    (if (<< (first x) e) (lessp e (rest x))
      nil)))
)

(local
(defun not-lessp (e x)
  (if (endp x) T
    (if (<<= e (first x)) (not-lessp e (rest x))
      nil)))
)
;; Now prove the congruences between perm, and lessp and not-lessp

(local
(defcong perm equal (lessp x l) 2)
)

(local
(defcong perm equal (not-lessp x l) 2)
)

;; End proof of congruences between perm, and lessp and not-lessp

(local
(defthm ordp-lessp-not-lessp-reduction
  (implies (and (ordp x)
                (ordp y)
                (lessp e x)
                (not-lessp e y))
           (ordp (append x (cons e y)))))
)

;; The next two theorems establish the correspondence of lessp and
;; not-lessp functions with the function ordp. So if you were thinking
;; what was I doing with these two functions, then it is to provide
;; the following correspondence that I was working. I would love for
;; someone to give me an easier correspondence, if they can read the
;; proof.:-)

(local
(defthm ordp-lessp-not-lessp-reduction-1
  (implies (and (ordp x)
		(ordp y)
		(lessp e x)
		(not-lessp e y))
	   (ordp (append x y)))
  :hints (("Subgoal *1/4"
           :in-theory (enable <<))))

)

(local
(defthm ordp-lessp-not-lessp-reduction-2
  (implies (and (ordp x)
		(not-lessp e x))
	   (ordp (cons e x))))
)

(local
(defthm func-partition-x-is-lessp
  (lessp splitter
	 (lower-part x splitter)))
)

(local
(defthm func-partition-y-is-not-lessp
  (not-lessp splitter
	     (upper-part x splitter)))
)

(local
(defthm qsort-lower-is-lessp
  (lessp splitter
	 (qsort-fn (lower-part x splitter))))
)

(local
(defthm qsort-upper-is-not-lessp
  (not-lessp splitter
	     (qsort-fn (upper-part x splitter))))
)

(defthm if-lower-is-endp-upper-is-the-actual-list
  (implies (and (true-listp x)
		(endp (lower-part x (first x))))
	   (equal (upper-part x (first x)) x))
  :rule-classes nil)

(local
(defthm not-lessp-implies-not-lessp-cdr
  (implies (not-lessp e x)
	   (not-lessp e (rest x)))
  :rule-classes nil)
)

;; The proofs of the following two functions are really ugly. Just
;; look at the number of hints I had to give it. I need to talk to Rob
;; about cleaning it up.

(local
(defthm qsort-not-lessp-for-lower-endp
  (implies (and (true-listp x)
		(endp (lower-part x (first x))))
	   (not-lessp (first x) (qsort-fn (rest x))))
  :hints (("Goal"
           :in-theory (disable lower-part qsort-fn)
	   :use if-lower-is-endp-upper-is-the-actual-list)
	  ("Goal'''"
	   :use ((:instance not-lessp-implies-not-lessp-cdr
			    (e (car x))
			    (x (upper-part x (first x))))))))
)

;; The following theorem means that I am really done. The next theorem
;; should be a breeze from perm-ordp-unique.

(local
(defthm qsort-fn-is-ordp
  (implies (true-listp x)
	   (ordp (qsort-fn x)))
  :hints (("Goal"
           :induct (qsort-fn x))
          ("Subgoal *1/4"
           :use ((:instance ordp-lessp-not-lessp-reduction-1
                            (e (car x))
                            (x (qsort-fn (lower-part x (car x))))
                            (y (qsort-fn (upper-part x (car x)))))))
          ("Subgoal *1/3"
           :use ((:instance ordp-lessp-not-lessp-reduction-2
                            (e (car x))
                            (x (qsort-fn (cdr x))))))))
)

(defthm qsort-fn-equivalent-isort
  (implies (true-listp x)
	   (equal (isort x)
		  (qsort-fn x)))
  :hints (("Goal"
	   :use ((:instance any-ordered-permutation-of-integers-is-isort
			    (y (qsort-fn x)))))))

(in-theory (enable qsort-fn))