(in-package "ACL2")
(include-book "programs")
(include-book "permutations")

#|

 spec-properties.lisp
 ~~~~~~~~~~~~~~~~~~~~

In this file we prove certain theorems on the insertion sort spec we had. In
particular, we prove that isort produces a sorted permutation of its input, and
that if a function produces a sorted permutation of its input that function is
the same as isort.

Thus now to prove another function to be equivalent to it, all that is required
to be proved is that it produces an ordered permutation of its input.

|#


(defun ordp (x)
  (cond ((endp x) t)
        ((endp (rest x)) t)
        ((<<= (car x) (cadr x))
         (ordp (rest x)))
        (t nil)))

(defthm ordp-my-del-reduction
  (implies (ordp x)
           (ordp (my-del e x))))

(local
(defthm ordp-deduces-not-perm-if-<
  (implies (and (ordp y)
		(consp x)
		(<< (car x) (car y)))
	   (not (perm x y))))
)

(local
(defthm ordp-consp-reduction
  (implies (and (ordp y)
		(ordp x)
		(consp x)
		(perm x y))
	   (equal (car x) (car y)))
  :hints (("Goal"
	   :do-not-induct t
	   :cases ((<< (car x) (car y)) (<<= (car y) (car x))
		   (equal (car x) (car y))))
	  ("Subgoal 1"
           :in-theory (disable ordp-deduces-not-perm-if-<)
	   :use ((:instance ordp-deduces-not-perm-if-<
			    (x y) (y x)))))
  :rule-classes nil)
)

(local
(defthm perm-ordp-unique
  (implies (and (ordp x)
		(ordp y)
                (true-listp x)
                (true-listp y)
		(perm x y))
	   (equal x y))
    :hints (("Goal"
	   :induct (perm x y))
	  ("Subgoal *1/2"
	   :use  ordp-consp-reduction))
  :rule-classes nil)
)


(defthm isort-is-a-permutation
  (perm (isort x) x))

(defthm isort-is-ordered
  (ordp (isort x)))

(defthm insert-preserves-true-listp
  (implies (true-listp x)
           (true-listp (insert e x))))

;; I have to learn how to give ACL2 the hint to set otf-flg to t. So I am
;; breaking this up into two cases

(defthm isort-is-a-true-listp
  (implies (true-listp x)
           (true-listp (isort x)))
  :hints (("Subgoal *1/2"
           :expand (isort x)))
  :rule-classes :forward-chaining)

(in-theory (disable isort))

(defthm any-ordered-permutation-of-integers-is-isort
  (implies (and (perm x y)
                (true-listp x)
                (true-listp y)
                (ordp y))
           (equal (isort x) y))
  :hints (("Goal"
           :use ((:instance perm-ordp-unique
                            (x (isort x)))))))


