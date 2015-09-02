; In this book we prove the ACL2 version of:

; (forall e : (how-many e a) = (how-many e b)) -> (perm a b)

; where (how-many e a) is the number of occurrences of e as an
; element in a.

; We actually constrain (alpha) and (beta) to satisfy the hypothesis
; and prove that they satisfy the conclusion.

; We use the perm from this book which we happened to have.  We don't
; have to load these books until the first time we need them, but we
; know we will need them so we load them now.

(in-package "ACL2")

(include-book "perm")

(local (include-book "arithmetic/top" :dir :system))

; ---------------------------------------------------------------------------
; Exercise 11.47

(defun how-many (e lst)
  (if (endp lst)
      0
      (if (equal e (car lst))
          (+ 1 (how-many e (cdr lst)))
          (how-many e (cdr lst)))))

; ---------------------------------------------------------------------------
; Exercise 11.48

; Here I define mergesort again.

(defun split (x)
  (cond ((atom x) (mv nil nil))
	((atom (cdr x)) (mv x nil))
	(t (mv-let (a b)
		   (split (cddr x))
		   (mv (cons (car x) a) (cons (cadr x) b))))))

(defun mergelist (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((atom x) y)
	((atom y) x)
	((< (car x) (car y))
	 (cons (car x) (mergelist (cdr x) y)))
	(t (cons (car y) (mergelist x (cdr y))))))

(defthm measure-for-mergesort
  (implies (consp (cdr x))
	   (and
	    (< (acl2-count (car (split x))) (acl2-count x))
	    (< (acl2-count (cadr (split x))) (acl2-count x)))))

(defthm mv-nth-cadr
  (equal (mv-nth 1 x)
	 (cadr x)))

(defun mergesort (x)
  (cond ((atom x) nil)
	((atom (cdr x)) x)
	(t (mv-let (a b)
		   (split x)
		   (mergelist (mergesort a) (mergesort b))))))

(defthm how-many-mergelist
  (equal (how-many e (mergelist a b))
         (+ (how-many e a)
            (how-many e b))))

(defthm how-many-split-list
  (equal (+ (how-many a (car (split x)))
            (how-many a (cadr (split x))))
         (how-many a x)))

(defthm how-many-mergesort
  (equal (how-many e (mergesort lst))
         (how-many e lst)))

; ---------------------------------------------------------------------------
; Exercise 11.49

; We hope you didn't waste too much time on this problem!

; As noted in the errata:

; On page 220, Exercise 11.49 is simply wrong.  The formula alleged not
; to be a theorem is a theorem, so no counterexample is possible!  What
; we had in mind has nothing to do with mergesort but instead is an
; observation about perm, how-many, and quantification.  The exercise
; should have been:

;  Exercise 11.49  The following is a theorem in a suitable logic
;  permitting ACL2 terms and first-order quantification.

;    (perm a b)
;  <->
;    (ALL e (equal (how-many e a)
;                  (how-many e b)))

; Here, by ALL we mean the universal quantifier.  The universal
; quantifier in the above theorem is important.  The similar looking
; ACL2 formula

; (iff (perm a b)
;      (equal (how-many e a)
;             (how-many e b)))

; is not a theorem.  Exhibit a counterexample.

; Here is our solution to THAT problem!

(defthm counterexample-49
  (equal
   (let ((a '(1 2))
         (b '(1 3))
         (e 1))
     (iff (perm a b)
          (equal (how-many e a)
                 (how-many e b))))
   nil)
  :rule-classes nil)

; Note that to make this command a suitable event for a book, we had to
; phrase it as a theorem.  Our theorem is just that a certain instance
; of the formula evaluates to nil.

; ---------------------------------------------------------------------------
; Exercise 11.50

; Constrain (alpha) and (beta) to be any two constants with the property
; that every e occurs in one as many times as it occurs in the other.

(encapsulate ((alpha nil t)
              (beta nil t))
 (local (defun alpha nil nil))
 (local (defun beta nil nil))
 (defthm how-many-alpha-beta
   (equal (how-many e (alpha))
          (how-many e (beta)))))

; Now we will prove that (alpha) and (beta) are permutations of eachother.

; We start with routine facts about perm.

(defcong perm perm (cons x y) 2)

(defthm in-append
    (equal (in e (append a b))
           (or (in e a)
               (in e b))))

(defthm del-append
    (equal (del e (append a b))
           (if (in e a)
               (append (del e a) b)
             (append a (del e b)))))

(defcong perm perm (append x y) 1)

(defcong perm perm (append x y) 2)

; We don't have universal quantification.  But we can define a recursive
; function that checks any particular ACL2 predicate over a finite list.
; And it is clear that it suffices to check the how-many property just over
; all the elements that occur either in (alpha) or (beta).  So a finite
; quantifier will do.

; We define (bounded-quantifierp x a b) to check that for every e in
; x, (how-many e a) is (how-many e b).  We prove that this implis
; (perm (restrict x a) (restrict x b)).  Basically, (restrict x a) is
; just a restricted to the elements of x.  If we let x be the
; concatentation of a and b, then (restrict x a) is just (a perm of) a
; and (restict x b) is just b.  So we can prove (perm a b) if we can
; prove (bounded-quantifierp (append a b) a b).  But if a is (alpha)
; and b is (beta) then we can prove (bounded-quantifierp any a b), by
; induction on any.

(local
 (encapsulate
  nil
  (defun bounded-quantifierp (x a b)
    (if (endp x)
        t
      (and (equal (how-many (car x) a)
                  (how-many (car x) b))
           (bounded-quantifierp (cdr x) a b))))

  (defun rep (e n)
    (if (zp n)
        nil
      (cons e (rep e (- n 1)))))

  (defun rmv (e lst)
    (if (endp lst)
        nil
      (if (equal e (car lst))
          (rmv e (cdr lst))
        (cons (car lst) (rmv e (cdr lst))))))

  (defthm append-rep-rmv
    (perm (append (rep e (how-many e lst))
                  (rmv e lst))
          lst))

  (defun restrict (x y)
    (if (endp x)
        nil
      (append (rep (car x) (how-many (car x) y))
              (restrict (cdr x) (rmv (car x) y)))))

  (defthm subsetp-append-1
    (subsetp a (append a b)))

  (defthm subsetp-append-2
    (subsetp b (append a b)))

  (defun hint (x a b)
    (if (endp x)
        (list a b)
      (hint (cdr x)
            (rmv (car x) a)
            (rmv (car x) b))))

  (defthm how-many-rmv
    (equal (how-many e (rmv x a))
           (if (equal e x)
               0
             (how-many e a))))

  (defthm bounded-quantifierp-rmv
    (implies (bounded-quantifierp x2 a b)
             (bounded-quantifierp x2
                                 (rmv x1 a)
                                 (rmv x1 b))))

  (defthm fundamental
    (implies (bounded-quantifierp x a b)
             (perm (restrict x a) (restrict x b)))
    :hints (("Goal" :induct (hint x a b))))

; So we know that (bounded-quantifierp x a b) implies that the restrictions
; of a and b to x are permutations of eachother.  But if a is a subset of x,
; then the restriction of a to x is (a perm of) a.

  (defthm subsetp-rmv-cdr
    (implies (and (consp b)
                  (subsetp a b))
             (subsetp (rmv (car b) a) (cdr b))))

  (defthm restrict-subsetp
    (implies (subsetp a x)
             (perm (restrict x a) a))
    :hints (("Goal" :induct (restrict x a))))

; And no matter what x is, (bounded-quantifierp x (alpha) (beta)) holds,
; by the constraint on (alpha) and (beta).

  (defthm bounded-quantifierp-alpha-beta
    (bounded-quantifierp x (alpha) (beta)))))

; So we can put all these facts together, using for x the concatenation of
; (alpha) and (beta), thereby insuring that both (alpha) and (beta) are
; subsets of the set x we quantify over.

(defthm perm-alpha-beta
  (perm (alpha) (beta))
  :hints (("Goal"
           :in-theory (disable fundamental)
           :use (:instance fundamental
                           (x (append (alpha) (beta)))
                           (a (alpha))
                           (b (beta))))))

; ---------------------------------------------------------------------------
; Exercise 11.51

(defthm perm-mergesort
  (perm (mergesort lst) lst)
  :hints (("Goal" :use (:functional-instance
                        perm-alpha-beta
                        (alpha (lambda nil (mergesort lst)))
                        (beta  (lambda nil lst))))))
