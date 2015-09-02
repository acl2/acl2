(in-package "ACL2")

#|

  permutations.lisp
  ~~~~~~~~~~~~~~~~~

In this book we develop the definition of permutation, and justify that
permutation is an equivalence relation. We also prove some properties relating
to congruences of permutations with other functions. This is by no means an
adequate theory on permutations to gain the status of a reusable book. However,
the proof on equivalence of permutations is interesting because I base the
proof on simple equality reasoning.

|#

(defun memberp (e x)
  (if (endp x) nil
    (if (equal e (first x)) T
      (memberp e (rest x)))))

(defun my-del (e x)
  (if (endp x) nil
    (if (equal e (first x))
	(rest x)
      (cons (first x) (my-del e (rest x))))))

(defun perm (x y)
  (if (endp x) (endp y)
    (and (memberp (first x) y)
	 (perm (rest x) (my-del (first x) y)))))

;; To prove properties of perm however, we take resort to a completely
;; different function which we call how-many


(defun how-many (e x)
   (if (endp x) 0
    (+ (if (equal e (first x)) 1 0)
       (how-many e (rest x)))))


(local
(defthm how-many-same-my-del-reduction
   (implies (memberp e x)
	    (equal (how-many e (my-del e x)) (1- (how-many e x)))))
)


(local
(defthm how-many-diff-my-del-reduction
   (implies (not (equal e f))
	    (equal (how-many e (my-del f y)) (how-many e y))))
)


(defthm perm-implies-how-many-equal
   (implies (perm x y)
            (equal (how-many e x) (how-many e y))))

;; The following has been added by Matt K. to account for a mod to ACL2 v2-8
;; that does better matching for calls of equivalence relations against the
;; current context.  Once we prove (defequiv perm), the original version of
;; perm-implies-how-many-equal above can cause looping because of the better
;; matching.  The one just below avoids rewriter loop during proof of (defcong
;; perm perm (append x y) 1)).  If however it is proved just before that
;; defcong, we still get a loop.  I have not investigated this issue further;
;; I'm content to know that the syntaxp test preserves the pre-v-2-8 behavior.
(defthmd perm-implies-how-many-equal-new
   (implies (and (perm x y)
                 (syntaxp (not (term-order x y))))
            (equal (how-many e x) (how-many e y)))
   :hints (("Goal" :by perm-implies-how-many-equal)))

(defun falsifier-perm (x y)
   (if (endp x)
       (if (endp y) nil
	 (first y))
     (if (not (equal (how-many (first x) x)
		     (how-many (first x) y)))
	 (first x)
       (falsifier-perm (rest x) (my-del (first x) y)))))


(defthm falsifier-witnesses-for-how-many-in-perm
   (implies (equal
	     (how-many (falsifier-perm x y) x)
	     (how-many (falsifier-perm x y) y))
	    (perm x y)))

(in-theory (disable falsifier-perm))

(defequiv perm)

(in-theory (e/d (perm-implies-how-many-equal-new) (perm-implies-how-many-equal)))

;; Now that we know perm is an equivalence we will try to reason about and
;; prove congruence rules for perm. This will be useful when we reason about
;; perm later.


(defthm how-many-append-reduction
  (equal (how-many e (append x y))
         (+ (how-many e x)
            (how-many e y))))


(defcong perm perm (append x y) 1)
(defcong perm perm (append x y) 2)
(defcong perm perm (cons e x) 2)

;; The following theorem is a fact about perm, that we use in admitting a qsort
;; algorithm we wrote...

(defthm perm-len-reduction
  (implies (perm x y)
           (equal (len x)
                  (len y)))
  :rule-classes :forward-chaining)


