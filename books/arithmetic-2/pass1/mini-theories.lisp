; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;
;; mini-theories.lisp
;;

(in-package "ACL2")

(local (include-book "basic-arithmetic"))

(local (include-book "inequalities"))

(local (include-book "prefer-times"))

(local (include-book "expt"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some proofs of linear equalities don't work when presented as
; equalities because they need to be proved by linear arithmetic,
; but linear arithmetic only works at the literal level.  This
; lemma allows you to state the equality as an equality rewrite
; rule, but breaks the equality into literals for the proof.


(defthm rewrite-linear-equalities-to-iff
   (equal (equal (< w x) (< y z))
          (iff (< w x) (< y z))))

(in-theory (disable rewrite-linear-equalities-to-iff))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See the note above equal-/ in basic-arithmetic.lisp.

(encapsulate
 ()

 (local
  (defthm Uniqueness-of-*-inverses-lemma-2
    (equal (equal (* x y)
                  1)
           (and (not (equal x 0))
                (acl2-numberp x)
                (equal y (/ x))))))

 (defthm Uniqueness-of-*-inverses
   (equal (equal (* x y)
                 1)
          (and (not (equal (fix x) 0))
               (equal y (/ x))))
   :hints (("Goal" :in-theory (disable equal-/)))))

(in-theory (disable Uniqueness-of-*-inverses))

;; This, and the inverse for exponents-add, should use
;; a macro to enforce the theory invariant more fully.

(theory-invariant
 (not (and (active-runep '(:rewrite Uniqueness-of-*-inverses))
           (active-runep '(:rewrite equal-/)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm expts-add-aggressive
  (implies (and (integerp i)
		(integerp j))
	   (equal (expt x (+ i j))
		  (if (equal (+ i j) 0)
		      1
		      (if (equal (fix x) 0)
			  0
			  (* (expt x i) (expt x j)))))))

(defthm expts-add-inverse
  (implies (and (integerp i)
		(integerp j))
	   (equal (* (expt x i) (expt x j))
		  (if (and (equal i 0)
			   (equal j 0))
		      1
		      (if (equal (fix x) 0)
			  0
			  (expt x (+ i j)))))))

(in-theory (disable expts-add-aggressive expts-add-inverse))

