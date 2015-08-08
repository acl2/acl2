;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 5.

;; This exercise is challenging because more than
;;  rewriting is required for manipulating equalities.
;;  That is, during the proofs, expressions must often be
;;  made more complicated before they can be simplified.

;;Part A.
;; Axiomatize, in ACL2, an arbitrary ring with unity.
;; Specifically, use encapsulate to introduce and constrain ACL2
;; versions of the following functions:
;;  o The predicate Rp. This is the test for membership in the
;;    Ring, i.e., X is in R iff Rp(X) is not nil.
;;  o The operations +_r, *_r, -_r, and the constants 0_r and 1_r.
;;    These satisfy the closure, associative, distributive,
;;    identity, and right inverse axioms for a ring with unity.

;;Part B.
;; Verify, in ACL2, that in any ring with unity, the additive
;; identity and additive inverses behave as expected on the left
;; as well as on the right. That is, prove for all X in R,
;; (-_r X) +_r X = 0_r and 0_r +_r X = X.
;; Hint: Show 0_r is the only additive idempotent in the ring.
;; That is, prove if X +_r X = X, then X = 0_r.

;;Part C.
;; Verify, in ACL2, that addition is always commutative in any
;; ring with unity. That is, prove for all X, Y in R,
;; X +_r Y = Y +_r X.
;; Hint. Consider the two ways the distributive axioms can be used
;; to expand (X +_r Y) *_r (1_r +_r 1_r).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer to all parts.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

;;------------------
;; Answer to Part A:
(encapsulate
 ;; Signatures:
 ((Rp (x) t)
  (+_r (x y) t)
  (*_r (x y) t)
  (-_r (x) t)
  (0_r () t)
  (1_r () t))
 ;;--------------
 ;; Provide witnesses:
 (local
  (defun
    Rp (x)
    (rationalp x)))

 (local
  (defun
    +_r (x y)
    (+ x y)))

 (local
  (defun
    *_r (x y)
    (* x y)))

 (local
  (defun
    -_r (x)
    (- x)))

 (local
  (defun
    0_r ()
    0))

 (local
  (defun
    1_r ()
    1))
 ;;----------------
 ;; Consistent
 ;;  Ring with Unity axioms:
 (defthm
     Closure-Laws
     (and (implies (Rp x)
		   (and (implies (Rp y)
				 (and (Rp (+_r x y))
				      (Rp (*_r x y))))
			(Rp (-_r x))))
	  (Rp (0_r))
	  (Rp (1_r))))

 (defthm
     Associative-Laws
     (implies (and (Rp x)
		   (Rp y)
		   (Rp z))
	      (and (equal (+_r (+_r x y) z)
			  (+_r x (+_r y z)))
		   (equal (*_r (*_r x y) z)
			  (*_r x (*_r y z))))))

 (defthm
     Distributive-Laws
     (implies (and (Rp x)
		   (Rp y)
		   (Rp z))
	      (and (equal (*_r x (+_r y z))
			  (+_r (*_r x y)
			       (*_r x z)))
		   (equal (*_r (+_r x y) z)
			  (+_r (*_r x z)
			       (*_r y z))))))

 (defthm
     Identity-Laws
     (implies (Rp x)
	      (and (equal (+_r x (0_r)) x)
		   (equal (*_r (1_r) x) x)
		   (equal (*_r x (1_r)) x))))

 (defthm
     Right-Inverse-Law
     (implies (Rp x)
	      (equal (+_r x (-_r x)) (0_r))))
 ) ;; End encapsulate


;;------------------
;; Answer to Part B:
(defthm
    Only-+_r-idempotent-is-0_r
    (implies (and (Rp x)
		  (equal (+_r x x) x))
	     (equal x (0_r)))
   :rule-classes nil
   :hints (("Goal"
	    :use ((:instance
		   (:theorem
		    (implies (equal a b)
			     (equal (+_r a c)
				    (+_r b c))))
		   (a (+_r x x))
		   (b x)
		   (c (-_r x)))
		  (:instance
		   Associative-Laws
		   (y x)(z (-_r x)))))))

(defthm
    Cancellation-version-1
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r x (+_r (-_r x) y))
		    (+_r (0_r) y)))
    :hints (("Goal"
	     :use ((:theorem
		    (implies (and (Rp x)
				  (Rp y))
			     (equal (+_r (+_r x (-_r x)) y)
				    (+_r (0_r) y))))
		   (:instance
		    Associative-Laws
		    (y (-_r x))(z y))))))

(defthm
    Identity-version-1
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r x (+_r (0_r) y))
		    (+_r x y)))
    :hints (("Goal"
	     :use ((:theorem
		    (implies (and (Rp x)
				  (Rp y))
			     (equal (+_r (+_r x (0_r)) y)
				    (+_r x y))))
		   (:instance
		    Associative-Laws
		    (y (0_r))(z y))))))

(defthm
    Left-Inverse-Law
    (implies (Rp x)
	     (equal (+_r (-_r x) x)
		    (0_r)))
    :hints (("Goal"
	     :use (:instance
		   Only-+_r-idempotent-is-0_r
		   (x (+_r (-_r x) x))))))

(defthm
    Left-Identity-Law
    (implies (Rp x)
	     (equal (+_r (0_r) x) x))
    :hints (("Goal"
	     :use (:theorem
		   (implies (Rp x)
			    (equal (+_r (0_r) x)
				   (+_r (+_r x (-_r x)) x)))))
	    ("Subgoal 2"
	     :in-theory (disable Right-Inverse-Law))))


;;------------------
;; Answer to Part C:
(defthm
    Cancellation-version-2
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r (-_r x) (+_r x y))
		    y))
    :hints (("Goal"
	     :use ((:theorem
		    (implies (and (Rp x)
				  (Rp y))
			     (equal (+_r (+_r (-_r x) x) y)
				    (+_r (0_r) y))))
		   (:instance
		    Associative-Laws
		    (x (-_r x))(y x)(z y))))))

(defthm
    Equality-1
    (implies (and (Rp x)
		  (Rp y))
	     (equal (*_r (+_r x y)
			 (+_r (1_r) (1_r)))
		    (+_r x (+_r x (+_r y y)))))
    :rule-classes nil)

 (defthm
     Distributive-Laws
     (implies (and (Rp x)
		   (Rp y)
		   (Rp z))
	      (and (equal (*_r x (+_r y z))
			  (+_r (*_r x y)
			       (*_r x z)))
		   (equal (*_r (+_r x y) z)
			  (+_r (*_r x z)
			       (*_r y z))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This next theorem is one of the axioms.
;;  By restating the axiom here, I ensure
;;  that the left distributive rewrite rule
;;  is applied before the right distributive
;;  rule. Before this restatement, ACL2 applied
;;  the right rule before the left rule.
;; The order of the rewrite rules CAN affect the
;;  proofs.
(defthm
    Left-Distributive-Law
     (implies (and (Rp x)
		   (Rp y)
		   (Rp z))
	      (and (equal (*_r x (+_r y z))
			  (+_r (*_r x y)
			       (*_r x z))))))

(defthm
    Equality-2
    (implies (and (Rp x)
		  (Rp y))
	     (equal (*_r (+_r x y)
			 (+_r (1_r) (1_r)))
		    (+_r x (+_r y (+_r x y)))))
    :rule-classes nil)

(defthm
    Equality-3
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r x (+_r x (+_r y y)))
		    (+_r x (+_r y (+_r x y)))))
    :rule-classes nil
    :hints (("Goal"
	     :use (Equality-1 Equality-2))))

(defthm
    Equality-4
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r (-_r x)(+_r x (+_r x (+_r y y))))
		    (+_r (-_r x)(+_r x (+_r y (+_r x y))))))
    :rule-classes nil
    :hints (("Goal"
	     :use Equality-3)))

(defthm
    Equality-5
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r x (+_r y y))
		    (+_r y (+_r x y))))
    :rule-classes nil
    :hints (("Goal"
	     :use Equality-4)))

(defthm
    Equality-6
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r (+_r x (+_r y y))(-_r y))
		    (+_r (+_r y (+_r x y))(-_r y))))
    :rule-classes nil
    :hints (("Goal"
	     :use Equality-5)))

(defthm
    Commutative-Law-for-+_r
    (implies (and (Rp x)
		  (Rp y))
	     (equal (+_r x y)
		    (+_r y x)))
    :hints (("Goal"
	     :use Equality-6)))
