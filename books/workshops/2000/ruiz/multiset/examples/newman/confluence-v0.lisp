;;; confluence-v0.lisp
;;; Church-Rosser and normalizing abstract reductions.
;;; Definition, properties and decidability
;;; *** We prove here the same properties than
;;; *** confluence.lisp, but we extend here our language to talk about
;;; *** reducibility, by means of the function (reducible x)
;;; Created: 10-6-99 Last Revision: 06-10-2000
;;; =======================================================

;;; To certify this book:
#|
(in-package "ACL2")


(defconst *abstract-proofs-exports*
  '(last-elt r-step direct operator elt1 elt2 r-step-p make-r-step
    first-of-proof last-of-proof steps-up steps-down steps-valley
    proof-before-valley proof-after-valley inverse-r-step inverse-proof
    local-peak-p proof-measure proof-before-peak proof-after-peak
    local-peak peak-element))

(defconst *cnf-package-exports*
  (union-eq *acl2-exports*
	    (union-eq
	     *common-lisp-symbols-from-main-lisp-package*
	     *abstract-proofs-exports*)))

(defpkg "CNF" *cnf-package-exports*)

(certify-book "confluence-v0" 3)
|#

;;;
(in-package "CNF")
(include-book "abstract-proofs")

;;; ********************************************************************
;;; A FORMALIZATION OF NORMALIZING AND CHURCH-ROSSER ABSTRACT REDUCTIONS
;;; ********************************************************************

;;; ********* IMPORTANT REMARK:

;;; We formalize here normalizing and Church-Rosser reduction relations,
;;; and show decidability of its equivalence closure. We do the same
;;; thing in confluence.lisp. But unlike there, we extend our language
;;; by a function called reducible, supposed to return a legal operator
;;; for every input, whenever it exists.
;;; The main advantage of this presentation is clarity. The main
;;; disadvantage comes from a theoretical point of view. The results in
;;; confluence.lisp are stronger since we can show decidability without
;;; having an algorithm to check reducibility. That is the reason why we
;;; chose the presentation in confluence.lisp. But from a practical
;;; point of view there is no such distinction: we need anyway a function
;;; proof-irreducible, returning a proof connecting every element to an
;;; equivalent normal form. It's hard to think in one case in which we
;;; have such function and we do not have the reducibility test (for
;;; example, if we think in a noetherian reduction, to define
;;; proof-irreducible, we need a reducibility test, as we will show in
;;; local-confluence.lisp)

;;; ============================================================================
;;; 1. Definition of a normalizing and (CR) abstract reduction
;;; ============================================================================

(encapsulate
 ((legal (x u) boolean)
  (reduce-one-step (x u) element)
  (reducible (x) boolean)
  (transform-to-valley (x) valley-proof)
  (proof-irreducible (x) proof))

 (local (defun legal (x u) (declare (ignore x u)) nil))
 (local (defun reduce-one-step (x u) (+ x u)))
 (local (defun reducible (x) (declare (ignore x)) nil))

 (defthm legal-reducible-1
   (implies (reducible x) (legal x (reducible x))))

 (defthm legal-reducible-2
   (implies (not (reducible x)) (not (legal x u))))

 (defun proof-step-p (s)
   (let ((elt1 (elt1 s)) (elt2 (elt2 s))
	 (operator (operator s)) (direct (direct s)))
     (and (r-step-p s)
	  (implies direct (and (legal elt1  operator)
			       (equal (reduce-one-step elt1 operator)
				      elt2)))
	  (implies (not direct) (and (legal elt2 operator)
				     (equal (reduce-one-step elt2 operator)
					    elt1))))))

 (defun equiv-p (x y p)
   (if (endp p)
       (equal x y)
       (and (proof-step-p (car p))
	    (equal x (elt1 (car p)))
	    (equiv-p (elt2 (car p)) y (cdr p)))))

 (local (defun transform-to-valley (x) (declare (ignore x)) nil))

 (defthm Chuch-Rosser-property
   (let ((valley (transform-to-valley p)))
     (implies (equiv-p x y p)
	      (and (steps-valley valley)
		   (equiv-p x y valley)))))

 (local (defun proof-irreducible (x) (declare (ignore x)) nil))

 (defthm normalizing
   (let* ((p-x-y (proof-irreducible x))
	  (y (last-of-proof x p-x-y)))
     (and (equiv-p x y p-x-y)
	  (not (reducible y))))))

;;; ----------------------------------------------------------------------------
;;; 1.1 Useful rules
;;; ----------------------------------------------------------------------------

;;; Two useful rewrite rules about normalizing

(local
 (defthm normalizing-not-consp-proof-irreducible
   (implies (not (consp (proof-irreducible x)))
	    (not (reducible x)))
   :hints (("Goal" :use (:instance normalizing)))))

(local
 (defthm normalizing-consp-proof-irreducible
   (let ((p-x-y (proof-irreducible x)))
     (implies (consp p-x-y)
	      (and (equiv-p x (elt2 (last-elt p-x-y)) p-x-y)
		   (not (reducible (elt2 (last-elt p-x-y)))))))
   :hints (("Goal" :use (:instance normalizing)))))

;;; Since equiv-p is "infected", we have to specify the induction scheme.
;;; Suggested by M. Kaufman

(local
 (defun induct-equiv-p (x p) (declare (ignore x))
   (if (endp p)
       t
     (induct-equiv-p (elt2 (car p)) (cdr p)))))

(local
 (defthm equiv-p-induct t
   :rule-classes
   ((:induction :pattern (equiv-p x y p)
	       :condition t
	       :scheme (induct-equiv-p x p)))))

;;; The first and the last element of a proof

(local
 (defthm first-element-of-equivalence
   (implies (and (equiv-p x y p) (consp p))
	    (equal (elt1 (car p)) x))))

(local
 (defthm last-elt-of-equivalence
   (implies (and (equiv-p x y p) (consp p))
	    (equal (elt2 (last-elt p)) y))))


;;; ---------------------------------------------------------------------------
;;; 1.2 equiv-p is an equivalence relation (the least containing the reduction)
;;; ---------------------------------------------------------------------------

;;; To be confident of the definition of equiv-p we show that equiv-p is
;;; the least equivalence relation containing the reduction steps.

;;; REMARK: To say it properly, we show that the relation
;;; "exists p such that (equiv-p x y p)" is an equivalence relation.

;;; An useful rule to deal with concatenation of proofs
(local
 (defthm proof-append
   (implies (equal z (last-of-proof x p1))
	    (equal (equiv-p x y (append p1 p2))
		   (and (equiv-p x z p1)
			(equiv-p z y p2))))))

;;; The properties of equivalence relations are met by equiv-p

(defthm equiv-p-reflexive
  (equiv-p x x nil))

(defthm equiv-p-symmetric
  (implies (equiv-p x y p)
	   (equiv-p y x (inverse-proof p))))

(defthm equiv-p-transitive
  (implies (and (equiv-p x y p1)
		(equiv-p y z p2))
	   (equiv-p x z (append p1 p2)))
  :rule-classes nil)

;;; REMARK: We have an "algebra" of proofs:
;;;   - append for the concatenation of proofs
;;;   - inverse-proof is already defined in abstract-proofs.lisp
;;;   - nil is the identity.

;;; Obviously, the reduction relaton is contained in equiv-p

(defthm equiv-p-containd-reduction
  (implies (legal x op)
	   (equiv-p x (reduce-one-step x op)
		   (list
		    (make-r-step
		     :elt1 x
		     :elt2 (reduce-one-step x op)
		     :direct t
		     :operator op)))))


;;; Let us assume that we have a relation eqv of equivalence, containing
;;; the reduction steps. Let us show that it contains equiv-p


(local
 (encapsulate
  ((eqv (t1 t2) boolean))

  (local (defun eqv (t1 t2) (declare (ignore t1 t2)) t))

  (defthm eqv-contains-reduction
    (implies (legal x op)
             (eqv x (reduce-one-step x op))))

  (defthm eqv-reflexive
    (eqv x x))

  (defthm eqv-symmetric
    (implies (eqv x y) (eqv y x)))

  (defthm eqv-transitive
    (implies (and (eqv x y) (eqv y z))
            (eqv x z)))))


(local
 (defthm equiv-p-the-least-equivalence-containing-reduction
   (implies (equiv-p x y p)
            (eqv x y))
   :hints (("Subgoal *1/3" :use
	    (:instance eqv-transitive (y (elt2 (car p)))
		       (z y))
	    :in-theory (disable eqv-transitive)))))



;;; ----------------------------------------------------------------------------
;;; 1.3 There are no equivalent and distinct normal forms
;;; ----------------------------------------------------------------------------

;;; Two lemmas

(local
  (defthm reducible-steps-up
    (implies (and  (consp p) (steps-up p)
		   (not (reducible y)))
 	    (not (equiv-p x y p)))))


(local
 (defthm two-ireducible-connected-by-a-valley-are-equal
   (implies (and (steps-valley p)
 		 (equiv-p x y p)
 		 (not (reducible x))
 		 (not (reducible y)))
 	    (equal x y))
   :rule-classes nil))

;;; And the theorem

(local
  (defthm if-confluent--two-ireducible-connected-are-equal
    (implies (and (equiv-p x y p)
		  (not (reducible x))
		  (not (reducible y)))
 	    (equal x y))
    :rule-classes nil
    :hints (("Goal" :use (:instance
 			  two-ireducible-connected-by-a-valley-are-equal
 			  (p (transform-to-valley p)))))))


;;; ============================================================================
;;; 2. Decidability of Church-Rosser and normalizing redutions
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 2.1 Normal forms, definition and fundamental properties.
;;; ----------------------------------------------------------------------------

(defun normal-form (x)
  (last-of-proof x (proof-irreducible x)))

(local
 (defthm irreducible-normal-form
   (not (reducible (normal-form x)))))

(local
 (defthm proof-irreducible-proof
   (equiv-p x (normal-form x) (proof-irreducible x))))

(local
 (defthm proof-irreducible-atom-normal-form
   (implies (atom (proof-irreducible x))
	    (equal (normal-form x) x))))

(local
 (defthm proof-irreducible-consp-normal-form
   (implies (consp (proof-irreducible x))
	    (equal (elt2 (last-elt (proof-irreducible x))) (normal-form x)))))


;;; We can disable normal-form (its fundamental properties are rewrite
;;; rules).
(local (in-theory (disable normal-form)))

;;; ----------------------------------------------------------------------------
;;; 2.2  A decision algorithm for [<-reduce-one-step->]*
;;; ----------------------------------------------------------------------------


(defun provably-equivalent (x y)
  (equal (normal-form x) (normal-form y)))

;;; ············································································
;;; 2.2.1 Completeness
;;; ············································································

;;; A proof between normal forms
(local
 (defun make-proof-between-normal-forms (x y p)
   (append (inverse-proof (proof-irreducible x))
	   p
	   (proof-irreducible y))))

;;;; Some needed lemmas

(local
 (defthm consp-inverse-proof
   (iff (consp (inverse-proof p))
	(consp p))))

(local
 (defthm last-elt-append
   (implies (consp p2)
	    (equal (last-elt (append p1 p2)) (last-elt p2)))))
(local
 (defthm last-elt-inverse-proof
   (implies (consp p)
	    (equal (last-elt (inverse-proof p))
		   (inverse-r-step (car p))))))

(local
 (defthm first-element-of-proof-irreducible
   (implies (consp (proof-irreducible x))
	    (equal (elt1 (car (proof-irreducible x))) x))
   :hints (("Goal" :use ((:instance
			  first-element-of-equivalence
			  (y (normal-form x)) (p (proof-irreducible
						   x))))))))
;;; The main lemma for completeness: the proof constructed is a proof
;;; indeed.
(local
 (defthm make-proof-between-normal-forms-indeed
   (implies (equiv-p x y p)
	    (equiv-p (normal-form x)
		     (normal-form y)
		     (make-proof-between-normal-forms x y p)))))

(local (in-theory (disable make-proof-between-normal-forms)))

;;; COMPLETENESS

(defthm provably-equivalent-complete
  (implies (equiv-p x y p)
	   (provably-equivalent x y))
  :hints (("Goal" :use ((:instance
			 if-confluent--two-ireducible-connected-are-equal
			 (x (normal-form x))
			 (y (normal-form y))
			 (p (make-proof-between-normal-forms x y p)))))))


;;; ············································································
;;; 2.2.1 Soundness
;;; ············································································

;;; A proof between x and y (if their normal forms are equal)

(defun make-proof-common-n-f (x y)
   (append (proof-irreducible x) (inverse-proof (proof-irreducible y))))

;;; SOUNDNESS

(defthm provably-equivalent-sound
  (implies (provably-equivalent x y)
	   (equiv-p x y (make-proof-common-n-f x y)))
  :hints (("Goal" :use (:instance
			       equiv-p-symmetric
			       (x y)
			       (y (normal-form y))
			       (p (proof-irreducible y))))))

;;; REMARK: :use is needed due to a weird behaviour that sometimes of
;;; ACL2 has with equalities in hypotesis.







