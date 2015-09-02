;;; confluence.lisp
;;; Church-Rosser and normalizing abstract reductions.
;;; Created: 06-10-2000 Last Revision: 06-03-2001
;;; =============================================================================

#| To certify this book:

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

(certify-book "confluence" 3)

|#

(in-package "CNF")

(include-book "abstract-proofs")

;;; ********************************************************************
;;; A FORMALIZATION OF NORMALIZING AND CHURCH-ROSSER ABSTRACT REDUCTIONS
;;; ********************************************************************

;;; See chapter 2 of the book "Term Rewriting and all that", Baader &
;;; Nipkow, 1998.


;;; ============================================================================
;;; 1. Definition of a normalizing and (CR) abstract reduction
;;; ============================================================================



(encapsulate
 ((q (x) boolean)
  (legal (x u) boolean)
  (reduce-one-step (x u) element)
  (transform-to-valley (x) valley-proof)
  (proof-irreducible (x) proof))

;;; We define an abstract reduction relation using three functions:
;;; - q is the predicate defining the set where the reduction relation
;;;   is defined.
;;; - reduce-one-step is the function applying one step of reduction,
;;;   given an element an an operator. Note that elements are reduced by
;;;   means of the action of "abstract" operators.
;;; - legal is the function testing if an operator can be applied to a
;;;   term.

 (local (defun q (x) (declare (ignore x)) t))
 (local (defun legal (x u) (declare (ignore x u)) nil))
 (local (defun reduce-one-step (x u) (+ x u)))

;;; With these functions one can define what is a legal proof step: a
;;; r-step-p structure (see abstract-proofs.lisp) such that one the
;;; elements is obtained applying a reduction step to the other (using a
;;; legal operator).

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

;;; And now we can define the equivalence closure of the reduction
;;; relation, given by equiv-p: two elements are equivalent if there
;;; exists a list of concatenated legal proof-steps (a PROOF) connecting
;;; the elements, such that every element involved in the proof is in
;;; the set defined by q:

 (defun equiv-p (x y p)
   (if (endp p)
       (and (equal x y) (q x))
       (and
	(q x)
	(proof-step-p (car p))
	(equal x (elt1 (car p)))
	(equiv-p (elt2 (car p)) y (cdr p)))))


;;; To state the Church-Rosser property of the reduction relation, we
;;; reformulate the propery in terms of proofs: "for every proof there
;;; is an equivalent valley proof". The function transform-to-valley is
;;; assumed to return this equivalente valley proof.

 (local (defun transform-to-valley (x) (declare (ignore x)) nil))

 (defthm Chuch-Rosser-property
   (let ((valley (transform-to-valley p)))
     (implies (equiv-p x y p)
	      (and (steps-valley valley)
		   (equiv-p x y valley)))))

;;; The normalizing property of the reduction relation is defined also
;;; in terms of proofs: for every element in the set defined by q there
;;; is a proof connecting it to an irreducible element (where
;;; irreducible means here that there is no legal operator which can be
;;; applied)

 (local (defun proof-irreducible (x) (declare (ignore x)) nil))

 (defthm normalizing
   (implies (q x)
	    (let* ((p-x-y (proof-irreducible x))
		   (y (last-of-proof x p-x-y)))
	      (and (equiv-p x y p-x-y)
		   (not (legal y op)))))))



;;; We think all these properties are a reasonable abstraction of every
;;; normalizing and Church-Rosser reduction relation.

;;; ----------------------------------------------------------------------------
;;; 1.1 Useful rules
;;; ----------------------------------------------------------------------------

;;; The following are two useful rewrite rules about the normalizing
;;; property.

(local
 (defthm normalizing-not-consp-proof-irreducible
   (implies (and (q x) (not (consp (proof-irreducible x))))
	    (not (legal x op)))
   :hints (("Goal" :use normalizing))))

(local
 (defthm normalizing-consp-proof-irreducible
   (let ((p-x-y (proof-irreducible x)))
     (implies (and (q x) (consp p-x-y))
	      (and (equiv-p x (elt2 (last-elt p-x-y)) p-x-y)
		   (not (legal (elt2 (last-elt p-x-y)) op)))))
   :hints (("Goal" :use normalizing))))


;;; Since equiv-p is "infected" (see subversive-recursions in the ACL2
;;; manual), we have to specify the induction scheme by means of a rule.

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

;;; The first and the last element of a non-empty proof

(local
 (defthm first-element-of-equivalence
   (implies (and (equiv-p x y p) (consp p))
	    (equal (elt1 (car p)) x))))

(local
 (defthm last-elt-of-equivalence
   (implies (and (equiv-p x y p) (consp p))
	    (equal (elt2 (last-elt p)) y))))

;;; If x and y are related by equiv-p, then they are in the set defined
;;; by q

(local
 (defthm equiv-p-is-in-p-f-c
   (implies (equiv-p x y p)
	    (and (q x) (q y)))
   :rule-classes :forward-chaining))

;;; ---------------------------------------------------------------------------
;;; 1.2 equiv-p is an equivalence relation (the least containing the reduction)
;;; ---------------------------------------------------------------------------

;;; To be confident of the definition of equiv-p we show that equiv-p is
;;; the least equivalence relation (in the set defined by q) containing
;;; reduction steps.

;;; REMARK: To say it properly, we show that for the relation
;;; "exists p such that (equiv-p x y p)".

;;; REMARK: Note that in order to prove this property we do
;;; not need the properties confluence and normalizing: this is a
;;; general result that can be derived only from the definition of
;;; equiv-p and proof-step-p.


;;; An useful rule to deal with concatenation of proofs
(local
 (defthm proof-append
   (implies (equal z (last-of-proof x p1))
	    (equal (equiv-p x y (append p1 p2))
		   (and (equiv-p x z p1)
			(equiv-p z y p2))))))

;;; 1.2.1. equiv-p is an equivalence relation
;;; ·········································

;;; The properties of equivalence relations (in q) are met by equiv-p:

(defthm equiv-p-reflexive
  (implies (q x)
	   (equiv-p x x nil)))

(defthm equiv-p-symmetric
  (implies (equiv-p x y p)
	   (equiv-p y x (inverse-proof p))))

(defthm equiv-p-transitive
  (implies (and (equiv-p x y p1)
		(equiv-p y z p2))
	   (equiv-p x z (append p1 p2)))
  :rule-classes nil)

;;; NOTE: We have an "algebra" of proofs:
;;;   - append for the concatenation of proofs
;;;   - inverse-proof is already defined in abstract-proofs.lisp
;;;   - nil is the identity.


;;; 1.2.2. equiv-p contains the reduction relation
;;; ··············································

(defthm equiv-p-contains-reduction
  (implies (and (q x)
		(legal x op)
		(q (reduce-one-step x op)))
	   (equiv-p x (reduce-one-step x op)
		    (list
		     (make-r-step
		      :elt1 x
		      :elt2 (reduce-one-step x op)
		      :direct t
		      :operator op)))))


;;; 1.2.3. equiv-p is the least equivalence relation with the above
;;; properties
;;; ································································

;;; Let us assume that we have a relation eqv of equivalence in the set
;;; defined by q, containing the reduction steps, and let us show that
;;; it contains equiv-p

(encapsulate
 ((eqv (t1 t2) boolean))

 (local (defun eqv (t1 t2) (declare (ignore t1 t2)) t))

 (defthm eqv-contains-reduction
   (implies (and (q x)
		 (legal x op)
		 (q (reduce-one-step x op)))
	    (eqv x (reduce-one-step x op))))

 (defthm eqv-reflexive
   (implies (q x) (eqv x x)))

 (defthm eqv-symmetric
   (implies (and (q x) (eqv x y) (q y))
	    (eqv y x)))

 (defthm eqv-transitive
   (implies (and (q x) (q y) (q z) (eqv x y) (eqv y z))
            (eqv x z))))

;;; Then eqv contains equiv-p

(defthm equiv-p-the-least-equivalence-containing-reduction
  (implies (equiv-p x y p)
	   (eqv x y))
  :hints (("Subgoal *1/3"
	   :use
	   (:instance eqv-transitive
		      (y (elt2 (car p))) (z y)))))


;;; ----------------------------------------------------------------------------
;;; 1.3 There are no equivalent and distinct normal forms
;;; ----------------------------------------------------------------------------

;;; Two lemmas

(local
  (defthm reducible-steps-up
    (implies (and  (consp p) (steps-up p)
		   (not (legal y (operator (last-elt p)))))
 	    (not (equiv-p x y p)))))


(local
 (defthm two-ireducible-connected-by-a-valley-are-equal
   (implies (and (steps-valley p)
		 (equiv-p x y p)
		 (not (legal x (operator (first p))))
		 (not (legal y (operator (last-elt p)))))
	    (equal x y))
   :rule-classes nil))

;;; And the theorem

(local
 (defthm if-CR--two-ireducible-connected-are-equal
   (implies (and (equiv-p x y p)
		 (not (legal x (operator (first (transform-to-valley p)))))
		 (not (legal y (operator (last-elt (transform-to-valley p))))))
	    (equal x y))
   :rule-classes nil
   :hints (("Goal" :use (:instance
			  two-ireducible-connected-by-a-valley-are-equal
			  (p (transform-to-valley p)))))))

;;; REMARK: although this lemma is weaker than the statement "every two
;;; equivalent normal forms are equal" (we cannot state this in our
;;; current language, see confluence-v0.lisp), it is a tool to show
;;; equality of every two particular elements known to be equivalent and
;;; irreducible, as we will see.

;;; ============================================================================
;;; 2. Decidability of Church-Rosser and normalizing redutions
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 2.1 Normal forms, definition and fundamental properties.
;;; ----------------------------------------------------------------------------


;;; The normal form of an element is the las element in the proof
;;; obtained by the function proof-irreducible.

(defun normal-form (x) (last-of-proof x (proof-irreducible x)))


;;; No operator can be applied to (normal-form x) (it is an irreducible
;;; element)

(local
 (defthm irreducible-normal-form
   (implies (q x)
	    (not (legal (normal-form x) op)))))

;;; And (normal-form x) is equivalent to x (the proof is given by
;;; proof-irreducible).
(local
 (defthm equivalent-proof-n-f
   (implies (q x)
	    (equiv-p x (normal-form x) (proof-irreducible x)))))


;;; And two useful rewrite rules, showing how normal-form is related to
;;; proof-irreducible.

(local
 (defthm proof-irreducible-atom-normal-form
   (implies (atom (proof-irreducible x))
	    (equal (normal-form x) x))))

(local
 (defthm proof-irreducible-consp-normal-form
   (implies (consp (proof-irreducible x))
	    (equal (elt2 (last-elt (proof-irreducible x))) (normal-form x)))))


;;; We can disable normal-form (its fundamental properties are now
;;; rewrite rules):

(local (in-theory (disable normal-form)))


;;; ----------------------------------------------------------------------------
;;; 2.2  A decision algorithm for [<-reduce-one-step->]*
;;; ----------------------------------------------------------------------------

;;; We define a decision procedure for the equivalence closure of the
;;; reduction relation. The decision procedure (provided normal-form is
;;; computable) is: we simply test if normal-forms are equal.

(defun r-equiv (x y)
  (equal (normal-form x) (normal-form y)))

;;; ············································································
;;; 2.2.1 Completeness
;;; ············································································

;;; We want to show that if (equiv-p x y p) the the normal forms of x
;;; and y are the same. The idea is the following: if we have a proof
;;; between x and y, we can build a proof between (normal-form x) and
;;; (normal-form y). But then, from the theorem
;;; if-CR--two-ireducible-connected-are-equal and the fact that
;;; normal-forms are irreducible we can conclude that both normal-forms
;;; are equal.

;;; This is the proof between (normal-form x) and (normal-form y).
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
   (implies (and (q x) (consp (proof-irreducible x)))
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

;;; And the intended theorem:
;;; COMPLETENESS

(defthm r-equiv-complete
  (implies (equiv-p x y p)
	   (r-equiv x y))
  :hints (("Goal" :use ((:instance
			 if-CR--two-ireducible-connected-are-equal
			 (x (normal-form x))
			 (y (normal-form y))
			 (p (make-proof-between-normal-forms x y p)))))))


;;; ············································································
;;; 2.2.1 Soundness
;;; ············································································

;;; We want to prove that if x and y have common normal forms then there
;;; is a proof between x and y.

;;; We build such proof between x and y (if their normal forms are
;;; equal), given by the following function:

(defun make-proof-common-n-f (x y)
   (append (proof-irreducible x) (inverse-proof (proof-irreducible y))))

;;; And the intended theorem.
;;; SOUNDNESS

(defthm r-equiv-sound
  (implies (and (q x) (q y) (r-equiv x y))
	   (equiv-p x y (make-proof-common-n-f x y)))
  :hints (("Subgoal 3"
	   :use ((:instance
		  equiv-p-symmetric
		  (x y)
		  (y (normal-form y))
		  (p (proof-irreducible y)))
		 (:instance equivalent-proof-n-f
			    (x y))))))

;;; REMARK: :use is needed due to a weird behaviour that sometimes
;;; ACL2 has with equalities in hypotesis.








