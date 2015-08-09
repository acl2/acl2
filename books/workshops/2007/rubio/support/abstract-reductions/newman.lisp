;;; newman.lisp
;;; A mechanical proof of Newman's lemma for abstract reduction relations
;;; Created: 6-8-99 Last revison: 07-03-2001
;;; ============================================================================

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

(defpkg "NWM" (cons 'multiset-diff *cnf-package-exports*))

(certify-book "newman" 3)

|#


(in-package "NWM")

(include-book "../multisets/defmul")

(include-book "abstract-proofs")


;;; *******************************************************************
;;; A MECHANICAL PROOF OF NEWMAN'S LEMMA:
;;; For terminating relations, local confluence implies
;;; confluence [see "Term Rewriting and all that..." (Baader & Nipkow),
;;; chapter 2, pp. 28-29]
;;; *******************************************************************

;;; ============================================================================
;;; 1. Formalizing the statement of the theorem
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 1.1 A noetherian and locally confluent reduction relation
;;; ----------------------------------------------------------------------------


(encapsulate
 ((rel (x y) booleanp)
  (q (x) booleanp)
  (fn (x) o-p)
  (legal (x u) boolean)
  (reduce-one-step (x u) element)
  (transform-local-peak (x) proof))


;;; A general noetherian partial order rel is (partially) defined. The
;;; function is well founded on the set defined by a predicate q, and fn
;;; is the order-preserving mapping from objects to ordinals. It will be
;;; used (see below) to justify noetherianity of the reduction relation,
;;; based on the following meta-theorem: "A reduction is noetherian iff
;;; it is contained in a noetherian partial order"

;;; REMARK: Transitivity is required, but this is not a real
;;; restriction, since a reduction is noetherian iff its included in a
;;; transitive and noetherian relation.  We need it because transitive
;;; closure, in general, is not decidable even if the relation is
;;; decidable, so we cannot define the transitive closure of a relation.

 (local (defun rel (x y) (declare (ignore x y)) nil))
 (local (defun fn (x) (declare (ignore x)) 1))
 (local (defun q (x) (declare (ignore x)) t))

 (defthm rel-well-founded-relation-on-q
   (and
    (implies (q x) (o-p (fn x)))
    (implies (and (q x) (q y) (rel x y))
	     (o< (fn x) (fn y))))
   :rule-classes (:well-founded-relation :rewrite))

 (defthm rel-transitive
   (implies (and (q x) (q y) (q z) (rel x y) (rel y z))
 	    (rel x z))
   :rule-classes nil)

;;; As in confluence.lisp, we define an abstract reduction relation
;;; using three functions:
;;; - q is the predicate defining the set where the reduction relation
;;;   is defined (introduced above).
;;; - reduce-one-step is the function applying one step of reduction,
;;;   given an element and an operator. Note that elements are reduced by
;;;   means of the action of "abstract" operators.
;;; - legal is the function testing if an operator can be applied to a
;;;   term.


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
;;; the set defined by q. In the book confluece.lisp is proved that
;;; equiv-p defines the least equivalence relation in the set defined by
;;; q, containing the reduction relation.


 (defun equiv-p (x y p)
   (if (endp p)
       (and (equal x y) (q x))
     (and
      (q x)
      (proof-step-p (car p))
      (equal x (elt1 (car p)))
      (equiv-p (elt2 (car p)) y (cdr p)))))

;;; Local confluence is reformulated in terms of proofs: "for every
;;; local-peak, there is an equivalent valley proof" This equivalent
;;; valley proof is returned by a function transform-local-peak:

 (local (defun transform-local-peak (x) (declare (ignore x)) nil))

 (defthm local-confluence
   (let ((valley (transform-local-peak p)))
     (implies (and (equiv-p x y p) (local-peak-p p))
              (and (steps-valley valley)
		   (equiv-p x y valley)))))

;;;  Noetherianity of the reduction relation, justified by inclusion in
;;;  the well founded relation rel: if we permorm one (legal) reduction
;;;  step in the set defined by q, then we obtain a smaller element
;;;  (with respect to rel):

 (defthm noetherian
   (implies (and (q x) (legal x u) (q (reduce-one-step x u)))
	    (rel (reduce-one-step x u) x))))


;;; We think all these properties are a reasonable abstraction of every
;;; noetherian and locally confluent reduction relation.


;;; A first theorem: irreflexivity of rel

;; Añadido para la 2.8
(defthm o<-irreflexive
  (not (o< x x)))


(local
 (defthm rel-irreflexive
   (implies (q x) (not (rel x x)))
   :hints (("Goal"
	    :in-theory (disable  rel-well-founded-relation-on-q)
	    :use (:instance rel-well-founded-relation-on-q
			     (y x))))))

;;; REMARK: e0-ord-irreflexive (in multiset.lisp) is needed


;;; ----------------------------------------------------------------------------
;;; 1.3 Our goal
;;; ----------------------------------------------------------------------------

;;; REMARK: We will prove that the reduction relation has the
;;; Church-Rosser property, instead of showing confluence (which is
;;; equivalent).

;;; Our definition of the Church-Rosser property (see confluence.lisp) is:
;;; (defthm Chuch-Rosser-property
;;;   (let ((valley (transform-to-valley p)))
;;;     (implies (equiv-p x y p)
;;;	      (and (steps-valley valley)
;;;		   (equiv-p x y valley)))))
;;; So our goal is to define transform-to-valley with these properties.


;;; ----------------------------------------------------------------------------
;;; 1.4 Some useful stuff
;;; ----------------------------------------------------------------------------


;;; Since equiv-p is "infected" (see subversive-recursions in the ACL2
;;; manual), we have to specify the induction scheme.  Suggested by
;;; M. Kaufman

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


;;; Proof-p: sometimes it will be useful to talk about proofs without
;;; mentioning equiv-p. Proof-p recognizes sequences of legal
;;; concatenated steps without mentioning endpoints.

(local
 (defun proof-p (p)
   (if (atom p)
       t
     (and (proof-step-p (car p)) (q (elt1 (car p))) (q (elt2 (car p)))
	  (if (atom (cdr p))
	      t
	    (and (equal (elt2 (car p)) (elt1 (cadr p)))
		 (proof-p (cdr p))))))))

;;;; Relation between proof-p y equiv-p

(local
 (defthm equiv-p-proof-p
   (implies (equiv-p x y p)
	    (proof-p p))))

;;; A rule without free variables (almost) expressing local conf.

(local
 (defthm local-confluence-w-f-v
   (implies (and (proof-p p) (local-peak-p p))
	    (and (steps-valley (transform-local-peak p))
		 (proof-p (transform-local-peak p))))
    :hints (("Goal" :use (:instance local-confluence
				    (x (elt1 (car p)))
				    (y (elt2 (last-elt p))))
	     :in-theory (disable local-confluence)))))

;;; ============================================================================
;;; 2. Towards the definition of transform-to-valley
;;; ============================================================================


(defun exists-local-peak (p)
  (cond ((or (atom p) (atom (cdr p))) nil)
	((and
	  (not (direct (car p)))
	  (direct (cadr p)))
	  (and (proof-step-p (car p))
	       (proof-step-p (cadr p))
	       (q (elt1 (car p)))
               (q (elt2 (car p))) (q (elt2 (cadr p)))
	       (equal (elt2 (car p)) (elt1 (cadr p)))))
	(t (exists-local-peak (cdr p)))))

(defun replace-local-peak (p)
  (cond ((or (atom p) (atom (cdr p))) nil)
	((and (not (direct (car p))) (direct (cadr p)))
	 (append (transform-local-peak (list (car p) (cadr p)))
		 (cddr p)))
	(t (cons (car p) (replace-local-peak (cdr p))))))


;;; The idea is to define a function like this (i.e. to replace local peaks
;;; iteratively until there are no local peaks left):

;(defun transform-to-valley (p)
;  (if (not (exists-local-peak p))
;      p
;    (transform-to-valley (replace-local-peak p))))

;;; A minor modification has to be done to the condition of the base case
;;; of this definition, as we will see. But the main point here is that,
;;; as expected, this function is not admitted without help from the
;;; user (the length of the proof (replace-local-peak p) may be greater
;;; than the length of p). So the hard part of the theorem is to provide
;;; that help as a suitable set of rules and hints, to get the admission
;;; of transform-to-valley.


;;; ============================================================================
;;; 3. Admission of transform-to-valley
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 3.1 A multiset measure
;;; ----------------------------------------------------------------------------


;;; We will lead the prover to the admission of the theorem by means of
;;; a multiset measure (following a hand proof by Klop).  The idea is to
;;; assign to every proof the multiset of elements involved in it. These
;;; multisets are compared w.r.t. the well-founded multiset relation
;;; induced by rel (mul-rel)

;;; We define the well-founded extension of rel to multisets.
;;; See defmul.lisp


; (acl2::defmul-components rel)
;The list of components is:
; (REL REL-WELL-FOUNDED-RELATION-ON-Q Q FN X Y)

(acl2::defmul (rel rel-well-founded-relation-on-q q fn x y)
	      :verify-guards t)

;;; This defmul call defines the well-founded multiset relation mul-rel,
;;; defined on multisets of elements satisfying q (defined by
;;; q-true-listp), induced by the well-founded relation rel.

;;; ----------------------------------------------------------------------------
;;; 3.2 Proof steps in the set defined by q.
;;; ----------------------------------------------------------------------------

;;; Our measure hint for the admission of transform-to-valley will be
;;; (see the definition of proof-measure in abstract-proofs.lisp) the
;;; proof-measure of the proof, and the well founded relation will be
;;; mul-rel. Note that mul-rel is known to be well-founded ONLY on
;;; multisets of elements satisfying q, so the recursion has only to be
;;; called for proofs such that its proof-measure is a set of elements
;;; satisfying q.

;;; With these considerations, our goal now is to define
;;; the following function, with the following measure and w.f. relation
;;; hints.

;(defun transform-to-valley (p)
;  (declare (xargs :measure (if (steps-q p) (proof-measure p) nil)
;		   :well-founded-relation mul-rel))
;  (if (and (steps-q p) (exists-local-peak p))
;      (transform-to-valley (replace-local-peak p))
;     p))

;;; where the function steps-q checks if we have a sequence of proof
;;; steps connecting elements satisfying q:

(defun steps-q (p)
  (if (endp p)
      t
    (and (r-step-p (car p))
	 (q (elt1 (car p)))
	 (q (elt2 (car p)))
	 (steps-q (cdr p)))))

;;; This property steps-q implies that proof-measure is an object
;;; representing a multiset where the well-founded relation is defined.

(local
 (defthm steps-q-implies-q-true-listp-proof-measure
   (implies (steps-q p)
	    (q-true-listp (proof-measure p)))))

;;; ----------------------------------------------------------------------------
;;; 3.2 The proof of the main lemma for admission of transform-to-valley
;;; ----------------------------------------------------------------------------

;;; In order to admit transform-to-valley, our main goal is:

;;; (defthm transform-to-valley-admission
;;;   (implies (exists-local-peak p)
;;; 	   (mul-rel (proof-measure (replace-local-peak p))
;;; 		    (proof-measure p)))
;;;   :rule-classes nil)

;;; REMARK: Note that we can even restrict p to be steps-q, but it is
;;; not needed, as we will see.

;;; This conjecture generates the following two goals:

;;; Subgoal 2
;;; (IMPLIES (EXISTS-LOCAL-PEAK P)
;;;          (CONSP (MULTISET-DIFF (PROOF-MEASURE P)
;;;                                (PROOF-MEASURE (REPLACE-LOCAL-PEAK P))))).
;;; Subgoal 1
;;; (IMPLIES (EXISTS-LOCAL-PEAK P)
;;;          (FORALL-EXISTS-REL-BIGGER
;;;               (MULTISET-DIFF (PROOF-MEASURE (REPLACE-LOCAL-PEAK P))
;;;                              (PROOF-MEASURE P))
;;;               (MULTISET-DIFF (PROOF-MEASURE P)
;;;                              (PROOF-MEASURE (REPLACE-LOCAL-PEAK P))))).

;;; In the sequel, we build a collection of rules to prove these two goals.

;;; ············································································
;;; 3.2.1 Removing initial and final common parts
;;; ············································································


(local
 (defthm proof-peak-append
   (implies (exists-local-peak p)
	    (equal
	     (append (proof-before-peak p)
		     (append (local-peak p)
			     (proof-after-peak p)))
	     p))
   :rule-classes (:elim :rewrite)))

;;; REMARK: This decomposition only makes sense when (exists-local-peak
;;; p). The elim rule is for avoiding :use.


;;; We use a rewrite rule to decompose proof-measure of proofs with
;;; local peaks. This rule implements a rewriting rule strategy: every
;;; proof with a local peak can be divided into three pieces (w.r.t. its
;;; complexity)

(local
 (defthm proof-measure-with-local-peak
   (implies (exists-local-peak p)
	    (equal (proof-measure p)
		   (append (proof-measure (proof-before-peak p))
			   (proof-measure (local-peak p))
			   (proof-measure (proof-after-peak p)))))))


(local (in-theory (disable proof-peak-append)))

;;; The following rule helps to express the proof-measure of
;;; (replace-local-peak p) in a similar way than the previous rule does
;;; with the proof-measure of p

(local
 (defthm replace-local-peak-another-definition
   (implies (exists-local-peak p)
	    (equal (replace-local-peak p)
		   (append (proof-before-peak p)
			   (append (transform-local-peak (local-peak p))
				   (proof-after-peak p)))))))


;;; The above rules rewrite the proof-measure's of p and
;;; (replace-local-peak p) in a way such that the initial and final
;;; common parts are explicit. In this way the rules
;;; multiset-diff-append-1 and multiset-diff-append-2 rewrite the
;;; expression, simplifying the common parts (see multiset.lisp and
;;; defmul.lisp to read also the role of the congruence rules generated
;;; by the above defmul call). The simplified goals now are:

;;; Subgoal 2'
;;; (IMPLIES
;;;  (EXISTS-LOCAL-PEAK P)
;;;  (CONSP
;;;      (MULTISET-DIFF (PROOF-MEASURE (LOCAL-PEAK P))
;;;                     (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P)))))).

;;; Subgoal 1'
;;; (IMPLIES
;;;  (EXISTS-LOCAL-PEAK P)
;;;  (FORALL-EXISTS-REL-BIGGER
;;;      (MULTISET-DIFF (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P)))
;;;                     (PROOF-MEASURE (LOCAL-PEAK P)))
;;;      (MULTISET-DIFF (PROOF-MEASURE (LOCAL-PEAK P))
;;;                     (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P)))))).




;;; ············································································
;;; 3.2.2 Removing the first element of the local peak
;;; ············································································

;;; First, let's prove that the local peak and the transformed are
;;; proofs with the same endpoints, so their proof measures have the
;;; same first element. This will be useful in 3.2.3 where we will look
;;; for an explicit reference to the peak-element of the local peak.

(local
 (defthm local-peak-equiv-p
   (implies (exists-local-peak p)
	    (equiv-p (elt1 (car (local-peak p)))
		     (elt2 (cadr (local-peak p)))
		     (local-peak p)))))

(local
 (defthm transform-local-peak-equiv-p
   (implies (exists-local-peak p)
	    (equiv-p (elt1 (car (local-peak p)))
		     (elt2 (cadr (local-peak p)))
		     (transform-local-peak (local-peak p))))))


;;; Using the above, now we will see that we can simplify further the
;;; multiset difference of the measures of the the proofs,
;;; removing the first element. This is not so easy as one can think at
;;; first sight, since there is a subtle point: the transformed proof
;;; can be empty.


(local
 (defthm consp-proof-measure
   (equal (consp (proof-measure p))
	  (consp p))))

(local
 (defthm car-equiv-p-proof-measure
   (implies (and (equiv-p x y p)
		 (consp p))
	    (equal (car (proof-measure p)) x))))

;;; The main lemma of this sub-subsection. Note how we distinguish two
;;; cases: proofs empty or not.

(local
 (defthm multiset-diff-proof-measure
   (implies (and (equiv-p x y p1)
		 (equiv-p x z p2))
	    (equal (multiset-diff
		    (proof-measure p1)
		    (proof-measure p2))
		   (if (consp p1)
		       (if (consp p2)
			   (multiset-diff (cdr (proof-measure p1))
					  (cdr (proof-measure p2)))
			 (proof-measure p1))
		     nil)))
   :rule-classes nil))

(local
 (defthm consp-local-peak
   (implies (exists-local-peak p)
	    (consp (local-peak p)))
   :rule-classes :type-prescription))

;;; And now the two rules needed for the intended simplification

(local
 (defthm multiset-diff-proof-measure-local-peak-transform-1
   (implies (exists-local-peak p)
	    (equal
	     (multiset-diff (proof-measure (transform-local-peak (local-peak p)))
			    (proof-measure (local-peak p)))
	     (if (consp (transform-local-peak (local-peak p)))
		 (multiset-diff
		  (cdr (proof-measure (transform-local-peak (local-peak p))))
		  (cdr (proof-measure (local-peak p))))
		 nil)))
   :hints (("Goal" :use
	    (:instance multiset-diff-proof-measure
		       (x (elt1 (car (local-peak p))))
		       (y (elt2 (cadr (local-peak p))))
		       (z (elt2 (cadr (local-peak p))))
		       (p1 (transform-local-peak (local-peak p)))
		       (p2 (local-peak p)))))))


(local
 (defthm multiset-diff-proof-measure-local-peak-transform-2
   (implies (exists-local-peak p)
	    (equal
	     (multiset-diff
	      (proof-measure (local-peak p))
	      (proof-measure (transform-local-peak (local-peak p))))
	    (if (consp (transform-local-peak (local-peak p)))
		(multiset-diff
		 (cdr (proof-measure (local-peak p)))
		 (cdr (proof-measure (transform-local-peak (local-peak p)))))
	      (proof-measure (local-peak p)))))
   :hints (("Goal" :use
	    (:instance multiset-diff-proof-measure
		       (x (elt1 (car (local-peak p))))
		       (y (elt2 (cadr (local-peak p))))
		       (z (elt2 (cadr (local-peak p))))
		       (p2 (transform-local-peak (local-peak p)))
		       (p1 (local-peak p)))))))

;;; REMARK: it could seem that in the lemma multiset-diff-proof-measure
;;; variables x, y and z are not needed and that proof-p could be used
;;; instead of equiv-p. But we think that in that case, to deal with the
;;; empty proof would be somewhat unnatural.


;;; With the rules we have at this moment, our unresolved goals are
;;; simplified to:

;;; Subgoal 2.2
;;; (IMPLIES
;;;   (AND (EXISTS-LOCAL-PEAK P)
;;;        (CONSP (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;   (CONSP (MULTISET-DIFF
;;;               (CDR (PROOF-MEASURE (LOCAL-PEAK P)))
;;;               (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))))).

;;; Subgoal 1.2
;;; (IMPLIES
;;;  (AND (EXISTS-LOCAL-PEAK P)
;;;       (CONSP (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;  (FORALL-EXISTS-REL-BIGGER
;;;    (MULTISET-DIFF (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;                   (CDR (PROOF-MEASURE (LOCAL-PEAK P))))
;;;    (MULTISET-DIFF
;;;         (CDR (PROOF-MEASURE (LOCAL-PEAK P)))
;;;         (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))))).


;;; ············································································
;;; 3.2.3 An explicit reference to the peak-element
;;; ············································································


;;; Definition and properties of peak-element
;;; ·········································

;;; See the definition in abstract-proofs.lisp

(local
 (defthm peak-element-member-proof-measure-local-peak
   (implies (exists-local-peak p)
	    (member (peak-element p) (proof-measure (local-peak p))))))

(local
 (defthm peak-element-rel-1
   (implies (exists-local-peak p)
	    (rel (elt1 (car (local-peak p)))
		 (peak-element p)))))

(local
 (defthm peak-element-rel-2
   (implies (exists-local-peak p)
	    (rel (elt2 (cadr (local-peak p)))
		 (peak-element p)))))

(local
 (defthm cdr-proof-measure-local-peak
   (implies (exists-local-peak p)
	    (equal (cdr (proof-measure (local-peak p)))
		   (list (peak-element p))))))
(local
 (defthm p-local-peak
   (implies (exists-local-peak p)
	    (q (peak-element p)))))

(local (in-theory (disable peak-element)))


;;; Now our unresolved goals reduces to (note the explicit reference to
;;; the peak element):

;;; Subgoal 2.2
;;; (IMPLIES
;;;   (AND (EXISTS-LOCAL-PEAK P)
;;;        (CONSP (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;   (CONSP (MULTISET-DIFF
;;;               (LIST (PEAK-ELEMENT P))
;;;               (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))))).

;;; Subgoal 1.2
;;; (IMPLIES
;;;  (AND (EXISTS-LOCAL-PEAK P)
;;;       (CONSP (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;  (FORALL-EXISTS-REL-BIGGER
;;;      (ACL2::REMOVE-ONE
;;;            (PEAK-ELEMENT P)
;;;            (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P)))))
;;;      (MULTISET-DIFF
;;;           (LIST (PEAK-ELEMENT P))
;;;           (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))))).


;;; ············································································
;;; 3.2.4 The peak element is bigger than any element of
;;; (transform-local-peak (local-peak p))
;;; ············································································

;;; Definition of being bigger (w.r.t rel) than every element of a list
;;; ···································································

(local
 (defun rel-bigger-than-list (x l)
   (if (atom l)
       t
     (and (rel (car l) x) (rel-bigger-than-list x (cdr l))))))


;;; Conditions assuring that an element m is rel-bigger-than-list than
;;; the elements of the proof-measure of a proof, when the proof is,
;;; respectively, steps-up or steps-down:
;;; ···································································

;;; A previous lemma: transitivity of rel is needed here

(local
 (defthm transitive-reduction
   (implies (and
             (legal e1 op)
	     (q e1) (q (reduce-one-step e1 op)) (q m)
             (rel e1 m))
            (rel (reduce-one-step e1 op) m))
   :hints (("Goal"
            :use (:instance rel-transitive
                            (x (reduce-one-step e1 op)) (y e1) (z m))))))

;;; And the two lemmas

(local
 (defthm steps-down-proof-measure-w-f-v
   (implies (and (proof-p p) (steps-down p) (q m))
            (iff (rel-bigger-than-list m (proof-measure p))
                 (if (consp p)
                     (rel (elt1 (car p)) m)
                   t)))))

(local
 (defthm steps-up-proof-measure-w-f-v
   (implies (and (proof-p p) (steps-up p) (q m)
                 (if (consp p) (rel (elt2 (last-elt p)) m) t))
            (rel-bigger-than-list m (proof-measure p)))))

;;; REMARKS:
;;; 1) The reverse implication in the steps-up case is not true as in
;;; the steps-down case. The reason is that the proof measure does not
;;; contain the final endpoint.

;;; 2) The form of the rule allows one to distinguish between p empty or
;;; non-empty.


;;; In order to apply the two lemmas above we try to split
;;; (transform-local-peak (local-peak p)) in two proofs: the proof
;;; before the valley (steps-up) and the proof after the valley
;;; (steps-down). The following lemmas are needed for that purpose.
;;; ····································································

;;; If p is a proof, so they are the proofs after and before the
;;; valley.

(local
 (defthm proof-p-two-pieces-of-a-valley
   (implies (proof-p p)
            (and (proof-p (proof-before-valley p))
                 (proof-p (proof-after-valley p))))))

;;; rel-bigger-than-list when the list is splitted in two pieces

(local
 (defthm rel-bigger-than-list-append
   (equal
    (rel-bigger-than-list x (append l1 l2))
    (and (rel-bigger-than-list x l1)
         (rel-bigger-than-list x l2)))))



;;; REMARK: In abstract-proofs.lisp it is also shown that
;;; (proof-before-valley p) is steps-up and that when p is a valley then
;;; (proof-after-valley p) is steps-down. And also the lemma
;;; proof-valley-append splits the proof in these two pieces.


;;; The transformed proof is a valley
;;; ·································

(local
 (defthm local-peak-local-peak-p
   (implies (exists-local-peak p)
            (local-peak-p (local-peak p)))))


(local
 (defthm exists-local-peak-implies-proof-p-trasform-local-peak
   (implies (exists-local-peak p)
	    (proof-p (local-peak p)))))

(local
 (defthm transform-local-peak-steps-valley
   (implies (exists-local-peak p)
	    (steps-valley (transform-local-peak (local-peak p))))))

;;; We show a simplified expression of the endpoints of
;;; (transform-local-peak (local-peak p)) In this way, the lemmas
;;; peak-element-rel-1 and peak-element-rel-2 can be used to reveal the
;;; hypothesis of steps-down-proof-measure-w-f-v and
;;; steps-up-proof-measure-w-f-v (and then prove that the peak-element
;;; is bigger than every element of the complexities of the
;;; proof-after-valley and the proof-before-valley, respectively.
;;; ····································································



(local
 (encapsulate
  ()
  (local
   (defthm endpoints-of-a-proof
     (implies (and (equiv-p x y p) (consp p))
	      (and (equal (elt1 (car p)) x)
		   (equal (elt2 (last-elt p)) y)))))

  (defthm endpoints-of-transform-of-a-local-peak
    (implies (and (exists-local-peak p)
		  (consp (transform-local-peak (local-peak p))))
	     (and (equal (elt1 (car (transform-local-peak (local-peak p))))
			 (elt1 (car (local-peak p))))
		  (equal (elt2 (last-elt (transform-local-peak (local-peak p))))
			 (elt2 (cadr (local-peak p))))))
    :hints (("Goal" :use (:instance endpoints-of-a-proof
				    (x (elt1 (car (local-peak p))))
				    (y (elt2 (cadr (local-peak p))))
				    (p (transform-local-peak (local-peak p)))))))))


;;; Some technical lemmas
;;; ·····················

(local
 (defthm consp-proof-after-proof-instance
   (let ((q (transform-local-peak (local-peak p))))
     (implies (consp (proof-after-valley q))
              (consp q)))))

(local
 (defthm consp-proof-before-proof-instance
   (let ((q (transform-local-peak (local-peak p))))
     (implies (consp (proof-before-valley q))
              (consp q)))))


;;; And finally, the intended lemma
;;; ·······························

(local
 (defthm valley-rel-bigger-peak-lemma
   (implies (exists-local-peak p)
            (rel-bigger-than-list
             (peak-element p)
             (proof-measure (transform-local-peak (local-peak p)))))
   :hints (("Goal" :use (:instance acl2::proof-valley-append
                                   (acl2::p
                                    (transform-local-peak (local-peak p))))))))


;;; ············································································
;;; 3.2.5 Using valley-rel-bigger-peak-lemma to simplify the goals
;;; ············································································

;;; The two unresolved goals, as stated at the end of 3.2.3, can be
;;; simplified to t by using the previously proved
;;; valley-rel-bigger-peak-lemma.  This is lemma can be used for two
;;; purposes:

;;; 1: Using multiset-diff-member (see multiset.lisp) and the
;;; following lemma (stating that the peak-element is not a member of
;;; the proof-meassure of the transformed proof),
;;; the calls to multiset-diff in the goals now disappear.
;;; ···································································

(local
 (encapsulate
  ()
  (local
   (defthm rel-bigger-than-list-not-member
     (implies (and (q x) (rel-bigger-than-list x l))
              (not (member x l)))))

  (defthm peak-element-not-member-proof-measure
    (implies (exists-local-peak p)
             (not (member (peak-element p)
                          (proof-measure (transform-local-peak
                                          (local-peak p)))))))))

;;; We are dealing with the cdr of the proof-measure:

(local
 (defthm not-member-cdr
   (implies (not (member x l))
	    (not (member x (cdr l))))))

;;; In this moment the only unresolved goal is:

;;; Subgoal 1.2
;;; (IMPLIES (AND (EXISTS-LOCAL-PEAK P)
;;;               (CONSP (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;          (FORALL-EXISTS-REL-BIGGER
;;;               (CDR (PROOF-MEASURE (TRANSFORM-LOCAL-PEAK (LOCAL-PEAK P))))
;;;               (LIST (PEAK-ELEMENT P)))).


;;; 2: Using the following lemma, the call to forall-exists-rel-bigger
;;; in the unresolved goal above, is reduced to a call to
;;; rel-bigger-than-list (and then valley-rel-bigger-peak-lemma will be
;;; applied)
;;; ···································································


(local
 (defthm rel-bigger-than-list-forall-exists-rel-bigger
   (equal (forall-exists-rel-bigger l (list x))
          (rel-bigger-than-list x l))))

;;; We are dealing with the cdr of the proof-measure:
(local
 (defthm rel-bigger-than-list-cdr
   (implies (rel-bigger-than-list x l)
            (rel-bigger-than-list x (cdr l)))))

;;; With this two rules altogether with valley-rel-bigger-peak-lemma our
;;; unresolved goal becomes T, so we have:

;;; ············································································
;;; 3.2.6  The main lemma of this book
;;; ············································································

(defthm transform-to-valley-admission
  (implies (exists-local-peak p)
	   (mul-rel (proof-measure (replace-local-peak p))
		    (proof-measure p))))

;;; ············································································
;;; 3.2.7  Some final technical events
;;; ············································································

;;; Needed in the admission proof of transform-to-valley

(local
 (defthm mul-rel-nil
   (implies (consp l)
	    (mul-rel nil l))))

(local
 (defthm exists-local-peak-proof-measure-consp
   (implies (exists-local-peak p)
	    (consp (proof-measure p)))))

(local (in-theory (disable mul-rel
			   proof-measure-with-local-peak
			   replace-local-peak-another-definition)))


;;; ----------------------------------------------------------------------------
;;; 3.3 The definition of transform-to-valley
;;; ----------------------------------------------------------------------------


(defun transform-to-valley (p)
  (declare (xargs :measure (if (steps-q p) (proof-measure p) nil)
                  :well-founded-relation mul-rel))
  (if (and (steps-q p) (exists-local-peak p))
      (transform-to-valley (replace-local-peak p))
      p))




;;; ============================================================================
;;; 4. Properties of transform-to-valley (Newman's lemma)
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 4.1 Some previous events
;;; ----------------------------------------------------------------------------

;;; ·············································································
;;; 4.1.1 Previous rules needed to show that (transform-to-valley p) is eqv. to p
;;; ·············································································


;;; We have to see that (replace-local-peak p) is equivalent to p
;;; ·····························································

;;; An useful rule to deal with concatenation of proofs
(local
 (defthm proof-append
   (implies (equal z (last-of-proof x p1))
	    (equal (equiv-p x y (append p1 p2))
		   (and (equiv-p x z p1)
			(equiv-p z y p2))))))

;;; Last element of a local peak
(local
 (defthm last-element-of-a-local-peak
   (implies (local-peak-p p)
            (equal (last-elt p) (cadr p)))))

;;; The case where (transform-local-peak (local-peak p)) is empty:

(local
 (defthm atom-proof-endpoints-are-equal
   (implies (and (equiv-p x y p) (atom p))
            (equal x y))
   :rule-classes nil))

(local
 (defthm atom-transform-local-peak-forward-chaining-rule
   (implies (and
             (not (consp (transform-local-peak (local-peak p))))
             (exists-local-peak p)
             (equiv-p x y (local-peak p)))
            (equal x y))
   :hints (("Goal" :use ((:instance atom-proof-endpoints-are-equal
                                    (p (transform-local-peak (local-peak p)))))))
   :rule-classes :forward-chaining))

;;; REMARK: interesting use of forward-chaining.

;;; In the following bridge lemma it is fundamental
;;; replace-local-peak-another-definition and the case distinction
;;; generated by proof-append:

(local
 (defthm equiv-p-x-y-replace-local-peak-bridge-lemma
   (implies (and (exists-local-peak p)
                 (equiv-p x y (append
                               (proof-before-peak p)
                               (append (local-peak p)
                                       (proof-after-peak p)))))
            (equiv-p x y (replace-local-peak p)))
   :hints (("Goal"
	    :in-theory (enable replace-local-peak-another-definition)))))

;;; And finally the intended lemma:

(local
 (defthm equiv-p-x-y-replace-local-peak
   (implies (and (equiv-p x y p) (exists-local-peak p))
            (equiv-p x y (replace-local-peak p)))
   :hints (("Goal" :in-theory (enable proof-peak-append)))))

;;; REMARK: It's interesting how we avoid explicit expansion of the
;;; three pieces of p (before, at and after the peak), using the
;;; previous bridge lemma.

;;; ·············································································
;;; 4.1.2 A rule needed to show that (transform-to-valley p) is a valley
;;; ·············································································



;;; If a proof does not have local peaks, then it is a valley:

(local
 (defthm steps-valley-not-exists-local-peak
   (implies (equiv-p x y p)
            (equal  (steps-valley p) (not (exists-local-peak p))))))

;;; ·············································································
;;; 4.1.3 If equiv-p, then steps-q
;;; ·············································································

(local
 (defthm equiv-p-implies-stetps-q
   (implies (equiv-p x y p)
	    (steps-q p))
   :rule-classes :forward-chaining))

;;; ·············································································
;;; 4.1.4 Disabling the induction rule for equiv-p
;;; ·············································································


(local (in-theory (disable equiv-p-induct)))

;;; REMARK: It is important to disable the induction rule of equiv-p
;;; because we want the two main properties of transform-to-valley
;;; to be proved by the induction suggested by transform-to-valley
;;; (i.e. and induction based on the multiset relation mul-rel)


;;; ----------------------------------------------------------------------------
;;; 4.2 The intended properties of transform-to-valley
;;; ----------------------------------------------------------------------------


;;; It returns an equivalent proof
;;; ······························


(defthm equiv-p-x-y-transform-to-valley
  (implies (equiv-p x y p)
           (equiv-p x y (transform-to-valley p))))




;;; It returns a valley proof
;;; ·························


(defthm valley-transform-to-valley
   (implies (equiv-p x y p)
            (steps-valley (transform-to-valley p))))


;;; CONCLUSION:
;;; The definition of transform-to-valley and the theorems
;;; equiv-p-x-y-transform-to-valley and valley-transform-to-valley prove
;;; the Newman's lemma









