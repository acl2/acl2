;;; convergent.lisp
;;; Convergent reduction relations have a decidable equivalence closure
;;; Created: 1-11-99 Last modified: 11-10-00
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

(defpkg "NWM" (cons 'multiset-diff *cnf-package-exports*))

(defpkg "CNV" (cons 'multiset-diff *cnf-package-exports*))

(certify-book "convergent" 5)

|#

;;;
(in-package "CNV")

(local (include-book "confluence"))

(include-book "newman")


;;; ****************************************************************************
;;; LOCALLY CONFLUENT AND TERMINATING REDUCTION RELATIONS HAVE A
;;; DECIDABLE EQUIVALENCE CLOSURE
;;; ****************************************************************************


;;; We prove that every noetherian, locally confluent reduction relation
;;; has decidable equivalence closure. A good example of functional
;;; instantiation. This result can be easily proved by functional
;;; instantiation of the results in the books previously
;;; developed. Using confluence.lisp, we need to show that the reduction
;;; relation is normalizing and has the Church-Rosser property. And the
;;; Church-Rosser property can be proved by using Newman's lemma, proved
;;; in newman.lisp. The normalizing property is an easy consequence of
;;; noetherianity.

;;; REMARK: To undersatand this book, you should read previously the
;;; books abstract-proofs.lisp, confluence.lisp and newman.lisp.

;;; ============================================================================
;;; 1. A Tool for functional instantation
;;; ============================================================================

;;; In this file we have to extensively use functional
;;; instantiation of results previously proved. The functional
;;; instantiations we have to carry out are always of the same kind:
;;; the functional substitution relates functions with the same symbol
;;; name but in different package and the same happen with individual
;;; variables.  We define the following functions in :program
;;; mode to provide a tool to make this kind of functional-instance
;;; hints convenient.

(local
 (defun pkg-functional-instance-pairs (lemma-name symbols)
   (declare (xargs :mode :program))
   (if (endp symbols)
       nil
     (cons (list (acl2::intern-in-package-of-symbol
		 (string (car symbols)) lemma-name)
		 (car symbols))
	   (pkg-functional-instance-pairs lemma-name (cdr symbols))))))

(local
 (defun pkg-functional-instance
   (id lemma-name variable-symbols function-symbols)
   (declare (xargs :mode :program))
   (if (equal id (acl2::parse-clause-id "Goal"))
       (list :use (list* :functional-instance
			 (list* :instance
				lemma-name
				(pkg-functional-instance-pairs
				 lemma-name variable-symbols))
			 (pkg-functional-instance-pairs
			  lemma-name function-symbols)))
     nil)))


;;; The function pkg-functional-instance computes a hint (see
;;; computed-hints in the ACL2 manual) and is called
;;; in the following way:

;;; (pkg-functional-instance id lemma-name variable-symbols
;;;                          function-symbols)

;;; where:

;;; id:               is always the variable acl2::id
;;; lemma-name:       the name of the lemma to be instantiated
;;;                   (including the package).
;;; variable-symbols: the list of symbol names of variables to be
;;;                   instantiated.
;;; function-symbols: the list of symbol names of functions to be
;;;                   instantiated.

;;; The computed hint is the functional instantiation of the lemma-name,
;;; relating each variable name and function name (of the package where
;;; the lemma has been proved) to the same symbol name in the current
;;; package.


;;; ============================================================================
;;; 2. Formalizing the hypothesis of the theorem
;;; ============================================================================

;;; REMARK: This section is the same as in newman.lisp: formalization of
;;; noetherianity and local confluence. Nevertheless, since we have to
;;; compute normal forms and the function proof-irreducible, we have to
;;; assume the existence of a reducibility test given by a function
;;; "reducible" with the following properties for every element x in the
;;; set defined by a predicate q:

;;; 1) When "reducible" returns non-nil, it returns a legal operator for x.
;;; 2) When "reducible" returns nil, there are no legal operators for
;;;    x.  See newman.lisp and confluence-v0.lisp for more details

;;; Furthermore, since "reducible" will be used to define a function
;;; proof-irreducible with the same properties as defined in
;;; confluence.lisp, we will also assume a "closure" property:

;;; 3) For every x such that (q x) and (legal x op) the legal operator
;;; op appplied to x returns an element in q.

;;; This assumptions on the function reducible are "reasonable" if we
;;; want to talk about computation of normal forms.


(encapsulate
 ((rel (x y) boolean)
  (q (x) boolean)
  (q-w () elemement)
  (fn (x) o-p)
  (legal (x u) boolean)
  (reducible (x) boolean)
  (reduce-one-step (x u) element)
  (transform-local-peak (x) proof))


;;; A general noetherian partial order rel is (partially) defined. The
;;; function is well founded on the set defined by a predicate q, and fn
;;; is the order-preserving mapping from objects to ordinals. It will be
;;; used (see below) to justify noetherianity of the reduction relation,
;;; based on the following meta-theorem: "A reduction is noetherian iff
;;; it is contained in a noetherian partial order" (see newman.lisp for
;;; more information):

 (local (defun rel (x y) (declare (ignore x y)) nil))
 (local (defun q (x) (declare (ignore x)) t))
 (local (defun fn (x) (declare (ignore x)) 1))

 (defthm rel-well-founded-relation-on-q
   (and
    (implies (q x) (o-p (fn x)))
    (implies (and (q x) (q y) (rel x y))
	     (o< (fn x) (fn y))))
   :rule-classes (:well-founded-relation
		  :rewrite))

 (defthm rel-transitive
   (implies (and (q x) (q y) (q z) (rel x y) (rel y z))
 	    (rel x z)))

 (in-theory (disable rel-transitive))

;;; For resons that will be clear later, we need to assume that the set
;;; defined by the predicate "q" is not empty (by the way, a reasonable
;;; assumption). We assume the existence of an element (q-w):

 (local (defun q-w () 0))

 (defthm one-element-of-q (q (q-w)))


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


;;; As in confluence.lisp, with these three functions one can define
;;; what is a legal proof step: a r-step-p structure (see
;;; abstract-proofs.lisp) such that one the elements is obtained
;;; applying a reduction step to the other (using a legal operator).

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

;;; As in confluence.lisp, now we can define the equivalence closure of
;;; the reduction relation, given by equiv-p: two elements are
;;; equivalent if there exists a list of concatenated legal proof-steps
;;; (a PROOF) connecting the elements, such that every element involved
;;; in the proof is in the set defined by q. In the book confluence.lisp
;;; is proved that equiv-p defines the least equivalence relation in the
;;; set defined by q, containing the reduction relation.

 (defun equiv-p (x y p)
   (if (endp p)
       (and (equal x y) (q x))
       (and
	(q x)
	(proof-step-p (car p))
	(equal x (elt1 (car p)))
	(equiv-p (elt2 (car p)) y (cdr p)))))

;;; We will assume also that for every x in q, application of legal
;;; operators is a closed operation in q. This property will be needed
;;; when we define the function proof-irreducible (the counterpart of
;;; proof-irreducible in confluence.lisp)

 (defthm legal-reduce-one-step-closure
   (implies (and (q x) (legal x op))
	    (q (reduce-one-step x op))))


;;; As we said before, we assume the existence of a reducibility test (a
;;; function called "reducible") because we are going to define
;;; normal-form computation:

 (local (defun reducible (x) (declare (ignore x)) nil))

;;; These are the two properties required to "reducible"


 (defthm legal-reducible-1
   (implies (and (q x) (reducible x))
	    (legal x (reducible x))))

 (defthm legal-reducible-2
   (implies (and (q x) (not (reducible x)))
	    (not (legal x u))))

;;; As in newman.lisp local confluence is reformulated in terms of
;;; proofs: "for every local-peak, there is an equivalente valley proof"
;;; This equivalent valley proof is returned by the function
;;; transform-local-peak:


 (local (defun transform-local-peak (x) (declare (ignore x)) nil))


 (defthm local-confluence
   (let ((valley (transform-local-peak p)))
     (implies (and (equiv-p x y p) (local-peak-p p))
              (and (steps-valley valley)
		   (equiv-p x y valley)))))

;;;  As in newman.lisp, this is noetherianity of the reduction relation,
;;;  justified by inclusion in the well founded relation rel: if we
;;;  permorm one (legal) reduction step in the set defined by q, then we
;;;  obtain a smaller element (with respect to rel):

 (defthm noetherian
   (implies (and (q x) (legal x u))
	    (rel (reduce-one-step x u) x))))

;;; We think all these properties are a reasonable abstraction of every
;;; concrete convergent reduction relation.

;;; ============================================================================
;;; 2. Theorem: The reduction relation has the Church-Rosser property
;;; ============================================================================


;;; REMARK: We show that it is possible to define a function
;;; transform-to-valley with the property of transforming every proof
;;; in an equivalent valley proof. This is done as in newman.lisp, but
;;; now we can functionally instantiate the main results proved there.
;;; See newman.lisp for details.

;;; Well-founded multiset extension of rel
;;; ······································

;(acl2::defmul-components rel)
;The list of components is:
; (REL REL-WELL-FOUNDED-RELATION-ON-Q T FN X Y)
(local
 (acl2::defmul (rel rel-well-founded-relation-on-q q fn x y)))


;;; Auxiliary functions in the definition of transform-to-valley
;;; ····························································

(local
 (defun exists-local-peak (p)
   (cond ((or (atom p) (atom (cdr p))) nil)
	 ((and
	   (not (direct (car p)))
	   (direct (cadr p)))
	  (and (proof-step-p (car p))
	       (proof-step-p (cadr p))
	       (q (elt1 (car p))) (q (elt2 (car p)))
	       (q (elt1 (cadr p))) (q (elt2 (cadr p)))
	       (equal (elt2 (car p)) (elt1 (cadr p)))))
	 (t (exists-local-peak (cdr p))))))

(local
 (defun replace-local-peak (p)
   (cond ((or (atom p) (atom (cdr p))) nil)
	 ((and (not (direct (car p))) (direct (cadr p)))
	  (append (transform-local-peak (list (car p) (cadr p)))
		  (cddr p)))
	 (t (cons (car p) (replace-local-peak (cdr p)))))))

(local
 (defun steps-q (p)
   (if (endp p)
       t
     (and (r-step-p (car p))
	  (q (elt1 (car p)))
	  (q (elt2 (car p)))
	  (and (steps-q (cdr p)))))))

;;; This property steps-q implies that proof-measure is an object
;;; representing a multiset where the well-founded relation is defined.

(local
 (defthm steps-q-implies-q-true-listp-proof-measure
   (implies (steps-q p)
	    (q-true-listp (proof-measure p)))))


;;; transform-to-valley terminates
;;; ······························

;;; By functional instantiation of the same result in newman.lisp

(local
 (defthm transform-to-valley-admission
   (implies (exists-local-peak p)
	    (mul-rel (proof-measure (replace-local-peak p))
		     (proof-measure p)))

   :hints ((pkg-functional-instance
	    acl2::id
	    'nwm::transform-to-valley-admission
	    '(p) '(q fn legal forall-exists-rel-bigger reduce-one-step
		      proof-step-p equiv-p rel mul-rel
		      exists-local-peak replace-local-peak
		      transform-local-peak exists-rel-bigger))
	   ("Subgoal 7" ; changed by J Moore after v5-0, from "Subgoal 8", for tau
            :use
	    (:instance rel-transitive
		       (x nwm::x) (y nwm::y) (z nwm::z))))))

;;; Additional technical lemmas:

(local
 (defthm mul-rel-nil
   (implies (consp l)
	    (mul-rel nil l))))

(local
 (defthm exists-local-peak-proof-measure-consp
   (implies (exists-local-peak p)
	    (consp (proof-measure p)))))


;;; Definition of transform-to-valley
;;; ·································
(local
 (defun transform-to-valley (p)
   (declare (xargs :measure (if (steps-q p) (proof-measure p) nil)
		   :well-founded-relation mul-rel
		   :hints (("Goal" :in-theory (disable mul-rel)))))
   (if (and (steps-q p) (exists-local-peak p))
      (transform-to-valley (replace-local-peak p))
     p)))


;;; Properties of transform-to-valley: the Church-Rosser property
;;; ·····························································

;;; By functional instantiation of the same results in newman.lisp


(local
 (defthm equiv-p-x-y-transform-to-valley
   (implies (equiv-p x y p)
	    (equiv-p x y (transform-to-valley p)))
   :hints ((pkg-functional-instance
	    acl2::id
	    'nwm::equiv-p-x-y-transform-to-valley
	    '(p x y)
	    '(q fn transform-to-valley reduce-one-step legal
		 proof-step-p equiv-p rel exists-local-peak
		 steps-q replace-local-peak transform-local-peak)))))

(local
 (defthm valley-transform-to-valley
   (implies (equiv-p x y p)
	    (steps-valley (transform-to-valley p)))
   :hints ((pkg-functional-instance
	    acl2::id
	    'nwm::valley-transform-to-valley
	    '(p x y)
	    '(q fn transform-to-valley reduce-one-step legal
		 proof-step-p equiv-p rel exists-local-peak
		 steps-q replace-local-peak transform-local-peak)))))

;;; These two properties trivially implies the Church-Rosser-property:
; (defthm Chuch-Rosser-property
;   (let ((valley (transform-to-valley p)))
;     (implies (equiv-p x y p)
;              (and (steps-valley valley)
;                   (equiv-p x y valley)))))


;;; ============================================================================
;;; 3. Theorem: The reduction relation is normalizing
;;; ============================================================================

;;; To instantiate the results in confluence.lisp, we have to define a
;;; function proof-irreducible and prove the properties assumed there as
;;; axioms. Remember from confluence.lisp that proof-irreducible returns
;;; for every x in q, a proof showing the equivalence of x with an
;;; element in normal form (i.e. such that no operator is legal
;;; w.r.t. it).

;;; Definition of proof-irreducible
;;; ·······························

;;; REMARK: Iteratively apply reduction steps until an irreducible
;;; element is found, and collect all those proof steps.

(defun proof-irreducible (x)
  (declare (xargs :measure (if (q x) x (q-w))
		  :well-founded-relation rel))
  (if (q x)
      (let ((red (reducible x)))
	(if red
	    (cons (make-r-step
		   :direct t :elt1 x :elt2 (reduce-one-step x red)
		   :operator red)
		  (proof-irreducible (reduce-one-step x red)))
	  nil))
    nil))

;;; REMARKS:

;;; - This proof-irreducible computation is only guaranteed to terminate
;;; when its input is an element such that (q x), since well-foundedness
;;; is only assumed in q. But ACL2 is a logic of total functions. Thus,
;;; we define as nil (the concrete value is irrelevant) the value of
;;; normal-form outside q.

;;; - Note that to admit this function, we must provide a measure and a
;;; well-founded relation. The well-founded relation is rel, and the
;;; measure has to assign to every element x, an object in the set where
;;; rel is known to be well-founded (i.e. in the set defined by q). When
;;; x is in q, there is no problem (we assign x). But if x is not in q,
;;; we have to assign an arbitrary element in q. That's the reason why
;;; we defined before a witness element (q-w) in q.



;;; Main property of proof-irreducible (normalizing property)
;;; ·························································

;;; REMARK: This is the assumed property of proof-irreducible in
;;; confluence.lisp.

(local
 (defthm normalizing
   (implies (q x)
	    (let* ((p-x-y (proof-irreducible x))
		   (y (last-of-proof x p-x-y)))
	      (and (equiv-p x y p-x-y)
		   (not (legal y op)))))))


;;; Exactly as in confluence.lisp, we can express the normalizing
;;; property as two rewrite rules:

(local
 (defthm normalizing-not-consp-proof-irreducible
   (implies (and (q x) (not (consp (proof-irreducible x))))
	    (not (legal x op)))
   :hints (("Goal" :use (:instance normalizing)))))

(local
 (defthm normalizing-consp-proof-irreducible
   (let ((p-x-y (proof-irreducible x)))
     (implies (and (q x) (consp p-x-y))
	      (and (equiv-p x (elt2 (last-elt p-x-y)) p-x-y)
		   (not (legal (elt2 (last-elt p-x-y)) op)))))
   :hints (("Goal" :use (:instance normalizing)))))


;;; ============================================================================
;;; 4. Definition: normal form computation
;;; ============================================================================

;;; Normal-form computation

(defun normal-form (x)
  (declare (xargs :measure (if (q x) x (q-w))
		  :well-founded-relation rel))
  (if (q x)
      (let ((red (reducible x)))
	(if red
	    (normal-form (reduce-one-step x red))
	    x))
    x))

;;; REMARK: The same REMARKS as in proof-ireducible applies here. Here,
;;; the value returned for elements x outside q is irrelevant in
;;; principle. We return x to make it analogue to the definition of
;;; normal-form in confluence.lisp (since we are going to functionally
;;; instantiate).

;;; ============================================================================
;;; 5. Theorem: The equivalence closure is decidable
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 5.1 Definition of a decison procedure for <--*--reduce-one-step--*-->
;;; ----------------------------------------------------------------------------


(defun r-equivalent (x y)
  (equal (normal-form x) (normal-form y)))


;;; REMARK: Note that this is not exactly the same definition of the
;;; decision procedure given in confluence.lisp. The point is that in
;;; confluence.lisp the normal-form computation is through the proof
;;; given by proof-irreducible. In order to functionally instantiate the
;;; result of confluence.lisp, we show that it is the same function.


;;; This is the same function as r-equiv in confluence.lisp
;;; ·······················································

;;; REMARK: normal-form-aux is analogue NWM::normal-form, but
;;; normal-form is more "eficcient". The same for r-equiv.

(local
 (defun normal-form-aux (x)
   (last-of-proof x (proof-irreducible x))))


(local
 (defthm normal-form-aux-normal-form
   (equal (normal-form x)
	  (normal-form-aux x))))

(local
 (defun r-equiv (x y)
   (equal (normal-form-aux x) (normal-form-aux y))))



;;; ----------------------------------------------------------------------------
;;; 4.2 Soundness and completeness
;;; ----------------------------------------------------------------------------

;;; Completeness
;;; ············

;;; By functional instantiation of the same results in confluence.lisp

(defthm r-equivalent-complete
  (implies (equiv-p x y p)
	   (r-equivalent x y))

  :rule-classes nil
  :hints ((pkg-functional-instance
	   acl2::id
	   'cnf::r-equiv-complete
	   '(p x y)
	   '(q legal proof-step-p r-equiv
	    equiv-p reduce-one-step proof-irreducible
	    transform-to-valley normal-form))))



;;; Soundness
;;; ·········

;;; By functional instantiation of the same results in confluence.lisp

;;; Skolem function
(defun make-proof-common-n-f (x y)
   (append (proof-irreducible x) (inverse-proof (proof-irreducible y))))


(defthm r-equivalent-sound
  (implies (and (q x) (q y) (r-equivalent x y))
	   (equiv-p x y (make-proof-common-n-f x y)))

  :hints ((pkg-functional-instance
	   acl2::id
	   'cnf::r-equiv-sound
	   '(x y)
	   '(q legal make-proof-common-n-f proof-step-p
		   r-equiv  equiv-p
		   reduce-one-step proof-irreducible transform-to-valley
		   normal-form))))








