;;; local-confluence.lisp
;;; Convergent reduction relations have a decidable equivalence closure
;;; Created: 1-11-99 Last modified: 11-10-00
;;; =============================================================================


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

(defpkg "NWM" (cons 'multiset-diff *cnf-package-exports*))

(defpkg "LCNF" (cons 'multiset-diff *cnf-package-exports*))

(certify-book "local-confluence" 5)
|#

;;;
(in-package "LCNF")

(local (include-book "confluence"))

(include-book "newman")


;;; ****************************************************************************
;;; LOCALLY CONFLUENT AND TERMINATING REDUCTION RELATIONS HAVE A
;;; DECIDABLE EQUIVALENCE CLOSURE
;;; ****************************************************************************


;;; We prove that every noetherian, locally confluent reduction relation
;;; has decidable equivalence closure. This is a good example of how
;;; functional instantiation can be useful. This result can be easily
;;; proved by functional instantiation of the results in the books
;;; previously developed. Using confluence.lisp, we need to show that
;;; the reduction relation is normalizing and has the Church-Rosser
;;; property. And the Church-Rosser property can be proved by using
;;; Newman's lemma, proved in newman.lisp. The normalizing property is
;;; an easy consequence of noetherianity.

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

;;; REMARK: This section is exactly the same as in newman.lisp:
;;; formalization of noetherianity and local confluence. Nevertheless,
;;; since we have to compute normal forms and the function
;;; proof-irreducible, we have to assume the existence of a reducibility
;;; test given by a function reducible with the following properties for
;;; every element x:
;;; 1) When reducible returns non-nil, it returns a legal operator for x.
;;; 2) When reducible returns nil, there are no legal operators for x.
;;; See newman.lisp and confluence-v0.lisp for more details.


;;; A noetherian partial order rel (used to justify noetherianity of the
;;; reduction relation defined later)
;;; .....................................................................

(encapsulate
 ((rel (x y) booleanp)
  (fn (x) e0-ordinalp))


 (local (defun rel (x y) (declare (ignore x y)) nil))
 (local (defun fn (x) (declare (ignore x)) 1))

 (defthm rel-well-founded-relation-on-mp
   ;; modified for v2-8 ordinals changes
   (and
    (o-p (fn x))
    (implies (rel x y)
	     (o< (fn x) (fn y))))
   :rule-classes (:well-founded-relation
		  :rewrite))

 (defthm rel-transitive
   (implies (and (rel x y) (rel y z))
	    (rel x z))))

(in-theory (disable rel-transitive))


;;; A noetherian and locally confluent reduction relation
;;; ·····················································


(encapsulate
 ((legal (x u) boolean)
  (reduce-one-step (x u) element)
  (reducible (x) boolean)
  (transform-local-peak (x) proof))

 (local (defun legal (x u) (declare (ignore x u)) nil))
 (local (defun reduce-one-step (x u) (+ x u)))
 (local (defun reducible (x) (declare (ignore x)) nil))
 (local (defun transform-local-peak (x) (declare (ignore x)) nil))


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

; The following was added by Matt Kaufmann after ACL2 Version 3.4 because of
; a soundness bug fix; see ``subversive'' in :doc note-3-5.
 (defthm equiv-p-type
   (booleanp (equiv-p x y p))
   :rule-classes :type-prescription)

 (defthm local-confluence
   (let ((valley (transform-local-peak p)))
     (implies (and (equiv-p x y p) (local-peak-p p))
              (and (steps-valley valley)
		   (equiv-p x y valley)))))

 (defthm noetherian
   (implies (legal x u) (rel (reduce-one-step x u) x))))


;;; ============================================================================
;;; 2. Theorem: The reduction relation has the Church-Rosser property
;;; ============================================================================



;;; REMARK: We show that it is possible to define a function
;;; transform-to-valley with the propertiy of transforming every proof
;;; ina an equivalent valley proof. This is done in newman.lisp, so
;;; now we can functionally instantiate the main results proved there.
;;; See newman.lisp for details.

;;; Well-founded multiset extension of rel
;;; ······································

;(acl2::defmul-components rel)
;The list of components is:
; (REL REL-WELL-FOUNDED-RELATION-ON-MP T FN X Y)
(local
 (acl2::defmul (REL REL-WELL-FOUNDED-RELATION-ON-MP T FN X Y)))


;;; Auxiliary functions in the definition of transform-to-valley
;;; ···························································

(local
 (defun exists-local-peak (p)
   (cond ((or (atom p) (atom (cdr p))) nil)
	 ((and
	   (not (direct (car p)))
	   (direct (cadr p)))
	  (and (proof-step-p (car p))
	       (proof-step-p (cadr p))
	       (equal (elt2 (car p)) (elt1 (cadr p)))))
	 (t (exists-local-peak (cdr p))))))

(local
 (defun replace-local-peak (p)
   (cond ((or (atom p) (atom (cdr p))) nil)
	 ((and (not (direct (car p))) (direct (cadr p)))
	  (append (transform-local-peak (list (car p) (cadr p)))
		  (cddr p)))
	 (t (cons (car p) (replace-local-peak (cdr p)))))))


;;; transform-to-valley terminates
;;; ······························

;;; By functional instantiation of the same result in newman.lisp

(local
 (defthm transform-to-valley-admission
   (implies (exists-local-peak p)
	    (mul-rel (proof-measure (replace-local-peak p))
		     (proof-measure p)))

   :rule-classes nil
   :hints ((pkg-functional-instance
	    acl2::id
	    'nwm::transform-to-valley-admission
	    '(p) '(fn legal forall-exists-rel-bigger reduce-one-step
		      proof-step-p equiv-p rel mul-rel
		      exists-local-peak replace-local-peak
		      transform-local-peak exists-rel-bigger))
	   ("Subgoal 10" :in-theory (enable rel-transitive)))))



;;; Definition of transform-to-valley
;;; ·································

(local
 (defun transform-to-valley (p)
   (declare (xargs :measure (proof-measure p)
		   :well-founded-relation mul-rel
		   :hints (("Goal" :use
			    (:instance transform-to-valley-admission)))))

  (if (not (exists-local-peak p))
      p
    (transform-to-valley (replace-local-peak p)))))


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
	    '(fn transform-to-valley reduce-one-step legal
		 proof-step-p equiv-p rel exists-local-peak
		 replace-local-peak transform-local-peak)))))

(local
 (defthm valley-transform-to-valley
   (implies (equiv-p x y p)
	    (steps-valley (transform-to-valley p)))
   :hints ((pkg-functional-instance
	    acl2::id
	    'nwm::valley-transform-to-valley
	    '(p x y)
	    '(fn transform-to-valley reduce-one-step legal
		 proof-step-p equiv-p rel exists-local-peak
		 replace-local-peak transform-local-peak)))))



;;; ============================================================================
;;; 3. Theorem: The reduction relation is normalizing
;;; ============================================================================

;;; To instantiate the results in confluence.lisp, we have to define a
;;; function proof-irreducible and prove the properties assumed there as
;;; axioms.

;;; Definition of proof-irreducible
;;; ·······························

;;; REMARK: Iteratively apply reduction steps until an irreducible
;;; element is found. This function termination can be justified by the
;;; well-founded relation rel. That is, the normal-form computation
;;; terminates because the reduction relation is assumed to be
;;; noetherian.

(defun proof-irreducible (x)  (declare (xargs :measure x
					       :well-founded-relation rel))
  (let ((red (reducible x)))
    (if (not red)
	nil
      (cons (make-r-step
	      :direct t :elt1 x :elt2 (reduce-one-step x red)
	      :operator red)
	    (proof-irreducible (reduce-one-step x red))))))


;;; Properties of proof-irreducible (normalizing property)
;;; ······················································

;;; REMARK: These are the assumed proerties of proof-irreducible in
;;; confluence.lisp, in rewriting rule form:

(local
 (defthm normalizing-1
   (let ((y (elt2 (last-elt (proof-irreducible x)))))
     (implies (consp (proof-irreducible x))
	      (and (equiv-p x y (proof-irreducible x))
		   (not (legal y op)))))))
(local
 (defthm normalizing-2
   (implies
    (not (consp (proof-irreducible x)))
    (not (legal x op)))))

;;; ============================================================================
;;; 4. Theorem: The equivalence closure is decidable
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 4.1 Definition of a decison procedure for <--*--reduce-one-step--*-->
;;; ----------------------------------------------------------------------------

(defun normal-form (x)
  (declare (xargs :measure x
		  :well-founded-relation rel))
  (let ((red (reducible x)))
    (if (not red)
	x
      (normal-form (reduce-one-step x red)))))

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
;;; normal-form is more eficcient. The same for r-equiv.

(local
 (defun normal-form-aux (x) (last-of-proof x (proof-irreducible x))))

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
	   '(legal proof-step-p r-equiv
	    equiv-p reduce-one-step proof-irreducible
	    transform-to-valley normal-form))))



;;; Soundness
;;; ·········

;;; By functional instantiation of the same results in confluence.lisp

;;; Skolem function
(defun make-proof-common-n-f (x y)
   (append (proof-irreducible x) (inverse-proof (proof-irreducible y))))


(defthm r-equivalent-sound
  (implies (r-equivalent x y)
	   (equiv-p x y (make-proof-common-n-f x y)))

  :hints ((pkg-functional-instance
	   acl2::id
	   'cnf::r-equiv-sound
	   '(x y)
	   '(legal make-proof-common-n-f proof-step-p
		   r-equiv  equiv-p
		   reduce-one-step proof-irreducible transform-to-valley
		   normal-form))))
