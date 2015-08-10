;;; lattice-of-terms.lisp
;;; A compilation of previous results to prove that we can define a
;;; complete well-founded lattice in the set of objects of the ACL2 logic.
;;; The lattice is defined w.r.t. the subsumption relation.
;;; Creation: 26-10-99. Last revision: 11-12-2000
;;; =================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "lattice-of-terms")

|#

(in-package "ACL2")


(include-book "subsumption-well-founded")

(include-book "mg-instance")

(include-book "anti-unification")

;;; *********************************************************
;;; THE COMPLETE LATTICE OF FIRST-ORDER TERMS WITH RESPECT TO
;;; SUBSUMPTION
;;; *********************************************************

;;; We compile the results of this library about first-order terms, to
;;; prove that we can define a complete well-founded lattice
;;; w.r.t. subsumption in the set of objects of the ACL2 logic. We also
;;; prove that the set of terms of a given signature  is a sublattice.


;;; ============================================================================
;;; 1. Introducing one distinguished top term and substitution.
;;; ============================================================================


;;; ------
;;; Macros
;;; ------

;;; We will distinguish one term, called the top term:

(defmacro the-top-term ()
  ''the-top-term)

(defmacro is-the-top-term (term)
  `(equal ,term (the-top-term)))

;;; We will distinguish one substitution, called the top substitution:

(defmacro the-top-substitution ()
  ''the-top-substitution)

(defmacro is-the-top-substitution (subst)
  `(equal ,subst (the-top-substitution)))

;;; Some previous technical definitions:


(defun fix-substitution (sigma)
  (declare (xargs :guard t))
  (if (atom sigma) nil sigma))

;;; REMARK: This will force to every empty substitution returned
;;; by subs to be distinct from the-top-substitution.

(defun fix-term (term)
  (declare (xargs :guard t))
  (if (variable-p term) 0 term))

;;; REMARK: This forces to every term returned by anti-unification and
;;; mg-instance to be distinct from the-top-term.

;;; A few technical lemmas:


(local
 (defthm the-top-term-anti-unify-variable-p
  (implies (and (variable-p (anti-unify t1 t2))
                 (subs term t1) (subs term t2))
            (variable-p term))
   :hints (("Goal" :use
            ((:instance minimum-subsumption-implies-variable
                        (x (anti-unify t1 t2))))))))

; (local (in-theory (disable the-top-term-anti-unify-variable-p)))

(local
 (defthm the-top-term-mg-instance-variable-p-1
   (implies (and (mg-instance term t2)
                 (variable-p (mg-instance term t2)))
            (variable-p term))
   :hints (("Goal" :use
           ((:instance minimum-subsumption-implies-variable
                       (x (mg-instance term t2))))))))

(local
 (defthm the-top-term-mg-instance-variable-p-2
   (implies (and (mg-instance t1 term)
                 (variable-p (mg-instance t1 term)))
            (variable-p term))
   :hints (("Goal" :use
            ((:instance minimum-subsumption-implies-variable
                        (x (mg-instance t1 term))))))))


(local (in-theory (enable variable-minimum-subsumption)))

(local
 (defthm substitution-p-alistp-forward-chaining
   (implies (substitution-p sigma)
	    (alistp sigma))
   :rule-classes :forward-chaining))



;;; In the following, we will state (and mechanichally prove) the
;;; properties of a well founded lattice: the set of terms w.r.t
;;; subsumption.


;;; ============================================================================
;;; 2. Terms and substitutions
;;; ============================================================================


;;; Every object can be seen as a term (see terms.lisp for details). But
;;; we can define (extended) terms of a given signature:

(defun ext-term-s-p (term)
  (or (term-s-p term) (is-the-top-term term)))

;;; For guard verification purpouses, we can define well-formed
;;; (extended) terms:

(defun ext-term-p (term)
  (declare (xargs :guard t))
  (or (term-p term) (is-the-top-term term)))


;;; Every object can be seen as a substitution (see terms.lisp). But we
;;; can define (extended) substitutions of a given signature:


(defun ext-substitution-s-p (sigma)
  (or (substitution-s-p sigma) (is-the-top-substitution sigma)))



;;; For guard verification purpouses, we can define wel-formed
;;; (extended) substitutions:

(defun ext-substitution-p (sigma)
  (declare (xargs :guard t))
  (or (substitution-p sigma) (is-the-top-substitution sigma)))


;;; Applying substitutions to terms
;;; (see terms.lisp)

(defun app<= (sigma term)
  (declare (xargs :guard (and (ext-substitution-p sigma)
			      (ext-term-p term))))
  (if (or (is-the-top-substitution sigma)
	  (is-the-top-term term))
      (the-top-term)
    (instance term sigma)))



;;; ============================================================================
;;; 3. Subsumption relation between terms.
;;; ============================================================================

;;; (see subsumption-one-definition-and-properties.lisp for details)

(defun s<= (t1 t2)
  (declare (xargs :guard (and (ext-term-p t1)
			      (ext-term-p t2))))
  (cond  ((is-the-top-term t2) t)
	 ((is-the-top-term t1) nil)
	 (t (subs t1 t2))))

(defun match<= (t1 t2)
  (declare (xargs :guard (and (ext-term-p t1)
			      (ext-term-p t2))))
  (cond  ((is-the-top-term t2)
	  (the-top-substitution))
	 ((is-the-top-term t1)
	  nil)
	 (t (fix-substitution (matching t1 t2)))))


;;; Closure properties:

(defthm match<=-ext-substitution-s-p
  (implies (and (ext-term-s-p t1) (ext-term-s-p t2))
           (ext-substitution-s-p (match<= t1 t2))))


(defthm app<=-substitution-s-p
  (implies (and (ext-term-s-p term)
		(ext-substitution-s-p sigma))
	   (ext-term-s-p (app<= sigma term))))


;;; Relation between app<= and subsumption
;;; (see subsumption-one-definition-and-properties.lisp for details)

;;; If exists sigma such that t2 = (app<= sigma term), then term subsumes
;;; t2:

(defthm app<=-s<=-relationship-1

  (implies (equal t2 (app<= sigma t1))
	   (s<= t1 t2)))


;;; If t1 susbsumes t2, then exists a substitution s.t. applied to t1
;;; returns t2. That substitution is given by match<=.

(defthm app<=-s<=-relationship-2

  (implies (s<= t1 t2)
	   (equal (app<= (match<= t1 t2) t1) t2))

  :hints (("Goal" :in-theory (enable apply-atom))))



;;; ============================================================================
;;; 4. s<= is a quasi-ordering
;;; ============================================================================

;;; (see subsumption-one-definition-and-properties.lisp for details)


;;; Reflexivity

(defthm s<=-reflexivity

  (s<= term term))


;;; Transitivity

(defthm s<=-transitivity

  (implies (and (s<= t1 t2) (s<= t2 t3))
	   (s<= t1 t3))

  :hints (("Goal" :in-theory (enable subsumption-transitive))))



;;; ============================================================================
;;; 5. s<= is well-founded
;;; ============================================================================


;;; (see subsumption-well-founded.lisp for details)


;;; The strict part of s<=

(defun s< (t1 t2)
  (and (s<= t1 t2) (not (s<= t2 t1))))



;;; A measure on terms.

(defun measure-s< (term)
  (if (is-the-top-term term)
      (make-ord (omega) 1 0) ;;; This is omega^{omega}
    (subsumption-measure term)))

;;; The measure is an ordinal.

(defthm measure-s<-ordinalp

  (o-p (measure-s< term)))


;;; Strictly decreasing in s<= implies strictly decreasing in measure.

(in-theory (disable (:executable-counterpart make-ord)))
(in-theory (disable (:executable-counterpart measure-s<)))

(defthm s<-well-founded

  (implies (s< t1 t2)
	   (o< (measure-s< t1) (measure-s< t2))))

;;; REMARK:

;;; The above two lemmas implies in our meta-logic that there no
;;; infinite decreasing (w.r.t. s<) chain of terms. Thus, subsumption
;;; between first order terms is a well founded relation.


;;; ============================================================================
;;; 6. Greatest lower bound of two terms (w.r.t. s<=)
;;; ============================================================================

;;; (see anti-unification.lisp for details)

(defun glb-s<= (t1 t2)
  (declare (xargs :guard (and (ext-term-p t1) (ext-term-p t2))))
  (cond ((is-the-top-term t1) t2)
	((is-the-top-term t2) t1)
	(t (fix-term (anti-unify t1 t2)))))


;;; glb-s<= is a lower bound of t1 and t2.

(defthm glb-s<=-lower-bound-1

  (s<= (glb-s<= t1 t2) t1))


(defthm glb-s<=-lower-bound-2

  (s<= (glb-s<= t1 t2) t2))


;;; glb-s<= is greater (or equivalent) than any lower-bound.


(defthm glb-s<=-is-greater-than-any-lower-bound

  (implies (and (s<= term t1)
                (s<= term t2))
           (s<= term (glb-s<= t1 t2))))


;;; glb-s<= of two terms of a given signature is a term of that
;;; signature:

(defthm glb-s<=-closure-property
  (implies (and (ext-term-s-p t1) (ext-term-s-p t2))
           (ext-term-s-p (glb-s<= t1 t2))))

;;; ============================================================================
;;; 7. Least upper bound of two terms (w.r.t. s<=)
;;; ============================================================================
;;; (see mg-instance.lisp for details)


(defun lub-s<= (t1 t2)
  (declare (xargs :guard (and (ext-term-p t1) (ext-term-p t2))))
  (cond ((or (is-the-top-term t1)
	     (is-the-top-term t2))
	 (the-top-term))
	((mg-instance t1 t2) (fix-term (mg-instance t1 t2)))
	(t (the-top-term))))

;;; lub-s<= is an upper bound of t1 y t2

(defthm lub-s<=-upper-bound-1

  (s<= t1 (lub-s<= t1 t2)))


(defthm lub-s<=-upper-bound-2

  (s<= t2 (lub-s<= t1 t2)))


;;; lub-s<= es less (or equivalent) than any upper bound

(defthm lub-s<=-less-than-any-upper-bound

  (implies (and (s<= t1 term)
                (s<= t2 term))
           (s<= (lub-s<= t1 t2) term)))


;;; lub-s<= of two terms of a given signature is a term of that
;;; signature:

(defthm lub-s<=-closure-property
  (implies (and (ext-term-s-p t1) (ext-term-s-p t2))
           (ext-term-s-p (lub-s<= t1 t2))))



;;; CONCLUSION:

;;; So the set of objects of ACL2 logic is well-founded lattice
;;; w.r.t. the s<= relation (in particular this implies tha it is a
;;; complete lattice). And the set of terms of a given signature is a
;;; sublattice.
