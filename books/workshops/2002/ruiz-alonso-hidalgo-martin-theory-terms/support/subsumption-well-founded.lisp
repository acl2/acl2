;;; subsumption-well-founded.lisp
;;; Well-foundedness of the subsumption relation
;;; Created: 8-10-99 Last revison: 09-12-2000
;;; =============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "subsumption-well-founded")

|#

(in-package "ACL2")
(local (include-book "renamings"))
(include-book "subsumption")
(include-book "../../../../ordinals/ordinals-without-arithmetic")

;;; *******************************************************
;;; A PROOF OF WELL-FOUNDEDNESS OF THE SUBSUMPTION RELATION
;;; *******************************************************

;;; We will prove that the following ordinal measure:
;;; (defun subsumption-measure (term)
;;;   (cons (1+ (size t term))
;;;	 (- (len (variables t term))
;;;	    (len (make-set (variables t term))))))
;;; is order-preserving with respect the stric subsumption relation.

;;; That is to say:
;;; - If (subs t1 t2), then (size t t1) is less or equal than (size t
;;; t2).
;;; - If, in addition, (not (subs t2 t1)) and (size t t1) = (size t t2),
;;; then the number of distinct variables of t1 is greater than the
;;; number of distinct variables of t2, and both of them are at most the
;;; number of variable positions of t1 (or t2).

;;; Note that the properties described below only use the soundness and
;;; completeness  properties of the subsumption algorithm given in
;;; subsumption-one-definition-and-properties.lisp: The
;;; definition and executable-counterpart of subs, matching and subs-mv
;;; are disabled.


;;; ============================================================================
;;; 1. Preliminaries
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 1.1 val-mapcar and properties
;;; ----------------------------------------------------------------------------

;;; ===== VAL-MAPCAR
;;; The list of values returned by delta for the elements of the list l

(local
 (defun val-mapcar (delta l)
   (if (atom l)
       nil
     (cons (val (car l) delta) (val-mapcar delta (cdr l))))))

;;; Properties:

(local
 (defthm val-map-car-append
  (equal (val-mapcar delta (append l m))
	 (append (val-mapcar delta l) (val-mapcar delta m)))))

(local
 (defthm val-mapcar-elimination-1
  (implies (not (member x l))
	   (equal (val-mapcar (cons (cons x y) delta) l)
		  (val-mapcar delta l)))))


(local
 (defthm val-mapcar-elimination-2
  (implies (and (atom x)
		(not (member nil l)))
		(equal (val-mapcar (cons x delta) l)
		       (val-mapcar delta l)))))


(local
 (defthm val-mapcar-main-lemma
  (implies (member x l)
	   (member (val x delta) (val-mapcar delta l)))))

(local
 (encapsulate
  ()
  (local
   (defthm val-mapcar-only-one-make-set-is-needed-lemma-1
     (implies (member x (val-mapcar delta (make-set m)))
	      (member x (val-mapcar delta m)))))

  (local
   (defthm  val-mapcar-only-one-make-set-is-needed-lemma-2
     (implies (member x (val-mapcar delta m ))
	      (member x (val-mapcar delta (make-set m))))))


  (defthm  val-mapcar-only-one-make-set-is-needed
    (equal (make-set (val-mapcar delta (make-set l)))
	   (make-set (val-mapcar delta l))))))

(local
 (defthm length-val-mapcar
   (equal (len (val-mapcar delta l)) (len l))))


;;; ----------------------------------------------------------------------------
;;; 1.2 variable-substitution:  definition and properties
;;; ----------------------------------------------------------------------------

;;; A substitution is a variable substitution if every element in its
;;; co-domain is a variable.


;;; Properties:

(local
 (defthm variable-substitution-make-set-append
   (implies (and (variable-substitution (restriction delta (make-set l)))
		 (variable-substitution (restriction delta (make-set m))))
	    (variable-substitution
	     (restriction delta (make-set (append l m)))))))



(local
 (defthm variable-substitution-value-variable-p
   (implies (and (variable-substitution delta)
		 (variable-p term))
	    (variable-p (val term delta)))))


;;; value of variable substitutions are variables:

(local
 (defthm variable-p-value
   (implies (and (variable-substitution delta)
		 (member x (domain delta)))
	    (variable-p (val x delta)))))


;;; If delta is a variable substitution, the the variables of delta(t1)
;;; are obtained mapping the variables of t1 by the val of delta.



(local
 (defthm variables-apply-subst-variable-substitution
   (implies (variable-substitution delta)
	    (equal
	     (val-mapcar delta (variables flg term))
	     (variables flg (apply-subst flg delta term))))))


;;; An additional lemma:
(local
 (defthm val-domain-in-co-domain
   (implies (member x (domain delta))
	    (member (val x delta) (co-domain delta)))))




;;; ============================================================================
;;; 2. The main part of the proof.
;;; ============================================================================


;;; size(t1) <= size(sigma(t1))

(local
 (defthm size-instance-geq
   (>= (size flg (apply-subst flg sigma t1))
       (size flg t1))
   :rule-classes :linear))


;;; If t1 and sigma(t1) have the same size, sigma restricted to the set
;;; of variables of t1 is a variable substitution. That's the reason why
;;; we need the properties of subsection 1.2


(local
 (defthm size-equal-variable-substitution
   (implies (equal (size flg t1) (size flg (apply-subst flg sigma t1)))
	    (variable-substitution
	      (normal-form-subst flg sigma t1)))))


;;; If t1 and sigma(t1) have equal size, and the inverse substitution of
;;; the restriction of sigma to the variables of t1 applied to sigma(t1)
;;; is different from t1, then such substitution (which is a variable
;;; substitution, by the above lemma), IS NOT injective (i.e., its
;;; co-domain is not a set).
;;; Note that the hypothesis of the lemma are met as a particular case
;;; of  (subs t1 t2), (not (subs t2 t1)), and (size t t1) = (size t t2).

(local
 (encapsulate
  ()

;;; This is almost the intended lemma, but for the restriction of sigma
;;; to the set of variables of t1, instead of sigma.
  (local
   (defthm
     equal-size-and-not-inverse-subsumption-implies-not-renaming-almost
     (let ((sigmar (normal-form-subst flg sigma t1)))
       (implies
	(and
	 (not (equal (apply-subst flg (inverse sigmar)
				  (apply-subst flg sigmar t1)) t1))
	 (equal (size flg t1) (size flg (apply-subst flg sigma t1))))
	(not (setp (co-domain sigmar)))))
     :hints (("Goal" :in-theory (disable subsetp-restriction)))))
;;; REMARK: Intentar que esta se hage so'lo aplicando la reglka de
;;; renamings.lisp

;;; The intended lemma:
 (defthm
    equal-size-and-not-inverse-subsumption-implies-not-renaming
    (let ((sigmar (normal-form-subst flg sigma t1)))
      (implies
       (and
	(not (equal (apply-subst flg (inverse sigmar)
				 (apply-subst flg sigma t1))
		    t1))
	(equal (size flg t1) (size flg (apply-subst flg sigma t1))))
       (not (setp (co-domain sigmar))))))))



;;; If a substitution is not injective (i.e., its co-domain is not a
;;; set), then the length of the set of elements of the co-domain is
;;; less than the length of the domain.

(local
 (defthm not-injective-implies-co-domain-lessp-than-domain
   (implies (not (setp (co-domain delta)))
	    (< (len (make-set (co-domain delta)))
	       (len (domain delta))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable same-length-co-domain-and-domain)))))





;;; Relation between domain and co-domain. That is the reason why we
;;; need the properties of 1.2.



(local
 (defthm co-domain-val-mapcar
    (implies (setp (domain delta))
	   (equal (co-domain delta)
		  (val-mapcar delta (domain delta))))))

;;; NOTE: this is not true if the domain is not a set



;;; -------------------------------------------------------------------------
;;; REMARK:
;;; The above lemmas implies the following two results:

;;; Let sigmar = (restriction sigma (make-set (variables flg t1))), then
;;;
;;; I) IF sigmar is a variable-substitution THEN
;;; (make-set (co-domain sigmar))
;;;        =
;;; (make-set (variables flg (apply-subst flg sigma t1))),
;;;

;;; WITH THE FOLLOWING PROOF SKETCH:

;;; (make-set (co-domain (restriction sigma
;;;                           (make-set (variables flg t1))))))
;;;
;;; = (** USING co-domain-val-mapcar and (setp (domain sigmar)) **)
;;;
;;; (make-set (val-mapcar sigma (domain (restriction sigma
;;;                                  (make-set (variables flg t1))))))
;;;
;;; = (** USING domain-restriction **)
;;;
;;; (make-set (val-mapcar sigma (make-set (variables flg t1))))
;;;
;;; = (** USING val-mapcar-only-one-make-set-is-needed **)
;;;
;;; (make-set (val-mapcar sigma (variables flg t1)))
;;;
;;; = (** USING variables-apply-substing-variable-substitution, because sigmar
;;;     is a variable-substitution **)
;;;
;;; (make-set (variables flg (apply-subst flg sigma t1)))



;;;
;;; II) ALSO,
;;; (domain sigmar) = (make-set (variables flg t1)),
;;;                  (** USING domain-restriction **)
;;;


;;; These are the following theorem. WE DON'T USE them, its only for
;;; presentation of the result (there are some problems with the
;;; orientation of the rule).
(local
 (defthm n-variables-decreases-lemma-2
   (let ((sigmar (normal-form-subst flg sigma t1)))
     (implies
      (equal (size flg t1) (size flg (apply-subst flg sigma t1)))
      (equal (make-set (co-domain sigmar))
	     (make-set (variables flg (apply-subst flg sigma t1))))))
   :rule-classes nil))

(local
 (defthm n-variables-decreases-lemma-1
   (let ((sigmar (normal-form-subst flg sigma t1)))
      (equal (domain sigmar) (make-set (variables flg t1))))
   :rule-classes nil))


;;; -------------------------------------------------------------------------

(local
 (encapsulate
  ()


;;; The following lemma is a bridge between domain and co-domains and
;;; the set of variables, using the above proof sketch.

  (local
   (defthm n-variables-decreases-bridge-lemma
     (let ((sigmar (normal-form-subst flg sigma t1)))
       (implies
	(and
	 (equal (size flg t1) (size flg (apply-subst flg sigma t1)))
	 (< (len (make-set (co-domain sigmar)))
	    (len (domain sigmar))))
	(< (len (make-set (variables flg (apply-subst flg sigma t1))))
	   (len (make-set (variables flg t1))))))
     :rule-classes :linear))

;;; If size(t1) = size(sigma(t1)) and t1 is not an instance of sigma(t1)
;;; then the number of variables of t1 is greater tha the number of
;;; variables of sigma(t1)

  (defthm n-variables-decreases
    (let ((sigmar (normal-form-subst flg sigma t1)))
      (implies
       (and
	(equal (size flg t1) (size flg (apply-subst flg sigma t1)))
	(not (equal (apply-subst flg
				 (inverse sigmar)
				 (apply-subst flg sigma t1))
		    t1)))

       (< (len (make-set (variables flg (apply-subst flg sigma t1))))
	  (len (make-set (variables flg t1))))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (disable domain-restriction))))))



(local
 (encapsulate
  ()

;;; If delta is a variable substitution, then the length of the list of
;;; variables of t1 and the list of variables of delta(t1) is the same.
;;; Note that this common length is the number of variable positions of
;;; t1.

  (local
   (defthm n-variables-bounded-substitution-variable-almost
     (implies (variable-substitution delta)
	      (equal (len (variables flg (apply-subst flg delta term)))
		     (len (variables flg term))))
     :hints (("Goal"
	      :use (:instance variables-apply-subst-variable-substitution)
	      :in-theory
	      (disable variables-apply-subst-variable-substitution)))))


;;; The following lemma gives a bound for the number of distinct
;;; variables of the terms of a chain t1 <= t2 <= t3 <= ..., all having
;;; the same size. This bound is the number of variables positions of t1.

  (defthm n-variables-bounded-substitution-variable
    (implies (variable-substitution
	      (normal-form-subst flg sigma t1))
	     (equal (len (variables flg (apply-subst flg sigma t1)))
		    (len (variables flg t1))))
    :hints (("Goal"
	     :use
	     ((:instance
	       n-variables-bounded-substitution-variable-almost
	       (term t1)
	       (delta (restriction sigma
				   (make-set (variables flg t1)))))))))))



;;; A technical lemma


(local
 (defthm completeness-in-reverse-order
   (implies (not (subs t1 t2))
	    (not (equal (instance t1 delta) t2)))
   :hints (("Goal" :use (:instance subs-completeness)))))


;;; ============================================================================
;;; 3. The well-foundedness theorem
;;; ============================================================================

;;; ===== SUBSUMPTION-MEASURE
;;; An ordinal measure to prove well-foundedness of subsumption.
;;; The lexicographic combination of the size of the term and the
;;; difference between the number of variable positions and the number
;;; of distinct variables.


(defun subsumption-measure (term)
  (make-ord (1+ (size t term))
	    1
	    (- (len (variables t term))
	       (len (make-set (variables t term))))))


;;; Lemma: well-foundedness, instance version

(local
 (defthm subsumption-well-founded-instance-version
   (implies (not (subs (instance t1 sigma) t1))
	    (o< (subsumption-measure t1)
		(subsumption-measure (instance t1 sigma))))
   :rule-classes nil))


;;; Lemma: subsumption-measure, o-p

(local
 (defthm subsumption-measure-o-p
   (o-p (subsumption-measure term))))

;;; An upper bound for subsumption-measure (omega^{omega})


(defthm subsumption-measure-upper-bounded
  (o< (subsumption-measure term) (make-ord (omega) 1 0)))

;;; REMARK: This lemma is not needed here, but will be useful in
;;; lattice-of-terms.lisp where an additional top term is added.


(in-theory (disable subsumption-measure))


;;; ======== STRICT-SUBS
;;; The strict subsumption relation

(defun strict-subs (t1 t2)
  (and (subs t1 t2) (not (subs t2 t1))))


;;; ===============================
;;; The well-foundedness theorem
;;; ===============================


(defthm subsumption-well-founded
  (and (o-p (subsumption-measure t1))
       (implies (strict-subs t1 t2)
		(o< (subsumption-measure t1)

                    (subsumption-measure t2))))
  :rule-classes (:rewrite :well-founded-relation)
  :hints (("Goal" :use
	   (:instance subsumption-well-founded-instance-version
		      (sigma (matching t1 t2))))))
