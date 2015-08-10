;;; subsumption.lisp Definition of a particular RULE-BASED matching
;;; algorithm between terms.  We use functional instantion of the
;;; pattern given in matching.lisp Using this algorithm, we define the
;;; subsumption relñation between terms and lists of terms in a
;;; constructive way, and we prove that subsumption is a preorder.
;;; Created: 11-10-99 Last revison: 07-12-2000
;;; =============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "subsumption")

|#

(in-package "ACL2")
(local (include-book "matching"))
(include-book "terms")

;;; *************************************************
;;; A PARTICULAR AND EXECUTABLE SUBSUMPTION ALGORITHM
;;; *************************************************

;;; Here we show how we can obtain a correct subsumption algorithm from
;;; the "pattern"  verified in subsumption-definition.lisp:
;;; - We define a particular selection function.
;;; - We introduce multi-values to deal with the pair of systems
;;;   S-match.
;;; - Some other minor improvements concerning efficency are done.
;;; - Guards are verified, allowing execution in raw Common Lisp.

;;; ============================================================================
;;; 1. The subsumption algorithm between terms
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 1.1 A particular version of transform-subs
;;; ----------------------------------------------------------------------------

;;; Selection function. If we detect an inmediate fail, we select it.

(defun sel-match (S)
  (declare (xargs :guard (and (consp S) (system-p S))))
  (if (endp (cdr S))
      (car S)
    (let* ((equ (car S))
	   (t1 (car equ))
	   (t2 (cdr equ)))
	(cond ((variable-p t1)
	       (sel-match (cdr S)))
	      ((variable-p t2) equ)
	      ((eql (car t1) (car t2))
	       (sel-match (cdr S)))
	      (t equ)))))

;;; Main property, needed to instantiate from
;;; subsumption-definition.lisp:
(local
 (defthm sel-match-select-a-pair
   (implies (consp S)
	    (member (sel-match S) S))))


;;; The following lemmas help the guard verification of
;;; transform-subs (although they are not strictly needed)

(local
 (defthm sel-match-consp
   (implies (and (consp S)
		 (alistp S))
	    (consp (sel-match S)))
   :rule-classes :type-prescription))


(encapsulate
 ()
 (local
  (defthm transform-subs-guard-verification-stuff-1
    (implies (and (system-p S)
		  (member equ S))
	     (and
	      (implies (variable-p (car equ)) (eqlablep (car equ)))
	      (implies (variable-p (cdr equ)) (eqlablep (cdr equ)))))))


 (local
  (defthm transform-subs-guard-verification-stuff-2
    (implies (and (system-p S)
		  (member equ S))
	     (and
	      (eqlablep (cadr equ))
	      (true-listp (cdar equ))
	      (true-listp (cddr equ))
	      (iff (variable-p (car equ)) (eqlablep (car equ)))
	      (iff (variable-p (cdr equ)) (eqlablep (cdr equ)))))))

;;; The rules of transformation:

 (defun transform-subs (S match)
   (declare (xargs :guard (and (consp S) (system-p S)
			       (alistp match))))
   (let* ((ecu (sel-match S))
	  (t1 (car ecu)) (t2 (cdr ecu))
	  (R (eliminate ecu S)))
     (cond
      ((variable-p t1)
       (let ((bound (assoc t1 match)))
	 (if bound
	     (if (equal (cdr bound) t2)
		 (mv R match t)
	       (mv nil nil nil))
	   (mv R (cons (cons t1 t2) match) t))))
      ((variable-p t2) (mv nil nil nil))
      ((eql (car t1) (car t2))
       (mv-let (empareja bool)
	       (pair-args (cdr t1) (cdr t2))
	       (if bool
		   (mv (append empareja R) match t)
		 (mv nil nil nil))))
      (t (mv nil nil nil))))))


;;; REMARK: transform-subs will not be the counterpart of
;;; transform-subs in our functional instantiation. Instead we have to
;;; define a function acting on pair of systems:

(local
 (defun transform-subs-bridge (S-match)
   (mv-let (S1 match1 bool1)
	   (transform-subs (car S-match) (cdr S-match))
	   (if bool1 (cons S1 match1) nil))))

;;; ----------------------------------------------------------------------------
;;; 1.2 A particular version of a matching algorithm for systems of equations
;;; ----------------------------------------------------------------------------


;;; Termination properties of transform-subs.

(local
 (defthm transform-subs-decreases-length-of-first-system
   (implies (consp S)
	    (< (length-system (first (transform-subs S match)))
		(length-system S)))
   :hints (("Goal" :use ((:functional-instance
			  (:instance
			   transform-subs-sel-decreases-length-of-first-system
			   (S-match (cons S match)))
			  (transform-subs-sel transform-subs-bridge)
			  (a-pair sel-match)))))))

;;; A particular version of subs-system

(defun subs-system (S match bool)
  (declare (xargs
 	    :guard (and (system-p S) (alistp match))
	    :measure (length-system S)
	    :hints (("Goal" :in-theory (disable transform-subs)))))
  (if (or (not bool) (not (consp S)))
      (mv S match bool)
    (mv-let (S1 match1 bool1)
	    (transform-subs S match)
	    (subs-system S1 match1 bool1))))

;;; Matching algorithm for systems of equations:

(defun match-mv (S)
  (declare (xargs :guard (system-p S)))
  (mv-let (S1 sol1 bool1)
	  (subs-system S nil t)
	  (declare (ignore S1))
	  (mv sol1 bool1)))

;;; REMARK: Again, subs-system and match-mv will not be the counterpart
;;; of subs-system-sel, match-sel in our functional instantiation,
;;; because of signature mismatch. Instead we have to
;;; define functions acting on pair of systems:

(local
 (defun subs-system-bridge (S-match)
   (if (normal-form-syst S-match)
       S-match
     (mv-let (S1 match1 bool1)
	     (subs-system (car S-match) (cdr S-match) t)
	     (if bool1 (cons S1 match1) nil)))))



(local
 (defun match-mv-bridge (S)
   (let ((subs-system-bridge (subs-system-bridge (cons S nil))))
     (if subs-system-bridge (list (cdr subs-system-bridge)) nil))))



;;; ----------------------------------------------------------------------------
;;; 1.3 Main properties of the matching algorithm for systems of equations
;;; ----------------------------------------------------------------------------

;;; Some technical lemmas

(local
 (defthm booleanp-third-subs-system
   (implies (booleanp bool)
	    (booleanp (third (subs-system S match bool))))
   :rule-classes :type-prescription))

(local
 (defthm nil-third-implies-nil-second-subs-system
   (implies (not (third (subs-system s match t)))
	    (not (second (subs-system s match t))))))

;;; And the main properties of match-mv

(defthm match-mv-soundness
  (implies (second (match-mv S))
	   (matcher (first (match-mv S)) S))
  :hints (("Goal" :use ((:functional-instance
			 match-sel-soundness
			 (match-sel match-mv-bridge)
			 (subs-system-sel subs-system-bridge)
			 (transform-subs-sel transform-subs-bridge)
			 (a-pair sel-match))))))


(defthm match-mv-completeness
  (implies (matcher sigma S)
	   (second (match-mv S)))
  :hints (("Goal" :use ((:functional-instance
			 match-sel-completeness
			 (match-sel match-mv-bridge)
			 (subs-system-sel subs-system-bridge)
			 (transform-subs-sel transform-subs-bridge)
			 (a-pair sel-match))))))


(defthm match-mv-substitution-s-p
  (implies (system-s-p S)
	   (substitution-s-p (first (match-mv S))))
  :hints (("Goal" :use ((:functional-instance
			 match-sel-substitution-s-p
			 (match-sel match-mv-bridge)
			 (subs-system-sel subs-system-bridge)
			 (transform-subs-sel transform-subs-bridge)
			 (a-pair sel-match))))))


;;; ----------------------------------------------------------------------------
;;; 1.4 A particular and executable version of subsumption of two terms.
;;; ----------------------------------------------------------------------------

;;; The subsumption algorithm

(defun subs-mv (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (match-mv (list (cons t1 t2))))

;;; The subsumption relation

(defun subs (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mv-let (matching subs)
	  (subs-mv t1 t2)
	  (declare (ignore matching))
	  subs))

;;; The witness substitution for matching (when (subs t1 t2))

(defun matching (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mv-let (matching subs)
	  (subs-mv t1 t2)
	  (declare (ignore subs))
	  matching))


;;; REMARK:
;;; subs-mv will be used to compute the subsumption relation and
;;; matching substitutions at the same time. The functions subs and
;;; matching are defined to be used in the statements of theorems.


;;; ----------------------------------------------------------------------------
;;; 1.5 Fundamental properties of subs, matching and subs-mv
;;; ----------------------------------------------------------------------------
;;; Most of these properties are obtained by functional instantiation.

;;; Soundness
;;; ·········

(defthm subs-soundness
  (implies (subs t1 t2)
	   (equal (instance t1 (matching t1 t2)) t2))
  :rule-classes (:rewrite :elim)
  :hints (("Goal" :use
	   (:instance match-mv-soundness (S (list (cons t1 t2)))))))


;;; Completeness
;;; ·············

(defthm subs-completeness
  (implies (equal (instance t1 sigma) t2)
	   (subs t1 t2))
  :rule-classes nil
  :hints (("Goal" :use
	   (:instance match-mv-completeness (S (list (cons t1 t2)))))))

;;; Substitution-s-p (closure property)
;;; ···································


(defthm matching-substitution-s-p
  (implies (and (term-s-p t1) (term-s-p t2))
	   (substitution-s-p (matching t1 t2)))
  :hints (("Goal" :use
	   (:instance match-mv-substitution-s-p (S (list (cons t1 t2)))))))

;;; Substitution-p (needed for guard verification)
;;; ··············································


(defthm matching-substitution-p
  (implies (and (term-p t1) (term-p t2))
	   (substitution-p (matching t1 t2)))
  :hints (("Goal" :use (:functional-instance
			matching-substitution-s-p
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)
			(substitution-s-p substitution-p)))))

;;; Later, We will disable match-mv, subs-mv, matching and subs and
;;; their executable counter-parts, to be sure that ONLY the above two
;;; properties are used in the sequel. But before doing this, we state
;;; the relations between subs-mv and subs and matching. Note that, from
;;; now on, we will not assume any relations between match-mv and
;;; subs-mv

(defthm subs-mv-subs
  (equal (second (subs-mv t1 t2)) (subs t1 t2)))

(defthm subs-mv-matching
  (equal (first (subs-mv t1 t2)) (matching t1 t2)))



;;; ============================================================================
;;; 2. The subsumption algorithm between lists of terms
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 2.1 Subsumption between lists of terms
;;; ----------------------------------------------------------------------------

;;; Sometimes it will be useful to talk abou subsumption between lists
;;; of terms (see, for example, kb/critical-pairs.lisp). We define here
;;; such concept and its main properties, in a similar way to subs.

;;; The subsumption algorithm (between lists of terms)

(defun subs-list-mv (l1 l2)
  (declare (xargs :guard (and (term-p-aux nil l1)
			      (term-p-aux nil l2))))
    (mv-let (pair-lists bool)
	    (pair-args l1 l2)
	    (if bool (match-mv pair-lists) (mv nil nil))))



;;; The subsumption relation between lists of terms

(defun subs-list (l1 l2)
  (declare (xargs :guard (and (term-p-aux nil l1)
			      (term-p-aux nil l2))))
  (mv-let (matching subs-list)
	  (subs-list-mv l1 l2)
	  (declare (ignore matching))
	  subs-list))

;;; The witness substitution for matching lists of terms (when
;;; (subs-list l1 l2))

(defun matching-list (l1 l2)
  (declare (xargs :guard
		  (and (term-p-aux nil l1)
		       (term-p-aux nil l2))))
  (mv-let (matching subs-list)
	  (subs-list-mv l1 l2)
	  (declare (ignore subs-list))
	  matching))


;;; ----------------------------------------------------------------------------
;;; 2.2 Main properties of subsumption between lists of terms
;;; ----------------------------------------------------------------------------

;;; Two previous lemmas relating matcher with instances:

(local
 (defthm matcher-apply-subst-nil
   (implies (second (pair-args l1 l2))
	    (iff (matcher sigma (first (pair-args l1 l2)))
		 (equal (apply-subst nil sigma l1) l2)))))


(local
 (defthm apply-subst-nil-pair-args
   (second (pair-args l1 (apply-subst nil sigma l1)))))

;;; Soundness
;;; ·········


(defthm subs-list-soundness
  (implies (subs-list l1 l2)
	   (equal (apply-subst nil (matching-list l1 l2) l1) l2))
  :rule-classes (:rewrite :elim)
  :hints (("Goal" :use
	   (:instance match-mv-soundness (S (first (pair-args l1 l2)))))))


;;; Completeness
;;; ·············

(defthm subs-list-completeness
  (implies (equal (apply-subst nil sigma l1) l2)
	   (subs-list l1 l2))
  :rule-classes nil
  :hints (("Goal" :use
	   (:instance match-mv-completeness (S (first (pair-args l1 l2)))))))

;;; Substitution-s-p (closure property)
;;; ···································


(defthm matching-list-substitution-s-p
  (implies (and (term-s-p-aux nil l1) (term-s-p-aux nil l2))
	   (substitution-s-p (matching-list l1 l2)))
  :hints (("Goal" :use
	   (:instance match-mv-substitution-s-p
		      (S (first (pair-args l1 l2)))))))



;;; Substitution-p (needed for guard verification)
;;; ··············································


(defthm matching-list-substitution-p
  (implies (and (term-p-aux nil l1)
		(term-p-aux nil l2))
	   (substitution-p (matching-list l1 l2)))
  :hints (("Goal" :use (:functional-instance
			matching-list-substitution-s-p
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)
			(substitution-s-p substitution-p)))))


;;; As with subs, we will disable the definitions related to subs-list to be
;;; sure that ONLY the above two properties are used in the sequel. But
;;; before doing this, we state the relations between subs-list-mv and subs-list
;;; and matching-list.

(defthm subs-list-mv-subs-list
  (equal (second (subs-list-mv t1 t2)) (subs-list t1 t2)))

(defthm subs-list-mv-matching-list
  (equal (first (subs-list-mv t1 t2)) (matching-list t1 t2)))


(in-theory
 (disable
  subs-list-mv (subs-list-mv) subs-list (subs-list) matching-list
  (matching-list)))



;;; ============================================================================
;;; 3. Properties of the subsumption relation
;;; ============================================================================


(in-theory
 (disable
  match-mv (match-mv) subs-mv (subs-mv) subs (subs) matching (matching)))


;;; REMARK: Note that the properties described below only use the
;;; soundness and completeness properties of the subsumption
;;; algorithm (the definition and executable-counterpart of subs
;;; are disabled)


;;; ----------------------------------------------------------------------------
;;; 3.1 Subsumption is a quasi-order
;;; ----------------------------------------------------------------------------

;;;; Subsumption reflexive
;;;; ·····················

(defthm subsumption-reflexive
   (subs t1 t1)
   :hints (("Goal" :use (:instance
 			 subs-completeness
 			 (sigma nil) (t2 t1)))))


;;;; Subsumption transitive
;;;; ······················


(defthm subsumption-transitive
   (implies (and (subs t1 t2) (subs t2 t3))
	    (subs t1 t3))
   :hints (("Goal" :use ((:instance
 			 subs-completeness
 			 (sigma (composition
 				 (matching t2 t3)
 				 (matching t1 t2)))
 			 (t2 t3))))))

(in-theory (disable subsumption-transitive ))

;;; ----------------------------------------------------------------------------
;;; 3.2 Several properties of subsumption
;;; ----------------------------------------------------------------------------

;;; An useful rule:
;;; ···············

(defthm subsumption-apply-subst
  (subs term (instance term sigma))
  :hints (("Goal" :use (:instance subs-completeness
				  (t1 term) (t2 (instance term sigma))))))

;;; Variables are minimum elements in this quasi-order
;;; ··················································

(defthm variable-minimum-subsumption
  (implies (variable-p x)
	   (subs x term))
  :hints (("Goal" :use ((:instance subs-completeness
				   (sigma (list (cons x term)))
				   (t1 x)
				   (t2 term))))))

(in-theory (disable variable-minimum-subsumption))

(defthm minimum-subsumption-implies-variable
  (implies (and (variable-p x) (subs term x))
	   (variable-p term))
  :hints (("Goal" :use (:instance
			apply-returns-variable-implies-variable
			(flg t) (sigma (matching term x)))))
  :rule-classes nil)








