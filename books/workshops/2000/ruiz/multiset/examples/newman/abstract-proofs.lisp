;;; abstract-proofs.lisp
;;; Definition and properties of abstract proofs.
;;; Created: 10-6-99 Last Revision: 05-10-00
;;; =============================================================================

(in-package "ACL2")

(include-book "../../../../../../data-structures/structures")
(local (include-book "../../../../../../ordinals/e0-ordinal"))

;;; *******************************************
;;; ABSTRACT PROOFS: DEFINITIONS AND PROPERTIES
;;; *******************************************

;;; ============================================================================
;;; 1. Proof steps
;;; ============================================================================

;;; We see here proofs from a very general point of view. Proofs are
;;; lists of r-steps, and r-steps are structures with four fields:
;;; elt1, elt2, direct and operator (every step "connect" elt1 and elt2
;;; in the direction given by direct, and by application of operator).

;;; Definition and properties about manipulation of proofs and its form
;;; are given here.

;;; The following is the definition of an abstract reduction step:

(defstructure r-step
   direct
   operator
   elt1
   elt2
   (:options (:conc-name nil)
	     (:do-not :tag)))

;;; REMARK: An abstract proof will be defined as a list of r-steps. Note
;;; that, in this book, we do not require that the operator is applicable
;;; to one of the elements returning the other. This will be required
;;; for each particular reduction relation. We are only concerned with the
;;; "shape" of proofs.


;;; ============================================================================
;;; 2. Useful definitions
;;; ============================================================================

;;; The last element of a non-empty list

(defmacro last-elt (l)
  `(car (last ,l)))

;;; First and last elements of a proof (including empty proofs)

(defun first-of-proof (x p)
   (if (endp p) x (elt1 (car p))))

(defun last-of-proof (x p)
   (if (endp p) x (elt2 (last-elt p))))

;;; Steps-up: A chain of inverse steps

(defun steps-up (p)
   (if (endp p)
       t
     (and
      (not (direct (car p)))
      (steps-up (cdr p)))))

;;; Steps-down: A chain of direct steps

(defun steps-down (p)
   (if (endp p)
       t
     (and
      (direct (car p))
      (steps-down (cdr p)))))

;;; Steps-valley: down and up

(defun steps-valley (p)
   (cond ((endp p) t)
	 ((direct (car p)) (steps-valley (cdr p)))
	 (t (steps-up (cdr p)))))


;;; Steps-mountain: up and down

(defun steps-mountain (p)
   (cond ((endp p) t)
	 ((direct (car p)) (steps-down (cdr p)))
	 (t (steps-mountain (cdr p)))))


;;; A local peak

(defun local-peak-p (p)
   (and (consp p)
	(consp (cdr p))
	(atom (cddr p))
	(not (direct (car p)))
	(direct (cadr p))))


;;; Inverse step

(defun inverse-r-step (st)
   (make-r-step
    :direct (not (direct st))
    :elt1 (elt2 st)
    :elt2 (elt1 st)
    :operator (operator st)))

;;; The piece of proof just before the first local-peak

(defun proof-before-peak (p)
  (cond ((or (atom p) (atom (cdr p))) p)
	((and (not (direct (car p))) (direct (cadr p))) nil)
	(t (cons (car p) (proof-before-peak (cdr p))))))

;;; The piece of proof just after the first local peak

(defun proof-after-peak (p)
  (cond ((atom p) p)
	((atom (cdr p)) (cdr p))
	((and (not (direct (car p))) (direct (cadr p)))
	 (cddr p))
	(t (proof-after-peak (cdr p)))))

;;; The first peak of a proof

(defun local-peak (p)
  (cond ((atom p) p)
	((atom (cdr p)) (cdr p))
	((and (not (direct (car p))) (direct (cadr p)))
	 (list (car p) (cadr p)))
	(t (local-peak (cdr p)))))

;;; The top element of a peak

(defun peak-element (p)
   (elt1 (cadr (local-peak p))))

;;; The down part of a valley

(defun proof-before-valley (p)
  (cond ((atom p) p)
	((direct (car p)) (cons (car p)
				(proof-before-valley (cdr p))))
	(t nil)))

;;; Inverse proof

(defun inverse-proof (p)
   (if (atom p)
       p
     (append (inverse-proof (cdr p))
	     (list (inverse-r-step (car p))))))

;;; The up part of a valley

(defun proof-after-valley (p)
  (cond ((atom p) p)
	((direct (car p)) (proof-after-valley (cdr p)))
	(t p)))

;;; The list of elements involved in a proof

(defun proof-measure (p)
  (if (endp p)
      nil
    (cons (elt1 (car p)) (proof-measure (cdr p)))))


;;; ============================================================================
;;; 3. Useful properties
;;; ============================================================================

(defthm steps-down-append
  (equal (steps-down (append p1 p2))
	 (and (steps-down p1) (steps-down p2))))

(defthm steps-up-append
  (equal (steps-up (append p1 p2))
	 (and (steps-up p1) (steps-up p2))))


(defthm steps-valley-append
  (implies (and (steps-down p1)
		(steps-up p2))
	   (steps-valley (append p1 p2))))


(defthm steps-mountain-append
  (implies (and (steps-up p1)
		(steps-down p2))
	   (steps-mountain (append p1 p2))))


(defthm steps-up-inverse-proof
  (equal
   (steps-up (inverse-proof p))
   (steps-down p)))


(defthm steps-down-inverse-proof
  (equal
   (steps-down (inverse-proof p))
   (steps-up p)))


(defthm proof-measure-append
  (equal (proof-measure (append p1 p2))
	 (append (proof-measure p1)
		 (proof-measure p2))))


(defthm steps-down-proof-before-valley
  (steps-down (proof-before-valley p)))


(defthm steps-up-proof-before-valley
  (implies (steps-valley p)
	   (steps-up (proof-after-valley p))))


(defthm proof-valley-append
  (equal
   (append (proof-before-valley p)
	   (proof-after-valley p))
   p)
  :rule-classes nil)

(defthm first-element-of-proof-before-valley
  (implies (consp (proof-before-valley p))
	   (equal (elt1 (car (proof-before-valley p)))
		  (elt1 (car p)))))

(defthm last-element-of-proof-after-valley
   (implies (consp (proof-after-valley p))
 	   (equal (elt2 (last-elt (proof-after-valley p)))
 		  (elt2 (last-elt p)))))


(defthm steps-valley-append-steps-up
  (implies (and (steps-up p2)
		(steps-valley p1))
	   (steps-valley (append p1 p2))))

(defthm steps-dowm-append-steps-valley
  (implies (and (steps-down p1)
		(steps-valley p2))
	   (steps-valley (append p1 p2))))

(defthm steps-up-steps-valley
  (implies (steps-up p)
	   (steps-valley p)))

(defthm steps-down-steps-valley
  (implies (steps-down p)
	   (steps-valley p)))

(defthm steps-valley-inverse-proof
  (implies (steps-valley p)
	   (steps-valley (inverse-proof p))))



