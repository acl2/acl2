;;; ackermann.lisp
;;; Admissibility of an iterative version of Ackermann function.
;;; Created: 06-06-2000 Last Revised: 19-09-00
;;;============================================================================

;;; To certify this book:

#|
(in-package "ACL2")
(certify-book "ackermann")
|#

(in-package "ACL2")

(include-book "../../defmul")
(set-well-founded-relation e0-ord-<)

;;;****************************************************************************
;;; USING MULTISETS RELATIONS TO PROVE TERMINATION OF AN ITERATIVE
;;; VERSION OF ACKERMANN'S FUNCTION
;;;****************************************************************************

;;; ===========================================================================
;;; 1. Admission of an iterative version of Ackermann's function
;;; ===========================================================================

;;; This is the Ackermann function, classical definition:
;;; ·····················································

(defun ack (m n)
  (declare (xargs :measure (cons (+ (nfix m) 1) (nfix n))
		  :guard (and (integerp m) (>= m 0)
			      (integerp n) (>= n 0))
		  :verify-guards nil))
  (cond ((zp m) (+ n 1))
	((zp n) (ack (- m 1) 1))
	(t (ack (- m 1) (ack m (- n 1))))))

(defthm ack-non-negative-integer
  (implies (and (integerp n) (>= n 0))
	   (and (integerp (ack m n))
		(>= (ack m n) 0))))

(verify-guards ack)

;;; Our goal is to define an iterative version of ack:
;;; ··················································

; (defun ack-it-aux (s z)
;   (declare (xargs :mode :program))
;   (if (endp s)
;       z
;       (let ((head (first s))
;             (tail (rest s)))
;         (cond ((zp head) (ack-it-aux tail (+ z 1)))
;               ((zp z) (ack-it-aux (cons (- head 1) tail) 1))
;               (t (ack-it-aux (cons head (cons (- head 1) tail))
;                              (- z 1)))))))

; (defun ack-it (m n)
;   (declare (xargs :mode :program))
;   (ack-it-aux (list m) n))

;;; And prove that ack-it is equal to ack

;;; We will replay the proof of Dershowitz & Manna in "Proving
;;; termination with multiset orderings"

;;; ---------------------------------------------------------------------------
;;; 1.1 A well-founded relation rel-ack
;;; ---------------------------------------------------------------------------

;;; The measures:
(defun mp-ack (p)
  (declare (xargs :verify-guards t))
  (and (consp p)
       ;; slight mod (use of natp) for v2-8 ordinals changes
       (natp (car p))
       (natp (cdr p))))

;;; The relation:
(defun rel-ack (p1 p2)
  (declare (xargs :guard (and (mp-ack p1) (mp-ack p2))))
  (cond ((< (car p1) (car p2)) t)
	((= (car p1) (car p2)) (< (cdr p1) (cdr p2)))))

;;; The embedding:
(defun fn-ack (p)
  (declare (xargs :guard (mp-ack p)))
  ;; modified for v2-8 ordinals changes
  (make-ord (1+ (car p)) 1 (cdr p)))

;;; The well-foundedness-theorem:
; modified for v2-8 ordinals changes
(defthm rel-ack-well-founded
  (and (implies (mp-ack x)
		(o-p (fn-ack x)))
       (implies (and (mp-ack x)
		     (mp-ack y)
		     (rel-ack x y))
		(o< (fn-ack x) (fn-ack y))))
  :rule-classes :well-founded-relation)


;;; ---------------------------------------------------------------------------
;;; 1.2 Extension of rel-ack to mul-rel-ack (well founded).
;;;----------------------------------------------------------------------------

; (defmul-components rel-ack)
; => The list of components is:
;     (REL-ACK REL-ACK-WELL-FOUNDED MP-ACK FN-ACK X Y)

(defmul (REL-ACK REL-ACK-WELL-FOUNDED MP-ACK FN-ACK X Y)
  :verify-guards t)

;;;----------------------------------------------------------------------------
;;; 1.3 Definition of a measure in order to accept ack-it-aux.
;;;----------------------------------------------------------------------------

(defun get-pairs-add1-0 (s)
  (declare (xargs :guard (true-listp s)))
  (if (atom s)
      nil
      (cons (cons (+ (nfix (car s)) 1) 0)
	    (get-pairs-add1-0 (cdr s)))))

(defun measure-ack-it-aux (s z)
  (declare (xargs :guard (true-listp s)))
  (if (endp s)
      nil
      (cons (cons (nfix (car s)) (nfix z))
	    (get-pairs-add1-0 (cdr s)))))

;;;----------------------------------------------------------------------------
;;; 1.4 Definition of ack-it-aux.
;;;----------------------------------------------------------------------------

;;; Some lemmas needed to the admission of ack-it-aux
;;; ·················································

;;; 1)

(in-theory (enable natp)) ; modified for v2-8 ordinals changes

(encapsulate
 ()

 (local (in-theory (disable nfix)))

 (local
  (defthm mp-ack-true-listp-get-pairs-add1-0
    (mp-ack-true-listp (get-pairs-add1-0 l))))

 (defthm measure-ack-it-aux-mp-ack-true-lisp
   (mp-ack-true-listp (measure-ack-it-aux s z))))

;;; 2)

(in-theory (disable multiset-diff))

(encapsulate
 ()

 (local (in-theory (disable nfix zp)))

 (defthm measure-ack-it-aux-mp-decreases-1
   (implies (zp y)
	    (mul-rel-ack (measure-ack-it-aux l (+ 1 z))
			 (measure-ack-it-aux (cons y l) z)))
   :hints (("Subgoal 2" :in-theory (disable multiset-diff))
	   ("Subgoal 2.2" :in-theory (enable multiset-diff))
	   ("Subgoal 2.1" :in-theory (enable multiset-diff)))))

;;; 3)

(defthm measure-ack-it-aux-mp-decreases-2
  (implies (and (not (zp y)) (zp z))
	   (mul-rel-ack (measure-ack-it-aux (cons (+ -1 y) l)
					    1)
			(measure-ack-it-aux (cons y l) z)))
  :hints (("Goal" :in-theory (disable multiset-diff))))

;;; 4)

(defthm measure-ack-it-aux-mp-decreases-3
  (implies
   (and (not (zp y)) (not (zp z)))
   (mul-rel-ack (measure-ack-it-aux (list* y (+ -1 y) l) (+ -1 z))
		(measure-ack-it-aux (cons y l) z)))
  :hints (("Goal" :in-theory (disable multiset-diff))
	  ("Subgoal 1" :in-theory (enable multiset-diff))))


;;; At last, admission of ack-it-aux and definition of ack-it
;;; ·························································

(defun nn-integer-true-listp (s)
  (declare (xargs :guard t))
  (if (atom s)
      (equal s nil)
      (and (integerp (car s)) (>= (car s) 0)
	   (nn-integer-true-listp (cdr s)))))

(defun ack-it-aux (s z)
  (declare (xargs
	    :guard (and (nn-integer-true-listp s) (integerp z) (>= z 0))
	    :measure (measure-ack-it-aux s z)
	    :well-founded-relation mul-rel-ack
	    :hints (("Goal" :in-theory
		     (disable measure-ack-it-aux mul-rel-ack zp)))))
  (if (endp s)
      z
      (let ((head (first s))
	    (tail (rest s)))
	(cond ((zp head) (ack-it-aux tail (+ z 1)))
	      ((zp z) (ack-it-aux (cons (- head 1) tail) 1))
	      (t (ack-it-aux (cons head (cons (- head 1) tail)) (- z 1)))))))

(defun ack-it (m n)
  (declare (xargs
	    :guard (and (integerp m) (>= m 0)
			(integerp n) (>= n 0))))
  (ack-it-aux (list m) n))


;;; ============================================================================
;;; 2. Main property of ack-it: ack-it is equal to ack
;;; ============================================================================


(defun ack-stack (s z)
  (declare (xargs
	    :guard (and (nn-integer-true-listp s) (integerp z) (>= z 0))))
  (if (endp s)
      z
      (ack-stack (cdr s) (ack (car s) z))))

(encapsulate
 ()

 (local (defthm ack-stack-cons-expand
	  (equal (ack-stack (cons s1 s) z)
		 (ack-stack s (ack s1 z)))))

 (defthm ack-it-aux-ack-stack
   (equal (ack-it-aux s z) (ack-stack s z))))

(defthm ack-it-equal-ack
  (equal (ack-it m n) (ack m n)))
