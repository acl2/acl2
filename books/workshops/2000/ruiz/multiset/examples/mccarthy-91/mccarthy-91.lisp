;;; mccarthy-91.lisp
;;; Admissibility of an iterative version of McCarthy's 91 function.
;;; Created: 6-6-2000 Last revised: 2-8-00
;;;============================================================================

;;; To certify this book:

#|
(in-package "ACL2")
(certify-book "mccarthy-91")
|#

(in-package "ACL2")

(include-book "../../defmul")
;(include-book "../../../../../../ordinals/e0-ordinal")

(set-verify-guards-eagerness 2)


;;;****************************************************************************
;;; USING MULTISETS RELATIONS TO PROVE TERMINATION OF McCARTHY'S 91 FUNCTION
;;;****************************************************************************


;;; ===========================================================================
;;; 1. Admission of an iterative version of McCarthy 91 function.
;;; ===========================================================================

;;; Instead of defining the following definition of McCarthy's 91 function:

; (defun mc (x)
;   (declare (xargs :mode :program))
;   (if (> x 100)
;       (- x 10)
;       (mc (mc (+ x 11)))))

;;; Our goal is to define in ACL2 the following iterative version:

; (defun mc-aux (n z)
;   (declare (xargs :measure ...
; 		    :well-founded-relation ...))
;   (cond ((or (zp n) (not (integerp z))) z)
; 	((> z 100) (mc-aux (- n 1) (- z 10)))
; 	(t (mc-aux (+ n 1) (+ z 11)))))

; (defun mc-it (x)
;   (mc-aux 1 x))

;;; We will replay the proof of Dershowitz & Manna in "Proving
;;; termination with multiset orderings"

;;; ---------------------------------------------------------------------------
;;; 1.1 A well-founded relation rel-mc
;;; ---------------------------------------------------------------------------

;;; The measures:
(defun integerp-<=-111 (x)
  (and (integerp x) (<= x 111)))

;;; REMARK : There is a mistake in the proof by D&M, because they say
;;; that the domain is 0 <= x < 111.

;;; The relation:
(defun rel-mc (x y)
  (and (integerp-<=-111 x)
       (integerp-<=-111 y)
       (< y x)))

;;; The embedding:
(defun fn-rel-mc (x)
  (if (integerp-<=-111 x)
      (- 111 x)
      0))

;;; The well-foundedness theorem:
; modified for v2-8 ordinals changes
(defthm rel-mc-well-founded
  (and (o-p (fn-rel-mc x))
       (implies (rel-mc x y)
		(o< (fn-rel-mc x) (fn-rel-mc y))))
  :rule-classes :well-founded-relation)

;;; REMARK: One could think that integerp-<=-111 is the MP property of the
;;; well-founded relation, instead of T. But there is a subtle difference: our
;;; measure (our multisets) can contain elements greater than 111, although
;;; those elements are not comparable.

;;; ---------------------------------------------------------------------------
;;; 1.2 Extension of rel-mc to mul-rel-mc (well founded).
;;;----------------------------------------------------------------------------

;;; (defmul-components rel-mc)
; => The list of components is:
;     (REL-MC REL-MC-WELL-FOUNDED T FN-REL-MC X Y)

(defmul (REL-MC REL-MC-WELL-FOUNDED T FN-REL-MC X Y) :verify-guards t)

;;;----------------------------------------------------------------------------
;;; 1.3 Definition of a measure in order to accept mc-aux.
;;;----------------------------------------------------------------------------

(defun f91 (x)
  (cond ((not (integerp x)) x)
	((> x 100) (- x 10))
	(t 91)))

(defun measure-mc-aux (n z)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      nil
      (cons z (measure-mc-aux (- n 1) (f91 z)))))

;;;----------------------------------------------------------------------------
;;; 1.4 Definition of "mc-aux".
;;;----------------------------------------------------------------------------

;;; Fundamental rewrite rule for our proof strategy:
;;; The rule measure-mc-aux-expand expands measure-mc-aux where the
;;; expansion heuristics of the system fail. This is important for two
;;; reasons. First, measure-mc-aux definition is expanded whenever it
;;; can be deduced that n>0, and the multiset obtained explicitly
;;; present the first (and second sometimes) elements and the same tail,
;;; allowing the meta rule of multiset.lisp to rewrite. Second, the IF
;;; in the rule performs almost the same case distinction as in the hand
;;; proof.

(defthm measure-mc-aux-expand
  (implies (and (not (zp n)) (integerp z))
	   (equal (measure-mc-aux n z)
		  (cons z (measure-mc-aux (- n 1)
					  (if (> z 100) (- z 10) 91))))))

;;; The next theorem comes from the "equalities" book
;;; ("../distribution/books/arithmetic/equalities.lisp"). It's the only event
;;; from this book needed in the admission of "mc-aux".

(defthm fold-consts-in-+
  (implies (and (syntaxp (quotep x))
		(syntaxp (quotep y)))
	   (equal (+ x (+ y z))
		  (+ (+ x y) z))))

(in-theory (disable multiset-diff))

;;; At last:

(defun mc-aux (n z)
  (declare (xargs
	    :guard (and (integerp n) (>= n 0))
	    :measure (measure-mc-aux n z)
	    :well-founded-relation mul-rel-mc))
  (cond ((or (zp n) (not (integerp z))) z)
	((> z 100) (mc-aux (- n 1) (- z 10)))
	(t (mc-aux (+ n 1) (+ z 11)))))

(defun mc-it (x)
  (mc-aux 1 x))


;;; ============================================================================
;;; 2. Properties of mc-it
;;; ============================================================================


;;; ----------------------------------------------------------------------------
;;; 2.1 mc-it is equal to f91
;;; ----------------------------------------------------------------------------


(defun iter-f91 (n x)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      x
      (iter-f91 (- n 1) (f91 x))))

;;; Fundamental rewrite rule for our proof strategy:

(defthm iter-f91-expand
  (implies (and (not (zp n)) (integerp z))
	   (equal (iter-f91 n z)
		  (iter-f91 (- n 1)
			    (if (> z 100) (- z 10) 91)))))

(defthm iter-f91-mc-aux
  (equal (mc-aux n z) (iter-f91 n z))
  :hints (("Goal" :induct (mc-aux n z))))

(defthm mc-it-equals-f91-for-non-integers
  (implies (not (integerp x))
	   (equal (iter-f91 n x) x)))

(defthm equal-mc-it-and-f91
  (equal (mc-it x) (f91 x)))


;;; ----------------------------------------------------------------------------
;;; 2.2 mc-it verifies the recursion scheme of mc
;;; ----------------------------------------------------------------------------

(defthm mc-it-recursive-schema
  (equal (mc-it x)
	 (cond ((not (integerp x)) x)
	       ((> x 100) (- x 10))
	       (t (mc-it (mc-it (+ x 11))))))
  :rule-classes nil)


;;; ----------------------------------------------------------------------------
;;; 2.3 Every function satisfying the recursion scheme of mc is equal to f91
;;; ----------------------------------------------------------------------------



;;; A general function M satisfying the above recursive equation:

(encapsulate
 ((M (x) t))

 (local (defun M (x) (mc-it x)))

 (defthm M-it-recursive-schema
   (equal (M x)
	  (cond ((not (integerp x)) x)
		((> x 100) (- x 10))
		(t (M (M (+ x 11))))))
   :rule-classes :definition))

(defun iter-M (n x)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (if (zp n)
      x
      (iter-M (- n 1) (M x))))

(defthm M-expand
  (implies (and (not (zp n)) (integerp z))
	   (equal (iter-M n z)
		  (iter-M (- n 1)
			  (if (> z 100) (- z 10) (M (M (+ z 11))))))))

(defthm iter-M-equals-mc-aux
  (equal (iter-M n z) (mc-aux n z))
  :hints (("Goal" :in-theory (disable iter-f91-mc-aux))))

;;; Then M is equal to f91

(encapsulate
 ()

 (local
  (defthm iter-M-1-M
    (equal (M x) (iter-M 1 x))
    :hints (("Goal" :in-theory (disable iter-M-equals-mc-aux)
	     :expand (iter-M 1 x)))))

 (defthm M-equal-f91
   (equal (M x) (f91 x))))




