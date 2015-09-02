;;; unification.lisp
;;; Definition of a particular rule-based unification algorithm.
;;; This is an executable instance of the general pattern verified in
;;; unification-pattern.lisp
;;; Created 17-10-99. Last revision: 10-12-2000
;;; =================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "unification")

|#





(in-package "ACL2")
(include-book "subsumption-subst")
(local (include-book "unification-pattern"))
(set-well-founded-relation e0-ord-<)


;;; *************************************************
;;; A CONCRETE AND EXECUTABLE UNIFICATION ALGORITHM
;;; *************************************************

;;; Here we show how we can obtain a correct and executable unification
;;; algorithm from the "pattern"  verified in unification-definition.lisp:
;;; - We define a particular selection function.
;;; - We introduce multi-values to deal with the pair of systems
;;;   S-sol and with the returned values, to improve efficiency.
;;; - Some other improvements concerning efficency are done.
;;; - Guards are verified, allowing execution in Common Lisp.

;;; ============================================================================
;;; 1. The unification algorithm
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 1.1 A particular version of transform-mm-sel
;;; ----------------------------------------------------------------------------

;;; ············································································
;;; 1.1.1 A particular "selection" function. If we detect an inmediate fail,
;;; we select it.
;;; ············································································

(defun sel-unif (S)
  (declare (xargs :guard (and (consp S) (system-p S))))
  (if (endp (cdr S))
      (car S)
    (let* ((equ (car S))
	   (t1 (car equ))
	   (t2 (cdr equ)))
	(cond ((or (variable-p t1) (variable-p t2))
	       (sel-unif (cdr S)))
	      ((eql (car t1) (car t2))
	       (sel-unif (cdr S)))
	      (t equ)))))

;;; Main property, needed to instantiate from unification-definition.lisp:
(local
 (defthm sel-unif-select-a-pair
   (implies (consp S)
	    (member (sel-unif S) S))))



;;; ············································································
;;; 1.1.2 Some lemmas needed for guard verification:
;;; ············································································

(encapsulate
 ()

 (local
  (defthm sel-unif-consp
    (implies (and (alistp S)
		  (consp S)
		  (system-p S))
	     (consp (sel-unif S)))
    :rule-classes :type-prescription))

 (defthm termp-p-sel-unif-system-p
   (implies (and (consp S)
		 (system-p S))
	    (and
	     (term-p (car (sel-unif S)))
	     (term-p (cdr (sel-unif S))))))

 (local
  (defthm term-p-true-listp-arguments
    (implies (and (term-p term) (not (variable-p term)))
	     (true-listp (cdr term)))))

 (local
  (defthm system-p-eqlable-function-symbols
    (implies (and (system-p S)
		  (member equ S))
	     (eqlablep (cadr equ)))))

 (defthm system-p-eqlablep-car
   (implies (and (system-p S)
		 (consp S)
		 (variable-p (car (sel-unif S))))
	    (eqlablep (car (sel-unif S)))))

;;; ············································································
;;; 1.1.3 The function transform-mm
;;; ············································································


 (defun transform-mm (S sol)
   (declare (xargs :guard (and (system-p S)
			       (system-p sol)
			       (consp S))))
   (let* ((ecu (sel-unif S))
	  (t1 (car ecu)) (t2 (cdr ecu))
	  (R (eliminate ecu S)))
     (cond ((equal t1 t2) (mv R sol t))                  ;;; *DELETE*
	   ((variable-p t1)
	    (if (member t1 (variables t t2))
		(mv nil nil nil)                         ;;; *CHECK*
	      (mv                                        ;;; *ELIMINATE*
	       (substitute-syst t1 t2 R)
	       (cons ecu
		     (substitute-range t1 t2 sol))
	       t)))
	   ((variable-p t2)
	    (mv (cons (cons t2 t1) R) sol t))            ;;; *ORIENT*
	   ((not (eql (car t1) (car t2)))
	    (mv nil nil nil))                            ;;; *CONFLICT*
	   (t (mv-let (pairs bool)
		      (pair-args (cdr t1) (cdr t2))
		      (if bool
			  (mv (append pairs R) sol t)    ;;; *DESCOMPOSE*
			(mv nil nil nil))))))))           ;;; *NOT-PAIR*



;;; ----------------------------------------------------------------------------
;;; 1.2 Some lemmas needed for functional instantiation (first part)
;;; ----------------------------------------------------------------------------

;;; Here we define some lemmas to show that the efficiency improvements
;;; done in transform-mm does not affect the logic:

(local
 (defthm substitute-var-apply-subst
   (equal (apply-subst flg (list equ) term)
	  (substitute-var (car equ) (cdr equ) flg term))))


(local
 (defthm substitute-syst-apply-syst
   (equal (apply-syst (list equ) S)
	  (substitute-syst (car equ) (cdr equ) S))))

(local
 (defthm substitute-range-apply-range
   (equal (apply-range (list equ) S)
	  (substitute-range (car equ) (cdr equ) S))))


;;; transform-mm-sel of unification-definition.lisp cannot be
;;; instantiated by transform-mm, since they different signatures, due
;;; to the use of multi values in transform-mm. Instead, we will
;;; instantiate transform-mm-sel for the following function:

(local
 (defun transform-mm-bridge (S-sol)
   (mv-let (S1 sol1 bool1)
	   (transform-mm (car S-sol) (cdr S-sol))
	   (if bool1 (cons S1 sol1) nil))))


;;; ----------------------------------------------------------------------------
;;; 1.3 Termination properties of transform-mm
;;; ----------------------------------------------------------------------------

;;; The theorem to justify the definition. This lemma is easily obtained
;;; by functional instantiation:

(local
 (encapsulate
  ()
;;; A technical lemma, to make the proof shorter:
  (local
   (defthm um-technical
     (equal (unification-measure '(nil))
	    (unification-measure nil))))

  (defthm unification-measure-decreases-instance
    (let ((transform-mm (transform-mm S sol)))
      (implies (consp S)
	       (e0-ord-<
		(unification-measure (cons (first transform-mm)
					   (second transform-mm)))
		(unification-measure (cons S sol)))))
    :hints (("Goal" :use (:functional-instance
			  (:instance unification-measure-decreases
				     (S-sol (cons S sol)))
			  (transform-mm-sel transform-mm-bridge)
			  (sel sel-unif)))
	    ("Subgoal 3" :in-theory (disable unification-measure
					     (unification-measure)))))))



(local (in-theory (disable unification-measure)))



;;; ----------------------------------------------------------------------------
;;; 1.4 Guard verification
;;; ----------------------------------------------------------------------------

;;; Some lemmas needed for guard verification of mgu-mv

(local
 (defthm system-p-substitute-var
   (implies (and (term-p t1)
		 (term-p-aux flg term))
	    (term-p-aux flg (substitute-var x t1 flg term)))))

(local
 (defthm system-p-substitute-syst
   (implies (and (system-p S)
		 (term-p term))
	    (system-p (substitute-syst x term S)))))

(local
 (defthm system-p-substitute-range
   (implies (and (system-p S)
		 (term-p term))
	    (system-p (substitute-range x term S)))))


;;; ----------------------------------------------------------------------------
;;; 1.5 The unification algorithm
;;; ----------------------------------------------------------------------------

;;; Appling transform-mm until a normal form is found:

(defun solve-system (S sol bool)
  (declare
   (xargs
    :guard (and (system-p S)
      		(system-p sol))
    :measure (unification-measure (cons S sol))
    :hints
    (("Goal" :in-theory (disable transform-mm)))))
  (if (or (not bool) (not (consp S)))
      (mv S sol bool)
    (mv-let (S1 sol1 bool1)
            (transform-mm S sol)
	    (solve-system S1 sol1 bool1))))



;;; Most general solutions of systems of equations

(defun mgs-mv (S)
  (declare (xargs :guard (system-p S)))
  (mv-let (S1 sol1 bool1)
	  (solve-system S nil t)
	  (declare (ignore S1))
	  (mv sol1 bool1)))

;;; The unification algorithm

(defun mgu-mv (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mgs-mv (list (cons t1 t2))))



;;; We also define as functions the property of being unifiable and the
;;; umg substitution:
(defun unifiable (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mv-let (mgu unifiable)
	  (mgu-mv t1 t2)
	  (declare (ignore mgu))
	  unifiable))

(defun mgu (t1 t2)
  (declare (xargs :guard (and (term-p t1) (term-p t2))))
  (mv-let (mgu unifiable)
	  (mgu-mv t1 t2)
	  (declare (ignore unifiable))
	  mgu))


;;; REMARK: mgu-mv will be used to compute unifiability and most general
;;; unifier at the same time. The functions unifiable and mgu are
;;; defined to be used in the statements of theorems.

;;; ============================================================================
;;; 2. Fundamental properties of mgu-mv, unifiable and mgu
;;; ============================================================================

;;; ----------------------------------------------------------------------------
;;; 2.1 Some lemmas needed for the functional instantiation (second part)
;;; ----------------------------------------------------------------------------

(local
 (defthm booleanp-third-solve-system
   (implies (booleanp bool)
	    (booleanp (third (solve-system S sol bool))))
   :rule-classes :type-prescription))

(local
 (defthm nil-third-implies-nil-second-solve-system
   (implies (not (third (solve-system S sol t)))
	    (not (second (solve-system S sol t))))))


;;; solve-system-sel of unification-pattern.lisp cannot be
;;; instantiated by solve-system, since they different signatures, due
;;; to the use of multi values in transform-mm. Instead, we will
;;; instantiate solve-system-sel for the following function:

(local
 (defun solve-system-bridge (S-sol)
   (if (not (consp S-sol))
       S-sol
     (mv-let (S1 sol1 bool1)
	     (solve-system (car S-sol) (cdr S-sol) t)
	     (if bool1 (cons S1 sol1) nil)))))

;;; The same happens with mgs-sel and mgu-sel

(local
 (defun mgs-mv-bridge (S)
   (let ((solve-system-bridge (solve-system-bridge (cons S nil))))
     (if solve-system-bridge (list (cdr solve-system-bridge)) nil))))

(local
 (defun unifiable-bridge (t1 t2)
   (mgs-mv-bridge (list (cons t1 t2)))))

(local
 (defun mgu-bridge (t1 t2)
   (first (unifiable-bridge t1 t2))))


;;; ----------------------------------------------------------------------------
;;; 2.2 The properties
;;; ----------------------------------------------------------------------------
;;; Most of these properties are obtained by functional instantiation.

;;; Completeness
;;; ············

(defthm  mgu-completeness
  (implies (equal (instance t1 sigma)
		  (instance t2 sigma))
	   (unifiable t1 t2))
  :rule-classes nil
  :otf-flg t
  :hints
  (("Goal"
    :use
    ((:functional-instance
      unifiable-sel-completeness
      (sel sel-unif)
      (transform-mm-sel transform-mm-bridge)
      (solve-system-sel solve-system-bridge)
      (mgs-sel mgs-mv-bridge)
      (unifiable-sel unifiable-bridge))))))

;;; The hint is not necessary, but makes the proof shorter.

;;; Soundness
;;; ·········


(defthm mgu-soundness
  (implies (unifiable t1 t2)
	   (equal (instance t1 (mgu t1 t2))
		  (instance t2 (mgu t1 t2))))
  :hints
  (("Goal"
    :use
    ((:functional-instance
      unifiable-sel-soundness
      (sel sel-unif)
      (transform-mm-sel transform-mm-bridge)
      (solve-system-sel solve-system-bridge)
      (mgs-sel mgs-mv-bridge)
      (unifiable-sel unifiable-bridge)
      (mgu-sel mgu-bridge))))))


;;; Idempotence
;;; ···········

(defthm mgu-idempotent
  (idempotent (mgu t1 t2))
  :hints
  (("Goal"
    :use
    ((:functional-instance
      mgu-sel-idempotent
      (sel sel-unif)
      (transform-mm-sel transform-mm-bridge)
      (solve-system-sel solve-system-bridge)
      (mgs-sel mgs-mv-bridge)
      (unifiable-sel unifiable-bridge)
      (mgu-sel mgu-bridge))))))



;;; Generality of the unifier
;;; ·························

(defthm mgu-most-general-unifier
  (implies (equal (instance t1 sigma)
		  (instance t2 sigma))
	   (subs-subst (mgu t1 t2) sigma))
   :hints
   (("Goal"
    :use
    ((:functional-instance
      mgu-sel-most-general-unifier
      (sel sel-unif)
      (transform-mm-sel transform-mm-bridge)
      (solve-system-sel solve-system-bridge)
      (mgs-sel mgs-mv-bridge)
      (unifiable-sel unifiable-bridge)
      (mgu-sel mgu-bridge))))))



;;; Substitution-s-p (closure property of mgu)
;;; ··············································


(defthm mgu-substitution-s-p
  (implies (and (term-s-p t1) (term-s-p t2))
	   (substitution-s-p (mgu t1 t2)))
   :hints
   (("Goal"
    :use
    ((:functional-instance
      mgu-sel-substitution-s-p
      (sel sel-unif)
      (transform-mm-sel transform-mm-bridge)
      (solve-system-sel solve-system-bridge)
      (mgs-sel mgs-mv-bridge)
      (unifiable-sel unifiable-bridge)
      (mgu-sel mgu-bridge))))))



;;; Substitution-p (needed for guard verification)
;;; ··············································


(defthm mgu-substitution-p
  (implies (and (term-p t1) (term-p t2))
	   (substitution-p (mgu t1 t2)))
  :hints (("Goal" :use (:functional-instance
			mgu-substitution-s-p
			(signat (lambda (x n) (eqlablep x)))
			(term-s-p-aux term-p-aux)
			(substitution-s-p substitution-p)))))



;;; We disable mgu-mv, unifiable and mgu and their executable
;;; counter-parts, to be sure that ONLY the above two properties are
;;; used in the sequel. But before doind this, we state the relations
;;; between mgu-mv and unifiable and mgu.

(defthm mgu-mv-unifiable
  (equal (second (mgu-mv t1 t2)) (unifiable t1 t2)))

(defthm mgu-mv-mgu
  (equal (first (mgu-mv t1 t2)) (mgu t1 t2)))


(in-theory (disable mgu-mv (mgu-mv) mgu (mgu) unifiable (unifiable)))


;;; ============================================================================
;;; 3. Some examples
;;; ============================================================================

;;; ACL2 !>(mgu '(h u) '(h (b)))
;;; ((U B))
;;; ACL2 !>(mgu  1 1)
;;; NIL
;;; ACL2 !>(mgu '(f (g x y) (g y x)) '(f u u))
;;; ((X . Y) (U G Y Y))
;;; ACL2 !>(unifiable '(f (g x y) (g y x)) '(f x x))
;;; NIL
;;; ACL2 !>(mgu '(f (h z) (h (h z))) '(f u (h (h (g v v)))))
;;; ((Z G V V) (U H (G V V)))
;;; ACL2 !>(mgu '(f x (g (a) y)) '(f x (g y x)))
;;; ((X A) (Y A))
;;; ACL2 !>(mgu '(f x (g a y)) '(f x (g y x)))
;;; ((A . X) (Y . X))
;;; ACL2 !>(mgu '(f x (g (a) y)) '(f x (g y x)))
;;; ((X A) (Y A))
;;; ACL2 !>(mgu '(f x (g a y)) '(f x (g y x)))
;;; ((A . X) (Y . X))




