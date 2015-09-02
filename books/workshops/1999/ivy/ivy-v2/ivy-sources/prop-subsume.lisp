(in-package "ACL2")

;; In this book we define a relation (prop-subsume c d), which
;; checks if formula c propositionally subsumes formula d.
;; This is intended for quantifier-free formulas (in particular,
;; clauses and lists of clauses), but it is sound for all formulas.
;; For quantified formulas, prop-subsume is true iff the formulas
;; are equal.
;;
;; Soundness: if (prop-subsume c d), then
;; (univ-closure c) => (univ-closure d).
;;
;; This is not propositionally complete; that is, it is weaker
;; than "implies".

(include-book "stage")

(defun prop-subsume (c d)
  (declare (xargs :guard (and (wff c) (wff d))
		  :measure (+ (acl2-count c) (acl2-count d))))
  (cond ((equal c d) t)
	((equal c 'false) t)
	((equal d 'true) t)
	((and (wfnot c) (equal (a1 c) 'true)) t)
	((and (wfnot d) (equal (a1 d) 'false)) t)
	;;
	;; The order of these tests is important.
	;; For example, if the last test is moved to the front,
	;; (prop-subsume '(or (p) (q)) '(or (p) (or (q) (r))))
	;; will fail.
	;;
	((wfor c)  (and (prop-subsume (a1 c) d)
			(prop-subsume (a2 c) d)))
	((wfand d) (and (prop-subsume c (a1 d))
			(prop-subsume c (a2 d))))
	((wfand c) (or  (prop-subsume (a1 c) d)
		        (prop-subsume (a2 c) d)))
	((wfor d)  (or  (prop-subsume c (a1 d))
			(prop-subsume c (a2 d))))
	(t nil)))

;; Some tests:
;; (prop-subsume '(or (p) (q)) '(or (p) (or (q) (r))))
;;
;; (prop-subsume
;;  '(and (and (or (p) (q)) (r)) (or (s) (or (t) (u))))
;;  '(or (r) (r1)))

;; Using this induction scheme is somewhat faster than using prop-subsume
;; on the following theorem.

(defun prop-subsume-i (c d)
  (declare (xargs :guard (and (wff c) (wff d))
		  :measure (+ (acl2-count c) (acl2-count d))))
  (cond ((equal c d) 'junk)
	((equal c 'false) 'junk)
	((equal d 'true) 'junk)
	((and (wfnot c) (equal (a1 c) 'true)) 'junk)
	((and (wfnot d) (equal (a1 d) 'false)) 'junk)
	((wfor c)  (cons (prop-subsume-i (a1 c) d)
			 (prop-subsume-i (a2 c) d)))
	((wfand d) (cons (prop-subsume-i c (a1 d))
			 (prop-subsume-i c (a2 d))))
	((wfand c) (cons (prop-subsume-i (a1 c) d)
			 (prop-subsume-i (a2 c) d)))
	((wfor d)  (cons (prop-subsume-i c (a1 d))
			 (prop-subsume-i c (a2 d))))
	(t nil)))

(defthm subst-free-preserves-prop-subsume  ;; very long time
  (implies (prop-subsume c d)
	   (prop-subsume (subst-free c x tm) (subst-free d x tm)))
  :hints (("Goal"
	   :induct (prop-subsume-i c d))))

(defthm prop-subsume-ground-xsound
  (implies (and (prop-subsume c d)
		(xeval c dom i))
	   (xeval d dom i))
  :hints (("Goal"
	   :induct (prop-subsume c d)))
  :rule-classes nil)

(defthm car-of-alls-is-all
  (implies (consp vars)
	   (equal (car (alls vars f)) 'all)))

(defthm prop-subsume-xsound-vars
  (implies (and (prop-subsume c d)
		(var-set vars)
		(xeval (alls vars c) dom i))
	   (xeval (alls vars d) dom i))
  :hints (("Goal"
	   :induct (var-induct-2 vars c d dom i))
	  ("Subgoal *1/1'''"
	   :use ((:instance prop-subsume-ground-xsound))
	   ))
  :rule-classes nil)

;; Now, get it in terms of universal closure.

(local (include-book "close"))  ;; for xeval-alls-subset

(defthm prop-subsume-xsound
  (implies (and (prop-subsume c d)
		(xeval (universal-closure c) (domain i) i))
	   (xeval (universal-closure d) (domain i) i))
  :hints (("Goal"
           :do-not-induct t
	   :use ((:instance xeval-alls-subset
			    (f c)
			    (a (free-vars c))
			    (b (union-equal (free-vars c) (free-vars d))))
		 (:instance xeval-alls-subset
			    (f d)
			    (a (free-vars d))
			    (b (union-equal (free-vars c) (free-vars d))))
		 (:instance prop-subsume-xsound-vars
			    (vars (union-equal (free-vars c) (free-vars d)))
			    (dom (domain i)))))))
