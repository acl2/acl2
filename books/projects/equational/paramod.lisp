;; UTEP - Utrecht Texas Equational Prover
;; Written by Grant Olney Passmore {grant@math.utexas.edu}
;;
;; Paramodulation routines.

(in-package "ACL2")
(include-book "weighting")

;; BINARY-PARAMODULATION (clause1 clause2 eq-lit c2-term eq-side)
;; Given two clauses, a singled out positive equality literal, a chosen side of the equality to
;; focus on (either 'LHS or 'RHS) and a term (in clause2) to paramodulate off of,
;; return the result of paramodulating the above choices if possible.
;; (I need to write a better description of this process; presumably, anyone reading this
;;  already understand paramodulation, so a thorough explanation of the process doesn't seem
;;  pertinent right now).
;; G. Passmore :: 03/05/06

(defun binary-paramodulation (clause1 clause2 eq-lit c2-term eq-side)
  (let ((eq-arg (if (equal eq-side 'LHS) (cadr eq-lit) (caddr eq-lit)))
	(eq-arg^ (if (equal eq-side 'LHS) (caddr eq-lit) (cadr eq-lit))))
    (mv-let (unified-instance mgu) (unify eq-arg c2-term)
	    (cond
	     ((equal unified-instance 'DNU) 'DNU)
	     (t (let ((unified-c1 (apply-unifier clause1 mgu))
		      (unified-c2 (apply-unifier clause2 mgu)))
		  (deepsubst
		   (append (remove-elements-once-each unified-c1 (list (apply-unifier eq-lit mgu))) unified-c2)
		   (apply-unifier c2-term mgu)
		   (apply-unifier eq-arg^ mgu))))))))

;; LINEAR-PARAMODULATION+ (clause1 clause2 eq-side clause1-id clause2-id top-clause-id clause1-eq-id-count)
;; Given two clauses s.t. clause1 contains at least one equality, return the result of performing paramodulation
;; upon each c1-equality and each c2-term, focussing on the appropriate eq-side (either LHS or RHS).
;; G. Passmore :: 03/08/06

(defun linear-paramodulation** (eq-lit c2-terms clause1 clause2 eq-side clause1-id clause2-id clause2-lit-id clause1-eq-id top-clause-id count)
  (cond ((endp c2-terms) nil)
	(t (let ((paramoduli (binary-paramodulation clause1 clause2 eq-lit (car c2-terms) eq-side)))
	     (cond ((and (not (equal paramoduli 'DNU))
			 (not (equal paramoduli '((= (E) (E)))))) ; Hard-coding throwing away some stupid clauses in a group theory example.
		   (cons
		    (list (list 'S (1+ top-clause-id))
			  (list 'MOVE ':PARAMODULATION (list clause1-id clause1-eq-id) (list clause2-id clause2-lit-id count))
			  paramoduli)
		    (linear-paramodulation** eq-lit (cdr c2-terms) clause1 clause2 eq-side clause1-id clause2-id
					     clause2-lit-id clause1-eq-id (+ 1 top-clause-id) (1+ count))))
		   (t (linear-paramodulation** eq-lit (cdr c2-terms) clause1 clause2 eq-side clause1-id clause2-id
					     clause2-lit-id clause1-eq-id top-clause-id (1+ count))))))))

(defun linear-paramodulation* (eq-lit clause1 clause2 eq-side clause1-id clause2-id clause1-eq-id top-clause-id clause2-lit-count)
  (cond ((endp clause2) nil)
	(t (let ((cur-c2-literal (car clause2)))
	     (let ((paramoduli (linear-paramodulation** eq-lit (collect-all-terms cur-c2-literal)
					      clause1 clause2 eq-side clause1-id clause2-id clause2-lit-count clause1-eq-id top-clause-id 0)))
	       (append paramoduli (linear-paramodulation* eq-lit clause2 (cdr clause2) eq-side clause1-id clause2-id clause1-eq-id
							  (+ (len paramoduli) top-clause-id) (1+ clause2-lit-count))))))))

(defun linear-paramodulation+ (clause1 clause2 eq-side clause1-id clause2-id top-clause-id clause1-eq-id-count)
  (cond ((endp clause1) nil)
	(t (let ((cur-c1-eq (car clause1)))
	     (if (or (not (consp cur-c1-eq))
		     (not (equal *equality-symbol* (car cur-c1-eq))))
		 (linear-paramodulation+ (cdr clause1) clause2 eq-side clause1-id clause2-id top-clause-id (1+ clause1-eq-id-count))
	       (let ((paramoduli (linear-paramodulation* cur-c1-eq clause1 clause2 eq-side clause1-id clause2-id clause1-eq-id-count top-clause-id 0)))
	       (append paramoduli
		       (linear-paramodulation+ (cdr clause1) clause2 eq-side clause1-id clause2-id (+ (len paramoduli) top-clause-id) (1+ clause1-eq-id-count)))))))))

;; LINEAR-PARAMODULATION (all-proof-moves top-clause-id last-cycle-top-clause)

(defun linear-paramodulation$* (cur-clause0 remaining-proof-moves eq-side top-clause-id cur-clause-id0)
  (if (endp remaining-proof-moves) nil
    ;(if (not (and (< cur-clause-id0 (/ last-cycle-top-clause 3/2)) (< cur-clause-id1 last-cycle-top-clause))) ;; This is a silly heuristic of mine.
      (let ((new-paramoduli (linear-paramodulation+ cur-clause0 (extract-clause (car remaining-proof-moves))
							eq-side cur-clause-id0 (caar remaining-proof-moves) top-clause-id 0)))
	(append new-paramoduli
		(linear-paramodulation$* cur-clause0 (cdr remaining-proof-moves) eq-side (+ (len new-paramoduli) top-clause-id)
					 cur-clause-id0)))))

(defun linear-paramodulation (all-proof-moves eq-side top-clause-id max-clause-weight)
  (if (endp all-proof-moves) nil
    (let ((new-paramoduli (linear-paramodulation$* (extract-clause (car all-proof-moves)) (cdr all-proof-moves) eq-side top-clause-id (caar all-proof-moves))))
      (append (filter-out-heavy-clauses new-paramoduli max-clause-weight)
	      (linear-paramodulation (cdr all-proof-moves) eq-side (+ top-clause-id (len new-paramoduli)) max-clause-weight)))))
