;; UTEP - Utrecht Texas Equational Prover
;; Written by Grant Olney Passmore {grant@math.utexas.edu}
;;
;; Resolution, merging, and factoring routines with Set-Of-Support
;; and term weighting.

(in-package "ACL2")
(include-book "general")
(include-book "unification")
(include-book "weighting")

;; BINARY-RESOLVENT (clause0 clause1 lit0 lit1)
;; Given two input clauses and one literal from each clause s.t.
;; the two literals contain identical predicates of opposite sign,
;; we form a binary resolvent resulting from disjoining clause0 and clause1
;; to form clause2, removing lit0 and lit1 from clause2, and returning the
;; result of applying the MGU of lit0 and lit1 to clause2.
;; Note: Before disjoining the two clauses, we standardize the variables
;; apart, by renaming every variable in clause1 that occurs in clause0
;; with new "fresh" variable names.
;;
;; If unification fails, we return 'DNR (i.e., Do Not Resolve).
;; G. Passmore :: 12/22/05
;;
;; Note: I'm changing this removing of resolved literals to call
;; a new function remove-elements-once-each to avoid the incorrect
;; behavior of NIL being returned as the resolvent for: ((P y))
;;                                          ((not (P y)) (P y))
;;
;; G. Passmore :: 12/24/05

(defun binary-resolvent (clause0 clause1 lit0 lit1)
  (mv-let (unified-instance mgu)
	  (unify (strip-negation lit0) (strip-negation lit1))
	  (if (not (member unified-instance '(DNU OUT-OF-TIME)))
	      (remove-elements-once-each
	       (apply-unifier
		(append clause0 (standardize-apart clause0 clause1)) mgu)
	       (list (apply-unifier lit0 mgu) (apply-unifier lit1 mgu)))
	    'DNR)))

;; CLASHING-LITERALS (lit0 lit1)
;; Given two literals, lit0 and lit1, return t if both literals are rooted
;; in the same predicate, with one positive and one negative.
;; G. Passmore :: 12/22/05

(defun clashing-literals (lit0 lit1)
  (and (equal (car (strip-negation lit0)) (car (strip-negation lit1)))
       (not (iff (negative-literalp lit0) (negative-literalp lit1)))))

;; FIND-LINEAR-RESOLVENTS (lit lit-id clause clause-id top-clause-id cur-clause-pos)
;; Given a literal and a clause, return all successful binary resolvents
;; between literal and members of clause.  The rest of the parameters are used for
;; referencing the input literals to resolution for documenting the proof steps.
;;
;; We return a list of the form:
;; '( (top-clause-id + 1
;;     (move :binary-resolution literal-id (clause-id lit-in-clause-id))
;;     ( RESOLVENT OF ABOVE MOVE ))
;;    (top-clause-id + 2
;;     (move :binary-resolution ...
;;      ...)
;;    ..
;;  )
;; G. Passmore :: 12/22/05
;;
;; Updated with CTR-CONS and IMPLICIT-MERGING on 11/14/06.

(defun find-linear-resolvents (lit0 lit0-id clause0 clause1 clause1-fresh clause1-id top-clause-id cur-clause1-pos)
  (cond ((endp clause1) nil)
	((clashing-literals lit0 (car clause1))
	 (let ((resolvent (binary-resolvent clause0 clause1-fresh lit0 (car clause1))))
	   (if (not (equal resolvent 'DNR))
	       (let ((removed-dup-eq (remove-duplicates-equal resolvent)))
		 (ctr-cons (list (list 'S (+ top-clause-id 1))
				 (list 'move
				       (if (equal (len resolvent) (len removed-dup-eq))
					   ':binary-resolution
					   ':binary-resolution-and-merging)
					   lit0-id (list clause1-id cur-clause1-pos))
				 ;; Experimenting with implicit merging during binary resolution.  G.P. :: 11/14/06.
				 removed-dup-eq)
			   (find-linear-resolvents lit0 lit0-id clause0 (cdr clause1) clause1-fresh clause1-id (1+ top-clause-id) (1+ cur-clause1-pos))))
		 (find-linear-resolvents lit0 lit0-id clause0 (cdr clause1) clause1-fresh clause1-id top-clause-id (1+ cur-clause1-pos)))))
	 (t (find-linear-resolvents lit0 lit0-id clause0 (cdr clause1) clause1-fresh clause1-id top-clause-id (1+ cur-clause1-pos)))))

;; FIND-ALL-BINARY-RESOLVENTS (clause0 clause1)
;; Given two clauses, find all of their binary resolvents.
;; I take the horribly nieve approach right now just to get things
;; moving -- I'll redo this in a much less bone-headed way
;; eventually!
;; G. Passmore :: 12/22/05

(defun find-all-binary-resolvents* (clause0 clause0-fresh clause1 clause0-id clause1-id top-clause-id cur-clause0-pos)
  (if (endp clause0) nil
    (let ((c0-literal (car clause0)))
      (let ((new-resolvents
	     (find-linear-resolvents c0-literal (list clause0-id cur-clause0-pos) clause0-fresh clause1 clause1
				     clause1-id top-clause-id 0)))
	(ctr-append new-resolvents
		(find-all-binary-resolvents* (cdr clause0) clause0-fresh clause1 clause0-id clause1-id
					     (+ (len new-resolvents) top-clause-id) (1+ cur-clause0-pos)))))))

(defun find-all-binary-resolvents (clause0 clause1 clause0-id clause1-id top-clause-id)
  (find-all-binary-resolvents* clause0 clause0 (standardize-apart clause0 clause1) clause0-id clause1-id top-clause-id 0))

;; MERGE-CLAUSE (clause clause-id top-clause)
;; Given a clause, attempt to merge any of its identical literals,
;; returning a new inference with id (1+ top-clause) if merging is
;; successful.
;; G. Passmore :: 12/22/05

(defun merge-clause* (clause clause-fresh clause-id top-clause cur-clause-pos cur-merge-positions cur-merge-lits)
  (cond ((endp clause) (if (not (consp cur-merge-positions)) nil
			 (list (list 'S (1+ top-clause))
			       (list 'MOVE ':MERGE-CLAUSE (list clause-id ':MERGED-LITERALS cur-merge-positions))
			       (remove-duplicates-equal clause-fresh))))
	((or (member-equal (car clause) (cdr clause))
	     (member-equal (car clause) cur-merge-lits))
	 (merge-clause* (cdr clause) clause-fresh clause-id top-clause (1+ cur-clause-pos) (list* cur-clause-pos cur-merge-positions)
			(append (list (car clause)) cur-merge-lits)))
	(t (merge-clause* (cdr clause) clause-fresh clause-id top-clause (1+ cur-clause-pos) cur-merge-positions cur-merge-lits))))

(defun merge-clause (clause clause-id top-clause)
  (merge-clause* clause clause clause-id top-clause 0 nil nil))

;; BINARY-FACTORS-FOR-LITERAL (lit clause lit-pos clause-id cur-clause-pos top-clause-id)
;; Given a literal in a clause, and its containing clause with lit removed,
;; find all moves of binary factors that may be extracted from lit and
;; the remaining literals in clause.
;; Note: if cur-clause-pos<lit-pos, then we do not perform factoring, as it would
;; be a duplicate factor (this is assuming this function is called by
;; FIND-ALL-BINARY-FACTORS*, and that factoring is done in order).
;; Note: We now do implicit merging upon factoring.
;; G. Passmore :: 12/22/05
;;
;; Updated to differentiate between SOS and USABLE at the ID level.
;; G.P. :: 11/14/06

(defun binary-factors-for-literal* (lit clause clause-fresh lit-pos clause-id cur-clause-pos top-clause-id)
  (if (endp clause) nil
    (let ((lit-pred (car (strip-negation lit)))
	  (cur-clause-lit-pred (car (strip-negation (car clause)))))
      (if (and (equal lit-pred cur-clause-lit-pred)
	       (iff (negative-literalp lit) (negative-literalp (car clause)))
	       (not (< cur-clause-pos lit-pos))
	       (not (equal lit (car clause))))
	  (mv-let (unified-instance mgu)
		  (unify (strip-negation lit) (strip-negation (car clause)))
		  (if (not (member unified-instance '(DNU OUT-OF-TIME)))
		      (let ((new-factor (remove-duplicates-equal (apply-unifier clause-fresh mgu)))) ;; We merge now implicitly.
			(cons (list (list 'S (1+ top-clause-id))
				    (list 'move :BINARY-FACTORING (list clause-id :PRODUCT-LITERALS (list lit-pos cur-clause-pos)))
				    new-factor)
			      (binary-factors-for-literal* lit (cdr clause) clause-fresh lit-pos clause-id (1+ cur-clause-pos) (1+ top-clause-id))))
		    (binary-factors-for-literal* lit (cdr clause) clause-fresh lit-pos clause-id (1+ cur-clause-pos) top-clause-id)))
	(binary-factors-for-literal* lit (cdr clause) clause-fresh lit-pos clause-id (1+ cur-clause-pos) top-clause-id)))))

(defun binary-factors-for-literal (lit clause lit-pos clause-id top-clause-id)
  (binary-factors-for-literal* lit clause clause
			       lit-pos clause-id 0 top-clause-id))

;; FIND-ALL-BINARY-FACTORS (clause clause-id top-clause-id cur-clause-pos)
;; G. Passmore :: 12/22/05

(defun find-all-binary-factors* (clause clause-fresh clause-id top-clause-id cur-clause-pos)
  (if (endp clause) nil
    (let ((cur-factors (binary-factors-for-literal (car clause) clause-fresh cur-clause-pos clause-id top-clause-id)))
      (cond ((consp cur-factors)
	     (append cur-factors (find-all-binary-factors* (cdr clause) clause-fresh clause-id (+ top-clause-id (len cur-factors)) (1+ cur-clause-pos))))
	    (t (find-all-binary-factors* (cdr clause) clause-fresh clause-id top-clause-id (1+ cur-clause-pos)))))))

(defun find-all-binary-factors (clause clause-id top-clause-id)
  (find-all-binary-factors* clause clause clause-id top-clause-id 0))

;; LINEAR-RESOLUTION (all-proof-moves top-clause-id last-cycle-top-clause)
;; Resolve all clauses within our set of proof moves that were not resolved together
;; in the previous cycle.
;; Note: I now discern the cur-clause-id for linear-resolution from all-proof-moves directly!
;; G. Passmore :: 12/23/05

(defun linear-resolution* (cur-clause0 remaining-proof-moves top-clause-id cur-clause-id0)
  (if (endp remaining-proof-moves) nil
    ;(if (not (and (< cur-clause-id0 (/ last-cycle-top-clause 3/2)) (< cur-clause-id1 last-cycle-top-clause))) ;; This is a silly heuristic of mine.
      (let ((new-resolvents (find-all-binary-resolvents cur-clause0 (extract-clause (car remaining-proof-moves))
							cur-clause-id0 (caar remaining-proof-moves) top-clause-id)))
	(append new-resolvents
		(linear-resolution* cur-clause0 (cdr remaining-proof-moves) (+ (len new-resolvents) top-clause-id)
				    cur-clause-id0 )))))

;;
;; ** New version of linear-resolution function, written on October 17th, 2006 **
;; The changes are now to allow full SOS usage at the linear-resolution level.
;;

(defun linear-resolution (sos-moves usable-moves top-clause-id prover-settings)
  (cond ((endp sos-moves) nil)
	(t (let ((max-clause-weight (get-setting prover-settings 'max-weight)))
	     (let (
		 ;(weight-schema (get-setting prover-settings 'weight-schema))
		   (new-sos-resolvents
		    (linear-resolution* (extract-clause (car sos-moves)) usable-moves
					top-clause-id (caar sos-moves))))
	       (append (filter-out-heavy-clauses new-sos-resolvents max-clause-weight)
		       (linear-resolution (cdr sos-moves) usable-moves (+ top-clause-id (len new-sos-resolvents)) prover-settings)))))))

;(defun linear-resolution (all-proof-moves top-clause-id last-cycle-top-clause)
;  (if (endp all-proof-moves) nil
;    (let ((new-resolvents (linear-resolution* (extract-clause (car all-proof-moves)) (cdr all-proof-moves) top-clause-id last-cycle-top-clause (caar all-proof-moves) 0)))
;      (append new-resolvents
;	      (linear-resolution (cdr all-proof-moves) (+ top-clause-id (len new-resolvents)) last-cycle-top-clause)))))

;; LINEAR-MERGING (all-proof-moves top-clause-id last-cycle-top-clause)
;; Merge all clauses within our set of proof moves that were not merged
;; in the previous cycle.
;; G. Passmore :: 12/23/05

(defun linear-merging (remaining-proof-moves top-clause-id last-cycle-top-clause cur-clause-id)
  (if (endp remaining-proof-moves) nil
     (let ((new-moves (if (> cur-clause-id last-cycle-top-clause)
                          (merge-clause (extract-clause (car remaining-proof-moves)) (caar remaining-proof-moves) top-clause-id)
                        nil)))
        (if (consp new-moves)
            (append (list new-moves) (linear-merging (cdr remaining-proof-moves) (+ top-clause-id (len new-moves)) last-cycle-top-clause (1+ cur-clause-id)))
          (linear-merging (cdr remaining-proof-moves) top-clause-id last-cycle-top-clause (1+ cur-clause-id))))))

(defun linear-factoring (remaining-proof-moves top-clause-id last-cycle-top-clause cur-clause-id)
  (if (endp remaining-proof-moves) nil
     (let ((new-moves (if (> cur-clause-id last-cycle-top-clause)
                          (find-all-binary-factors (extract-clause (car remaining-proof-moves)) (caar remaining-proof-moves) top-clause-id)
                         nil)))
        (if (consp new-moves)
            (append new-moves (linear-factoring (cdr remaining-proof-moves) (+ top-clause-id (len new-moves)) last-cycle-top-clause (1+ cur-clause-id)))
          (linear-factoring (cdr remaining-proof-moves) top-clause-id last-cycle-top-clause (1+ cur-clause-id))))))
