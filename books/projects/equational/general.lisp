;; UTEP - Utrecht Texas Equational Prover
;; Written by Grant Olney Passmore {grant@math.utexas.edu}
;;
;; General routines and declarations.

(in-package "ACL2")

;; *GLOBAL-MAX-CLAUSES*
;; A hard limit on max clauses.  We'll start selectively throwing some away
;; (certainly at the expense of completeness, but maybe helpful) when we
;; reach this point.
;; G. Passmore :: 12/24/05

(defconst *global-max-clauses* 10000)

;; *STANDARDIZE-APART-VARS-LIST*
;; Variable names we utilize when standardizing apart two clauses.
;; For now, I'll just define 36 of them.
;; G. Passmore :: 12/24/06

(defconst *standardize-apart-vars-lst*
  '(x y z u v w x1 y1 z1 u1 v1 w1 x2 y2 z3 u3 v3 w3 x4 y4 z4 u4 v4 w4 x5 y5 z5 u5 v5 w5 x6 y6 z6 u6 v6 w6))

;; *EQUALITY-SYMBOL*
;; The symbol that denotes the equality predicate.  This symbol will trigger
;; paramodulation inferences when appropriate (bounded by a paramodulation
;; application strategy).
;; G. Passmore :: 03/05/06

(defconst *equality-symbol* '=)

;; *DEF-CFG*
;; Default configuration constant, similar to Otter's `Auto' mode.
;; G. Passmore :: 11/06/06

(defconst *def-cfg*
  '( (raw-var-weight 2) ))

;; VARP (x)
;; Given x, return t if x is a variable.  We assume that x was passed in from
;; the top-level of the immediate predicate or subterm it appears in, and thus
;; x is a variable in that context iff it is not a cons.
;; G. Passmore :: 12/22/05

(defun varp (x)
  (not (consp x)))

;; REMOVE-ELEMENTS (lst elements)
;; Given a list, lst, and a list of elements contained in lst,
;; return the result of removing elements from lst.
;; G. Passmore :: 12/22/05

(defun remove-elements (lst elements)
  (cond ((endp lst) nil)
	((member-equal (car lst) elements)
	 (remove-elements (cdr lst) elements))
	(t (cons (car lst) (remove-elements (cdr lst) elements)))))

;; REMOVE-ELEMENTS-ONCE-EACH
;; Similar to above, but only affects one occurence per element flagged.
;; G. Passmore :: 12/24/05

(defun remove-elements-once-each (lst elements)
  (cond ((endp lst) nil)
	((member-equal (car lst) elements)
	 (remove-elements-once-each
	  (cdr lst)
	  (remove-elements elements (list (car lst)))))
	(t (cons (car lst) (remove-elements-once-each (cdr lst) elements)))))

;; ALL-SYMBOLS* (lst)
;; Given a list, lst, return all symbols contained within.
;; I need to define this as ALL-SYMBOLS in ACL2 is :program mode.
;; G. Passmore :: 12/22/05

(defun all-symbols* (lst)
  (cond ((equal lst nil) nil)
	((symbolp lst) (list lst))
	((consp lst) (append (all-symbols* (car lst))
			     (all-symbols* (cdr lst))))))


;;
;; Configuration is just done through an alist.
;;

(defun get-setting (prover-settings select)
  (cond ((endp prover-settings) nil) ; nil is default value
	((equal (caar prover-settings) select) (cadar prover-settings))
	(t (get-setting (cdr prover-settings) select))))

;; EXTRACT-CLAUSE (proof-move)
;; Given a single proof-move, extract its constituent clause.
;; G. Passmore :: 12/23/05

(defun extract-clause (proof-move)
  (caddr proof-move))

;; CLAUSE-MOVE-MEMBER (clause moves)

(defun clause-move-member (clause moves)
  (cond ((endp moves) nil)
	(t (or (equal clause
		      (extract-clause (car moves)))
	       (clause-move-member clause (cdr moves))))))

;; FILTER-DUPLICATES (new-moves sos-moves usable-moves)
;; A mild subsumption check that only checks to see if a newly derived clause in SOS
;; already exists in either SOS or USABLE.  Note, this check is totally nieve, and is
;; not even done modulo variable renaming.  More expensive redundancy and subsumption
;; checking will be done experimentally soon.

(defun filter-duplicates (new-moves sos-moves usable-moves)
  (cond ((endp new-moves) nil)
	((or (clause-move-member (extract-clause (car new-moves)) sos-moves)
	     (clause-move-member (extract-clause (car new-moves)) usable-moves))
	 (filter-duplicates (cdr new-moves) sos-moves usable-moves))
	(t (cons (car new-moves)
		 (filter-duplicates (cdr new-moves) sos-moves usable-moves)))))

(defun quad-filter-internal-dups (moves)
  (cond ((endp moves) nil)
	((clause-move-member (extract-clause (car moves)) (cdr moves))
	 (quad-filter-internal-dups (cdr moves)))
	(t (cons (car moves) (quad-filter-internal-dups (cdr moves))))))

;; CLAUSE-TAIL-RECURSIVE-CONS (a b)
;; A special version of CONS used when writing recursive functions
;; that would normally use CONS as the constructor for tail-recursion.
;; This special CONS will leave out a if clause(a) appears in clauseS(b).
;; G. Passmore :: 11/14/06

#|(defun ctr-cons (a b)
  (cond ((clause-move-member (extract-clause (car a)) b) b)
	(t (cons a b))))
|#

(defun ctr-cons (a b)
  (cons (filter-duplicates a b nil) b))

(defun ctr-append (a b)
  (cond ((clause-move-member (extract-clause (car a)) b) b)
	(t (append a b))))

;; COLLECT-ALL-TERMS (lit)
;; Given a literal, return all top-level terms.
;; Example: (*** '(not (G x (foo y (a))))) => (x (foo y (a)))
;; G. Passmore :: 03/07/06

(defun collect-all-terms (lit)
  (cond ((endp lit) nil)
	((equal (car lit) 'not) (collect-all-terms (cadr lit)))
	(t (cdr lit))))
