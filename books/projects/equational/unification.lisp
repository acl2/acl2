;; UTEP - Utrecht Texas Equational Prover
;; Written by Grant Olney Passmore {grant@math.utexas.edu}
;;
;; Unification routines.

(in-package "ACL2")
(include-book "general")

;; UNIFICATION
;;
;; Motivating example:
;; lit0 = (P x (f x y) (g (f (a) z)))    lit1 = (P u (f (g (a)) u) w)
;;
;; Searching for the MGU of lit0 and lit1 should yield:
;; pi = ( (u (g (a)))   (x (g (a)))   (y (g (a)))   (w (g (f (a) z))) ),
;; which when applied to lit0 and lit1 yields:
;;
;; lit0(pi) = (P (g (a)) (f (g (a)) (g (a))) (g (f (a) z))),
;; lit1(pi) = (P (g (a)) (f (g (a)) (g (a))) (g (f (a) z))).
;;
;; FIRST-UNMATCHED-SYMBOL-PAIR (lit0 lit1)
;; Given two literals, lit0 and lit1, return the first symbol upon
;; which they do not match.
;; G. Passmore : 12/22/05

(defun first-unmatched-symbol-pair (lit0 lit1)
  (if (or (and (equal lit0 nil) (equal lit1 nil))
	  (equal lit0 lit1)) nil
    (if (or (varp lit0) (varp lit1))
	(if (varp lit0) (list lit0 lit1) (list lit1 lit0)) ;; Orient the pair so that a variable is in the first position.
      (if (equal (car lit0) (car lit1))
	  (first-unmatched-symbol-pair (cdr lit0) (cdr lit1))
	(first-unmatched-symbol-pair (car lit0) (car lit1))))))

;; FUNCTION-SYMBOLS (lit)
;; Given a literal, lit, return a list of all function
;; symbols appearing within, possibly containing duplicates
;; (only a membership check will be done upon this list,
;; so duplicates are fine).
;; G. Passmore :: 12/22/05

;; FUNCTION-SYMBOLS* (lit cur-list)
;; This auxiliary function locates function symbols by noting that
;; they appear with an immediate left parenthesis.
;; Note that the literal here, lit*, is passed in as the cdr of the literal
;; given to the parent FUNCTION-SYMBOLS function, so that we omit the top-level
;; predicate.
;; G. Passmore :: 12/22/05

(defun function-symbols* (lit* cur-list)
  (if (equal lit* nil) cur-list
    (if (consp lit*)
	(if (consp (car lit*))
	    (function-symbols*
	     (cdr lit*)
	     (append (list (caar lit*)) (function-symbols* (cdar lit*) cur-list)))
	  (function-symbols* (cdr lit*) cur-list))
      nil)))

(defun function-symbols (lit)
  (cond ((consp lit) (function-symbols* (cdr lit) nil))
	 (t nil)))

;; PREDICATE-SYMBOL (lit)
;; Given a literal, lit, we return a list of the top-level predicate symbol,
;; which happens to just be the car.
;; G. Passmore :: 12/22/05

(defun predicate-symbol (lit)
  (cond ((consp lit) (list (car lit)))
	(t nil)))

;; VARIABLE-SYMBOLS (lit)
;; Given a literal, lit, we return a list of all variable symbols contained within.
;; G. Passmore :: 12/22/05

(defun variable-symbols (lit)
  (remove-elements (all-symbols* lit) (append (function-symbols lit) (predicate-symbol lit))))

;; DEEP-SUBST (sexpr old new)
;; Given a sexpr, return the result of replacing every occurrence of
;; old in sexpr with new.
;; G. Passmore :: 12/22/05

(defun deepsubst (sexpr old new)
  (cond ((equal sexpr old) new)
	((consp sexpr)
              (cons (deepsubst (car sexpr) old new)
                    (deepsubst (cdr sexpr) old new)))
	(t sexpr)))

;; DEEPMEMBER (sexpr element)
;; Given an element and a sexpr, return t if element is a member of sexpr,
;; totally traversing the sexpr tree.
;; Note: This is used for the OCCURS-CHECK.
;; G. Passmore :: 12/22/05

(defun deepmember (sexpr element)
  (cond ((equal sexpr element) t)
	((consp sexpr)
	 (or (deepmember (car sexpr) element)
	     (deepmember (cdr sexpr) element)))
	(t nil)))

;; APPLY-UNIFIER (form unifier)
;; Given a unifier, return the result of applying the unifier to a
;; form (either a literal or an entire clause).
;; G. Passmore : 12/22/05

(defun apply-unifier (form unifier)
  (if (endp unifier) form
    (let ((cur-subst (car unifier)))
      (apply-unifier
       (deepsubst form (car cur-subst) (cadr cur-subst))
       (cdr unifier)))))

;; NEGATIVE-LITERALP (lit)
;; Given a literal, return t if this literal is negative (i.e.
;; of the form (not (P x y)).
;; G. Passmore :: 12/22/05

(defun negative-literalp (lit)
  (equal (car lit) 'NOT))

;; STRIP-NEGATION (lit)
;; Given a literal, possibly negated, return the result of stripping
;; it of its negation symbol (i.e. (not (P x y)) becomes (P x y)).
;; If literal is not negated, return it unharmed.
;; G. Passmore :: 12/22/05

(defun strip-negation (lit)
  (if (negative-literalp lit)
      (cadr lit) lit))

;; LST-INTERSECTION (lst0 lst1)
;; Given two lists, lst0 and list1, return the list of their
;; intersecting elements.  Duplicates are OK.
;; G. Passmore :: 12/22/05

(defun lst-intersection (lst0 lst1)
  (if (or (endp lst0) (endp lst1)) nil
    (if (member-equal (car lst0) lst1)
	(cons (car lst0) (lst-intersection (cdr lst0) lst1))
      (lst-intersection (cdr lst0) lst1))))

;; CLAUSE-VARIABLE-SYMBOLS (clause)
;; Given a clause, return a list of variables appearing in
;; the entire clause.  We simply recur upon each literal
;; contained in clause, collecting the VARIABLE-SYMBOLS
;; in each of them.  Duplicates are OK.
;; G. Passmore :: 12/22/05

(defun clause-variable-symbols (clause)
  (if (endp clause) nil
    (append (variable-symbols (car clause))
	    (clause-variable-symbols (cdr clause)))))

;; CLAUSE-PREDICATE-SYMBOLS (clause)
;; Given a clause, return a list of all of its predicate symbols.
;; This is analogous to the above function, modulo the fact that
;; we must remove the negation from negative literals before passing
;; them to PREDICATE-SYMBOL.  Duplicates are OK.
;; G. Passmore :: 12/22/05

(defun clause-predicate-symbols (clause)
  (if (endp clause) nil
    (cons (predicate-symbol (strip-negation (car clause)))
	  (clause-predicate-symbols (cdr clause)))))

;; STANDARDIZE-CLAUSE (clause frozen-vars available-std-vars)
;; Given a clause, a list of frozen variables that must be renamed,
;; and a list of available unused standard variables to use,
;; return the result of performing substitutions upon clause
;; until its variables have been standardized.
;; G. Passmore :: 12/22/05

(defun standardize-clause (clause frozen-vars available-std-vars)
  (if (endp frozen-vars) clause
    (standardize-clause
     (deepsubst clause (car frozen-vars) (car available-std-vars))
     (cdr frozen-vars)
     (cdr available-std-vars))))

;; STANDARDIZE-APART (clause0 clause1)
;; Given two clauses, clause0 and clause1, we assign a new variable
;; name to every variable in clause1 that also appears in clause0.
;; We use *STANDARDIZE-APART-VARS-LST* to find unused variable names.
;; We return the adjusted clause1.
;; G. Passmore :: 12/22/05

(defun standardize-apart (clause0 clause1)
  (let ((clause0-vars (clause-variable-symbols clause0))
	(clause1-vars (clause-variable-symbols clause1)))
    (let ((c0-vars-intersect-c1-vars
	   (lst-intersection clause0-vars clause1-vars))
	  (usable-SAVL-vars
	   (remove-elements *standardize-apart-vars-lst* (append clause0-vars clause1-vars))))
      (standardize-clause clause1 (remove-duplicates c0-vars-intersect-c1-vars) usable-SAVL-vars))))

;; UNIFY (lit0 lit1) => (MV unified-instance mgu) | 'DNU | 'OUT-OF-TIME
;; Given two literals, lit0 and lit1, find and apply the most general unifier,
;; returning (mv lit0 NIL) if the terms are unified by the empty substitution,
;; returning (mv 'DNU nil) of the terms do not unify, and returning (mv unified-instance mgu)
;; if unification is successful.
;; Note: We may run out of time, in which case we return (mv 'OUT-OF-TIME nil).
;; We *do* utilize an occurs-check.
;; G. Passmore :: 12/22/05

(defun unify* (lit0 lit1 function-symbols predicate-symbols cur-mgu time-count)
  (declare (xargs :measure (acl2-count time-count)))
  (cond ((not (posp time-count)) (mv 'OUT-OF-TIME nil))
	((equal lit0 lit1) (mv lit0 cur-mgu))
	(t (let ((cur-unifier (first-unmatched-symbol-pair lit0 lit1)))
;; If the two literals disagree on a function symbol, they do not unify.
	     (cond ((and (member (car cur-unifier) function-symbols)
			 (member (cadr cur-unifier) function-symbols))
		    (mv 'DNU nil))
;; If the two literals disagree on a predicate symbol, they do not unify.
		   ((or (member (car cur-unifier) predicate-symbols)
			(member (cadr cur-unifier) predicate-symbols))
		    (mv 'DNU nil))
;; If the current unifier does not pass an OCCURS-CHECK, they do not unify.
		   ((and (consp (cadr cur-unifier))
			 (deepmember (cadr cur-unifier) (car cur-unifier))) (mv 'DNU nil))
;; Otherwise, we now perform the substitution and recur!
		   (t (unify* (deepsubst lit0 (car cur-unifier) (cadr cur-unifier))
			      (deepsubst lit1 (car cur-unifier) (cadr cur-unifier))
			      function-symbols predicate-symbols (list* cur-unifier cur-mgu) (1- time-count))))))))

;; Parent unification function: Given two literals, we return
;; a form of the species (mv unified-instance mgu) if lit0 and lit1
;; unify.  See above comments preceding UNIFY* for details on what
;; we return when unification fails.
;; G. Passmore :: 12/22/05

(defun unify (lit0 lit1)
  (unify* lit0 lit1
	  (append (function-symbols lit0) (function-symbols lit1))
	  (append (predicate-symbol lit0) (predicate-symbol lit1))
  nil 100))
