;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Computed Hints Enhancements
;;
;;   Jun Sawada
;;   sawada@cs.utexas.edu
;;   University of Texas at Austin, 1999
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(program)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; use-hint-always: Apply hints whenever possible.
;
; This hint fires always.
; (defthm thm-name body
;   :hints ((use-hint-always (:cases '((< 0 b))))))
;
; This hint looks like a hint supplied to "Goal", but it is not
; exactly the same.  If you supply more than one hints for "Goal",
; only one hint is applied, and the other will never be applied.
; Use-hint-always applies the hint whenever it is allowed to.  For
; example, if you want to case-split on the condition (equal x 0),
; and then, for each case, you want to case-split on the condition
; (equal y 0), you can write a hint like
;
; (defthm thm-name body
;   :hints ((use-hint-always :cases '((equal x 0)))
;           (use-hint-always :cases '((equal y 0)))))
;
; Computational hints are removed once it is applied. So
; use-hint-always never keep applying its hint. (Should have been
; named use-hint-whenever-possible or something.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro use-hint-always (&rest hint)
  `',hint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; When-occur:  Find an term occurence and fire the hint.
;
; When term is found in the goal clause, hint is invoked.  An example
; usage follows:
;:hints ((when-occur (FETCHED-INST MT (MT-FINAL-ISA MT)
;				  (MT-IN-SPECULTV? MT))
;		       :cases ((b1p (MT-IN-SPECULTV? MT)))))
;
; The case split is performed when the expression (FETCHED-INST ...)
; is found.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-occur (term &rest hint)
  `(and (occur-lst ',term clause) ',hint))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; When-occur-&:  Find an term occurence and try another computed hint.
;
; Compination version of When-occur.  User can combine more than
; one combination version of computation hints.  For example you can
; apply hint like:
; hints ((when-occur-& (foo x)
;            (when-occur (bar x) :cases ((b1p (MT-IN-SPECULTV? MT)))))
; This applies only when both (foo x) and (bar x) appears in the
; goal.  You can combine unlimited number of computed hints macros.
; Combined computed hint macros should end with a non combination
; version just like in the example shown above.  Unless the all
; computed hint conditions are met and the hint is actually fired,
; the computed hint is not elimiated from the hint list.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-occur-& (term hint)
  `(and (occur-lst ',term clause) ,hint))

;(defun multiple-occur-check (terms)
;  (if (endp terms)
;      nil
;      (if (endp (cdr terms))
;	  `(occur-lst ',(car terms) clause)
;	  `(and (occur-lst ',(car terms) clause)
;	    ,(multiple-occur-check (cdr terms))))))

;(defmacro when-multiple-occur (terms &rest hint)
;  `(and ,(multiple-occur-check terms) ',hint))

(defun multiple-occur-check (terms clause)
  (if (endp terms)
      nil
      (if (endp (cdr terms))
	  (occur-lst (car terms) clause)
	  (and (occur-lst (car terms) clause)
	       (multiple-occur-check (cdr terms) clause)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  when-multiple-occur: Fire hint when multiple terms appear in the
;  clause
;
;  Example:
;  (defthm p-is-true-2 (p z)
;   :hints ((when-multiple-occur ((buz x) (bar x))
;               :use (:instance bar-or-buz (x z)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-multiple-occur (terms &rest hint)
  `(and (multiple-occur-check ',terms clause) ',hint))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Combination version of when-multiple-occur
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-multiple-occur-& (terms hint)
  `(and (multiple-occur-check ',terms clause) ,hint))


;; This is from ACL2 manual
;; This function print out the used computed hints to the display.
;; This function is helpful to debug computed hints.
;; Usage:
;; (defthm ....
;;  :hints (...  (show-hint  <computed-hint>) ....))
(defmacro show-hint (hint &optional marker)
  (cond
   ((and (consp hint)
         (stringp (car hint)))
    hint)
   (t
    `(let ((marker ,marker)
           (ans ,(if (symbolp hint)
                     `(,hint id clause world)
                   hint)))
       (if ans
           (prog2$
            (cw "~%***** Computed Hint~#0~[~/ (from hint ~x1)~]****~%~x2~%~%"
                (if (null marker) 0 1)
                marker
                (cons (string-for-tilde-@-clause-id-phrase id)
                      ans))
            ans)
         nil)))))

;
; Pattern match functions
;
; do not check if x is a cons.
(defun fmeta-varp (x)
  (and (equal (car x) '@) (symbolp (cadr x))))

(defun fmeta-var-name (x) (cadr x))

(defmacro mv2-or (first second)
  `(mv-let (flg val) ,first
    (if flg (mv flg val) ,second)))


; restriction on pattern matching.
;  We don't look into quoted constants.  Quoted constants should be literally
; equal to the pattern or match to a meta-variable as it is.
; Pattern Match returns the substitution for the outer-most matching pattern.
; There may be more than two subterms that match the same pattern.
(mutual-recursion
(defun pattern-match (pattern term subst)
  (cond ((variablep pattern)
	 (if (eq pattern term) (mv t subst) (mv nil nil)))
	((fquotep pattern)
	 (if (equal pattern term) (mv t subst) (mv nil nil)))
	((fmeta-varp pattern)
	 (let ((inst (assoc-eq (fmeta-var-name pattern) subst)))
	   (if inst
	       (if (equal term (cdr inst)) (mv t subst) (mv nil nil))
	       (mv t (cons (cons (fmeta-var-name pattern) term) subst)))))
	((and (not (variablep term))
	      (not (fquotep term))
	      (eq (ffn-symb pattern) (ffn-symb term)))
	 (pattern-match-lst (fargs pattern) (fargs term) subst))
	(t (mv nil nil))))

(defun pattern-match-lst (patterns terms subst)
  (cond ((and (null patterns) (null terms))
	 (mv t subst))
	((or (null patterns) (null terms)) (mv nil nil))
	(t (mv-let (flg new-subst)
		   (pattern-match (car patterns) (car terms) subst)
	      (if flg
		  (pattern-match-lst (cdr patterns) (cdr terms) new-subst)
		  (mv nil nil))))))
)


(mutual-recursion
(defun pattern-occur (pattern term subst)
  (if (or (variablep term) (fquotep term))
      (pattern-match pattern term subst)
      (mv2-or (pattern-match pattern term subst)
	      (pattern-occur-lst pattern (fargs term) subst))))

(defun pattern-occur-lst (patterns args subst)
  (cond ((null args) (mv nil nil))
	(t (mv2-or (pattern-occur patterns (car args) subst)
		   (pattern-occur-lst patterns (cdr args) subst)))))
)

(mutual-recursion
(defun subst-meta (pattern subst)
  (cond ((or (variablep pattern) (fquotep pattern))
	 pattern)
	((fmeta-varp pattern)
	 (let ((inst (assoc-eq (fmeta-var-name pattern) subst)))
	   (if inst (cdr inst) pattern)))
	(t (subst-meta-lst pattern subst))))

(defun subst-meta-lst (patterns subst)
  (if (null patterns)
      nil
      (cons (subst-meta (car patterns) subst)
	    (subst-meta-lst (cdr patterns) subst))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; when-pattern:  Fire hint when a pattern appears in the current
; clause
;
; The pattern is provided with an expression including
; "meta-variables".  Meta variables is denoted by a list of symbol @
; and another symbol.  For example (f x (@ x)) matches a term
; (f x z), by substituting z for (@ x).  The computed hint:
;
;  (defthm f-of-f-of-x (f (f y))
;     :hints ((when-pattern (f (@ z))
;                  :use (:instance f-is-true (x (@ z))))))
;
; is applied when a pattern (f (@ z)) is found.  Before applying the
; hint, the meta-variables in the hints are replaced with the
; corresponding expression.  In the example above, (f (f y)) matches
; (f (@ z)) and we use the lemma f-is-true with the substitution
; (f y) for x.
;
; Note: we do not provide the combination version of when-pattern
; hints.  Variable substitution makes its implementation difficult.
; Users are recommended to put the when-pattern macro at the end
; of combined hints.  For example:
;  (defthm f-iterated-2
;    (and (f x) (f (f x)) (f (f (f x))))
;    :hints ((when-not-GS-match-& ((0) nil . 0)
;              (when-pattern (f (@ v))
;                  :use ((:instance f-is-true ((x (@ v)))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-pattern (term &rest hint)
  `(mv-let (flg subst) (pattern-occur-lst ',term clause nil)
    (if flg (subst-meta ',hint subst) nil)))


(defun multiple-pattern-check (terms)
  (if (endp terms)
      nil
      (if (endp (cdr terms))
	  `(pattern-occur-lst ',(car terms) clause nil)
	  `(mv-let (flg subst) ,(multiple-pattern-check (cdr terms))
	    (if flg
		(pattern-occur-lst ',(car terms) clause subst)
		(mv nil nil))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; When-multi-patterns: Apply hints when a multiple pattern
; matches to (possibly distinct) subexpressions of the clause.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-multi-patterns (terms &rest hint)
  `(mv-let (flg subst) ,(multiple-pattern-check (reverse terms))
    (if flg (subst-meta ',hint subst) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; when-GS-match:  Apply hints when the goal spec match the pattern.
;
; The hint is applied to any subgoal whose goal spec falls into the
; given pattern. For example:
;
;  (defthm f-iterated
;    (and (f x) (f (f x)) (f (f (f x))))
;    :hints ((when-GS-match ((0) (*) . 0) :in-theory (enable f-is-true))))
;
; This hint fires for any "Subgoal n" where n is arbitrary positive
; integer. The goal spec is specified with clause ID with wild cards.
; It is better to give a number of examples to illustrate how to use
; clause ID with wild cards.
;
;          (* * . *)		Any goal-specs
;	   ((0 1 2) * 2)	"Subgoal  *1.2/n0.n1....ni''
;	   ((0) (1 2 *) . 0)	"Subgoal *1.2.n"
;	   ((0) (1 2 . *) . 0)	"Subgoal *1.2.n0.n1....ni
;	   ((3 *) (1 2) . *)	"[3]Subgoal *n0/1.2'n'
;
; A wild card can be any natural number or a list of natural numbers.
; However, the clause ID is always of form
; ((m1 m2 ... mj) (n1 n2 ... ni) l)
; the wild card can match only a limited type of objects.  For
; example, the first two * in goal pattern (* * . *) match lists of
; natural numbers, while the last * matches a natural number.

; See ACL2 manual for detailed ID clause document.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro when-GS-match (spec-pattern &rest hint)
  `(and (gs-pattern-match id ',spec-pattern) ',hint))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Combination version of when-GS-match.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-GS-match-& (spec-pattern hint)
  `(and (gs-pattern-match id ',spec-pattern) ,hint))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Complement version of when-GS-match. The hint is applied when
; the goal spec does not match the pattern.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-not-GS-match (spec-pattern &rest hint)
  `(and (not (gs-pattern-match id ',spec-pattern)) ',hint))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Combination version of when-not-GS-match
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-not-GS-match-& (spec-pattern hint)
  `(and (not (gs-pattern-match id ',spec-pattern)) ,hint))

(defun gsnum-pattern-match (id pattern)
  (or (equal pattern '*) (equal id pattern)))

(defun gslist-pattern-match (id pattern)
  (if (atom pattern)
      (if (equal pattern '*) T (equal id pattern))
    (if (atom id) nil
      (and (gsnum-pattern-match (car id) (car pattern))
	   (gslist-pattern-match (cdr id) (cdr pattern))))))

(defun gs-pattern-match (id pattern)
  (and (gslist-pattern-match (car id) (car pattern))
       (gslist-pattern-match (cadr id) (cadr pattern))
       (gsnum-pattern-match (cddr id) (cddr pattern))))

;; Asserted or Disasserted


(defmacro show-clause (hint)
  (cond
   ((and (consp hint)
         (stringp (car hint)))
    hint)
   (t
    `(let ((ans ,(if (symbolp hint)
                     `(,hint id clause world)
                   hint)))
       (prog2$
	(cw "~%***** Computed Hint~x0~%~x1~%~%"
	    clause
	    (cons (string-for-tilde-@-clause-id-phrase id)
		  ans))
	(if ans ans nil))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; When-occur-positive.  If a literal appeas positively in the target
;  clause.
; When-occur-negative.  If a literal appeas negatively in the target
;  clause.
;
; The target clause is internally represeted as a disjunction of
; literals. A literal is an expression or a negation of an expression.
; When an expression is a literal, it is consider to appear in the
; clause positively.  If the negation of an expression is a literal in
; the clause, it is consider to appear negatively.
;
; Consider following example:
;  (defthm complex-lemma
;    (and (implies (f x) (f (g x x)))
;         (implies (h (h y)) (and (h y) (g x y)))))
;   :hints ((when-occur-negative (h (h y))
;               :use (:instance h-h-x-is-false (x y)))
;           (when-occur-positive (f (g x x))
;               :use (:insance f-is-true (x (g x x))))))
;   :rule-classes nil)
;
; From the body of the lemma, three clauses are generated
;  ~ (f y) \/ (f (g x x))
;  ~ (h (h y)) \/ (h y)
;  ~ (h (h y)) \/ (g x y)
; (f y) and (h (h y)) appear neagively in these clauses, and
; (f (g x x)) (h y) and (g x y) appear positvely.
; As a result h-h-x-is-false is applied to the second and the third
; clauses, while f-is-true is applied to the first clause.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-occur-positive (literal &rest hint)
  `(and (member-equal ',literal clause) ',hint))

(defmacro when-occur-negative (literal &rest hint)
  `(and (member-equal '(not ,literal) clause) ',hint))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Combination version of when-occur-positive and when-occur-negative
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-occur-positive-& (literal hint)
  `(and (member-equal ',literal clause) ,hint))

(defmacro when-occur-negative-& (literal hint)
  `(and (member-equal '(not ,literal) clause) ,hint))

(defun pattern-positive-p (lit clause subst)
  (if (endp clause)
      (mv nil nil)
    (mv2-or (pattern-match lit (car clause) subst)
	    (pattern-positive-p lit (cdr clause) subst))))

(defun pattern-negative-p (lit clause subst)
  (if (endp clause)
      (mv nil nil)
    (mv2-or (pattern-match `(not ,lit) (car clause) subst)
	    (pattern-negative-p lit (cdr clause) subst))))

(defun multi-patterns-positive-p (lts clause subst)
  (if (endp lts)
      (mv t subst)
    (mv-let (flag new-subst) (pattern-positive-p (car lts) clause subst)
	 (if flag
	     (multi-patterns-positive-p (cdr lts) clause new-subst)
	   (mv nil nil)))))

(defun multi-patterns-negative-p (lts clause subst)
  (if (endp lts)
      (mv t subst)
    (mv-let (flag new-subst) (pattern-negative-p (car lts) clause subst)
	 (if flag
	     (multi-patterns-negative-p (cdr lts) clause new-subst)
	   (mv nil nil)))))



(defun multi-patterns-asserted-p (plit nlit clause subst)
  (mv-let (flg new-subst) (multi-patterns-positive-p plit clause subst)
	  (if flg
	      (multi-patterns-negative-p nlit clause new-subst)
	    (mv nil nil))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; when-pos/neg-occur
; Combined occurence of positive and negative clauses fire hint.
;
; Example
;  :hints ((when-pos/neg-occur ((f x)) ((g x))
;                  :use (g-implies-f)))
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro when-pos/neg-occur (plit nlit &rest hint)
  `(mv-let (flg subst) (multi-patterns-asserted-p ',plit ',nlit clause nil)
    (if flg (subst-meta ',hint subst) nil)))
