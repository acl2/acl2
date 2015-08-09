(in-package "ACL2")

(include-book "base")

#|
    Expressions:
        varp                    ;; variable
	constp                  ;; constant
	integerp
	arithmetic              ;; +, -
	boolean                 ;; 'true, 'false, and, or, not, =, <, >, <=, >=
	list operations         ;; append, member, etc.
|#

(defun bfix (x)  ;; If x is not our kind of boolean, make it so.
  (declare (xargs :guard t))
  (if (equal x ''false) ''false ''true))

(in-theory (disable bfix))

(defun lfix (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
	((constp x) nil)
	(t (cons (car x) (lfix (cdr x))))))

(defun expressionp (e)
  (declare (xargs :guard t))
  (cond ((null e) t)
	((varp e) t)
	((constp e) t)
	((integerp e) t)
	((atom e) nil)
	(t (and (expressionp (car e))
		(expressionp (cdr e))))))

(defun evaluated-expressionp (e)
  (declare (xargs :guard t))
  (cond ((null e) t)
	((constp e) t)
	((integerp e) t)
	((varp e) nil)
	((atom e) nil)
	((equal (len e) 3)
	 (and (not (member-equal (car e) (list '+ '- '= '< '<= 'equal 'and 'or
					       'member 'assoc 'append
					       'cons 'ith)))
	      (evaluated-expressionp (car e))
	      (evaluated-expressionp (cdr e))))

	((equal (len e) 2)
	 (and (not (member-equal (car e) (list 'not 'length 'car 'cdr)))
	      (evaluated-expressionp (car e))
	      (evaluated-expressionp (cdr e))))

	(t (and (evaluated-expressionp (car e))
		(evaluated-expressionp (cdr e))))))

(defthm varp-not-cons
  (not (varp (cons x y)))
  :hints (("Goal"
           :in-theory (enable varp))))

;;(defthm constp-evaluated-expressionp
;;  (implies (constp x)
;;	   (evaluated-expressionp x)))

;;--------------------------
;; variables and memory

(defun memoryp (x)  ;;
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (consp (car x))
		(varp (caar x))
		(evaluated-expressionp (cdar x))
		(memoryp (cdr x))))))

(defthm memory-is-alist
  (implies (memoryp mem)
	   (alistp mem))
  :rule-classes :forward-chaining)

(defthm memory-access-gives-evaluated-expressionp
  (implies (and (memoryp mem)
		(assoc-equal e mem))
	   (evaluated-expressionp (cdr (assoc-equal e mem)))))

(defun val (var mem)  ;; memory access
  (declare (xargs :guard (and (varp var)
			      (memoryp mem))))
  (if (assoc-equal var mem)
      (cdr (assoc-equal var mem))
      nil))

(in-theory (disable val))

(defun asgn (var val mem)
  (declare (xargs :guard (and (varp var)
			      (evaluated-expressionp val)
			      (memoryp mem))))
  (cond ((atom mem) (list (cons var val)))
	((equal (caar mem) var) (cons (cons var val) (cdr mem)))
	(t (cons (car mem) (asgn var val (cdr mem))))))

(defthm asgn-gives-memoryp
  (implies (and (varp var)
		(evaluated-expressionp e)
		(memoryp mem))
	   (memoryp (asgn var e mem))))

(defun myassoc (key lst)  ;;
  (declare (xargs :guard (true-listp lst)))
  (cond ((atom lst) ''false)
	((atom (car lst)) (myassoc key (cdr lst)))
	((equal key (caar lst)) (car lst))
	(t (myassoc key (cdr lst)))))

(defthm const-cons-expressionp
  (implies (not (expressionp x))
	   (not (constp (cons x y))))
  :hints (("Goal"
           :in-theory (enable constp))))

(defthm const-list-expressionp
  (implies (not (expressionp y))
	   (not (constp (list* x y z))))
  :hints (("Goal"
           :in-theory (enable constp varp))))

(defun evl2 (e mem)
  (declare (xargs :guard (and (expressionp e)
			      (memoryp mem))))
  (cond
   ((integerp e) e)
   ((constp e) e)
   ((varp e) (val e mem))  ;; undefined variables evaluate to nil;
   ((atom e) nil)          ;; junk atom evaluates  to nil;
   ((equal (len e) 3)
    (case
       (car e)
       (+ (+ (rfix (evl2 (second e) mem)) (rfix (evl2 (third e) mem))))
       (- (- (rfix (evl2 (second e) mem)) (rfix (evl2 (third e) mem))))

       (= (if (equal (rfix (evl2 (second e) mem)) (rfix (evl2 (third e) mem)))
	      ''true ''false))
       (< (if (< (rfix (evl2 (second e) mem)) (rfix (evl2 (third e) mem)))
	      ''true ''false))
       (<= (if (<= (rfix (evl2 (second e) mem)) (rfix (evl2 (third e) mem)))
	       ''true ''false))
       (equal (if (equal (evl2 (second e) mem) (evl2 (third e) mem))
		  ''true ''false))
       (and (if (and (equal (bfix (evl2 (second e) mem)) ''true)
		     (equal (bfix (evl2 (third e) mem)) ''true))
		''true ''false))
       (or (if (or (equal (bfix (evl2 (second e) mem)) ''true)
		   (equal (bfix (evl2 (third e) mem)) ''true))
	       ''true ''false))

       (member (if (member-equal (evl2 (second e) mem)
				 (lfix (evl2 (third e) mem)))
		   ''true
		 ''false))

       (assoc (myassoc (evl2 (second e) mem)
		       (lfix (evl2 (third e) mem))))

       (append (append (lfix (evl2 (second e) mem))
		       (lfix (evl2 (third e) mem))))

       (cons (cons (evl2 (second e) mem)
		   (evl2 (third e) mem)))

       (ith (ith (nfix (evl2 (second e) mem)) (lfix (evl2 (third e) mem))))

       (otherwise (cons (evl2 (car e) mem)
			(evl2 (cdr e) mem)))))

   ((equal (len e) 2)
    (case
       (car e)
       (not (if (equal (bfix (evl2 (second e) mem)) ''false)
		''true ''false))
       (length (length (lfix (evl2 (second e) mem))))

       (car (if (consp (lfix (evl2 (second e) mem)))
		(car (evl2 (second e) mem))
	      nil))

       (cdr (if (consp (lfix (evl2 (second e) mem)))
		(cdr (evl2 (second e) mem))
	      nil))

       (otherwise (cons (evl2 (car e) mem)
			(evl2 (cdr e) mem)))))

   (t (cons (evl2 (car e) mem)
	    (evl2 (cdr e) mem)))))

#|
(evl2 '(append ('a 'b 'c) (1 2 3)) nil)
(evl2 '(member 'b  ('a 'b 'c)) nil)
(evl2 '(length (a b c)) nil)
(evl2 '(cons 2 (a b c)) nil)
(evl2 '(car ('a 'b 'c)) nil)
(evl2 '(cdr ('a 'b 'c)) nil)
(evl2 '(ith 2 (a b c)) '((a . 10) (b . 20) (c . 30)))
|#

(defthm not-constp-cons-cons
  (not (constp (cons (cons x y) z)))
  :hints (("Goal"
           :in-theory (enable constp))))

(defthm const-evaluated-myassoc
  (implies (constp (cons lst1 lst2))
	   (evaluated-expressionp (myassoc key lst2)))
  :hints (("goal"
           :in-theory (enable constp))))

(defthm myassoc-evaluated
  (implies (and (evaluated-expressionp key)
		(evaluated-expressionp lst))
	   (evaluated-expressionp (myassoc key lst)))
  :hints (("goal"
	   :induct (myassoc key lst))))

(defthm constp-not-rationalp
  (implies (constp x)
	   (not (rationalp x)))
  :hints (("goal"
           :in-theory (enable constp))))

(defthm evaluated-expressionp-lfix
  (implies (evaluated-expressionp lst)
	   (evaluated-expressionp (lfix lst))))

(defthm evaluated-append
  (implies (and (evaluated-expressionp a)
		(evaluated-expressionp b))
	   (evaluated-expressionp (append (lfix a) b))))

(defthm evaluated-member
  (implies (evaluated-expressionp lst)
	   (evaluated-expressionp (member-equal x (lfix lst)))))

(defthm evaluated-ith
  (implies (evaluated-expressionp lst)
	   (evaluated-expressionp (ith x (lfix lst))))
  :hints (("Goal"
	   :do-not generalize
	   :induct (ith x lst))))

(defthm car-const-expr
  (implies (constp c)
	   (expressionp (car c)))
  :hints (("Goal"
           :in-theory (enable constp))))

(defthm cdr-const-expr
  (implies (constp c)
	   (expressionp (cadr c)))
  :hints (("Goal"
           :in-theory (enable constp varp))))

(defthm integer-or-constp-not-varp
  (implies (or (integerp x)
	       (constp x))
	   (not (varp x)))
  :hints (("Goal"
           :in-theory (enable varp constp))))

(defthm sum-not-varp
  (not (varp (+ x y)))
  :hints (("Goal"
           :in-theory (enable varp))))

(defthm expressionp-3
  (implies (and (expressionp e)
		(equal (len e) 3))
	   (and (expressionp (second e))
		(expressionp (third e))))
  :hints (("Goal"
           :in-theory (enable constp))))

(defthm expressionp-2
  (implies (and (expressionp e)
		(equal (len e) 2))
	   (expressionp (second e)))
  :hints (("Goal"
           :in-theory (enable constp))))

(defthm evaluated-val
  (implies (and (varp v)
		(memoryp mem))
	   (evaluated-expressionp (val v mem)))
  :hints (("Goal"
           :in-theory (enable varp val))))

(defthm evl2-expressionp
  (implies (and (memoryp mem)
		(expressionp e))
	   (evaluated-expressionp (evl2 e mem))))

(in-theory (disable expressionp-2 expressionp-3))
